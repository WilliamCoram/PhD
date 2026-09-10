/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.PowerSeries.Basic
import PhD.LWX.PadicExpLog

/-!
# `p`-adic analytic functions on `1`-units (`p = 3`)

The analytic input to [Jacobs, *Slopes of Compact Hecke Operators*, Ch. 2]: the weight
character is evaluated as `κ(u) = exp₃(t log₃ u)` on `1`-units (§2.1 p. 29), and the
power-series version `κ(cx + d)` enters through the binomial expansion
`4^ρ = ∑ₕ 3^h (ρ choose h)` (loc. cit.).

The ultrametric exponential and logarithm themselves, with their convergence discs, live in
the `p`-generic development `PhD/LWX/PadicExpLog.lean` (namespace `LWX.PadicExpLog`, over an
abstract complete ultrametric field `K` with `‖p‖ < 1`, `p ≠ 2`).  This file is its `p = 3`
instance: the `p`-free declarations are re-exported into `JacobsSlash` unchanged, the
`‖3‖ < 1`-lemmas used downstream are restated in their original `p = 3` form (one-line
shims into the general lemmas at `p := 3`), and the genuinely `p = 3`-specific weight
material follows.

* `JacobsSlash.padicLog u` — `log u = ∑ (-1)ⁿ (u - 1)^(n+1) / (n+1)`, for `‖u - 1‖ < 1`.
* `JacobsSlash.padicExp w` — `exp w = ∑ wⁿ / n!`, for `‖w‖` below the radius `‖3‖^(1/2)`.
  (Both are `LWX.PadicExpLog.padicLog`/`padicExp`, re-exported.)
* `JacobsSlash.unitPow t u` — `u^t := exp (t * log u)`, the weight-`t` power of a `1`-unit.
* `JacobsSlash.binomialCoeff t n`, `JacobsSlash.binomialSeries t e` — the binomial series
  `(1 + ex)^t = ∑ₙ (t choose n) eⁿ xⁿ` as a formal power series.

Convergence-disc source for the standard facts: [Koblitz, *p-adic Numbers, p-adic
Analysis, and Zeta-Functions*, Ch. IV] (the thesis's own reference [Kob84]).
-/

open scoped Nat

namespace JacobsSlash

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The `p = 3` instance of `LWX.PadicExpLog`

`p`-free declarations are re-exported (same declarations, so `rw [padicLog]`-style unfolding
and the `@[simp]` attributes are unaffected); the `‖3‖ < 1` lemmas consumed by the rest of
`JacobsSlash` are restated in their `p = 3` form.  `Fact (Nat.Prime 3)` is
`Nat.fact_prime_three`, and `(3 : K) = ((3 : ℕ) : K)` is `Nat.cast_ofNat`, definitionally. -/

export LWX.PadicExpLog (padicLog padicExp padicLog_one padicExp_zero
  norm_eq_one_of_norm_sub_one_lt_one)

section LogExp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `(3 : K) ≠ 0` in characteristic zero, so `‖3‖ > 0`. -/
private lemma norm_three_pos : (0 : ℝ) < ‖(3 : K)‖ := norm_pos_iff.mpr (by norm_num)

variable (h3 : ‖(3 : K)‖ < 1)
include h3

omit [CompleteSpace K] [CharZero K] in
/-- Naturals coprime to `3` are units of norm one when `‖3‖ < 1`. -/
theorem norm_natCast_eq_one_of_coprime {n : ℕ} (hn : n.Coprime 3) : ‖(n : K)‖ = 1 :=
  LWX.PadicExpLog.norm_natCast_eq_one_of_coprime (p := 3) h3 hn

omit [CompleteSpace K] [CharZero K] in
/-- `‖n!‖² ≥ ‖3‖^(n-1)`, i.e. `2 v₃(n!) ≤ n - 1`. -/
theorem sq_norm_factorial_ge {n : ℕ} (hn : n ≠ 0) :
    ‖(3 : K)‖ ^ (n - 1) ≤ ‖((n ! : ℕ) : K)‖ ^ 2 :=
  LWX.PadicExpLog.sq_norm_factorial_ge (p := 3) h3 (by norm_num) hn

omit [CompleteSpace K] in
/-- `‖log u‖ ≤ ‖3‖` on the disc `‖u - 1‖ ≤ ‖3‖`. -/
theorem norm_padicLog_le {u : K} (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) : ‖padicLog u‖ ≤ ‖(3 : K)‖ :=
  LWX.PadicExpLog.norm_padicLog_le (p := 3) h3 hu

/-- `‖exp w - 1‖ ≤ ‖w‖` on the disc `‖w‖² < ‖3‖`. -/
theorem norm_padicExp_sub_one_le {w : K} (hw : ‖w‖ ^ 2 < ‖(3 : K)‖) :
    ‖padicExp w - 1‖ ≤ ‖w‖ :=
  LWX.PadicExpLog.norm_padicExp_sub_one_le (p := 3) h3 (by norm_num) hw

/-- `exp (a + b) = exp a * exp b` on the disc `‖·‖² < ‖3‖`. -/
theorem padicExp_add {a b : K} (ha : ‖a‖ ^ 2 < ‖(3 : K)‖) (hb : ‖b‖ ^ 2 < ‖(3 : K)‖) :
    padicExp (a + b) = padicExp a * padicExp b :=
  LWX.PadicExpLog.padicExp_add (p := 3) h3 (by norm_num) ha hb

/-- `‖log u‖ = ‖u - 1‖` on the disc `‖u - 1‖² < ‖3‖`. -/
theorem norm_padicLog_eq {u : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) : ‖padicLog u‖ = ‖u - 1‖ :=
  LWX.PadicExpLog.norm_padicLog_eq (p := 3) h3 (by norm_num) hu

/-- `exp (log u) = u` on the disc `‖u - 1‖² < ‖3‖`. -/
theorem padicExp_padicLog {u : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) :
    padicExp (padicLog u) = u :=
  LWX.PadicExpLog.padicExp_padicLog (p := 3) h3 (by norm_num) hu

/-- `log (u v) = log u + log v` on the disc `‖· - 1‖² < ‖3‖`. -/
theorem padicLog_mul {u v : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) (hv : ‖v - 1‖ ^ 2 < ‖(3 : K)‖) :
    padicLog (u * v) = padicLog u + padicLog v :=
  LWX.PadicExpLog.padicLog_mul (p := 3) h3 (by norm_num) hu hv

end LogExp

section UnitPow

/-- The weight-`t` power of a `1`-unit: `u^t := exp₃ (t log₃ u)`.  This is [Jacobs]'s
`κ(u) = (u)^t` (§2.1 pp. 22, 29: `κ(4) = 4^t`, `κ(cx+d) = exp₃(t log₃ (cx+d))`), the
only way the weight character is ever evaluated in Ch. 2. -/
noncomputable def unitPow (t u : K) : K := padicExp (t * padicLog u)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `1^t = 1`: the weight power of the trivial `1`-unit. -/
@[simp] theorem unitPow_one (t : K) : unitPow t (1 : K) = 1 := by
  simp [unitPow]

variable (h3 : ‖(3 : K)‖ < 1)
include h3

/-- Multiplicativity of `u ↦ u^t` on `1`-units with `‖u - 1‖ ≤ ‖3‖` and `‖t‖ ≤ 1`:
`(uv)^t = u^t v^t`.  The identity behind every `κ`-bookkeeping step of
[Jacobs] Lemma 2.11 and the `W³ = 1` scalar checks. -/
theorem unitPow_mul {t u v : K} (ht : ‖t‖ ≤ 1) (hu : ‖u - 1‖ ≤ ‖(3 : K)‖)
    (hv : ‖v - 1‖ ≤ ‖(3 : K)‖) : unitPow t (u * v) = unitPow t u * unitPow t v := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have hsq : ‖(3 : K)‖ ^ 2 < ‖(3 : K)‖ := by nlinarith
  have hu2 : ‖u - 1‖ ^ 2 < ‖(3 : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hu 2) hsq
  have hv2 : ‖v - 1‖ ^ 2 < ‖(3 : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hv 2) hsq
  have hbound : ∀ w : K, ‖w - 1‖ ≤ ‖(3 : K)‖ → ‖w - 1‖ ^ 2 < ‖(3 : K)‖ →
      ‖t * padicLog w‖ ^ 2 < ‖(3 : K)‖ := by
    intro w hw hw2
    refine lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) hsq
    rw [norm_mul, norm_padicLog_eq h3 hw2]
    calc ‖t‖ * ‖w - 1‖ ≤ 1 * ‖(3 : K)‖ := mul_le_mul ht hw (norm_nonneg _) zero_le_one
      _ = ‖(3 : K)‖ := one_mul _
  simp only [unitPow]
  rw [padicLog_mul h3 hu2 hv2, mul_add, padicExp_add h3 (hbound u hu hu2) (hbound v hv hv2)]

/-- The uniform `κ`-estimate: for `‖t‖ < 1` and `‖u - 1‖ ≤ ‖3‖`,
`‖u^t - 1‖ ≤ ‖t‖ * ‖3‖`.  This is [Jacobs] p. 38's "`exp₃(t(3 + 9L₀))` converges to an
element `1 + (2ω+1)t L₁`" in norm form (`‖t‖‖3‖ ≤ ‖t‖‖3‖^{1/2}·‖3‖^{1/2}`, so it is
finer than the `(2ω+1)t 𝒪`-form used there). -/
theorem norm_unitPow_sub_one_le {t u : K} (ht : ‖t‖ < 1) (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) :
    ‖unitPow t u - 1‖ ≤ ‖t‖ * ‖(3 : K)‖ := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have hsq : ‖(3 : K)‖ ^ 2 < ‖(3 : K)‖ := by nlinarith
  have hu2 : ‖u - 1‖ ^ 2 < ‖(3 : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hu 2) hsq
  have hw : ‖t * padicLog u‖ ≤ ‖t‖ * ‖(3 : K)‖ := by
    rw [norm_mul, norm_padicLog_eq h3 hu2]
    exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)
  have hw3 : ‖t * padicLog u‖ ≤ ‖(3 : K)‖ :=
    hw.trans (by
      calc ‖t‖ * ‖(3 : K)‖ ≤ 1 * ‖(3 : K)‖ := mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)
        _ = ‖(3 : K)‖ := one_mul _)
  have hdisc : ‖t * padicLog u‖ ^ 2 < ‖(3 : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hw3 2) hsq
  exact (norm_padicExp_sub_one_le h3 hdisc).trans hw

end UnitPow

section Binomial

/-- The generalised binomial coefficient `(t choose n) = t(t-1)⋯(t-n+1)/n!` in `K`.
[Jacobs] p. 29: "where by `(ρ choose h)` we mean `1/h! ∏ (ρ - k)`". -/
noncomputable def binomialCoeff (t : K) (n : ℕ) : K :=
  (∏ k ∈ Finset.range n, (t - k)) / (n ! : ℕ)

/-- The binomial series `(1 + e·x)^t = ∑ₙ (t choose n) eⁿ xⁿ` as a formal power series in
one variable.  [Jacobs] p. 29's expansion `4^ρ = ∑ₕ 3^h (ρ choose h)` in series form. -/
noncomputable def binomialSeries (t e : K) : PowerSeries K :=
  PowerSeries.mk fun n => binomialCoeff t n * e ^ n

omit [IsUltrametricDist K] [CompleteSpace K] in
set_option linter.unusedSectionVars false in
/-- `(t choose 0) = 1`: the empty product over the empty factorial. -/
@[simp] theorem binomialCoeff_zero (t : K) : binomialCoeff t 0 = 1 := by
  simp [binomialCoeff]

variable (h3 : ‖(3 : K)‖ < 1)
include h3

omit [CompleteSpace K] in
/-- The tail bound making the binomial series integral and `≡ 1`: for `‖t‖ < 1`,
`‖e‖² ≤ ‖3‖` and `1 ≤ n`, the coefficient satisfies
`‖(t choose n) eⁿ‖² ≤ ‖t‖² ‖3‖`  (i.e. `v((t choose n) eⁿ) ≥ v(t) + 1/2`, from
`v(n!) ≤ (n-1)/2` and `v(eⁿ) ≥ n/2`). -/
theorem sq_norm_binomialCoeff_mul_pow_le {t e : K} (ht : ‖t‖ < 1) (he : ‖e‖ ^ 2 ≤ ‖(3 : K)‖)
    {n : ℕ} (hn : n ≠ 0) :
    ‖binomialCoeff t n * e ^ n‖ ^ 2 ≤ ‖t‖ ^ 2 * ‖(3 : K)‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have hfacpos : (0 : ℝ) < ‖(((m + 1)! : ℕ) : K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hfac : ‖(3 : K)‖ ^ m ≤ ‖(((m + 1)! : ℕ) : K)‖ ^ 2 := by
    simpa using sq_norm_factorial_ge h3 (n := m + 1) (Nat.succ_ne_zero m)
  -- every factor `t - (k + 1)` of the tail of the product has norm at most one
  have htail : ‖∏ i ∈ Finset.range m, (t - ((i + 1 : ℕ) : K))‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_
    calc ‖t - ((i + 1 : ℕ) : K)‖ = ‖t + -((i + 1 : ℕ) : K)‖ := by rw [sub_eq_add_neg]
      _ ≤ max ‖t‖ ‖-((i + 1 : ℕ) : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖t‖ ‖((i + 1 : ℕ) : K)‖ := by rw [norm_neg]
      _ ≤ 1 := max_le ht.le (IsUltrametricDist.norm_natCast_le_one K _)
  -- so the whole product is controlled by its `k = 0` factor `t`
  have hprod : ‖∏ k ∈ Finset.range (m + 1), (t - (k : K))‖ ≤ ‖t‖ := by
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_zero, sub_zero, norm_mul]
    calc ‖∏ i ∈ Finset.range m, (t - ((i + 1 : ℕ) : K))‖ * ‖t‖ ≤ 1 * ‖t‖ :=
          mul_le_mul_of_nonneg_right htail (norm_nonneg _)
      _ = ‖t‖ := one_mul _
  have hnum : ‖∏ k ∈ Finset.range (m + 1), (t - (k : K))‖ ^ 2 ≤ ‖t‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hprod 2
  have hbc : ‖binomialCoeff t (m + 1)‖ ^ 2 ≤ ‖t‖ ^ 2 / ‖(3 : K)‖ ^ m := by
    rw [binomialCoeff, norm_div, div_pow]
    calc ‖∏ k ∈ Finset.range (m + 1), (t - (k : K))‖ ^ 2 / ‖(((m + 1)! : ℕ) : K)‖ ^ 2
        ≤ ‖t‖ ^ 2 / ‖(((m + 1)! : ℕ) : K)‖ ^ 2 := by gcongr
      _ ≤ ‖t‖ ^ 2 / ‖(3 : K)‖ ^ m :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
  have hepow : ‖e ^ (m + 1)‖ ^ 2 = (‖e‖ ^ 2) ^ (m + 1) := by rw [norm_pow]; ring
  calc ‖binomialCoeff t (m + 1) * e ^ (m + 1)‖ ^ 2
      = ‖binomialCoeff t (m + 1)‖ ^ 2 * (‖e‖ ^ 2) ^ (m + 1) := by
        rw [norm_mul, mul_pow, hepow]
    _ ≤ ‖t‖ ^ 2 / ‖(3 : K)‖ ^ m * ‖(3 : K)‖ ^ (m + 1) :=
        mul_le_mul hbc (pow_le_pow_left₀ (by positivity) he _) (by positivity) (by positivity)
    _ = ‖t‖ ^ 2 * ‖(3 : K)‖ := by
        field_simp
        ring

end Binomial

end JacobsSlash
