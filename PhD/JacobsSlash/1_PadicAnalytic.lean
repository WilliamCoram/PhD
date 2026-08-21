/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# `p`-adic analytic functions on `1`-units (`p = 3`)

The analytic input to [Jacobs, *Slopes of Compact Hecke Operators*, Ch. 2]: the weight
character is evaluated as `κ(u) = exp₃(t log₃ u)` on `1`-units (§2.1 p. 29), and the
power-series version `κ(cx + d)` enters through the binomial expansion
`4^ρ = ∑ₕ 3^h (ρ choose h)` (loc. cit.).  Mathlib has neither the ultrametric exponential
nor the ultrametric logarithm with their convergence discs, so this file develops them
over an abstract complete ultrametric field `K` with `‖3‖ < 1` (which forces the residue
characteristic to be `3`, hence `‖n‖ = ‖3‖ ^ (v₃ n)` for `n : ℕ`).

* `JacobsSlash.padicLog u` — `log u = ∑ (-1)ⁿ (u - 1)^(n+1) / (n+1)`, for `‖u - 1‖ < 1`.
* `JacobsSlash.padicExp w` — `exp w = ∑ wⁿ / n!`, for `‖w‖` below the radius `‖3‖^(1/2)`.
* `JacobsSlash.unitPow t u` — `u^t := exp (t * log u)`, the weight-`t` power of a `1`-unit.
* `JacobsSlash.binomialCoeff t n`, `JacobsSlash.binomialSeries t e` — the binomial series
  `(1 + ex)^t = ∑ₙ (t choose n) eⁿ xⁿ` as a formal power series.

Convergence-disc source for the standard facts: [Koblitz, *p-adic Numbers, p-adic
Analysis, and Zeta-Functions*, Ch. IV] (the thesis's own reference [Kob84]).
-/

open Filter Topology

open scoped Nat

namespace JacobsSlash

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

section ResidueChar

variable (h3 : ‖(3 : K)‖ < 1)
include h3

omit [CompleteSpace K] [CharZero K] in
set_option linter.unusedSectionVars false in
/-- If `‖3‖ < 1` in an ultrametric field, every natural number coprime to `3` has norm
one.  (Ultrametricity gives `‖n‖ ≤ 1`; if also `‖n‖ < 1` with `gcd n 3 = 1`, Bézout makes
`‖1‖ < 1`.) -/
theorem norm_natCast_eq_one_of_coprime {n : ℕ} (hn : n.Coprime 3) : ‖(n : K)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K n) (not_lt.mp fun hlt => ?_)
  have hb := Nat.gcd_eq_gcd_ab n 3
  rw [hn, Nat.cast_one] at hb
  have h1 : (1 : K) = (n : K) * ((n.gcdA 3 : ℤ) : K) + (3 : K) * ((n.gcdB 3 : ℤ) : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hb
    push_cast at this
    simpa using this
  have h2 : (1 : ℝ) ≤
      max (‖(n : K)‖ * ‖((n.gcdA 3 : ℤ) : K)‖) (‖(3 : K)‖ * ‖((n.gcdB 3 : ℤ) : K)‖) := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(n : K) * ((n.gcdA 3 : ℤ) : K) + (3 : K) * ((n.gcdB 3 : ℤ) : K)‖ := by rw [← h1]
      _ ≤ _ := by
          simpa only [norm_mul] using IsUltrametricDist.norm_add_le_max
            ((n : K) * ((n.gcdA 3 : ℤ) : K)) ((3 : K) * ((n.gcdB 3 : ℤ) : K))
  refine absurd h2 (not_le.mpr (max_lt ?_ ?_))
  · calc ‖(n : K)‖ * ‖((n.gcdA 3 : ℤ) : K)‖ ≤ ‖(n : K)‖ * 1 :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _)
    _ < 1 := by simpa using hlt
  · calc ‖(3 : K)‖ * ‖((n.gcdB 3 : ℤ) : K)‖ ≤ ‖(3 : K)‖ * 1 :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _)
    _ < 1 := by simpa using h3

omit [CompleteSpace K] [CharZero K] in
/-- `‖n‖ = ‖3‖ ^ v₃(n)` for `0 < n`: the norm on `ℕ ⊆ K` is determined by `‖3‖`. -/
theorem norm_natCast_eq_pow_padicValNat {n : ℕ} (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖(3 : K)‖ ^ padicValNat 3 n := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n 3]
  push_cast
  rw [norm_mul, norm_pow,
    norm_natCast_eq_one_of_coprime h3 ((Nat.coprime_ordCompl Nat.prime_three hn).symm),
    mul_one, Nat.factorization_def n Nat.prime_three]

omit [CompleteSpace K] [CharZero K] in
/-- Legendre bound in norm form: `‖(n! : K)‖ ≥ ‖3‖ ^ ((n - 1) / 2)` — more precisely
`‖3‖ ^ (n - 1) ≤ ‖(n !) : K‖ ^ 2`, the squared form avoiding half-integer exponents.
From `v₃(n!) = (n - s₃(n)) / 2 ≤ (n - 1) / 2` for `n ≥ 1`. -/
theorem sq_norm_factorial_ge {n : ℕ} (hn : n ≠ 0) :
    ‖(3 : K)‖ ^ (n - 1) ≤ ‖((n ! : ℕ) : K)‖ ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hleg := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := 3) hn
  rw [norm_natCast_eq_pow_padicValNat h3 n.factorial_ne_zero, ← pow_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) h3.le (by omega)

end ResidueChar

section NatAux

/-- `2 v ≤ 3 ^ v`. -/
private lemma two_mul_le_three_pow (v : ℕ) : 2 * v ≤ 3 ^ v := by
  induction v with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

/-- `4 v ≤ 3 ^ v + 3`. -/
private lemma four_mul_le_three_pow_add (v : ℕ) : 4 * v ≤ 3 ^ v + 3 := by
  induction v with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have h1 : 3 ≤ 3 ^ k := by
        calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [pow_succ]
      omega

/-- `3 ^ v₃(m) ≤ m` for `m ≠ 0`. -/
private lemma pow_padicValNat_three_le {m : ℕ} (hm : m ≠ 0) : 3 ^ padicValNat 3 m ≤ m :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hm) pow_padicValNat_dvd

/-- `2 v₃(m) ≤ m` for `m ≠ 0`: the exponent `m - v₃(m)` of the `m`-th term of a series with
denominator `m` is at least `m / 2`. -/
private lemma two_mul_padicValNat_three_le {m : ℕ} (hm : m ≠ 0) : 2 * padicValNat 3 m ≤ m := by
  have h1 := two_mul_le_three_pow (padicValNat 3 m)
  have h2 := pow_padicValNat_three_le hm
  omega

/-- `4 v₃(m) ≤ m + 3` for `m ≠ 0`: quantitative form of `m - 2 v₃(m) → ∞`. -/
private lemma four_mul_padicValNat_three_le {m : ℕ} (hm : m ≠ 0) :
    4 * padicValNat 3 m ≤ m + 3 := by
  have h1 := four_mul_le_three_pow_add (padicValNat 3 m)
  have h2 := pow_padicValNat_three_le hm
  omega

/-- `v₃(n + 1) ≤ n`: the `n`-th logarithm term loses at most `n` powers of `3` to its
denominator, so `‖3‖ ^ (n + 1) / ‖3‖ ^ v₃(n+1) ≤ ‖3‖`. -/
private lemma padicValNat_three_succ_le (n : ℕ) : padicValNat 3 (n + 1) ≤ n :=
  Nat.lt_succ_iff.mp <| (padicValNat_le_nat_log (n + 1)).trans_lt (Nat.log_lt_self 3 n.succ_ne_zero)

end NatAux

section LogExp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `(3 : K) ≠ 0` in characteristic zero, so `‖3‖ > 0`. -/
private lemma norm_three_pos : (0 : ℝ) < ‖(3 : K)‖ := norm_pos_iff.mpr (by norm_num)

/-- The ultrametric logarithm `log u = -∑ₙ (1 - u)^(n+1) / (n+1)`, converging for
`‖u - 1‖ < 1`; junk value otherwise.  [Kob84, Ch. IV §1]; used in [Jacobs] §2.1 p. 29 as
`log₃`. -/
noncomputable def padicLog (u : K) : K :=
  -∑' n : ℕ, (1 - u) ^ (n + 1) / (n + 1)

/-- The ultrametric exponential `exp w = ∑ₙ wⁿ / n!`, converging for
`‖w‖ < ‖3‖^(1/2)`; junk value otherwise.  [Kob84, Ch. IV §1]; `exp₃` of [Jacobs] p. 29. -/
noncomputable def padicExp (w : K) : K :=
  ∑' n : ℕ, w ^ n / (n ! : ℕ)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
set_option linter.unusedSectionVars false in
/-- `log 1 = 0`: every term of the series vanishes. -/
@[simp] theorem padicLog_one : padicLog (1 : K) = 0 := by
  simp [padicLog]

omit [IsUltrametricDist K] [CompleteSpace K] in
set_option linter.unusedSectionVars false in
/-- `exp 0 = 1`: only the constant term survives. -/
@[simp] theorem padicExp_zero : padicExp (0 : K) = 1 := by
  rw [padicExp, tsum_eq_single 0 fun b hb => by simp [zero_pow hb]]
  simp

omit [CompleteSpace K] [CharZero K] in
/-- A `1`-unit has norm one: `‖1 + x‖ = 1` as soon as `‖x‖ < 1`. -/
theorem norm_eq_one_of_norm_sub_one_lt_one {u : K} (hu : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have h : u = 1 + (u - 1) := by ring
  rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hu.ne'),
    norm_one, max_eq_left hu.le]

omit [CompleteSpace K] [CharZero K] in
/-- Dominated convergence for series in an ultrametric group: if all the families `F k` and the
limit family `G` are dominated by one `B` with `B → 0`, and `F k j → G j` for each fixed `j`,
then `∑' j, F k j → ∑' j, G j`.  (Elementary here: an ultrametric series is bounded by the sup
of its terms, so the domination controls the whole tail at once.) -/
private lemma tendsto_tsum_of_forall_norm_le {F : ℕ → ℕ → K} {G : ℕ → K} {B : ℕ → ℝ}
    (hF : ∀ k, Summable (F k)) (hG : Summable G) (hFB : ∀ k j, ‖F k j‖ ≤ B j)
    (hGB : ∀ j, ‖G j‖ ≤ B j) (hB : Tendsto B atTop (𝓝 0))
    (hlim : ∀ j, Tendsto (fun k => F k j) atTop (𝓝 (G j))) :
    Tendsto (fun k => ∑' j, F k j) atTop (𝓝 (∑' j, G j)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hB (ε / 2) (by linarith)
  have hfin : ∀ᶠ k in atTop, ∀ j ∈ Finset.range J, ‖F k j - G j‖ ≤ ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro j _
    have h0 : Tendsto (fun k => ‖F k j - G j‖) atTop (𝓝 0) := by
      simpa using ((hlim j).sub (tendsto_const_nhds (x := G j))).norm
    exact (h0.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith)).mono fun k hk => hk.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hfin
  refine ⟨N, fun k hk => ?_⟩
  have hterm : ∀ j, ‖F k j - G j‖ ≤ ε / 2 := by
    intro j
    rcases lt_or_ge j J with hj | hj
    · exact hN k hk j (Finset.mem_range.2 hj)
    · have hBj : B j ≤ ε / 2 := by
        have h := hJ j hj
        rw [Real.dist_eq, sub_zero] at h
        exact (le_abs_self _).trans h.le
      calc ‖F k j - G j‖ = ‖F k j + -G j‖ := by rw [sub_eq_add_neg]
        _ ≤ max ‖F k j‖ ‖-G j‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ ε / 2 := max_le ((hFB k j).trans hBj) (by rw [norm_neg]; exact (hGB j).trans hBj)
  calc dist (∑' j, F k j) (∑' j, G j) = ‖∑' j, (F k j - G j)‖ := by
        rw [(hF k).tsum_sub hG, dist_eq_norm]
    _ ≤ ε / 2 := IsUltrametricDist.norm_tsum_le_of_forall_le hterm
    _ < ε := by linarith

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `∏_{i < j} (-1 - i) = (-1)^j j !`: the value at `-1` of the polynomial `∏_{i<j} (X - i)`. -/
private lemma prod_range_neg_one_sub (j : ℕ) :
    (∏ i ∈ Finset.range j, ((-1 : K) - (i : K))) = (-1 : K) ^ j * ((j ! : ℕ) : K) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The binomial coefficient as a polynomial in its upper index:
`C(M, j) · j ! = ∏_{i < j} (M - i)` in a characteristic-zero field, for `j ≤ M`. -/
private lemma cast_choose_mul_factorial {M j : ℕ} (hj : j ≤ M) :
    ((M.choose j : ℕ) : K) * ((j ! : ℕ) : K) = ∏ i ∈ Finset.range j, ((M : K) - (i : K)) := by
  have h1 : ((M.descFactorial j : ℕ) : K) = ((j ! : ℕ) : K) * ((M.choose j : ℕ) : K) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have h2 : ((M.descFactorial j : ℕ) : K) = ∏ i ∈ Finset.range j, ((M : K) - (i : K)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    exact Finset.prod_congr rfl fun i hi =>
      Nat.cast_sub (le_trans (Finset.mem_range.mp hi).le hj)
  rw [← h2, h1, mul_comm]

variable (h3 : ‖(3 : K)‖ < 1)
include h3

/-- The logarithm series `∑ (1-u)^(n+1) / (n+1)` converges on the closed disc `‖u - 1‖² ≤ ‖3‖`
(which contains `‖u - 1‖ ≤ ‖3‖`, as `‖3‖ < 1`, and the exponential's disc `‖u - 1‖² < ‖3‖`).
The `n`-th squared term norm is `≤ ‖3‖ ^ ((n+1) - 2 v₃(n+1))`, and `4 v₃(m) ≤ m + 3` makes that
exponent grow at least like `(n - 2) / 2`. -/
theorem summable_padicLog_term {u : K} (hu : ‖u - 1‖ ^ 2 ≤ ‖(3 : K)‖) :
    Summable fun n : ℕ => (1 - u) ^ (n + 1) / ((n : K) + 1) := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have hbdd : ∀ n : ℕ, ‖(1 - u) ^ (n + 1) / ((n : K) + 1)‖ ^ 2 ≤ ‖(3 : K)‖ ^ ((n - 2) / 2) := by
    intro n
    set v := padicValNat 3 (n + 1) with hv
    have h2v : 2 * v ≤ n + 1 := two_mul_padicValNat_three_le (Nat.succ_ne_zero n)
    have h4v : 4 * v ≤ n + 1 + 3 := four_mul_padicValNat_three_le (Nat.succ_ne_zero n)
    have hcast : ((n : K) + 1) = ((n + 1 : ℕ) : K) := by push_cast; ring
    have hrev : ‖(1 : K) - u‖ = ‖u - 1‖ := norm_sub_rev 1 u
    rw [norm_div, norm_pow, hrev, hcast,
      norm_natCast_eq_pow_padicValNat h3 (Nat.succ_ne_zero n), ← hv, div_pow,
      div_le_iff₀ (pow_pos (pow_pos h3pos v) 2)]
    calc (‖u - 1‖ ^ (n + 1)) ^ 2 = (‖u - 1‖ ^ 2) ^ (n + 1) := by ring
      _ ≤ ‖(3 : K)‖ ^ (n + 1) := pow_le_pow_left₀ (sq_nonneg _) hu (n + 1)
      _ ≤ ‖(3 : K)‖ ^ ((n - 2) / 2 + 2 * v) :=
          pow_le_pow_of_le_one (norm_nonneg _) h3.le (by omega)
      _ = ‖(3 : K)‖ ^ ((n - 2) / 2) * (‖(3 : K)‖ ^ v) ^ 2 := by ring
  have hqt : Tendsto (fun n : ℕ => ‖(3 : K)‖ ^ ((n - 2) / 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h3).comp
      (tendsto_atTop_atTop.2 fun b => ⟨2 * b + 2, fun a ha => by omega⟩)
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [hqt.eventually_lt_const (show (0 : ℝ) < ε ^ 2 by positivity)] with n hn
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (lt_of_le_of_lt (hbdd n) hn)

omit [CompleteSpace K] in
/-- Norm bound for the logarithm on the small disc: if `‖u - 1‖ ≤ ‖3‖` then
`‖padicLog u‖ ≤ ‖3‖` (each term `(u-1)^(n+1)/(n+1)` has norm `≤ ‖3‖^(n+1) / ‖3‖^v₃(n+1)
≤ ‖3‖`).  [Jacobs] p. 38: "`log₃(−ν₃−1) = 3 + 9L₀`". -/
theorem norm_padicLog_le {u : K} (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) : ‖padicLog u‖ ≤ ‖(3 : K)‖ := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  rw [padicLog, norm_neg]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
  have hcast : ((n : K) + 1) = ((n + 1 : ℕ) : K) := by push_cast; ring
  have hrev : ‖(1 : K) - u‖ = ‖u - 1‖ := norm_sub_rev 1 u
  rw [norm_div, norm_pow, hrev, hcast,
    norm_natCast_eq_pow_padicValNat h3 (Nat.succ_ne_zero n), div_le_iff₀ (pow_pos h3pos _)]
  calc ‖u - 1‖ ^ (n + 1) ≤ ‖(3 : K)‖ ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) hu (n + 1)
    _ = ‖(3 : K)‖ * ‖(3 : K)‖ ^ n := by ring
    _ ≤ ‖(3 : K)‖ * ‖(3 : K)‖ ^ padicValNat 3 (n + 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg _) h3.le (padicValNat_three_succ_le n))
          (norm_nonneg _)

omit [CompleteSpace K] in
/-- Every nonconstant term of the exponential series is bounded by `‖w‖` on the closed disc
`‖w‖² ≤ ‖3‖`: squaring, `‖w‖^(2m) ≤ ‖w‖² ‖3‖^(m-1) ≤ ‖w‖² ‖m !‖²` by `sq_norm_factorial_ge`. -/
theorem norm_padicExp_term_le {w : K} (hw : ‖w‖ ^ 2 ≤ ‖(3 : K)‖) {m : ℕ} (hm : m ≠ 0) :
    ‖w ^ m / ((m ! : ℕ) : K)‖ ≤ ‖w‖ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hfac : (0 : ℝ) < ‖(((k + 1)! : ℕ) : K)‖ := by
    rw [norm_pos_iff, Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero _
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _) ?_
  rw [norm_div, norm_pow, div_pow, div_le_iff₀ (pow_pos hfac 2)]
  calc (‖w‖ ^ (k + 1)) ^ 2 = ‖w‖ ^ 2 * (‖w‖ ^ 2) ^ k := by ring
    _ ≤ ‖w‖ ^ 2 * ‖(3 : K)‖ ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hw k) (sq_nonneg _)
    _ ≤ ‖w‖ ^ 2 * ‖(((k + 1)! : ℕ) : K)‖ ^ 2 := by
        have h := sq_norm_factorial_ge h3 (n := k + 1) (Nat.succ_ne_zero k)
        simp only [Nat.add_sub_cancel] at h
        exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- The exponential series `∑ wⁿ / n !` converges on the open disc `‖w‖² < ‖3‖`: the squared
term norms are dominated by the geometric series of ratio `‖w‖² / ‖3‖ < 1`. -/
theorem summable_padicExp_term {w : K} (hw : ‖w‖ ^ 2 < ‖(3 : K)‖) :
    Summable fun n : ℕ => w ^ n / ((n ! : ℕ) : K) := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  set q : ℝ := ‖w‖ ^ 2 / ‖(3 : K)‖ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one h3pos).mpr hw
  have hbdd : ∀ k : ℕ, ‖w ^ (k + 1) / (((k + 1)! : ℕ) : K)‖ ^ 2 ≤ ‖w‖ ^ 2 * q ^ k := by
    intro k
    have hfac : ‖(3 : K)‖ ^ k ≤ ‖(((k + 1)! : ℕ) : K)‖ ^ 2 := by
      have h := sq_norm_factorial_ge h3 (n := k + 1) (Nat.succ_ne_zero k)
      simp only [Nat.add_sub_cancel] at h
      exact h
    rw [norm_div, norm_pow, div_pow]
    calc (‖w‖ ^ (k + 1)) ^ 2 / ‖(((k + 1)! : ℕ) : K)‖ ^ 2
        ≤ (‖w‖ ^ (k + 1)) ^ 2 / ‖(3 : K)‖ ^ k :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos h3pos k) hfac
      _ = ‖w‖ ^ 2 * q ^ k := by rw [hq, div_pow]; ring
  have hqt : Tendsto (fun k : ℕ => ‖w‖ ^ 2 * q ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (‖w‖ ^ 2)
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, ← tendsto_add_atTop_iff_nat 1, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [hqt.eventually_lt_const (show (0 : ℝ) < ε ^ 2 by positivity)] with k hk
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (lt_of_le_of_lt (hbdd k) hk)

/-- On the exponential's disc (`‖w‖² < ‖3‖`, i.e. `v(w) > 1/2 = 1/(p-1)` for `p = 3`),
`‖padicExp w - 1‖ ≤ ‖w‖`: the linear term dominates. -/
theorem norm_padicExp_sub_one_le {w : K} (hw : ‖w‖ ^ 2 < ‖(3 : K)‖) :
    ‖padicExp w - 1‖ ≤ ‖w‖ := by
  rw [padicExp, (summable_padicExp_term h3 hw).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, add_sub_cancel_left]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le fun n =>
    norm_padicExp_term_le h3 hw.le (Nat.succ_ne_zero n)

/-- Squared bound for the `(k+1)`-st exponential term: `‖w^(k+1)/(k+1)!‖² ≤ ‖w‖² (‖w‖²/‖3‖)ᵏ`.
This is the engine behind both the convergence of the series and the second-order estimate
`norm_padicExp_sub_one_sub_self`. -/
private lemma sq_norm_padicExp_term_le (w : K) (k : ℕ) :
    ‖w ^ (k + 1) / (((k + 1)! : ℕ) : K)‖ ^ 2 ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖(3 : K)‖) ^ k := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have hfac : ‖(3 : K)‖ ^ k ≤ ‖(((k + 1)! : ℕ) : K)‖ ^ 2 := by
    have h := sq_norm_factorial_ge h3 (n := k + 1) (Nat.succ_ne_zero k)
    simpa using h
  rw [norm_div, norm_pow, div_pow]
  calc (‖w‖ ^ (k + 1)) ^ 2 / ‖(((k + 1)! : ℕ) : K)‖ ^ 2
      ≤ (‖w‖ ^ (k + 1)) ^ 2 / ‖(3 : K)‖ ^ k :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos h3pos k) hfac
    _ = ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖(3 : K)‖) ^ k := by rw [div_pow]; ring

/-- On the exponential's disc the *real* series of term norms converges: the terms are bounded
by the geometric progression `‖w‖ (‖w‖²/‖3‖)^(k/2)`.  This absolute convergence is what the
Cauchy product formula needs. -/
theorem summable_norm_padicExp_term {w : K} (hw : ‖w‖ ^ 2 < ‖(3 : K)‖) :
    Summable fun n : ℕ => ‖w ^ n / ((n ! : ℕ) : K)‖ := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have hq0 : (0 : ℝ) ≤ ‖w‖ ^ 2 / ‖(3 : K)‖ := by positivity
  have hq1 : ‖w‖ ^ 2 / ‖(3 : K)‖ < 1 := (div_lt_one h3pos).mpr hw
  set r : ℝ := (1 + ‖w‖ ^ 2 / ‖(3 : K)‖) / 2 with hrdef
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hrsq : ‖w‖ ^ 2 / ‖(3 : K)‖ ≤ r ^ 2 := by
    rw [hrdef]; nlinarith [sq_nonneg (1 - ‖w‖ ^ 2 / ‖(3 : K)‖)]
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left ‖w‖)
  refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (by positivity) ?_
  calc ‖w ^ (k + 1) / (((k + 1)! : ℕ) : K)‖ ^ 2
      ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖(3 : K)‖) ^ k := sq_norm_padicExp_term_le h3 w k
    _ ≤ ‖w‖ ^ 2 * (r ^ 2) ^ k := by gcongr
    _ = (‖w‖ * r ^ k) ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Additivity of the ultrametric exponential on its disc:
`exp (a + b) = exp a * exp b` for `‖a‖² < ‖3‖`, `‖b‖² < ‖3‖`.  (Cauchy product plus the
binomial theorem; [Kob84, Ch. IV §2].) -/
theorem padicExp_add {a b : K} (ha : ‖a‖ ^ 2 < ‖(3 : K)‖) (hb : ‖b‖ ^ 2 < ‖(3 : K)‖) :
    padicExp (a + b) = padicExp a * padicExp b := by
  have key : ∀ n : ℕ, ∑ kl ∈ Finset.antidiagonal n,
      a ^ kl.1 / ((kl.1 ! : ℕ) : K) * (b ^ kl.2 / ((kl.2 ! : ℕ) : K))
      = (a + b) ^ n / ((n ! : ℕ) : K) := by
    intro n
    rw [(Commute.all a b).add_pow' n, Finset.sum_div]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    obtain ⟨i, j⟩ := kl
    rw [Finset.mem_antidiagonal] at hkl
    subst hkl
    have hi : ((i ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hj : ((j ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hC : (((i + j).choose i : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right i j)).ne'
    have hcast : (((i + j).choose i : ℕ) : K) * ((i ! : ℕ) : K) * ((j ! : ℕ) : K)
        = (((i + j)! : ℕ) : K) := by
      have h : (i + j).choose i * i ! * j ! = (i + j)! := by
        rw [Nat.choose_symm_add]
        exact Nat.add_choose_mul_factorial_mul_factorial i j
      exact_mod_cast congrArg (fun m : ℕ => (m : K)) h
    rw [nsmul_eq_mul, ← hcast]
    field_simp
  rw [padicExp, padicExp, padicExp, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_padicExp_term h3 ha) (summable_norm_padicExp_term h3 hb)]
  exact (tsum_congr key).symm

/-- Second-order estimate for the exponential on its disc: `‖exp w - 1 - w‖ ≤ ‖w‖² / ‖3‖`.
(The quadratic term `w²/2` already has norm `≤ ‖w‖²`, and `‖3‖ ≤ 1` absorbs the `1/2`.) -/
theorem norm_padicExp_sub_one_sub_self {w : K} (hw : ‖w‖ ^ 2 < ‖(3 : K)‖) :
    ‖padicExp w - 1 - w‖ ≤ ‖w‖ ^ 2 / ‖(3 : K)‖ := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have hsum := summable_padicExp_term h3 hw
  have hs1 : Summable fun n : ℕ => w ^ (n + 1) / (((n + 1)! : ℕ) : K) :=
    (summable_nat_add_iff (f := fun n : ℕ => w ^ n / ((n ! : ℕ) : K)) 1).2 hsum
  have h1 : padicExp w - 1 - w = ∑' m : ℕ, w ^ (m + 1 + 1) / (((m + 1 + 1)! : ℕ) : K) := by
    have e1 : padicExp w = 1 + ∑' n : ℕ, w ^ (n + 1) / (((n + 1)! : ℕ) : K) := by
      rw [padicExp, hsum.tsum_eq_zero_add]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have e2 : (∑' n : ℕ, w ^ (n + 1) / (((n + 1)! : ℕ) : K))
        = w + ∑' m : ℕ, w ^ (m + 1 + 1) / (((m + 1 + 1)! : ℕ) : K) := by
      rw [hs1.tsum_eq_zero_add]
      simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    rw [e1, e2]
    ring
  have hq0 : (0 : ℝ) ≤ ‖w‖ ^ 2 / ‖(3 : K)‖ := by positivity
  have hq1 : ‖w‖ ^ 2 / ‖(3 : K)‖ ≤ 1 := (div_le_one h3pos).2 hw.le
  rw [h1]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun m => ?_
  refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (by positivity) ?_
  calc ‖w ^ (m + 1 + 1) / (((m + 1 + 1)! : ℕ) : K)‖ ^ 2
      ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖(3 : K)‖) ^ (m + 1) := sq_norm_padicExp_term_le h3 w (m + 1)
    _ ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖(3 : K)‖) ^ 1 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 (by omega)) (by positivity)
    _ = ‖w‖ ^ 4 / ‖(3 : K)‖ := by ring
    _ ≤ ‖w‖ ^ 4 / ‖(3 : K)‖ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by nlinarith [norm_nonneg (3 : K), h3.le])
    _ = (‖w‖ ^ 2 / ‖(3 : K)‖) ^ 2 := by rw [div_pow]; ring

omit [CompleteSpace K] in
/-- Cubing a `1`-unit multiplies its distance to `1` by exactly `‖3‖`: on the disc
`‖u - 1‖² < ‖3‖` the cross terms `3(u-1)²` and `(u-1)³` are both dominated by `3(u-1)`. -/
theorem norm_cube_sub_one {u : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) :
    ‖u ^ 3 - 1‖ = ‖(3 : K)‖ * ‖u - 1‖ := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have hx1 : ‖u - 1‖ < 1 := lt_of_pow_lt_pow_left₀ 2 zero_le_one (by simpa using hu.trans h3)
  have hfact : u ^ 3 - 1 = (u - 1) * (3 + (3 * (u - 1) + (u - 1) ^ 2)) := by ring
  have hsmall : ‖3 * (u - 1) + (u - 1) ^ 2‖ < ‖(3 : K)‖ := by
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖(3 : K)‖ * ‖u - 1‖ < ‖(3 : K)‖ * 1 := mul_lt_mul_of_pos_left hx1 h3pos
        _ = ‖(3 : K)‖ := mul_one _
    · rw [norm_pow]
      exact hu
  rw [hfact, norm_mul, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsmall.ne',
    max_eq_left hsmall.le, mul_comm]

omit [CompleteSpace K] in
/-- Iterating `norm_cube_sub_one`: `‖u^(3^k) - 1‖ = ‖3‖^k ‖u - 1‖` on the disc.  This exact
(not merely bounded) decay is what makes the logarithm's limit description work. -/
theorem norm_pow_three_pow_sub_one {u : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) (k : ℕ) :
    ‖u ^ 3 ^ k - 1‖ = ‖(3 : K)‖ ^ k * ‖u - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ‖u ^ 3 ^ k - 1‖ ^ 2 < ‖(3 : K)‖ := by
      rw [ih, mul_pow]
      calc (‖(3 : K)‖ ^ k) ^ 2 * ‖u - 1‖ ^ 2 ≤ 1 * ‖u - 1‖ ^ 2 := by
            gcongr
            exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) h3.le)
        _ = ‖u - 1‖ ^ 2 := one_mul _
        _ < ‖(3 : K)‖ := hu
    have hpow : u ^ 3 ^ (k + 1) = (u ^ 3 ^ k) ^ 3 := by rw [pow_succ, pow_mul]
    rw [hpow, norm_cube_sub_one h3 hstep, ih, pow_succ]
    ring

/-- `exp` intertwines `3^k ·` with `(·)^(3^k)`, by iterated additivity. -/
theorem padicExp_pow_three_pow {w : K} (hw : ‖w‖ ^ 2 < ‖(3 : K)‖) (k : ℕ) :
    padicExp w ^ 3 ^ k = padicExp ((3 : K) ^ k * w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ‖(3 : K) ^ k * w‖ ^ 2 < ‖(3 : K)‖ := by
      rw [norm_mul, norm_pow, mul_pow]
      calc (‖(3 : K)‖ ^ k) ^ 2 * ‖w‖ ^ 2 ≤ 1 * ‖w‖ ^ 2 := by
            gcongr
            exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) h3.le)
        _ = ‖w‖ ^ 2 := one_mul _
        _ < ‖(3 : K)‖ := hw
    have hk2 : ‖(3 : K) ^ k * w + (3 : K) ^ k * w‖ ^ 2 < ‖(3 : K)‖ := by
      refine lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) hk
      simpa using IsUltrametricDist.norm_add_le_max ((3 : K) ^ k * w) ((3 : K) ^ k * w)
    rw [pow_succ, pow_mul, ih,
      show (3 : K) ^ (k + 1) * w = (3 : K) ^ k * w + ((3 : K) ^ k * w + (3 : K) ^ k * w) by ring,
      padicExp_add h3 hk hk2, padicExp_add h3 hk hk]
    ring

/-- **The logarithm as a limit** (Iwasawa): on the disc `‖u - 1‖² < ‖3‖`,
`log u = limₖ (u^(3^k) - 1)/3^k`.

The binomial expansion of `u^(3^k) - 1` has `j`-th coefficient
`C(3^k, j+1)/3^k = C(3^k - 1, j)/(j+1)`, which tends to `(-1)^j/(j+1)` because `3^k → 0` in
`K`; the uniform domination `‖(u-1)^(j+1) C(3^k, j+1)/3^k‖ ≤ ‖u-1‖^(j+1)/‖3‖^(v₃(j+1))` lets
one pass to the limit inside the sum.  This description is the engine for everything below:
it is visibly additive in `u`, which the series is not. -/
theorem tendsto_padicLog {u : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) :
    Tendsto (fun k : ℕ => (u ^ 3 ^ k - 1) / (3 : K) ^ k) atTop (𝓝 (padicLog u)) := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have h3ne : (3 : K) ≠ 0 := by norm_num
  set F : ℕ → ℕ → K := fun k j =>
    (u - 1) ^ (j + 1) * (((3 ^ k).choose (j + 1) : ℕ) : K) / (3 : K) ^ k with hFdef
  set G : ℕ → K := fun j => (-1 : K) ^ j * (u - 1) ^ (j + 1) / ((j : K) + 1) with hGdef
  set B : ℕ → ℝ := fun j => ‖u - 1‖ ^ (j + 1) / ‖(3 : K)‖ ^ padicValNat 3 (j + 1) with hBdef
  -- the shape of the terms after cancelling one power of `3`
  have hFalt : ∀ k j : ℕ,
      F k j = (u - 1) ^ (j + 1) * (((3 ^ k - 1).choose j : ℕ) : K) / ((j : K) + 1) := by
    intro k j
    have hNpos : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hj1 : ((j : K) + 1) ≠ 0 := by
      have : ((j : K) + 1) = ((j + 1 : ℕ) : K) := by push_cast; ring
      rw [this, Nat.cast_ne_zero]
      exact Nat.succ_ne_zero j
    have key : (3 : K) ^ k * (((3 ^ k - 1).choose j : ℕ) : K)
        = (((3 ^ k).choose (j + 1) : ℕ) : K) * ((j : K) + 1) := by
      have h := Nat.add_one_mul_choose_eq (3 ^ k - 1) j
      rw [Nat.sub_add_cancel hNpos] at h
      have h' := congrArg (fun m : ℕ => (m : K)) h
      push_cast at h'
      exact h'
    simp only [hFdef]
    rw [div_eq_div_iff (pow_ne_zero _ h3ne) hj1]
    calc (u - 1) ^ (j + 1) * (((3 ^ k).choose (j + 1) : ℕ) : K) * ((j : K) + 1)
        = (u - 1) ^ (j + 1) * ((((3 ^ k).choose (j + 1) : ℕ) : K) * ((j : K) + 1)) := by ring
      _ = (u - 1) ^ (j + 1) * ((3 : K) ^ k * (((3 ^ k - 1).choose j : ℕ) : K)) := by rw [key]
      _ = (u - 1) ^ (j + 1) * (((3 ^ k - 1).choose j : ℕ) : K) * (3 : K) ^ k := by ring
  -- the terms vanish beyond the binomial's range
  have hvanish : ∀ k : ℕ, ∀ j ∉ Finset.range (3 ^ k), F k j = 0 := by
    intro k j hj
    rw [Finset.mem_range, not_lt] at hj
    have hz : (3 ^ k).choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [hFdef, hz, Nat.cast_zero, mul_zero, zero_div]
  have hFsummable : ∀ k, Summable (F k) := fun k => summable_of_ne_finset_zero (hvanish k)
  -- the binomial expansion
  have hbin : ∀ N : ℕ, u ^ N - 1
      = ∑ j ∈ Finset.range N, (u - 1) ^ (j + 1) * ((N.choose (j + 1) : ℕ) : K) := by
    intro N
    have hpow : u ^ N = ((u - 1) + 1) ^ N := by ring
    rw [hpow, add_pow]
    simp only [one_pow, mul_one]
    rw [Finset.sum_range_succ']
    simp
  have hsum_eq : ∀ k : ℕ, (u ^ 3 ^ k - 1) / (3 : K) ^ k = ∑' j, F k j := by
    intro k
    rw [tsum_eq_sum (hvanish k), hbin, Finset.sum_div]
  -- the limit series is the logarithm
  have hterm : ∀ n : ℕ, -((1 - u) ^ (n + 1) / ((n : K) + 1)) = G n := by
    intro n
    have h1 : (1 : K) - u = -(u - 1) := by ring
    simp only [hGdef]
    rw [h1, neg_pow, pow_succ]
    ring
  have hlogeq : padicLog u = ∑' j, G j := by
    rw [padicLog, ← tsum_neg]
    exact tsum_congr hterm
  have hGsummable : Summable G := (summable_padicLog_term h3 hu.le).neg.congr hterm
  -- the uniform domination
  have hnormcast : ∀ j : ℕ, ‖((j : K) + 1)‖ = ‖(3 : K)‖ ^ padicValNat 3 (j + 1) := by
    intro j
    have hcast : ((j : K) + 1) = ((j + 1 : ℕ) : K) := by push_cast; ring
    rw [hcast, norm_natCast_eq_pow_padicValNat h3 (Nat.succ_ne_zero j)]
  have hFB : ∀ k j, ‖F k j‖ ≤ B j := by
    intro k j
    rw [hFalt k j, norm_div, norm_mul, norm_pow, hnormcast]
    simp only [hBdef]
    gcongr
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one K _)
  have hGnorm : ∀ j, ‖G j‖ = B j := by
    intro j
    simp only [hGdef, hBdef, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      hnormcast]
  -- the domination tends to zero
  have hq0 : (0 : ℝ) ≤ ‖u - 1‖ ^ 2 / ‖(3 : K)‖ := by positivity
  have hq1 : ‖u - 1‖ ^ 2 / ‖(3 : K)‖ < 1 := (div_lt_one h3pos).2 hu
  set r : ℝ := (1 + ‖u - 1‖ ^ 2 / ‖(3 : K)‖) / 2 with hrdef
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hrq : ‖u - 1‖ ^ 2 / ‖(3 : K)‖ ≤ r ^ 2 := by
    rw [hrdef]; nlinarith [sq_nonneg (1 - ‖u - 1‖ ^ 2 / ‖(3 : K)‖)]
  have hBr : ∀ j, B j ≤ r ^ (j + 1) := by
    intro j
    refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (by positivity) ?_
    have hge : ‖(3 : K)‖ ^ (j + 1) ≤ (‖(3 : K)‖ ^ padicValNat 3 (j + 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (norm_nonneg _) h3.le
        (by have := two_mul_padicValNat_three_le (m := j + 1) (Nat.succ_ne_zero j); omega)
    calc B j ^ 2
        = (‖u - 1‖ ^ 2) ^ (j + 1) / (‖(3 : K)‖ ^ padicValNat 3 (j + 1)) ^ 2 := by
          simp only [hBdef, div_pow, ← pow_mul, Nat.mul_comm]
      _ ≤ (‖u - 1‖ ^ 2) ^ (j + 1) / ‖(3 : K)‖ ^ (j + 1) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hge
      _ = (‖u - 1‖ ^ 2 / ‖(3 : K)‖) ^ (j + 1) := by rw [div_pow]
      _ ≤ (r ^ 2) ^ (j + 1) := by gcongr
      _ = (r ^ (j + 1)) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hBtend : Tendsto B atTop (𝓝 0) :=
    squeeze_zero (fun j => by simp only [hBdef]; positivity) hBr
      (by
        simpa [Function.comp_def] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1))
  -- termwise convergence of the binomial coefficients
  have hchoose : ∀ j : ℕ,
      Tendsto (fun k : ℕ => (((3 ^ k - 1).choose j : ℕ) : K)) atTop (𝓝 ((-1 : K) ^ j)) := by
    intro j
    have hfac : ((j ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hval := prod_range_neg_one_sub (K := K) j
    have hprod : Tendsto (fun k : ℕ => ∏ i ∈ Finset.range j, ((3 : K) ^ k - 1 - (i : K))) atTop
        (𝓝 (∏ i ∈ Finset.range j, ((-1 : K) - (i : K)))) := by
      refine tendsto_finsetProd _ fun i _ => ?_
      have h0 : Tendsto (fun k : ℕ => (3 : K) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one h3
      have h1 := (h0.sub_const (1 : K)).sub_const (i : K)
      rwa [zero_sub] at h1
    have hprod' : Tendsto
        (fun k : ℕ => (∏ i ∈ Finset.range j, ((3 : K) ^ k - 1 - (i : K))) / ((j ! : ℕ) : K))
        atTop (𝓝 ((-1 : K) ^ j)) := by
      have h := hprod.div_const ((j ! : ℕ) : K)
      rwa [hval, mul_div_assoc, div_self hfac, mul_one] at h
    refine hprod'.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop j] with k hk
    have hjk : j ≤ 3 ^ k - 1 := by
      have h1 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
      omega
    have h3sub : (((3 ^ k - 1 : ℕ)) : K) = (3 : K) ^ k - 1 := by
      have h1 : (1 : ℕ) ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
      rw [Nat.cast_sub h1]
      push_cast
      ring
    have hc := cast_choose_mul_factorial (K := K) hjk
    rw [h3sub] at hc
    rw [← hc, mul_div_assoc, div_self hfac, mul_one]
  have hFlim : ∀ j, Tendsto (fun k => F k j) atTop (𝓝 (G j)) := by
    intro j
    have h := ((hchoose j).const_mul ((u - 1) ^ (j + 1))).div_const ((j : K) + 1)
    rw [show (u - 1) ^ (j + 1) * (-1 : K) ^ j = (-1 : K) ^ j * (u - 1) ^ (j + 1) from
      mul_comm _ _] at h
    simpa only [hFalt, hGdef] using h
  simp only [hsum_eq, hlogeq]
  exact tendsto_tsum_of_forall_norm_le hFsummable hGsummable hFB (fun j => (hGnorm j).le)
    hBtend hFlim

/-- Sharp norm of the logarithm: `‖log u‖ = ‖u - 1‖` on the disc.  Every term of the
approximating sequence of `tendsto_padicLog` has norm exactly `‖u - 1‖`. -/
theorem norm_padicLog_eq {u : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) : ‖padicLog u‖ = ‖u - 1‖ := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have h := (tendsto_padicLog h3 hu).norm
  have hconst : (fun k : ℕ => ‖(u ^ 3 ^ k - 1) / (3 : K) ^ k‖) = fun _ : ℕ => ‖u - 1‖ := by
    funext k
    rw [norm_div, norm_pow, norm_pow_three_pow_sub_one h3 hu k,
      mul_div_cancel_left₀ _ (ne_of_gt (pow_pos h3pos k))]
  rw [hconst] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The logarithm is injective on the disc `‖u - 1‖² < ‖3‖`: the approximating sequences of
`u` and `v` differ by `v^(3^k)((u/v)^(3^k) - 1)/3^k`, whose norm is the constant `‖u - v‖`. -/
theorem eq_of_padicLog_eq {u v : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) (hv : ‖v - 1‖ ^ 2 < ‖(3 : K)‖)
    (h : padicLog u = padicLog v) : u = v := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have h3ne : (3 : K) ≠ 0 := by norm_num
  have hv1 : ‖v - 1‖ < 1 := lt_of_pow_lt_pow_left₀ 2 zero_le_one (by simpa using hv.trans h3)
  have hvnorm : ‖v‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one hv1
  have hv0 : v ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hvnorm
    exact zero_ne_one hvnorm
  have hquot : ‖u / v - 1‖ = ‖u - v‖ := by rw [div_sub_one hv0, norm_div, hvnorm, div_one]
  have hdisc : ‖u / v - 1‖ ^ 2 < ‖(3 : K)‖ := by
    rw [hquot]
    have hmax : ‖u - v‖ ≤ max ‖u - 1‖ ‖v - 1‖ := by
      calc ‖u - v‖ = ‖(u - 1) + -(v - 1)‖ := by congr 1; ring
        _ ≤ max ‖u - 1‖ ‖-(v - 1)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖u - 1‖ ‖v - 1‖ := by rw [norm_neg]
    rcases max_cases ‖u - 1‖ ‖v - 1‖ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hmax
    · exact lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hmax 2) hu
    · exact lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hmax 2) hv
  have hkey := (tendsto_padicLog h3 hu).sub (tendsto_padicLog h3 hv)
  rw [h, sub_self] at hkey
  have hnorm : ∀ k : ℕ,
      ‖(u ^ 3 ^ k - 1) / (3 : K) ^ k - (v ^ 3 ^ k - 1) / (3 : K) ^ k‖ = ‖u - v‖ := by
    intro k
    have hdiff : (u ^ 3 ^ k - 1) / (3 : K) ^ k - (v ^ 3 ^ k - 1) / (3 : K) ^ k
        = v ^ 3 ^ k * ((u / v) ^ 3 ^ k - 1) / (3 : K) ^ k := by
      rw [div_pow]
      field_simp
      ring
    rw [hdiff, norm_div, norm_mul, norm_pow, norm_pow, hvnorm, one_pow, one_mul,
      norm_pow_three_pow_sub_one h3 hdisc k, hquot,
      mul_div_cancel_left₀ _ (ne_of_gt (pow_pos h3pos k))]
  have hlim : Tendsto (fun _ : ℕ => ‖u - v‖) atTop (𝓝 0) := by
    have hn := hkey.norm
    simpa [hnorm] using hn
  have hzero : ‖u - v‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact sub_eq_zero.1 (norm_eq_zero.1 hzero)

/-- `log (exp w) = w` on the exponential's disc: by `padicExp_pow_three_pow` the approximating
sequence of `exp w` is `(exp (3^k w) - 1)/3^k = w + O(‖3‖^k)`. -/
theorem padicLog_padicExp {w : K} (hw : ‖w‖ ^ 2 < ‖(3 : K)‖) : padicLog (padicExp w) = w := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos
  have h3ne : (3 : K) ≠ 0 := by norm_num
  have hdisc : ‖padicExp w - 1‖ ^ 2 < ‖(3 : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) (norm_padicExp_sub_one_le h3 hw) 2) hw
  have hstep : ∀ k : ℕ, ‖(padicExp w ^ 3 ^ k - 1) / (3 : K) ^ k - w‖
      ≤ ‖(3 : K)‖ ^ k * (‖w‖ ^ 2 / ‖(3 : K)‖) := by
    intro k
    have hk : ‖(3 : K) ^ k * w‖ ^ 2 < ‖(3 : K)‖ := by
      rw [norm_mul, norm_pow, mul_pow]
      calc (‖(3 : K)‖ ^ k) ^ 2 * ‖w‖ ^ 2 ≤ 1 * ‖w‖ ^ 2 := by
            gcongr
            exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) h3.le)
        _ = ‖w‖ ^ 2 := one_mul _
        _ < ‖(3 : K)‖ := hw
    have hid : (padicExp w ^ 3 ^ k - 1) / (3 : K) ^ k - w
        = (padicExp ((3 : K) ^ k * w) - 1 - (3 : K) ^ k * w) / (3 : K) ^ k := by
      rw [padicExp_pow_three_pow h3 hw k]
      field_simp
    rw [hid, norm_div, norm_pow, div_le_iff₀ (by positivity)]
    calc ‖padicExp ((3 : K) ^ k * w) - 1 - (3 : K) ^ k * w‖
        ≤ ‖(3 : K) ^ k * w‖ ^ 2 / ‖(3 : K)‖ := norm_padicExp_sub_one_sub_self h3 hk
      _ = ‖(3 : K)‖ ^ k * (‖w‖ ^ 2 / ‖(3 : K)‖) * ‖(3 : K)‖ ^ k := by
          rw [norm_mul, norm_pow, mul_pow]
          ring
  refine tendsto_nhds_unique (tendsto_padicLog h3 hdisc) ?_
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm hstep ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h3).mul_const
    (‖w‖ ^ 2 / ‖(3 : K)‖)

/-- `exp (log u) = u` on the joint disc `‖u - 1‖² < ‖3‖`.  [Kob84, Ch. IV §2,
Proposition]. -/
theorem padicExp_padicLog {u : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) :
    padicExp (padicLog u) = u := by
  have hL : ‖padicLog u‖ ^ 2 < ‖(3 : K)‖ := by rw [norm_padicLog_eq h3 hu]; exact hu
  have hE : ‖padicExp (padicLog u) - 1‖ ^ 2 < ‖(3 : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) (norm_padicExp_sub_one_le h3 hL) 2) hL
  exact eq_of_padicLog_eq h3 hE hu (padicLog_padicExp h3 hL)

/-- The logarithm turns products of `1`-units into sums, on the joint disc.
Standard consequence of `padicExp_padicLog` and injectivity of `padicExp` on the disc. -/
theorem padicLog_mul {u v : K} (hu : ‖u - 1‖ ^ 2 < ‖(3 : K)‖) (hv : ‖v - 1‖ ^ 2 < ‖(3 : K)‖) :
    padicLog (u * v) = padicLog u + padicLog v := by
  have hLu : ‖padicLog u‖ ^ 2 < ‖(3 : K)‖ := by rw [norm_padicLog_eq h3 hu]; exact hu
  have hLv : ‖padicLog v‖ ^ 2 < ‖(3 : K)‖ := by rw [norm_padicLog_eq h3 hv]; exact hv
  have hsum : ‖padicLog u + padicLog v‖ ^ 2 < ‖(3 : K)‖ := by
    refine lt_of_le_of_lt
      (pow_le_pow_left₀ (norm_nonneg _) (IsUltrametricDist.norm_add_le_max _ _) 2) ?_
    rcases max_cases ‖padicLog u‖ ‖padicLog v‖ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
    · exact hLu
    · exact hLv
  have key : padicExp (padicLog u + padicLog v) = u * v := by
    rw [padicExp_add h3 hLu hLv, padicExp_padicLog h3 hu, padicExp_padicLog h3 hv]
  calc padicLog (u * v) = padicLog (padicExp (padicLog u + padicLog v)) := by rw [key]
    _ = padicLog u + padicLog v := padicLog_padicExp h3 hsum

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
