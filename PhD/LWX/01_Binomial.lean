/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import PhD.LWX.PadicExpLog
import PhD.QMF.Weight.Char

/-!
# The `p`-adic binomial theorem for an arbitrary exponent

`(1+x)^e = ∑_r C(e, r) x^r = exp(e·log(1+x))` for `e, x` in a complete ultrametric field `K`
with `‖p‖ < 1`, `p` odd, on the disc where both sides converge: `‖x‖ ≤ c`, `‖e‖·‖x‖ ≤ c`,
`c² < ‖p‖`.  The exponent `e` is **arbitrary** — in the lwx-seam application `e` is either
the normalised logarithm `ℓ⟨x⟩ ∈ 𝒪_K` of a `1`-unit (not in `ℤ_p` when `K/ℚ_p` is ramified)
or the halo exponent `s = log(1+T₀)/p` of norm `p‖T₀‖ > 1` — so the density-of-`ℕ` proof of
the Jacobs fork (`tsum_binomialCoeff_eq_unitPow`, which needs `e` in the closure of `ℕ`)
does not apply.

The proof is the identity theorem in the exponent: for fixed `x`, both sides are power
series in `e` with geometrically decaying coefficients (`chooseCoeff`), they agree at every
`e = n ∈ ℕ` (the finite binomial theorem and `exp(n·log u) = uⁿ`), and a series vanishing at
all natural numbers vanishes (`eq_zero_of_forall_tsum_natCast_eq_zero`, Strassman along
`p^k → 0`).

Source for the statement: [Koblitz, *p-adic Numbers*, Ch. IV §2]; [LWX, Notation 2.1] uses
`(1+T)^s = ∑ C(s,r)Tʳ` as the definition of the universal character.

## Main declarations

* `LWX.PadicExpLog.hasSum_choose_mul_pow` — **the binomial theorem**.
* `LWX.PadicExpLog.chooseCoeff`, `norm_chooseCoeff_le` — the exponent-series coefficients.
* `LWX.PadicExpLog.eq_zero_of_forall_tsum_natCast_eq_zero` — the identity theorem on `ℕ`.
-/

open Filter Topology

open scoped Nat

noncomputable section

namespace LWX.PadicExpLog

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

variable (h3 : ‖((p : ℕ) : K)‖ < 1) (hp2 : p ≠ 2)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem norm_p_pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ :=
  norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)

omit [CompleteSpace K] [CharZero K] in
private theorem norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `C(e, n)·n! = ∏_{k<n} (e − k)` over `K` (`Ring.descPochhammer_eq_factorial_smul_choose`,
read through `descPochhammer_map`). -/
theorem choose_mul_factorial (e : K) (n : ℕ) :
    Ring.choose e n * ((n ! : ℕ) : K) = ∏ k ∈ Finset.range n, (e - (k : K)) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose e n
  rw [nsmul_eq_mul, mul_comm] at h1
  rw [← h1, ← Polynomial.eval₂_smulOneHom_eq_smeval,
    show (RingHom.smulOneHom : ℤ →+* K) = Int.castRingHom K from RingHom.ext_int _ _,
    ← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range]

include h3 hp2

omit [CompleteSpace K] in
/-- The Legendre margin in inverse form: `‖1/r!‖ ≤ √(‖p‖⁻¹)^(r−1)` for `r ≥ 1`
(`sq_norm_factorial_ge`). -/
theorem norm_factorial_inv_le {r : ℕ} (hr : r ≠ 0) :
    ‖((r ! : ℕ) : K)‖⁻¹ ≤ Real.sqrt (‖((p : ℕ) : K)‖⁻¹) ^ (r - 1) := by
  have hP := norm_p_pos (p := p) (K := K)
  have hfac : (0 : ℝ) < ‖((r ! : ℕ) : K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r))
  have hs : Real.sqrt ‖((p : ℕ) : K)‖ ^ (r - 1) ≤ ‖((r ! : ℕ) : K)‖ := by
    rw [← pow_le_pow_iff_left₀ (by positivity) hfac.le two_ne_zero, ← pow_mul, mul_comm,
      pow_mul, Real.sq_sqrt hP.le]
    exact sq_norm_factorial_ge h3 hp2 hr
  rw [Real.sqrt_inv, inv_pow]
  exact inv_anti₀ (by positivity) hs

omit [IsUltrametricDist K] [CompleteSpace K] hp2 in
/-- `1 ≤ √(‖p‖⁻¹)`. -/
theorem one_le_sqrt_inv_norm_p : 1 ≤ Real.sqrt (‖((p : ℕ) : K)‖⁻¹) := by
  have hP := norm_p_pos (p := p) (K := K)
  have h := Real.sqrt_le_sqrt ((one_le_inv₀ hP).mpr h3.le)
  rwa [Real.sqrt_one] at h

omit [IsUltrametricDist K] [CompleteSpace K] h3 hp2 in
/-- `c² < ‖p‖` is the disc condition `c·√(‖p‖⁻¹) < 1`. -/
theorem mul_sqrt_inv_norm_p_lt_one {c : ℝ} (hc0 : 0 ≤ c) (hc : c ^ 2 < ‖((p : ℕ) : K)‖) :
    c * Real.sqrt (‖((p : ℕ) : K)‖⁻¹) < 1 := by
  have hP := norm_p_pos (p := p) (K := K)
  rw [Real.sqrt_inv, ← div_eq_mul_inv, div_lt_one (Real.sqrt_pos.mpr hP)]
  exact (Real.lt_sqrt hc0).mpr hc

omit [CompleteSpace K] h3 hp2 in
/-- The termwise bound: `‖C(e, r)·x^r‖ ≤ max(‖x‖, ‖e‖‖x‖)^r · ‖r!‖⁻¹` (every factor `e − k`
of the Pochhammer product has norm `≤ max(‖e‖, 1)`). -/
theorem norm_choose_mul_pow_le (e x : K) (r : ℕ) :
    ‖Ring.choose e r * x ^ r‖ ≤ max ‖x‖ (‖e‖ * ‖x‖) ^ r * ‖((r ! : ℕ) : K)‖⁻¹ := by
  have hfac : ((r ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hkey : Ring.choose e r * x ^ r
      = (∏ k ∈ Finset.range r, (e - (k : K))) * x ^ r / ((r ! : ℕ) : K) := by
    rw [eq_div_iff hfac, ← choose_mul_factorial e r]
    ring
  rw [hkey, norm_div, div_eq_mul_inv, norm_mul, norm_prod, norm_pow]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (norm_nonneg _))
  calc (∏ k ∈ Finset.range r, ‖e - (k : K)‖) * ‖x‖ ^ r
      ≤ (∏ _k ∈ Finset.range r, max ‖e‖ 1) * ‖x‖ ^ r := by
        refine mul_le_mul_of_nonneg_right
          (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_) (by positivity)
        exact (norm_sub_le_max' _ _).trans
          (max_le_max le_rfl (IsUltrametricDist.norm_natCast_le_one K k))
    _ = max ‖x‖ (‖e‖ * ‖x‖) ^ r := by
        rw [Finset.prod_const, Finset.card_range, ← mul_pow,
          max_mul_of_nonneg _ _ (norm_nonneg x), one_mul, max_comm]

/-- Summability of the binomial series on the disc `‖x‖ ≤ c`, `‖e‖‖x‖ ≤ c`, `c² < ‖p‖`
(the Legendre margin `‖p‖^(r−1) ≤ ‖r!‖²` of `sq_norm_factorial_ge`). -/
theorem summable_choose_mul_pow {c : ℝ} (hc : c ^ 2 < ‖((p : ℕ) : K)‖) {e x : K}
    (hx : ‖x‖ ≤ c) (hex : ‖e‖ * ‖x‖ ≤ c) :
    Summable fun r : ℕ => Ring.choose e r * x ^ r := by
  set q := Real.sqrt (‖((p : ℕ) : K)‖⁻¹) with hq
  have hq1 : 1 ≤ q := one_le_sqrt_inv_norm_p h3
  have hc0 : 0 ≤ c := (norm_nonneg x).trans hx
  have hcq : c * q < 1 := mul_sqrt_inv_norm_p_lt_one hc0 hc
  refine TateFredholm.summable_of_tendsto_cofinite ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (a := fun r : ℕ => (c * q) ^ r) (fun r => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hcq)
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · calc ‖Ring.choose e r * x ^ r‖
        ≤ max ‖x‖ (‖e‖ * ‖x‖) ^ r * ‖((r ! : ℕ) : K)‖⁻¹ := norm_choose_mul_pow_le e x r
      _ ≤ c ^ r * q ^ (r - 1) :=
          mul_le_mul (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg x)) (max_le hx hex) r)
            (norm_factorial_inv_le h3 hp2 hr.ne') (inv_nonneg.mpr (norm_nonneg _))
            (by positivity)
      _ ≤ (c * q) ^ r := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (Nat.sub_le r 1))
            (by positivity)

omit [IsUltrametricDist K] [CompleteSpace K] h3 hp2 in
/-- The finite binomial theorem, in the series shape: `∑_r C(n, r) x^r = (1 + x)^n`. -/
theorem tsum_choose_natCast_mul_pow (n : ℕ) (x : K) :
    ∑' r : ℕ, Ring.choose (n : K) r * x ^ r = (1 + x) ^ n := by
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun r hr => by
    rw [Finset.mem_range, not_lt] at hr
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]),
    add_comm (1 : K) x, add_pow]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Ring.choose_natCast, one_pow, mul_one, mul_comm]

/-- `exp(n·log(1+x)) = (1+x)^n` on the joint disc. -/
theorem padicExp_natCast_mul_padicLog (n : ℕ) {x : K} (hx : ‖x‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    padicExp ((n : K) * padicLog (1 + x)) = (1 + x) ^ n := by
  have hu : ‖(1 + x) - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ := by rwa [add_sub_cancel_left]
  have hw : ‖padicLog (1 + x)‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [norm_padicLog_eq h3 hp2 hu]
    exact hu
  rw [padicExp_natCast_mul h3 hp2 hw n, padicExp_padicLog h3 hp2 hu]

omit hp2 in
/-- **The identity theorem on `ℕ`**: a power series with geometrically decaying coefficients
that vanishes at every natural number is zero.  If `a_{j₀}` is the first nonzero coefficient,
at `n = p^k` the tail `∑_{j>j₀} a_j p^{k(j−j₀)}` is eventually smaller than
`‖a_{j₀}‖`, so `∑_j a_j (p^k)^j ≠ 0`. -/
theorem eq_zero_of_forall_tsum_natCast_eq_zero {a : ℕ → K} {C q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < 1) (ha : ∀ j, ‖a j‖ ≤ C * q ^ j) (h : ∀ n : ℕ, ∑' j, a j * (n : K) ^ j = 0) :
    ∀ j, a j = 0 := by
  by_contra hne
  push Not at hne
  classical
  obtain ⟨j₀, hj₀, hlt⟩ : ∃ j₀, a j₀ ≠ 0 ∧ ∀ j < j₀, a j = 0 :=
    ⟨Nat.find hne, Nat.find_spec hne, fun j hj => by simpa using Nat.find_min hne hj⟩
  have hP := norm_p_pos (p := p) (K := K)
  have hC : 0 ≤ C := (norm_nonneg (a 0)).trans (by simpa using ha 0)
  have hpos : 0 < ‖a j₀‖ / (C * q ^ (j₀ + 1) + 1) :=
    div_pos (norm_pos_iff.mpr hj₀) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos h3
  have hk' : C * q ^ (j₀ + 1) * ‖((p : ℕ) : K)‖ ^ k < ‖a j₀‖ := by
    calc C * q ^ (j₀ + 1) * ‖((p : ℕ) : K)‖ ^ k
        ≤ (C * q ^ (j₀ + 1) + 1) * ‖((p : ℕ) : K)‖ ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ < (C * q ^ (j₀ + 1) + 1) * (‖a j₀‖ / (C * q ^ (j₀ + 1) + 1)) :=
          mul_lt_mul_of_pos_left hk (by positivity)
      _ = ‖a j₀‖ := by field_simp
  obtain ⟨z, hz⟩ : ∃ z : K, z = ((p ^ k : ℕ) : K) := ⟨_, rfl⟩
  have hzn : ‖z‖ = ‖((p : ℕ) : K)‖ ^ k := by rw [hz, Nat.cast_pow, norm_pow]
  have hz0 : z ≠ 0 := by
    rw [hz]
    exact Nat.cast_ne_zero.mpr (pow_ne_zero k hp.out.ne_zero)
  have hterm : ∀ j, ‖a j * z ^ j‖ ≤ C * q ^ j := fun j => by
    rw [norm_mul, norm_pow, hzn]
    calc ‖a j‖ * (‖((p : ℕ) : K)‖ ^ k) ^ j ≤ ‖a j‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (pow_le_one₀ (by positivity) (pow_le_one₀ hP.le h3.le)) (norm_nonneg _)
      _ = ‖a j‖ := mul_one _
      _ ≤ C * q ^ j := ha j
  have hsum : Summable fun j => a j * z ^ j := by
    refine TateFredholm.summable_of_tendsto_cofinite ?_
    rw [Nat.cofinite_eq_atTop]
    exact squeeze_zero_norm hterm
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul C)
  have hshift : Summable fun i => a (i + (j₀ + 1)) * z ^ (i + (j₀ + 1)) :=
    hsum.comp_injective (add_left_injective _)
  have hsplit : (∑ i ∈ Finset.range (j₀ + 1), a i * z ^ i)
      + ∑' i, a (i + (j₀ + 1)) * z ^ (i + (j₀ + 1)) = ∑' i, a i * z ^ i :=
    Summable.sum_add_tsum_nat_add' (f := fun i => a i * z ^ i) (k := j₀ + 1) hshift
  have hzero : ∑' i, a i * z ^ i = 0 := by
    rw [hz]
    exact h (p ^ k)
  rw [hzero] at hsplit
  have hhead : ∑ i ∈ Finset.range (j₀ + 1), a i * z ^ i = a j₀ * z ^ j₀ := by
    have hz' : ∑ i ∈ Finset.range j₀, a i * z ^ i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hlt i (Finset.mem_range.mp hi), zero_mul]
    rw [Finset.sum_range_succ, hz', zero_add]
  have htail : ‖∑' i, a (i + (j₀ + 1)) * z ^ (i + (j₀ + 1))‖
      ≤ C * q ^ (j₀ + 1) * ‖((p : ℕ) : K)‖ ^ (k * (j₀ + 1)) := by
    refine (TateFredholm.norm_tsum_le_iSup hshift.tendsto_cofinite_zero).trans
      (ciSup_le fun i => ?_)
    rw [norm_mul, norm_pow, hzn, ← pow_mul]
    have h1 : ‖a (i + (j₀ + 1))‖ ≤ C * q ^ (j₀ + 1) :=
      (ha _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq.le (by omega)) hC)
    have h2 : ‖((p : ℕ) : K)‖ ^ (k * (i + (j₀ + 1))) ≤ ‖((p : ℕ) : K)‖ ^ (k * (j₀ + 1)) :=
      pow_le_pow_of_le_one hP.le h3.le (by nlinarith)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hheadn : ‖a j₀ * z ^ j₀‖ = ‖a j₀‖ * ‖((p : ℕ) : K)‖ ^ (k * j₀) := by
    rw [norm_mul, norm_pow, hzn, ← pow_mul]
  have hlt2 : ‖∑' i, a (i + (j₀ + 1)) * z ^ (i + (j₀ + 1))‖ < ‖a j₀ * z ^ j₀‖ := by
    refine htail.trans_lt ?_
    have hk2 : k * (j₀ + 1) = k + k * j₀ := by ring
    rw [hheadn, hk2, pow_add (‖((p : ℕ) : K)‖) k (k * j₀), ← mul_assoc]
    exact mul_lt_mul_of_pos_right hk' (pow_pos hP _)
  rw [hhead] at hsplit
  have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt2.ne'
  rw [hsplit, norm_zero, max_eq_left hlt2.le] at hmax
  exact hj₀ ((mul_eq_zero.mp (norm_eq_zero.mp hmax.symm)).resolve_right (pow_ne_zero _ hz0))

omit h3 hp2 in
/-- The coefficient of `e^j` in the binomial series `∑_r C(e, r) x^r`, read as a power series
in the exponent: `∑_r (coeff_j of descPochhammer_r)/r! · x^r`. -/
def chooseCoeff (x : K) (j : ℕ) : K :=
  ∑' r : ℕ, (((descPochhammer ℤ r).coeff j : ℤ) : K) / ((r ! : ℕ) : K) * x ^ r

/-- The coefficient bound `‖chooseCoeff x j‖ ≤ (‖x‖·√(‖p‖⁻¹))^j` on `‖x‖² < ‖p‖`
(the Pochhammer coefficients are integers, `‖1/r!‖ ≤ √(‖p‖⁻¹)^(r−1)`). -/
theorem norm_chooseCoeff_le {x : K} (hx : ‖x‖ ^ 2 < ‖((p : ℕ) : K)‖) (j : ℕ) :
    ‖chooseCoeff x j‖ ≤ (‖x‖ * Real.sqrt (‖((p : ℕ) : K)‖⁻¹)) ^ j := by
  set q := Real.sqrt (‖((p : ℕ) : K)‖⁻¹) with hq
  have hq1 : 1 ≤ q := one_le_sqrt_inv_norm_p h3
  have hxq : ‖x‖ * q < 1 := mul_sqrt_inv_norm_p_lt_one (norm_nonneg x) hx
  have hxq0 : 0 ≤ ‖x‖ * q := by positivity
  set F : ℕ → K := fun r => (((descPochhammer ℤ r).coeff j : ℤ) : K) / ((r ! : ℕ) : K) * x ^ r
    with hF
  have hterm : ∀ r, ‖F r‖ ≤ (‖x‖ * q) ^ r := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [hF]
      · rw [hF]
        simp only
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (show (descPochhammer ℤ 0).natDegree < j by rw [descPochhammer_natDegree]; exact hj),
          Int.cast_zero, zero_div, zero_mul, norm_zero]
        positivity
    · rw [hF]
      simp only
      rw [norm_mul, norm_div, norm_pow, div_eq_mul_inv]
      calc ‖(((descPochhammer ℤ r).coeff j : ℤ) : K)‖ * ‖((r ! : ℕ) : K)‖⁻¹ * ‖x‖ ^ r
          ≤ 1 * q ^ (r - 1) * ‖x‖ ^ r := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ ?_ (by positivity) zero_le_one)
              (by positivity)
            · exact IsUltrametricDist.norm_intCast_le_one K _
            · exact norm_factorial_inv_le h3 hp2 hr.ne'
        _ ≤ 1 * q ^ r * ‖x‖ ^ r := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ zero_le_one)
              (by positivity)
            exact pow_le_pow_right₀ hq1 (Nat.sub_le r 1)
        _ = (‖x‖ * q) ^ r := by rw [one_mul, mul_pow, mul_comm]
  have hterm' : ∀ r, ‖F r‖ ≤ (‖x‖ * q) ^ j := by
    intro r
    rcases lt_or_ge r j with hrj | hrj
    · rw [hF]
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt
        (show (descPochhammer ℤ r).natDegree < j by rw [descPochhammer_natDegree]; exact hrj)]
      positivity
    · exact (hterm r).trans (pow_le_pow_of_le_one hxq0 hxq.le hrj)
  have htend : Filter.Tendsto F Filter.cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop]
    exact squeeze_zero_norm hterm (tendsto_pow_atTop_nhds_zero_of_lt_one hxq0 hxq)
  exact (TateFredholm.norm_tsum_le_iSup htend).trans (ciSup_le hterm')

/-- The binomial series rearranged as a power series in the exponent (Fubini over the
absolutely convergent double family `(r, j) ↦ (descPochhammer_r)_j/r!·x^r·e^j`). -/
theorem tsum_choose_mul_pow_eq_tsum_chooseCoeff {c : ℝ} (hc : c ^ 2 < ‖((p : ℕ) : K)‖)
    {e x : K} (hx : ‖x‖ ≤ c) (hex : ‖e‖ * ‖x‖ ≤ c) :
    ∑' r : ℕ, Ring.choose e r * x ^ r = ∑' j : ℕ, chooseCoeff x j * e ^ j := by
  set q := Real.sqrt (‖((p : ℕ) : K)‖⁻¹) with hq
  have hq1 : 1 ≤ q := one_le_sqrt_inv_norm_p h3
  have hc0 : 0 ≤ c := (norm_nonneg x).trans hx
  have hcq : c * q < 1 := mul_sqrt_inv_norm_p_lt_one hc0 hc
  have hcq0 : 0 ≤ c * q := by positivity
  set F : ℕ → ℕ → K := fun r j =>
    (((descPochhammer ℤ r).coeff j : ℤ) : K) / ((r ! : ℕ) : K) * x ^ r * e ^ j with hF
  have hF0 : ∀ r j, r < j → F r j = 0 := fun r j hrj => by
    simp [hF, Polynomial.coeff_eq_zero_of_natDegree_lt
      (show (descPochhammer ℤ r).natDegree < j by rw [descPochhammer_natDegree]; exact hrj)]
  have hFb : ∀ r j, ‖F r j‖ ≤ (c * q) ^ r := by
    intro r j
    rcases lt_or_ge r j with hrj | hrj
    · rw [hF0 r j hrj, norm_zero]
      positivity
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · obtain rfl : j = 0 := by omega
      simp [hF]
    have hxe : ‖x‖ ^ r * ‖e‖ ^ j ≤ c ^ r := by
      calc ‖x‖ ^ r * ‖e‖ ^ j = ‖x‖ ^ (r - j) * (‖e‖ * ‖x‖) ^ j := by
            rw [show ‖x‖ ^ r = ‖x‖ ^ (r - j) * ‖x‖ ^ j by
              rw [← pow_add, Nat.sub_add_cancel hrj], mul_pow]
            ring
        _ ≤ c ^ (r - j) * c ^ j :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _)
              (pow_le_pow_left₀ (by positivity) hex _) (by positivity) (by positivity)
        _ = c ^ r := by rw [← pow_add, Nat.sub_add_cancel hrj]
    rw [hF]
    simp only
    rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, div_eq_mul_inv]
    calc ‖(((descPochhammer ℤ r).coeff j : ℤ) : K)‖ * ‖((r ! : ℕ) : K)‖⁻¹ * ‖x‖ ^ r * ‖e‖ ^ j
        ≤ 1 * q ^ r * c ^ r := by
          rw [mul_assoc (_ * _)]
          refine mul_le_mul (mul_le_mul (IsUltrametricDist.norm_intCast_le_one K _)
            ((norm_factorial_inv_le h3 hp2 hr.ne').trans (pow_le_pow_right₀ hq1 (Nat.sub_le r 1)))
            (by positivity) zero_le_one) hxe (by positivity) (by positivity)
      _ = (c * q) ^ r := by rw [one_mul, mul_pow, mul_comm]
  have hFs : Summable (Function.uncurry F) := by
    refine TateFredholm.summable_of_tendsto_cofinite ?_
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hcq0 hcq).eventually (gt_mem_nhds hε))
    rw [Filter.eventually_cofinite]
    refine ((Finset.range R).finite_toSet.prod (Finset.range R).finite_toSet).subset
      fun rj hrj => ?_
    have hε' : ε ≤ ‖Function.uncurry F rj‖ := not_lt.mp hrj
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · rw [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      rw [not_lt] at hcon
      have := (hFb rj.1 rj.2).trans_lt (hR _ hcon)
      exact absurd (hε'.trans_lt this) (lt_irrefl _)
    · rw [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      rw [not_lt] at hcon
      rcases lt_or_ge rj.1 rj.2 with h1 | h1
      · have : ‖Function.uncurry F rj‖ = 0 := by
          rw [show Function.uncurry F rj = F rj.1 rj.2 from rfl, hF0 _ _ h1, norm_zero]
        linarith
      · have := (hFb rj.1 rj.2).trans_lt (hR _ (le_trans hcon h1))
        exact absurd (hε'.trans_lt this) (lt_irrefl _)
  have hrow : ∀ r, Summable (F r) := fun r => hFs.prod_factor r
  have hcol : ∀ j, Summable fun r => F r j := fun j => hFs.prod_symm.prod_factor j
  calc ∑' r : ℕ, Ring.choose e r * x ^ r = ∑' r, ∑' j, F r j := by
        refine tsum_congr fun r => ?_
        rw [tsum_eq_sum (s := Finset.range (r + 1)) fun j hj => hF0 r j (by
          rw [Finset.mem_range, not_lt] at hj; omega)]
        have hfac : ((r ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
        have hev : ∑ j ∈ Finset.range (r + 1), (((descPochhammer ℤ r).coeff j : ℤ) : K) * e ^ j
            = Ring.choose e r * ((r ! : ℕ) : K) := by
          rw [choose_mul_factorial, ← descPochhammer_eval_eq_prod_range,
            Polynomial.eval_eq_sum_range' (n := r + 1)
              (by rw [descPochhammer_natDegree]; exact Nat.lt_succ_self r),
            ← descPochhammer_map (Int.castRingHom K) r]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Polynomial.coeff_map, eq_intCast]
        rw [← mul_div_cancel_right₀ (Ring.choose e r * x ^ r) hfac, mul_right_comm, ← hev,
          Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hF]
        simp only
        ring
    _ = ∑' j, ∑' r, F r j := (hFs.tsum_comm' hrow hcol).symm
    _ = ∑' j : ℕ, chooseCoeff x j * e ^ j := by
        refine tsum_congr fun j => ?_
        rw [chooseCoeff, ← tsum_mul_right]

omit [IsUltrametricDist K] [CompleteSpace K] h3 hp2 in
/-- `exp(e·L)` as a power series in `e`: `∑_j (L^j/j!)·e^j`. -/
theorem padicExp_mul_eq_tsum (e x : K) :
    padicExp (e * padicLog (1 + x))
      = ∑' j : ℕ, padicLog (1 + x) ^ j / ((j ! : ℕ) : K) * e ^ j := by
  unfold padicExp
  exact tsum_congr fun j => by rw [mul_pow]; ring

/-- **The exponent-coefficients agree**: `chooseCoeff x j = log(1+x)^j/j!` — both series in
`e` take the value `(1+x)^n` at every `e = n ∈ ℕ`, so the identity theorem applies. -/
theorem chooseCoeff_eq_padicLog_pow_div_factorial {c : ℝ} (hc : c ^ 2 < ‖((p : ℕ) : K)‖)
    {x : K} (hx : ‖x‖ ≤ c) (j : ℕ) :
    chooseCoeff x j = padicLog (1 + x) ^ j / ((j ! : ℕ) : K) := by
  set q := Real.sqrt (‖((p : ℕ) : K)‖⁻¹) with hq
  set L := padicLog (1 + x) with hLdef
  have hq1 : 1 ≤ q := one_le_sqrt_inv_norm_p h3
  have hc0 : 0 ≤ c := (norm_nonneg x).trans hx
  have hx2 : ‖x‖ ^ 2 < ‖((p : ℕ) : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hx 2) hc
  have hL : ‖L‖ = ‖x‖ := by
    rw [hLdef, norm_padicLog_eq h3 hp2 (by rwa [add_sub_cancel_left]), add_sub_cancel_left]
  have hxq : ‖x‖ * q < 1 := mul_sqrt_inv_norm_p_lt_one (norm_nonneg x) hx2
  have hxq0 : 0 ≤ ‖x‖ * q := by positivity
  have hLb : ∀ j, ‖L ^ j / ((j ! : ℕ) : K)‖ ≤ (‖x‖ * q) ^ j := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [norm_div, norm_pow, hL, div_eq_mul_inv, mul_pow]
      refine mul_le_mul_of_nonneg_left ((norm_factorial_inv_le h3 hp2 hj.ne').trans ?_)
        (by positivity)
      exact pow_le_pow_right₀ hq1 (Nat.sub_le j 1)
  have hbound : ∀ j, ‖chooseCoeff x j - L ^ j / ((j ! : ℕ) : K)‖ ≤ 1 * (‖x‖ * q) ^ j := by
    intro j
    rw [one_mul]
    exact (norm_sub_le_max' _ _).trans
      (max_le (norm_chooseCoeff_le h3 hp2 hx2 j) (hLb j))
  have hvan : ∀ n : ℕ, ∑' j, (chooseCoeff x j - L ^ j / ((j ! : ℕ) : K)) * (n : K) ^ j = 0 := by
    intro n
    have hn1 : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
    have hs : ∀ (g : ℕ → K), (∀ j, ‖g j‖ ≤ (‖x‖ * q) ^ j) →
        Summable fun j => g j * (n : K) ^ j := by
      intro g hg
      refine TateFredholm.summable_of_tendsto_cofinite ?_
      rw [Nat.cofinite_eq_atTop]
      refine squeeze_zero_norm (a := fun j => (‖x‖ * q) ^ j) (fun j => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hxq0 hxq)
      rw [norm_mul, norm_pow]
      calc ‖g j‖ * ‖(n : K)‖ ^ j ≤ (‖x‖ * q) ^ j * 1 :=
            mul_le_mul (hg j) (pow_le_one₀ (norm_nonneg _) hn1) (by positivity) (by positivity)
        _ = (‖x‖ * q) ^ j := mul_one _
    have hs1 := hs (fun j => chooseCoeff x j) fun j => norm_chooseCoeff_le h3 hp2 hx2 j
    have hs2 := hs (fun j => L ^ j / ((j ! : ℕ) : K)) hLb
    rw [show (fun j => (chooseCoeff x j - L ^ j / ((j ! : ℕ) : K)) * (n : K) ^ j)
        = fun j => chooseCoeff x j * (n : K) ^ j - L ^ j / ((j ! : ℕ) : K) * (n : K) ^ j from
        funext fun j => by ring]
    rw [hs1.tsum_sub hs2,
      ← tsum_choose_mul_pow_eq_tsum_chooseCoeff h3 hp2 hc hx
        (by calc ‖(n : K)‖ * ‖x‖ ≤ 1 * ‖x‖ :=
                mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)
              _ = ‖x‖ := one_mul _
              _ ≤ c := hx),
      ← padicExp_mul_eq_tsum, tsum_choose_natCast_mul_pow,
      padicExp_natCast_mul_padicLog h3 hp2 n hx2, sub_self]
  exact sub_eq_zero.mp
    (eq_zero_of_forall_tsum_natCast_eq_zero h3 hxq0 hxq hbound hvan j)

/-- **The `p`-adic binomial theorem for an arbitrary exponent**
([Koblitz, Ch. IV §2]): on `‖x‖ ≤ c`, `‖e‖·‖x‖ ≤ c`, `c² < ‖p‖`,
`∑_r C(e, r)·x^r = exp(e·log(1+x))`. -/
theorem hasSum_choose_mul_pow {c : ℝ} (hc : c ^ 2 < ‖((p : ℕ) : K)‖) {e x : K}
    (hx : ‖x‖ ≤ c) (hex : ‖e‖ * ‖x‖ ≤ c) :
    HasSum (fun r : ℕ => Ring.choose e r * x ^ r) (padicExp (e * padicLog (1 + x))) := by
  have hs := summable_choose_mul_pow h3 hp2 hc hx hex
  convert hs.hasSum using 1
  rw [tsum_choose_mul_pow_eq_tsum_chooseCoeff h3 hp2 hc hx hex, padicExp_mul_eq_tsum]
  exact tsum_congr fun j => by rw [chooseCoeff_eq_padicLog_pow_div_factorial h3 hp2 hc hx j]

end LWX.PadicExpLog

end
