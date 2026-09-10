/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.FunctionSeries
import PhD.LWX.HaloWeight

/-!
# `(1+T)^{pʰ}` and the binomial power identity — SKELETON

Two facts about a halo point `T` (`‖T‖ < 1`) needed to define the halo weight at analyticity
level `h` ([LWX, §2.1]: "the universal character … `χ(exp(pᵐ))^{(log x)/pᵐ}`", read with
`T = χ(exp(p)) − 1`, so `χ(exp(pᵐ)) = (1+T)^{p^{m−1}}`):

* the **binomial power identity** `(1+T)^{pʰ·u} = ((1+T)^{pʰ})^u` for a `p`-adic integer exponent
  `u`, i.e. `oneAddPow T (pʰu) = oneAddPow ((1+T)^{pʰ} − 1) u` — both sides are continuous in `u`
  and agree on `ℕ` (`Ring.choose_natCast`, `add_pow`), and `ℕ` is dense in `ℤ_p`;
* `(1+T)^{pʰ} − 1 → 0` as `h → ∞`, so that every halo point reaches the joint `exp/log` disc
  `‖(1+T)^{pʰ} − 1‖² < p⁻¹` for some `h` — the existence form of [LWX, §2.7]'s "`[−]_{m₀}` … is
  `m₀`-locally analytic".  The decay comes from iterating the one-step Kummer bound
  `‖(1+T)^p − 1‖ ≤ max(‖p‖‖T‖, ‖T‖^p)`, giving the contraction factor `max(‖p‖, ‖T‖^{p−1}) < 1`.

## Main declarations

* `LWX.oneAddPow_natCast`, `LWX.continuous_oneAddPow_intHom`, **`LWX.oneAddPow_pow_mul`**.
* `LWX.norm_one_add_pow_sub_one_le`, `LWX.norm_one_add_pow_prime_sub_one_le`,
  `LWX.norm_pow_prime_pow_sub_one_le`, `LWX.tendsto_pow_prime_pow_sub_one`,
  **`LWX.exists_sq_norm_pow_prime_pow_sub_one_lt`**.
-/

open Filter Topology

open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

/-- `pʰ ≠ 0`, as an instance (for `ZMod (p ^ h)`, the residue discs of level `h`). -/
instance instNeZeroPrimePow (h : ℕ) : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The binomial series at a natural exponent is the finite binomial expansion. -/
theorem oneAddPow_natCast (T : K) (n : ℕ) : oneAddPow T (n : K) = (1 + T) ^ n := by
  rw [oneAddPow, tsum_eq_sum (s := Finset.range (n + 1)) fun r hr => by
    rw [Finset.mem_range, not_lt] at hr
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul],
    add_comm (1 : K) T, add_pow]
  exact Finset.sum_congr rfl fun k _ => by rw [Ring.choose_natCast]; ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `‖C(ψ u, r)‖ ≤ 1` for a `p`-adic integer exponent. -/
theorem norm_choose_intHom_le_one (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (u : ℤ_[p])
    (r : ℕ) : ‖Ring.choose (intHom ψ u) r‖ ≤ 1 := by
  rw [← Ring.map_choose (intHom ψ) u r, norm_intHom ψ hψ]
  exact PadicInt.norm_le_one _

omit [IsUltrametricDist K] in
/-- For `‖T‖ < 1` the binomial series is a continuous function of a `p`-adic integer exponent
(uniform convergence, `continuous_choose`). -/
theorem continuous_oneAddPow_intHom (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T : K}
    (hT : ‖T‖ < 1) : Continuous fun u : ℤ_[p] => oneAddPow T (intHom ψ u) := by
  have hcont : Continuous (intHom ψ) :=
    AddMonoidHomClass.continuous_of_bound (intHom ψ) 1 fun x => by
      rw [norm_intHom ψ hψ, one_mul]
  refine continuous_tsum (u := fun r : ℕ => ‖T‖ ^ r) (fun r => ?_)
    (summable_geometric_of_lt_one (norm_nonneg T) hT) fun r x => ?_
  · refine Continuous.mul ?_ continuous_const
    simp only [← Ring.map_choose (intHom ψ)]
    exact hcont.comp (PadicInt.continuous_choose r)
  · rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (norm_choose_intHom_le_one ψ hψ x r)

omit [CompleteSpace K] [CharZero K] in
/-- A `1`-unit has norm one. -/
theorem norm_one_add_le {T : K} (hT : ‖T‖ < 1) : ‖1 + T‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_one]; exact max_le le_rfl hT.le)

omit [CompleteSpace K] [CharZero K] in
/-- `(1+T)^m − 1 = (∑_{i<m}(1+T)^i)·T`, so raising a `1`-unit to a power keeps it within `‖T‖`
of `1`. -/
theorem norm_one_add_pow_sub_one_le {T : K} (hT : ‖T‖ < 1) (m : ℕ) :
    ‖(1 + T) ^ m - 1‖ ≤ ‖T‖ := by
  rw [← geom_sum_mul (1 + T) m, show (1 : K) + T - 1 = T from by ring, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg T) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_one_add_le hT)

/-- **The binomial power identity** `(1+T)^{pʰu} = ((1+T)^{pʰ})^u`, `u ∈ ℤ_p`
([LWX, §2.1], the extension formula through `χ(exp(pᵐ)) = (1+T)^{p^{m−1}}`). -/
theorem oneAddPow_pow_mul (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T : K} (hT : ‖T‖ < 1)
    (h : ℕ) (u : ℤ_[p]) :
    oneAddPow T (intHom ψ ((p : ℤ_[p]) ^ h * u))
      = oneAddPow ((1 + T) ^ p ^ h - 1) (intHom ψ u) := by
  have hT' : ‖(1 + T) ^ p ^ h - 1‖ < 1 :=
    lt_of_le_of_lt (norm_one_add_pow_sub_one_le hT _) hT
  have hcont : Continuous (intHom ψ) :=
    AddMonoidHomClass.continuous_of_bound (intHom ψ) 1 fun x => by
      rw [norm_intHom ψ hψ, one_mul]
  have hc1 : Continuous fun v : ℤ_[p] => oneAddPow T (intHom ψ ((p : ℤ_[p]) ^ h * v)) :=
    (continuous_oneAddPow_intHom ψ hψ hT).comp (continuous_const.mul continuous_id)
  have hc2 : Continuous fun v : ℤ_[p] => oneAddPow ((1 + T) ^ p ^ h - 1) (intHom ψ v) :=
    continuous_oneAddPow_intHom ψ hψ hT'
  refine congrFun (PadicInt.denseRange_natCast.equalizer hc1 hc2 (funext fun j => ?_)) u
  show oneAddPow T (intHom ψ ((p : ℤ_[p]) ^ h * (j : ℕ))) = oneAddPow _ (intHom ψ (j : ℕ))
  rw [show (p : ℤ_[p]) ^ h * (j : ℕ) = ((p ^ h * j : ℕ) : ℤ_[p]) from by push_cast; ring]
  rw [show intHom ψ ((p ^ h * j : ℕ) : ℤ_[p]) = ((p ^ h * j : ℕ) : K) from by
      rw [map_natCast],
    show intHom ψ ((j : ℕ) : ℤ_[p]) = ((j : ℕ) : K) from by rw [map_natCast],
    oneAddPow_natCast, oneAddPow_natCast,
    show (1 : K) + ((1 + T) ^ p ^ h - 1) = (1 + T) ^ p ^ h from by ring, ← pow_mul]

omit [CompleteSpace K] [CharZero K] in
/-- **The one-step Kummer bound**: `(1+T)^p − 1 = ∑_{k=1}^{p} C(p,k)Tᵏ`, where every term with
`1 ≤ k < p` has `p ∣ C(p,k)` and the last term is `T^p`. -/
theorem norm_one_add_pow_prime_sub_one_le {T : K} (hT : ‖T‖ ≤ 1) :
    ‖(1 + T) ^ p - 1‖ ≤ max (‖((p : ℕ) : K)‖ * ‖T‖) (‖T‖ ^ p) := by
  have hexp : (1 + T) ^ p - 1
      = ∑ i ∈ Finset.range p, (((p.choose (i + 1) : ℕ) : K) * T ^ (i + 1)) := by
    rw [add_comm (1 : K) T, add_pow, Finset.sum_range_succ' (fun k => T ^ k * 1 ^ (p - k)
      * ((p.choose k : ℕ) : K)) p]
    simp only [one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, pow_zero]
    rw [add_sub_cancel_right]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases heq : i + 1 = p
  · rw [heq, Nat.choose_self, Nat.cast_one, one_mul, norm_pow]
    exact le_max_right _ _
  · refine le_trans ?_ (le_max_left _ _)
    obtain ⟨m, hm⟩ := hp.out.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
    rw [hm, norm_mul, norm_pow]
    push_cast
    rw [norm_mul]
    calc ‖((p : ℕ) : K)‖ * ‖(m : K)‖ * ‖T‖ ^ (i + 1)
        ≤ ‖((p : ℕ) : K)‖ * 1 * ‖T‖ ^ (i + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _)) (by positivity)
      _ = ‖((p : ℕ) : K)‖ * ‖T‖ ^ (i + 1) := by rw [mul_one]
      _ ≤ ‖((p : ℕ) : K)‖ * ‖T‖ :=
          mul_le_mul_of_nonneg_left (pow_le_of_le_one (norm_nonneg _) hT (by omega))
            (norm_nonneg _)

omit [CompleteSpace K] [CharZero K] in
/-- **Iterating the one-step bound**: `‖(1+T)^{pʰ} − 1‖ ≤ rʰ·‖T‖` with
`r = max(‖p‖, ‖T‖^{p−1}) < 1`. -/
theorem norm_pow_prime_pow_sub_one_le (_hpK : ‖((p : ℕ) : K)‖ < 1) {T : K} (hT : ‖T‖ < 1)
    (h : ℕ) :
    ‖(1 + T) ^ p ^ h - 1‖ ≤ max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1)) ^ h * ‖T‖ := by
  have hr0 : (0 : ℝ) ≤ max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1)) :=
    le_max_of_le_left (norm_nonneg _)
  induction h with
  | zero => simp
  | succ h ih =>
    have hS : ‖(1 + T) ^ p ^ h - 1‖ ≤ ‖T‖ := norm_one_add_pow_sub_one_le hT _
    have hp1 : p - 1 + 1 = p := by
      have := hp.out.two_le
      omega
    have hstep : ‖(1 + ((1 + T) ^ p ^ h - 1)) ^ p - 1‖
        ≤ max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1)) * ‖(1 + T) ^ p ^ h - 1‖ := by
      refine (norm_one_add_pow_prime_sub_one_le (hS.trans hT.le)).trans (max_le ?_ ?_)
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      · calc ‖(1 + T) ^ p ^ h - 1‖ ^ p
            = ‖(1 + T) ^ p ^ h - 1‖ ^ (p - 1) * ‖(1 + T) ^ p ^ h - 1‖ := by
              rw [← pow_succ, hp1]
          _ ≤ max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1)) * ‖(1 + T) ^ p ^ h - 1‖ :=
              mul_le_mul_of_nonneg_right
                ((pow_le_pow_left₀ (norm_nonneg _) hS _).trans (le_max_right _ _))
                (norm_nonneg _)
    rw [show (1 : K) + ((1 + T) ^ p ^ h - 1) = (1 + T) ^ p ^ h from by ring, ← pow_mul,
      ← pow_succ] at hstep
    refine hstep.trans ?_
    calc max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1)) * ‖(1 + T) ^ p ^ h - 1‖
        ≤ max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1))
            * (max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1)) ^ h * ‖T‖) :=
          mul_le_mul_of_nonneg_left ih hr0
      _ = max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1)) ^ (h + 1) * ‖T‖ := by ring

omit [CompleteSpace K] [CharZero K] in
/-- `x ↦ x^{pʰ}` contracts the `1`-units to `1`. -/
theorem tendsto_pow_prime_pow_sub_one (hpK : ‖((p : ℕ) : K)‖ < 1) {T : K} (hT : ‖T‖ < 1) :
    Tendsto (fun h : ℕ => (1 + T) ^ p ^ h - 1) atTop (𝓝 0) := by
  have hr1 : max ‖((p : ℕ) : K)‖ (‖T‖ ^ (p - 1)) < 1 := by
    have h2 := hp.out.two_le
    exact max_lt hpK (pow_lt_one₀ (norm_nonneg _) hT (by omega))
  refine squeeze_zero_norm (fun h => norm_pow_prime_pow_sub_one_le hpK hT h) ?_
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (le_trans (norm_nonneg _) (le_max_left _ _))
      hr1).mul_const ‖T‖

omit [CompleteSpace K] [CharZero K] in
/-- **The analyticity threshold**: every halo point reaches the joint `exp/log` disc at some
level `h` ([LWX, §2.7], existence form). -/
theorem exists_sq_norm_pow_prime_pow_sub_one_lt (hpK : ‖((p : ℕ) : K)‖ < 1) {T : K}
    (hT : ‖T‖ < 1) : ∃ h : ℕ, ‖(1 + T) ^ p ^ h - 1‖ ^ 2 < (p : ℝ)⁻¹ := by
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hlim : Tendsto (fun h : ℕ => ‖(1 + T) ^ p ^ h - 1‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_pow_prime_pow_sub_one hpK hT).norm
    simpa using this.pow 2
  obtain ⟨h, hh⟩ := (hlim.eventually_lt_const hpos).exists
  exact ⟨h, hh⟩

end LWX

end
