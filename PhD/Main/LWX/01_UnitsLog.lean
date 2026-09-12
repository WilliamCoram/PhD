/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.NumberTheory.Basic
import PhD.Main.LWX.«00_PadicExpLog»
import PhD.Main.TateFredholm.«00_Tate»
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.Finite.Basic

/-!
# Teichmüller lift and the normalised logarithm at odd `p` (lwx-halo board)

[LWX, Notation 2.1] writes `ℤ_p^× = Δ × (1 + qℤ_p)^×` and identifies `(1 + qℤ_p)^×`
with `ℤ_p` via `(1/q)·log`.  [LWX, Prop 3.14 proof] uses exactly three consequences at
`q = p` odd, and this file provides them and nothing more:

* the Teichmüller lift `ωT(x) = lim_n x^{pⁿ}` splitting `x = ωT(x)·⟨x⟩` with
  `⟨x⟩ ∈ 1 + pℤ_p` (AG1: not in mathlib — `WittVector.teichmuller` is a different map);
* the logarithm `qlog` on `1 + pℤ_p` (the restriction of the general ultrametric
  `PhD/Main/LWX/00_PadicExpLog.lean` along `ℤ_p ⊆ ℚ_p`): integrality bound and
  **additivity** (needed to split `g(z) = log((cz+d)/d₀)/q` into a constant plus a
  series of [LWX, Lemma 3.13]'s shape — the split is what makes Lemma 3.13
  applicable);
* the coefficient shape of `z ↦ qlog(1 + wz)` for `v(w) ≥ 1`: coefficients
  `(−1)^{k+1} w^k / k`, of the shape `p^{k−1}·a_k/k` demanded by [LWX, Lemma 3.13].

`p = 2` (`q = 4`) is out of scope for this board.
-/

open Filter Topology

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

/-- Fermat in `ℤ_p`: `p ∣ x^p − x`, via reduction to `ZMod p`. -/
private theorem p_dvd_pow_sub (x : ℤ_[p]) : (p : ℤ_[p]) ∣ x ^ p - x := by
  have h1 : PadicInt.toZMod (x ^ p - x) = 0 := by
    rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  have h2 : x ^ p - x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h1
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton] at h2
  exact h2

/-- The consecutive-difference bound `‖x^{p^{n+1}} − x^{pⁿ}‖ ≤ p^{−(n+1)}`. -/
private theorem norm_pow_p_succ_sub_le (x : ℤ_[p]) (n : ℕ) :
    ‖x ^ p ^ (n + 1) - x ^ p ^ n‖ ≤ (p : ℝ) ^ (-(n + 1 : ℤ)) := by
  have hdvd : ((p : ℤ_[p]) ^ (n + 1)) ∣ x ^ p ^ (n + 1) - x ^ p ^ n := by
    have h1 : ((p : ℤ_[p]) ^ (n + 1)) ∣ (x ^ p) ^ p ^ n - x ^ p ^ n :=
      dvd_sub_pow_of_dvd_sub (p_dvd_pow_sub x) n
    rwa [← pow_mul, ← pow_succ'] at h1
  rw [show (-(n + 1 : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring,
    PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  exact hdvd

/-- The Teichmüller sequence is Cauchy. -/
private theorem cauchySeq_pow_p (x : ℤ_[p]) : CauchySeq fun n => x ^ p ^ n := by
  refine SeminormedAddCommGroup.cauchySeq_of_le_geometric (C := (p : ℝ)⁻¹)
    (r := (p : ℝ)⁻¹) ?_ fun n => ?_
  · rw [inv_lt_one_iff₀]
    right
    exact_mod_cast hp.out.one_lt
  · rw [norm_sub_rev]
    refine (norm_pow_p_succ_sub_le x n).trans (le_of_eq ?_)
    rw [show (-(n + 1 : ℤ)) = -1 + -(n : ℤ) by ring, zpow_add₀
      (by exact_mod_cast hp.out.pos.ne' : (p : ℝ) ≠ 0), zpow_neg_one, zpow_neg,
      ← inv_zpow, zpow_natCast]

/-- The underlying Teichmüller limit on `ℤ_p`. -/
private noncomputable def teichAux (x : ℤ_[p]) : ℤ_[p] :=
  limUnder atTop fun n => x ^ p ^ n

private theorem tendsto_teichAux (x : ℤ_[p]) :
    Tendsto (fun n => x ^ p ^ n) atTop (𝓝 (teichAux x)) :=
  (cauchySeq_pow_p x).tendsto_limUnder

private theorem teichAux_mul (x y : ℤ_[p]) :
    teichAux (x * y) = teichAux x * teichAux y := by
  refine tendsto_nhds_unique (tendsto_teichAux (x * y)) ?_
  have h1 := (tendsto_teichAux x).mul (tendsto_teichAux y)
  refine h1.congr fun n => ?_
  rw [mul_pow]

private theorem teichAux_one : teichAux (1 : ℤ_[p]) = 1 := by
  refine tendsto_nhds_unique (tendsto_teichAux 1) ?_
  simp only [one_pow]
  exact tendsto_const_nhds

/-- The Teichmüller lift `ωT(x) = lim_n x^{pⁿ}` (AG1).  Source: standard; used by
[LWX, Notation 2.1]'s splitting `ℤ_p^× = Δ × (1+qℤ_p)^×`. -/
noncomputable def teichmuller (x : ℤ_[p]ˣ) : ℤ_[p]ˣ where
  val := teichAux (x : ℤ_[p])
  inv := teichAux ((x⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  val_inv := by rw [← teichAux_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    teichAux_one]
  inv_val := by rw [← teichAux_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    teichAux_one]

/-- `ωT` is multiplicative. -/
theorem teichmuller_mul (x y : ℤ_[p]ˣ) :
    teichmuller (x * y) = teichmuller x * teichmuller y := by
  ext
  show teichAux ((x * y : ℤ_[p]ˣ) : ℤ_[p]) = teichAux (x : ℤ_[p]) * teichAux (y : ℤ_[p])
  rw [Units.val_mul, teichAux_mul]

/-- `x^{pⁿ} ≡ x mod p` for every `n`, by telescoping. -/
private theorem norm_pow_p_sub_self_le (x : ℤ_[p]) (n : ℕ) :
    ‖x ^ p ^ n - x‖ ≤ (p : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n IH =>
      calc ‖x ^ p ^ (n + 1) - x‖
          = ‖(x ^ p ^ (n + 1) - x ^ p ^ n) + (x ^ p ^ n - x)‖ := by ring_nf
        _ ≤ max ‖x ^ p ^ (n + 1) - x ^ p ^ n‖ ‖x ^ p ^ n - x‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ ≤ (p : ℝ)⁻¹ := by
            refine max_le ((norm_pow_p_succ_sub_le x n).trans ?_) IH
            rw [show ((p : ℝ))⁻¹ = (p : ℝ) ^ (-1 : ℤ) by rw [zpow_neg_one]]
            exact zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega)

private theorem norm_teichAux_sub_self_le (x : ℤ_[p]) :
    ‖teichAux x - x‖ ≤ (p : ℝ)⁻¹ := by
  have h1 : Tendsto (fun n => x ^ p ^ n - x) atTop (𝓝 (teichAux x - x)) :=
    (tendsto_teichAux x).sub tendsto_const_nhds
  exact le_of_tendsto h1.norm
    (Eventually.of_forall fun n => norm_pow_p_sub_self_le x n)

/-- `ωT(x) ≡ x mod p`: the one-unit part `⟨x⟩ = x·ωT(x)⁻¹` lies in `1 + pℤ_p`. -/
theorem norm_mul_teichmuller_inv_sub_one_le (x : ℤ_[p]ˣ) :
    ‖((x * (teichmuller x)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by
  have hval : ((x * (teichmuller x)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
      = (x : ℤ_[p]) * teichAux ((x⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [Units.val_mul]
    rfl
  have hone : teichAux (x : ℤ_[p]) * teichAux ((x⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 :=
    (teichmuller x).val_inv
  calc ‖((x * (teichmuller x)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1‖
      = ‖((x : ℤ_[p]) - teichAux (x : ℤ_[p]))
          * teichAux ((x⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖ := by
        rw [hval, ← hone]
        ring_nf
    _ ≤ (p : ℝ)⁻¹ * 1 := by
        rw [norm_mul]
        refine mul_le_mul ?_ (PadicInt.norm_le_one _) (norm_nonneg _)
          (by positivity)
        rw [norm_sub_rev]
        exact norm_teichAux_sub_self_le _
    _ = (p : ℝ)⁻¹ := mul_one _

/-- The Teichmüller lift is locally constant: it depends only on the residue
disc `‖u − v‖ ≤ p⁻¹`. -/
theorem teichmuller_eq_of_norm_sub_le {u v : ℤ_[p]ˣ}
    (h : ‖(u : ℤ_[p]) - v‖ ≤ (p : ℝ)⁻¹) : teichmuller u = teichmuller v := by
  have hdvd : (p : ℤ_[p]) ∣ (u : ℤ_[p]) - v := by
    have h1 : ‖(u : ℤ_[p]) - v‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [show (p : ℝ) ^ (-((1 : ℕ) : ℤ)) = (p : ℝ)⁻¹ by
        rw [zpow_neg, zpow_natCast, pow_one]]
      exact h
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton, pow_one] at h1
    exact h1
  have hn : ∀ n : ℕ, ‖(v : ℤ_[p]) ^ p ^ n - (u : ℤ_[p]) ^ p ^ n‖
      ≤ (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
    intro n
    have h1 : ((p : ℤ_[p]) ^ (n + 1)) ∣ (u : ℤ_[p]) ^ p ^ n - (v : ℤ_[p]) ^ p ^ n :=
      dvd_sub_pow_of_dvd_sub hdvd n
    rw [norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h1
  ext
  show teichAux (u : ℤ_[p]) = teichAux (v : ℤ_[p])
  refine tendsto_nhds_unique (tendsto_teichAux _) ?_
  refine (tendsto_teichAux (v : ℤ_[p])).congr_dist ?_
  refine squeeze_zero (g := fun n : ℕ => (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)))
    (fun n => dist_nonneg) (fun n => ?_) ?_
  · rw [dist_eq_norm]
    exact hn n
  · have h2 : Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1)) atTop (𝓝 0) := by
      have h3 : (p : ℝ)⁻¹ < 1 := by
        rw [inv_lt_one_iff₀]
        right
        exact_mod_cast hp.out.one_lt
      simpa [Function.comp_def] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h3).comp
          (tendsto_add_atTop_nat 1)
    refine h2.congr fun n => ?_
    rw [zpow_neg, ← inv_zpow, zpow_natCast]

/-- The one-unit part `⟨x⟩ := x · ωT(x)⁻¹` of a unit ([LWX, Notation 2.1]). -/
def oneUnitPart (x : ℤ_[p]ˣ) : ℤ_[p] := ((x * (teichmuller x)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])

theorem norm_oneUnitPart_sub_one_le (x : ℤ_[p]ˣ) :
    ‖oneUnitPart x - 1‖ ≤ (p : ℝ)⁻¹ :=
  norm_mul_teichmuller_inv_sub_one_le x

/-- The (un-normalised) `p`-adic logarithm `qlog u = ∑_{k≥1} (−1)^{k+1}(u−1)^k/k`
valued in `ℚ_p`; junk outside `‖u − 1‖ ≤ p⁻¹`.  [LWX, Prop 3.14 proof]'s
`log((cz+d)/d₀)`.  Definitionally the restriction of the general ultrametric
logarithm `PhD/Main/LWX/00_PadicExpLog.lean` along `ℤ_p ⊆ ℚ_p`. -/
def qlog (u : ℤ_[p]) : ℚ_[p] := PadicExpLog.padicLog ((u : ℚ_[p]))

/-- The series formula for `qlog` (the sign-unfolded form of `padicLog`'s series). -/
theorem qlog_eq_tsum (u : ℤ_[p]) :
    qlog u = ∑' k : ℕ, (-1) ^ k * ((u : ℚ_[p]) - 1) ^ (k + 1) / (k + 1) := by
  rw [qlog, PadicExpLog.padicLog, ← tsum_neg]
  refine tsum_congr fun n => ?_
  have h1 : (1 : ℚ_[p]) - u = -((u : ℚ_[p]) - 1) := by ring
  rw [h1, neg_pow, pow_succ]
  ring

/-- The `ℤ_p`-norm of `u − 1` computes the `ℚ_p`-norm of `↑u − 1`. -/
private theorem norm_coe_sub_one (u : ℤ_[p]) : ‖(u : ℚ_[p]) - 1‖ = ‖u - 1‖ := by
  rw [show ((u : ℚ_[p]) - 1) = ((u - 1 : ℤ_[p]) : ℚ_[p]) by push_cast; ring,
    PadicInt.padic_norm_e_of_padicInt]

private theorem norm_p_lt_one : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
  rw [Padic.norm_p, inv_lt_one_iff₀]
  right
  exact_mod_cast hp.out.one_lt

/-- The closed disc `‖u − 1‖ ≤ p⁻¹` sits inside the joint exp/log disc
`‖·‖² < ‖p‖`. -/
private theorem sq_norm_coe_sub_one_lt {u : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖(u : ℚ_[p]) - 1‖ ^ 2 < ‖((p : ℕ) : ℚ_[p])‖ := by
  rw [norm_coe_sub_one, Padic.norm_p]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpi : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have h1 : ‖u - 1‖ ^ 2 ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by
    calc ‖u - 1‖ ^ 2 = ‖u - 1‖ * ‖u - 1‖ := sq (‖u - 1‖) ▸ by ring
      _ ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := mul_le_mul hu hu (norm_nonneg _) hpi.le
  calc ‖u - 1‖ ^ 2 ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := h1
    _ < 1 * (p : ℝ)⁻¹ := by
        refine mul_lt_mul_of_pos_right ?_ hpi
        rw [inv_lt_one_iff₀]
        right
        exact hp1
    _ = (p : ℝ)⁻¹ := one_mul _


/-- The joint termwise bound for the log series: with `‖u − 1‖ ≤ p⁻¹`,
`‖(u−1)^{k+1}/(k+1)‖ ≤ ‖u−1‖·(k+1)·p^{−k}`. -/
private theorem norm_qlog_term_le {u : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) (k : ℕ) :
    ‖(-1 : ℚ_[p]) ^ k * ((u : ℚ_[p]) - 1) ^ (k + 1) / ((k : ℚ_[p]) + 1)‖
      ≤ ‖u - 1‖ * ((k + 1 : ℝ) * (p : ℝ)⁻¹ ^ k) := by
  have hw : ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by rw [norm_coe_sub_one]; exact hu
  have hk0 : ((k : ℚ_[p]) + 1) ≠ 0 := by
    rw [show ((k : ℚ_[p]) + 1) = ((k + 1 : ℕ) : ℚ_[p]) by push_cast; ring]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have hknorm : ‖(k : ℚ_[p]) + 1‖ = (p : ℝ) ^ (-(padicValNat p (k + 1) : ℤ)) := by
    rw [show ((k : ℚ_[p]) + 1) = ((k + 1 : ℕ) : ℚ_[p]) by push_cast; ring,
      Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)),
      Padic.valuation_natCast]
  have hval : (p : ℝ) ^ ((padicValNat p (k + 1) : ℤ)) ≤ (k + 1 : ℝ) := by
    rw [zpow_natCast]
    have h1 : p ^ padicValNat p (k + 1) ≤ k + 1 := by
      have h2 := Nat.ordProj_le p (Nat.succ_ne_zero k)
      rwa [Nat.factorization_def _ hp.out] at h2
    exact_mod_cast h1
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    hknorm, div_eq_mul_inv, ← zpow_neg, neg_neg]
  calc ‖(u : ℚ_[p]) - 1‖ ^ (k + 1) * (p : ℝ) ^ ((padicValNat p (k + 1) : ℤ))
      ≤ (‖(u : ℚ_[p]) - 1‖ * (p : ℝ)⁻¹ ^ k) * (k + 1 : ℝ) := by
        refine mul_le_mul ?_ hval (zpow_nonneg (by positivity) _) (by positivity)
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hw k) (norm_nonneg _)
    _ = ‖u - 1‖ * ((k + 1 : ℝ) * (p : ℝ)⁻¹ ^ k) := by
        rw [norm_coe_sub_one]
        ring

private theorem tendsto_qlog_term {u : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    Tendsto (fun k : ℕ => (-1 : ℚ_[p]) ^ k * ((u : ℚ_[p]) - 1) ^ (k + 1) / (k + 1))
      cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  have hr : ‖(p : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by
      have := hp.out.pos
      positivity)]
    rw [inv_lt_one_iff₀]
    right
    exact_mod_cast hp.out.one_lt
  have hg : Tendsto (fun k : ℕ => ‖u - 1‖ * ((k + 1 : ℝ) * (p : ℝ)⁻¹ ^ k)) atTop
      (𝓝 0) := by
    rw [show (0 : ℝ) = ‖u - 1‖ * 0 by ring]
    refine Tendsto.const_mul _ ?_
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) * (p : ℝ)⁻¹ ^ k) atTop (𝓝 0) := by
      simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hr).tendsto_atTop_zero
    have h2 : Tendsto (fun k : ℕ => (p : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr fun k => ?_
    ring
  exact squeeze_zero_norm (fun k => norm_qlog_term_le hu k) hg

/-- Convergence of the log series on `1 + pℤ_p` (`p` odd not needed here). -/
theorem summable_qlog {u : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    Summable fun k : ℕ => (-1 : ℚ_[p]) ^ k * ((u : ℚ_[p]) - 1) ^ (k + 1) / (k + 1) :=
  TateFredholm.summable_of_tendsto_cofinite (tendsto_qlog_term hu)

/-- Integrality with a margin at odd `p`: `‖qlog u‖ ≤ ‖u − 1‖` on `1 + pℤ_p`
(each term has `v ≥ k − v(k) ≥ v(u−1)`; `p ≠ 2` makes `k − v(k)` ≥ 1 for `k ≥ 1`). -/
theorem norm_qlog_le (hp2 : p ≠ 2) {u : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖qlog u‖ ≤ ‖u - 1‖ := by
  rw [qlog, PadicExpLog.norm_padicLog_eq norm_p_lt_one hp2 (sq_norm_coe_sub_one_lt hu),
    norm_coe_sub_one]

/-- **Additivity of the logarithm** on `1 + pℤ_p`.  Needed by [LWX, Prop 3.14 proof] to
split `g(z) = log((cz+d)/d₀)/q` as `log⟨d⟩/q + log(1 + (c/d)z)/q`; the direct composite
estimate provably fails to give Lemma 3.13's shape at `k = pᵐ` (planning note). -/
theorem qlog_mul (hp2 : p ≠ 2) {u v : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹)
    (hv : ‖v - 1‖ ≤ (p : ℝ)⁻¹) : qlog (u * v) = qlog u + qlog v := by
  show PadicExpLog.padicLog (((u * v : ℤ_[p])) : ℚ_[p])
      = PadicExpLog.padicLog ((u : ℚ_[p])) + PadicExpLog.padicLog ((v : ℚ_[p]))
  rw [PadicInt.coe_mul]
  exact PadicExpLog.padicLog_mul norm_p_lt_one hp2
    (sq_norm_coe_sub_one_lt hu) (sq_norm_coe_sub_one_lt hv)

/-- The shape predicate of [LWX, Lemma 3.13]: a coefficient stream
`A : ℕ → ℚ_p` with `A_k = p^{k−1}·a_k/k`-sized entries, i.e.
`v(A_k) ≥ (k−1) − v(k)` for `k ≥ 1` and `A_0 ∈ ℤ_p`. -/
def IsLogShape (A : ℕ → ℚ_[p]) : Prop :=
  ‖A 0‖ ≤ 1 ∧ ∀ k : ℕ, 1 ≤ k → ‖A k‖ * ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ) + 1)

/-- The coefficient stream of `z ↦ qlog(1 + w·z)`:
`A_0 = 0`, `A_k = (−1)^{k+1} w^k / k`. -/
def qlogLinearCoeff (w : ℤ_[p]) : ℕ → ℚ_[p]
  | 0 => 0
  | k + 1 => (-1) ^ k * (w : ℚ_[p]) ^ (k + 1) / (k + 1)

/-- For `v(w) ≥ 1` the stream of `qlog(1 + wz)` has [LWX, Lemma 3.13]'s shape:
`v(w^k/k) ≥ k − v(k) ≥ (k−1) − v(k)`. -/
theorem isLogShape_qlogLinearCoeff {w : ℤ_[p]} (hw : ‖w‖ ≤ (p : ℝ)⁻¹) :
    IsLogShape (qlogLinearCoeff w) := by
  constructor
  · show ‖(0 : ℚ_[p])‖ ≤ 1
    simp
  · intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    show ‖(-1 : ℚ_[p]) ^ k * (w : ℚ_[p]) ^ (k + 1) / ((k : ℚ_[p]) + 1)‖
        * ‖((k + 1 : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ) + 1)
    have hcast : ((k : ℚ_[p]) + 1) = ((k + 1 : ℕ) : ℚ_[p]) := by push_cast; ring
    have hne : (((k + 1 : ℕ)) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    rw [norm_div, hcast, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hne), norm_mul,
      norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hwQ : ‖(w : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
      rw [PadicInt.padic_norm_e_of_padicInt]
      exact hw
    calc ‖(w : ℚ_[p])‖ ^ (k + 1) ≤ ((p : ℝ)⁻¹) ^ (k + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) hwQ _
      _ = (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
          rw [zpow_neg, ← inv_zpow, zpow_natCast]
      _ ≤ (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ) + 1) :=
          zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega)

/-- Pointwise expansion: `qlog (1 + w·z) = ∑ A_k z^k` for `z ∈ ℤ_p`, `v(w) ≥ 1`. -/
theorem hasSum_qlogLinearCoeff {w : ℤ_[p]} (hw : ‖w‖ ≤ (p : ℝ)⁻¹) (z : ℤ_[p]) :
    HasSum (fun k : ℕ => qlogLinearCoeff w k * (z : ℚ_[p]) ^ k) (qlog (1 + w * z)) := by
  have hu : ‖(1 + w * z) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [add_sub_cancel_left]
    calc ‖w * z‖ ≤ ‖w‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (p : ℝ)⁻¹ * 1 :=
          mul_le_mul hw (PadicInt.norm_le_one z) (norm_nonneg _) (by positivity)
      _ = (p : ℝ)⁻¹ := mul_one _
  have hqsum : HasSum
      (fun k : ℕ =>
        (-1 : ℚ_[p]) ^ k * (((1 + w * z : ℤ_[p]) : ℚ_[p]) - 1) ^ (k + 1) / (k + 1))
      (qlog (1 + w * z)) := by
    rw [qlog_eq_tsum]
    exact (summable_qlog hu).hasSum
  have hterm : ∀ k : ℕ,
      (-1 : ℚ_[p]) ^ k * (((1 + w * z : ℤ_[p]) : ℚ_[p]) - 1) ^ (k + 1) / (k + 1)
        = qlogLinearCoeff w (k + 1) * (z : ℚ_[p]) ^ (k + 1) := by
    intro k
    have h1 : ((1 + w * z : ℤ_[p]) : ℚ_[p]) - 1 = (w : ℚ_[p]) * (z : ℚ_[p]) := by
      push_cast
      ring
    rw [h1, mul_pow]
    show _ = (-1 : ℚ_[p]) ^ k * (w : ℚ_[p]) ^ (k + 1) / ((k : ℚ_[p]) + 1)
        * (z : ℚ_[p]) ^ (k + 1)
    ring
  rw [show (fun k : ℕ =>
      (-1 : ℚ_[p]) ^ k * (((1 + w * z : ℤ_[p]) : ℚ_[p]) - 1) ^ (k + 1) / (k + 1))
    = fun k : ℕ => qlogLinearCoeff w (k + 1) * (z : ℚ_[p]) ^ (k + 1) from
    funext hterm] at hqsum
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [Finset.range_one, Finset.sum_singleton,
    show qlogLinearCoeff w 0 * (z : ℚ_[p]) ^ 0 = 0 from by
      show (0 : ℚ_[p]) * _ = 0
      ring, sub_zero]
  exact hqsum

/-- An `IsLogShape` stream shifted by an integral constant is still `IsLogShape`
(the split `g = ℓ⟨d⟩ + ℓ(1 + (c/d)z)` of [LWX, Prop 3.14 proof]). -/
theorem IsLogShape.add_const {A : ℕ → ℚ_[p]} (hA : IsLogShape A) {x : ℤ_[p]} :
    IsLogShape (fun k => if k = 0 then A 0 + (x : ℚ_[p]) else A k) := by
  constructor
  · show ‖if (0 : ℕ) = 0 then A 0 + (x : ℚ_[p]) else A 0‖ ≤ 1
    rw [if_pos rfl]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA.1 ?_)
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_le_one x
  · intro k hk
    show ‖if k = 0 then A 0 + (x : ℚ_[p]) else A k‖ * _ ≤ _
    rw [if_neg (by omega)]
    exact hA.2 k hk

/-- `qlog` is `1`-Lipschitz on the disc `‖· − 1‖ ≤ p⁻¹`. -/
theorem norm_qlog_sub_qlog_le {u v : ℤ_[p]} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹)
    (hv : ‖v - 1‖ ≤ (p : ℝ)⁻¹) : ‖qlog u - qlog v‖ ≤ ‖u - v‖ := by
  have hpinv1 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  set x : ℚ_[p] := (u : ℚ_[p]) - 1 with hx
  set y : ℚ_[p] := (v : ℚ_[p]) - 1 with hy
  have hxn : ‖x‖ ≤ (p : ℝ)⁻¹ := by rw [hx, norm_coe_sub_one]; exact hu
  have hyn : ‖y‖ ≤ (p : ℝ)⁻¹ := by rw [hy, norm_coe_sub_one]; exact hv
  have hxy : x - y = ((u - v : ℤ_[p]) : ℚ_[p]) := by
    rw [hx, hy]
    push_cast
    ring
  have hsu := summable_qlog hu
  have hsv := summable_qlog hv
  have hsub : qlog u - qlog v = ∑' k : ℕ,
      ((-1 : ℚ_[p]) ^ k * x ^ (k + 1) / (k + 1)
        - (-1 : ℚ_[p]) ^ k * y ^ (k + 1) / (k + 1)) := by
    rw [qlog_eq_tsum, qlog_eq_tsum, ← hsu.tsum_sub hsv]
  -- the termwise Lipschitz bound
  have hterm : ∀ k : ℕ,
      ‖(-1 : ℚ_[p]) ^ k * x ^ (k + 1) / (k + 1)
        - (-1 : ℚ_[p]) ^ k * y ^ (k + 1) / (k + 1)‖ ≤ ‖u - v‖ := by
    intro k
    have hfac : (-1 : ℚ_[p]) ^ k * x ^ (k + 1) / (k + 1)
        - (-1 : ℚ_[p]) ^ k * y ^ (k + 1) / (k + 1)
        = (-1 : ℚ_[p]) ^ k * (x ^ (k + 1) - y ^ (k + 1)) / (k + 1) := by
      ring
    have hgeom : x ^ (k + 1) - y ^ (k + 1)
        = (∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i)) * (x - y) :=
      (Commute.geom_sum₂_mul (Commute.all x y) (k + 1)).symm
    have hsumnorm : ‖∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i)‖
        ≤ ((p : ℝ)⁻¹) ^ k := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [norm_mul, norm_pow, norm_pow]
      calc ‖x‖ ^ i * ‖y‖ ^ (k - i) ≤ ((p : ℝ)⁻¹) ^ i * ((p : ℝ)⁻¹) ^ (k - i) := by
            exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxn i)
              (pow_le_pow_left₀ (norm_nonneg _) hyn _) (by positivity) (by positivity)
        _ = ((p : ℝ)⁻¹) ^ k := by
            rw [← pow_add]
            congr 1
            omega
    have hkcast : ((k : ℚ_[p]) + 1) = ((k + 1 : ℕ) : ℚ_[p]) := by push_cast; ring
    have hkne : (((k + 1 : ℕ)) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hknorm : ((p : ℝ)⁻¹) ^ k * ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹ ≤ 1 := by
      have h1 : ‖((k + 1 : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p (k + 1) : ℤ)) := by
        rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hkne),
          Padic.valuation_natCast]
      have h2 : p ^ padicValNat p (k + 1) ≤ k + 1 := by
        have h3 := Nat.ordProj_le p (Nat.succ_ne_zero k)
        rwa [Nat.factorization_def _ hp.out] at h3
      have h4 : k + 1 ≤ p ^ k := by
        calc k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt Nat.lt_two_pow_self
          _ ≤ p ^ k := Nat.pow_le_pow_left hp.out.two_le k
      have h5 : padicValNat p (k + 1) ≤ k := by
        by_contra hcon
        rw [not_le] at hcon
        have h6 : p ^ (k + 1) ≤ p ^ padicValNat p (k + 1) :=
          Nat.pow_le_pow_right hp.out.pos (by omega)
        have h7 : p ^ k < p ^ (k + 1) :=
          Nat.pow_lt_pow_right hp.out.one_lt (by omega)
        omega
      rw [h1, ← zpow_neg, neg_neg]
      calc ((p : ℝ)⁻¹) ^ k * (p : ℝ) ^ ((padicValNat p (k + 1) : ℤ))
          ≤ ((p : ℝ)⁻¹) ^ k * (p : ℝ) ^ ((k : ℤ)) := by
            refine mul_le_mul_of_nonneg_left
              (zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) ?_) (by positivity)
            exact_mod_cast h5
        _ = 1 := by
            rw [← zpow_natCast ((p : ℝ)⁻¹) k, inv_zpow, ← zpow_neg,
              ← zpow_add₀ (by exact_mod_cast hp.out.pos.ne' : (p : ℝ) ≠ 0)]
            simp
    rw [hfac, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      hgeom, norm_mul, hxy, PadicInt.padic_norm_e_of_padicInt, hkcast,
      div_eq_mul_inv]
    calc ‖∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i)‖ * ‖u - v‖
          * ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹
        = ‖u - v‖ * (‖∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i)‖
            * ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹) := by ring
      _ ≤ ‖u - v‖ * (((p : ℝ)⁻¹) ^ k * ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumnorm ?_)
            (norm_nonneg _)
          positivity
      _ ≤ ‖u - v‖ * 1 := mul_le_mul_of_nonneg_left hknorm (norm_nonneg _)
      _ = ‖u - v‖ := mul_one _
  rw [hsub]
  refine (TateFredholm.norm_tsum_le_iSup ?_).trans
    (Real.iSup_le hterm (norm_nonneg _))
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (a := fun k : ℕ => max
    ‖(-1 : ℚ_[p]) ^ k * x ^ (k + 1) / ((k : ℚ_[p]) + 1)‖
    ‖(-1 : ℚ_[p]) ^ k * y ^ (k + 1) / ((k : ℚ_[p]) + 1)‖) (fun k => ?_) ?_
  · rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
  · have h1 := tendsto_qlog_term hu
    have h2 := tendsto_qlog_term hv
    rw [Nat.cofinite_eq_atTop] at h1 h2
    have h3 := h1.norm.max h2.norm
    simpa using h3


end LWX
