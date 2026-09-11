/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.Touching
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Classical points of the halo — SKELETON (tranche 6 of `lwx-theta`)

[LWX, §3.23] runs Step I at "the classical weights `χ_k = (k, ψ)` of conductor `q²` with
`k ∈ ℤ_{≥0}`, such that `χ_k|_Δ = ω`.  The corresponding `T`-coordinates `T_{χ_k}` have valuation
`q/ϕ(q²) = p/(q(p−1)) < 1`" (`lwx.txt:1794–1798`).  With `q = p` (odd `p`):
`T_{χ_k} = χ_k(exp p) − 1 = ζ·exp(pk) − 1` for `ζ = ψ(exp p)` a primitive `p`-th root of unity,
and `v(T_{χ_k}) = v(ζ − 1) = 1/(p−1)`.

This file supplies what `Touching.lean`'s `ClassicalData` asks of such a point, at level `h = 1`
(conductor `p²`, [LWX]'s `Iw_{q²}`):

* the halo conditions `p⁻¹ < ‖T_{χ_k}‖ < 1` and `‖T'_1‖² < p⁻¹` (`T'_1 = (1+T_{χ_k})^p − 1
  = exp(p²k) − 1`, since `ζ^p = 1`);
* the classical norm `‖T_{χ_k}‖^{p−1} = ‖p‖`;
* the level-`1` halo exponent is the integer `k` (`haloExponentH_one_classicalPoint`), so the
  binomial series in `autFactor_haloWeightH` is the polynomial `(1 + (c/d)z)^k` and the halo
  weight has the classical shape of exponent `k`, with nebentypus constants
  `u = haloCharFunH(d)·d^{−k}`.

What is **not** done here: identifying `haloCharFunH` at a classical point with `d ↦ d^k ψ(d)`.
Step I does not need it (the constants `u` are carried abstractly); Step III's intertwining
needs the constants of the source weight `(k, ψ)` and the target weight `(−k−2, ψ)` to agree,
which does need it — see `StepThree.lean` and the gap `AG-ζ` on the board.
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### Primitive `p`-th roots of unity in `K` -/

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A `p`-th root of unity is a `1`-unit: `(ζ − 1)^p ≡ ζ^p − 1 = 0 (mod p)`. -/
theorem norm_sub_one_lt_one_of_isPrimitiveRoot [IsUltrametricDist K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ < 1) : ‖ζ - 1‖ < 1 := by
  have hp0 : 0 < p := hp.out.pos
  have hζ1 : ζ ^ p = 1 := hζ.pow_eq_one
  set w : K := ζ - 1 with hw
  have hexp : ∑ i ∈ Finset.range (p + 1), (Nat.choose p i : K) * w ^ i = 1 := by
    have : (w + 1) ^ p = 1 := by rw [hw, sub_add_cancel]; exact hζ1
    rw [add_pow] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [one_pow, mul_one, mul_comm]
  have hsplit : w ^ p = -∑ i ∈ Finset.Ioo 0 p, (Nat.choose p i : K) * w ^ i := by
    have hrange : Finset.range (p + 1)
        = insert 0 (insert p (Finset.Ioo 0 p)) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
      omega
    rw [hrange, Finset.sum_insert (by simp [Finset.mem_Ioo]; omega),
      Finset.sum_insert (by simp [Finset.mem_Ioo])] at hexp
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul,
      Nat.choose_self] at hexp
    linear_combination hexp
  have hnormw : ‖w‖ ≤ 1 := by
    have hζn : ‖ζ‖ = 1 := by
      have h1 : ‖ζ‖ ^ p = 1 := by rw [← norm_pow, hζ1, norm_one]
      rcases lt_trichotomy ‖ζ‖ 1 with hlt | heq | hgt
      · have := pow_lt_one₀ (norm_nonneg ζ) hlt hp0.ne'
        linarith
      · exact heq
      · have := one_lt_pow₀ hgt hp0.ne'
        linarith
    calc ‖w‖ = ‖ζ - 1‖ := rfl
      _ ≤ max ‖ζ‖ ‖(1 : K)‖ := norm_sub_le_max_norm ζ 1
      _ = 1 := by rw [hζn, norm_one, max_self]
  have hterm : ∀ i ∈ Finset.Ioo 0 p, ‖(Nat.choose p i : K) * w ^ i‖ ≤ ‖((p : ℕ) : K)‖ := by
    intro i hi
    rw [Finset.mem_Ioo] at hi
    obtain ⟨m, hm⟩ := hp.out.dvd_choose_self hi.1.ne' hi.2
    rw [hm, Nat.cast_mul, norm_mul, norm_mul]
    calc ‖((p : ℕ) : K)‖ * ‖((m : ℕ) : K)‖ * ‖w ^ i‖
        ≤ ‖((p : ℕ) : K)‖ * 1 * 1 := by
          gcongr
          · exact IsUltrametricDist.norm_natCast_le_one K m
          · rw [norm_pow]
            exact pow_le_one₀ (norm_nonneg _) hnormw
      _ = ‖((p : ℕ) : K)‖ := by ring
  have hwp : ‖w‖ ^ p < 1 := by
    calc ‖w‖ ^ p = ‖w ^ p‖ := (norm_pow w p).symm
      _ = ‖∑ i ∈ Finset.Ioo 0 p, (Nat.choose p i : K) * w ^ i‖ := by rw [hsplit, norm_neg]
      _ ≤ ‖((p : ℕ) : K)‖ :=
          IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hterm
      _ < 1 := hpK
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd hwp (not_lt.2 (one_le_pow₀ hcon))

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **[C6.1a]** A root of unity has norm one. -/
theorem norm_of_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p) : ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ p = 1 := by rw [← norm_pow, hζ.pow_eq_one, norm_one]
  rcases lt_trichotomy ‖ζ‖ 1 with hlt | heq | hgt
  · have := pow_lt_one₀ (norm_nonneg ζ) hlt hp.out.pos.ne'
    linarith
  · exact heq
  · have := one_lt_pow₀ hgt hp.out.pos.ne'
    linarith

omit [CompleteSpace K] [CharZero K] in
/-- **[C6.1a]** A natural number prime to `p` is a unit of the valuation ring: Bezout plus
`‖p‖ < 1`. -/
theorem norm_natCast_eq_one_of_not_dvd {i : ℕ} (hpi : ¬ p ∣ i)
    (hpK : ‖((p : ℕ) : K)‖ < 1) : ‖((i : ℕ) : K)‖ = 1 := by
  have hcop : Nat.Coprime p i := (Nat.coprime_or_dvd_of_prime hp.out i).resolve_right hpi
  have hbez : ((Nat.gcdA p i : ℤ) : K) * ((p : ℕ) : K) + ((Nat.gcdB p i : ℤ) : K) * ((i : ℕ) : K)
      = 1 := by
    have hz := Nat.gcd_eq_gcd_ab p i
    rw [hcop] at hz
    have := congrArg (fun z : ℤ => ((z : ℤ) : K)) hz
    push_cast at this
    linear_combination -this
  have hle : (1 : ℝ) ≤ max ‖((p : ℕ) : K)‖ ‖((i : ℕ) : K)‖ := by
    calc (1 : ℝ) = ‖((Nat.gcdA p i : ℤ) : K) * ((p : ℕ) : K)
          + ((Nat.gcdB p i : ℤ) : K) * ((i : ℕ) : K)‖ := by rw [hbez, norm_one]
      _ ≤ max ‖((Nat.gcdA p i : ℤ) : K) * ((p : ℕ) : K)‖
            ‖((Nat.gcdB p i : ℤ) : K) * ((i : ℕ) : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max ‖((p : ℕ) : K)‖ ‖((i : ℕ) : K)‖ := by
          gcongr
          · rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _)
              (IsUltrametricDist.norm_intCast_le_one (R := K) (Nat.gcdA p i))
          · rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _)
              (IsUltrametricDist.norm_intCast_le_one (R := K) (Nat.gcdB p i))
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K i) ?_
  rcases max_cases ‖((p : ℕ) : K)‖ ‖((i : ℕ) : K)‖ with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he] at hle; linarith
  · rw [he] at hle; linarith

omit [CompleteSpace K] [CharZero K] in
/-- `‖1 − ζ^i‖ = ‖1 − ζ‖` for `0 < i < p`: the cofactor `1 + ζ + ⋯ + ζ^{i−1} ≡ i (mod ζ − 1)` is a
unit. -/
theorem norm_one_sub_pow_of_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ < 1) {i : ℕ} (hi0 : 0 < i) (hip : i < p) :
    ‖1 - ζ ^ i‖ = ‖1 - ζ‖ := by
  have hζn : ‖ζ‖ = 1 := norm_of_isPrimitiveRoot hζ
  have hgeom : ∀ m : ℕ, ‖∑ j ∈ Finset.range m, ζ ^ j‖ ≤ 1 := fun m =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => by
      rw [norm_pow, hζn, one_pow]
  have hpow : ∀ j : ℕ, ‖ζ ^ j - 1‖ ≤ ‖ζ - 1‖ := fun j => by
    calc ‖ζ ^ j - 1‖ = ‖(∑ l ∈ Finset.range j, ζ ^ l) * (ζ - 1)‖ := by rw [geom_sum_mul]
      _ = ‖∑ l ∈ Finset.range j, ζ ^ l‖ * ‖ζ - 1‖ := norm_mul _ _
      _ ≤ 1 * ‖ζ - 1‖ := by gcongr; exact hgeom j
      _ = ‖ζ - 1‖ := one_mul _
  have hlt : ‖ζ - 1‖ < 1 := norm_sub_one_lt_one_of_isPrimitiveRoot hζ hpK
  have hi : ‖((i : ℕ) : K)‖ = 1 :=
    norm_natCast_eq_one_of_not_dvd (fun hdvd => by
      have := Nat.le_of_dvd hi0 hdvd
      omega) hpK
  have hsum : ‖∑ j ∈ Finset.range i, ζ ^ j‖ = 1 := by
    have hdiff : ‖(∑ j ∈ Finset.range i, ζ ^ j) - ((i : ℕ) : K)‖ < 1 := by
      have hrw : (∑ j ∈ Finset.range i, ζ ^ j) - ((i : ℕ) : K)
          = ∑ j ∈ Finset.range i, (ζ ^ j - 1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hrw]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (norm_nonneg _) fun j _ => hpow j) hlt
    calc ‖∑ j ∈ Finset.range i, ζ ^ j‖
        = ‖((∑ j ∈ Finset.range i, ζ ^ j) - ((i : ℕ) : K)) + ((i : ℕ) : K)‖ := by
          rw [sub_add_cancel]
      _ = max ‖(∑ j ∈ Finset.range i, ζ ^ j) - ((i : ℕ) : K)‖ ‖((i : ℕ) : K)‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hi]; exact hdiff.ne)
      _ = 1 := by rw [hi, max_eq_right hdiff.le]
  calc ‖1 - ζ ^ i‖ = ‖ζ ^ i - 1‖ := by rw [← norm_neg (1 - ζ ^ i), neg_sub]
    _ = ‖(∑ j ∈ Finset.range i, ζ ^ j) * (ζ - 1)‖ := by rw [geom_sum_mul]
    _ = 1 * ‖ζ - 1‖ := by rw [norm_mul, hsum]
    _ = ‖ζ - 1‖ := one_mul _
    _ = ‖1 - ζ‖ := by rw [← norm_neg (ζ - 1), neg_sub]

omit [CompleteSpace K] [CharZero K] in
/-- **`v(ζ − 1) = v(p)/(p−1)`**: `∏_{0<i<p} (1 − ζ^i) = Φ_p(1) = p`, all factors of equal norm. -/
theorem norm_sub_one_pow_of_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ < 1) : ‖ζ - 1‖ ^ (p - 1) = ‖((p : ℕ) : K)‖ := by
  have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.out.pos
  have hζ' : IsPrimitiveRoot ζ ((p - 1) + 1) := by rwa [hp1]
  have hprod := hζ'.prod_one_sub_pow_eq_order
  have hcast : (((p - 1 : ℕ) : K) + 1) = ((p : ℕ) : K) := by
    rw [← Nat.cast_one (R := K), ← Nat.cast_add, hp1]
  rw [hcast] at hprod
  have hnorm : ‖((p : ℕ) : K)‖ = ∏ j ∈ Finset.range (p - 1), ‖1 - ζ ^ (j + 1)‖ := by
    rw [← norm_prod, hprod]
  rw [hnorm, Finset.prod_congr rfl (fun j hj =>
      norm_one_sub_pow_of_isPrimitiveRoot hζ hpK (Nat.succ_pos j)
        (by have := Finset.mem_range.1 hj; omega)),
    Finset.prod_const, Finset.card_range, ← norm_neg (1 - ζ), neg_sub]

/-! ### The classical point -/

variable (p) in
/-- **The classical point** `T_{χ_k} = χ_k(exp p) − 1 = ζ·exp(pk) − 1` of the weight
`χ_k = (k, ψ)`, `ψ` of conductor `p²` with `ψ(exp p) = ζ` ([LWX, §3.23], `lwx.txt:1794–1798`). -/
def classicalPoint (k : ℕ) (ζ : K) : K :=
  ζ * PadicExpLog.padicExp (((p : ℕ) : K) * k) - 1

omit [CompleteSpace K] [CharZero K] in
/-- **[C6.4a]** `‖p·k‖² < ‖p‖`: the exponential's disc contains `p·k` for every `k`. -/
private theorem norm_p_mul_natCast_sq_lt (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖((p : ℕ) : K) * ((k : ℕ) : K)‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  have hple : ‖((p : ℕ) : K) * ((k : ℕ) : K)‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, hpK]
    exact mul_le_of_le_one_right h0.le (IsUltrametricDist.norm_natCast_le_one K k)
  calc ‖((p : ℕ) : K) * ((k : ℕ) : K)‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := by gcongr
    _ < (p : ℝ)⁻¹ := by nlinarith
    _ = ‖((p : ℕ) : K)‖ := hpK.symm

/-- **[C6.4a]** `‖exp(p·k) − 1‖ ≤ p⁻¹`. -/
private theorem norm_padicExp_p_mul_sub_one_le (hp2 : p ≠ 2)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖PadicExpLog.padicExp (((p : ℕ) : K) * ((k : ℕ) : K)) - 1‖ ≤ (p : ℝ)⁻¹ := by
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  refine (PadicExpLog.norm_padicExp_sub_one_le (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2
    (norm_p_mul_natCast_sq_lt hpK k)).trans ?_
  rw [norm_mul, hpK]
  exact mul_le_of_le_one_right h0.le (IsUltrametricDist.norm_natCast_le_one K k)

omit [CompleteSpace K] [CharZero K] in
/-- **[C6.4a]** `p⁻¹ < ‖ζ − 1‖`: the valuation of `ζ − 1` is `1/(p−1) < 1` for odd `p`. -/
theorem inv_lt_norm_sub_one_of_isPrimitiveRoot (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) : (p : ℝ)⁻¹ < ‖ζ - 1‖ := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  have hpow := norm_sub_one_pow_of_isPrimitiveRoot hζ (by rw [hpK]; exact hp1)
  rw [hpK] at hpow
  by_contra hcon
  rw [not_lt] at hcon
  have h2 : ((p : ℝ)⁻¹) ^ (p - 1) ≤ ((p : ℝ)⁻¹) ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, p - 1 = 2 + m := ⟨p - 3, by omega⟩
    rw [hm, pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ h0.le hp1.le)
  have h3 : ‖ζ - 1‖ ^ (p - 1) ≤ ((p : ℝ)⁻¹) ^ (p - 1) := by gcongr
  rw [hpow] at h3
  nlinarith

/-- `‖T_{χ_k}‖ = ‖ζ − 1‖`: the factor `exp(pk)` is a `1`-unit closer to `1` than `ζ`. -/
theorem norm_classicalPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ = ‖ζ - 1‖ := by
  set E : K := PadicExpLog.padicExp (((p : ℕ) : K) * ((k : ℕ) : K)) with hE
  have hE1 : ‖E - 1‖ ≤ (p : ℝ)⁻¹ := norm_padicExp_p_mul_sub_one_le hp2 hpK k
  have hEn : ‖E‖ = 1 := norm_eq_one_of_norm_sub_le (p := p) norm_one hE1
  have hgt : (p : ℝ)⁻¹ < ‖ζ - 1‖ := inv_lt_norm_sub_one_of_isPrimitiveRoot hp2 hζ hpK
  have hsplit : classicalPoint p k ζ = (ζ - 1) * E + (E - 1) := by
    rw [classicalPoint, hE]; ring
  have hne : ‖(ζ - 1) * E‖ ≠ ‖E - 1‖ := by
    rw [norm_mul, hEn, mul_one]
    exact fun hcon => absurd (hcon ▸ hE1) (not_le.2 hgt)
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_mul, hEn, mul_one,
    max_eq_left (hE1.trans hgt.le)]

/-- The classical norm condition of `ClassicalData`: `‖T_{χ_k}‖^{p−1} = ‖p‖`. -/
theorem norm_classicalPoint_pow (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ ^ (p - 1) = ‖((p : ℕ) : K)‖ := by
  rw [norm_classicalPoint hp2 hζ hpK k]
  exact norm_sub_one_pow_of_isPrimitiveRoot hζ (by rw [hpK]; exact inv_lt_one_p (p := p))

/-- The classical point lies in the halo annulus: `p⁻¹ < ‖T_{χ_k}‖`. -/
theorem inv_lt_norm_classicalPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖ := by
  rw [norm_classicalPoint hp2 hζ hpK k]
  exact inv_lt_norm_sub_one_of_isPrimitiveRoot hp2 hζ hpK

/-- The classical point lies in the halo annulus: `‖T_{χ_k}‖ < 1`. -/
theorem norm_classicalPoint_lt_one (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ < 1 := by
  rw [norm_classicalPoint hp2 hζ hpK k]
  exact norm_sub_one_lt_one_of_isPrimitiveRoot hζ (by rw [hpK]; exact inv_lt_one_p (p := p))

/-- **[C6.8a]** `exp(w)^n = exp(n·w)` on the exponential's disc (induction from
`PadicExpLog.padicExp_add`). -/
private theorem padicExp_pow (h3 : ‖((p : ℕ) : K)‖ < 1) (hp2 : p ≠ 2) {w : K}
    (hw : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖) (n : ℕ) :
    PadicExpLog.padicExp w ^ n = PadicExpLog.padicExp ((n : K) * w) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, PadicExpLog.padicExp_zero]
  | succ n ih =>
    have hnw : ‖(n : K) * w‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
      calc ‖(n : K) * w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
            gcongr
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _)
              (IsUltrametricDist.norm_natCast_le_one K n)
        _ < ‖((p : ℕ) : K)‖ := hw
    rw [pow_succ, ih, ← PadicExpLog.padicExp_add h3 hp2 hnw hw]
    congr 1
    push_cast
    ring

/-- At level `1` the wild part disappears: `(1 + T_{χ_k})^p − 1 = exp(p²k) − 1`. -/
theorem TH_one_classicalPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    TH p 1 (classicalPoint p k ζ) = PadicExpLog.padicExp (((p : ℕ) : K) ^ 2 * k) - 1 := by
  have hdisc := norm_p_mul_natCast_sq_lt (K := K) hpK k
  rw [TH, classicalPoint, show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring,
    pow_one, mul_pow, hζ.pow_eq_one, one_mul,
    padicExp_pow (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2 hdisc p]
  congr 2
  ring

/-- The level-`1` analyticity condition at the classical point. -/
theorem norm_TH_one_classicalPoint_sq_lt (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹ := by
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  have hle : ‖TH p 1 (classicalPoint p k ζ)‖ ≤ (p : ℝ)⁻¹ := by
    rw [TH_one_classicalPoint hp2 hζ hpK k]
    refine (PadicExpLog.norm_padicExp_sub_one_le (by rw [hpK]; exact hp1) hp2 ?_).trans ?_
    · calc ‖((p : ℕ) : K) ^ 2 * ((k : ℕ) : K)‖ ^ 2
          ≤ ‖((p : ℕ) : K) * ((k : ℕ) : K)‖ ^ 2 := by
            gcongr
            rw [norm_mul, norm_mul, norm_pow, hpK]
            gcongr
            calc ((p : ℝ)⁻¹) ^ 2 ≤ ((p : ℝ)⁻¹) ^ 1 := by
                  exact pow_le_pow_of_le_one h0.le hp1.le (by omega)
              _ = (p : ℝ)⁻¹ := pow_one _
        _ < ‖((p : ℕ) : K)‖ := norm_p_mul_natCast_sq_lt hpK k
    · rw [norm_mul, norm_pow, hpK]
      calc ((p : ℝ)⁻¹) ^ 2 * ‖((k : ℕ) : K)‖ ≤ ((p : ℝ)⁻¹) ^ 2 * 1 := by
            gcongr
            exact IsUltrametricDist.norm_natCast_le_one K k
        _ = ((p : ℝ)⁻¹) ^ 2 := mul_one _
        _ ≤ (p : ℝ)⁻¹ := by nlinarith
  calc ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := by gcongr
    _ < (p : ℝ)⁻¹ := by nlinarith

/-- **The level-`1` halo exponent at a classical point is `k`**:
`s_1 = log(exp(p²k))/p² = k`. -/
theorem haloExponentH_one_classicalPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    haloExponentH p 1 (classicalPoint p k ζ) = k := by
  have h0 : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.pos.ne'
  have hdisc : ‖((p : ℕ) : K) ^ 2 * ((k : ℕ) : K)‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    calc ‖((p : ℕ) : K) ^ 2 * ((k : ℕ) : K)‖ ^ 2
        ≤ ‖((p : ℕ) : K) * ((k : ℕ) : K)‖ ^ 2 := by
          gcongr
          rw [norm_mul, norm_mul, norm_pow, hpK]
          gcongr
          calc ((p : ℝ)⁻¹) ^ 2 ≤ ((p : ℝ)⁻¹) ^ 1 := by
                refine pow_le_pow_of_le_one ?_ (inv_lt_one_p (p := p)).le (by omega)
                have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
                positivity
            _ = (p : ℝ)⁻¹ := pow_one _
      _ < ‖((p : ℕ) : K)‖ := norm_p_mul_natCast_sq_lt hpK k
  rw [haloExponentH, TH_one_classicalPoint hp2 hζ hpK k,
    show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring,
    PadicExpLog.padicLog_padicExp (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2 hdisc]
  field_simp
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The binomial series with a natural exponent is the polynomial `(1 + x·z)^k`. -/
theorem mk_choose_natCast_mul_pow (k : ℕ) (x : K) :
    PowerSeries.mk (fun m => Ring.choose (k : K) m * x ^ m)
      = (1 + PowerSeries.C x * PowerSeries.X) ^ k := by
  refine PowerSeries.ext fun m => ?_
  have key : ∀ i : ℕ, (PowerSeries.coeff m) ((PowerSeries.C x * PowerSeries.X) ^ i
        * (1 : PowerSeries K) ^ (k - i) * ((k.choose i : ℕ) : PowerSeries K))
      = if m = i then x ^ i * ((k.choose i : ℕ) : K) else 0 := by
    intro i
    rw [one_pow, mul_one, mul_pow, ← map_pow,
      ← map_natCast (PowerSeries.C : K →+* PowerSeries K) (k.choose i),
      mul_comm (PowerSeries.C (x ^ i) * PowerSeries.X ^ i), ← mul_assoc, ← map_mul,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs with hmi
    · rw [mul_one, mul_comm]
    · rw [mul_zero]
  rw [PowerSeries.coeff_mk, Ring.choose_natCast, add_comm (1 : PowerSeries K), add_pow, map_sum,
    Finset.sum_congr rfl (fun i _ => key i), Finset.sum_ite_eq (Finset.range (k + 1)) m]
  by_cases hm : m ∈ Finset.range (k + 1)
  · rw [if_pos hm, mul_comm]
  · rw [if_neg hm, Finset.mem_range, not_lt] at *
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-! ### The halo weight at a classical point has the classical shape -/

variable (ψ : ℚ_[p] →+* K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **The automorphy factor of the halo weight at a classical point** is
`haloCharFunH(d)·d^{−k}·(cz + d)^k`. -/
theorem autFactor_haloWeightH_classicalPoint (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖)
    (h1 : ‖classicalPoint p k ζ‖ < 1) (hT : ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹)
    (g : M1Kh 1 ψ) :
    (haloWeightH 1 ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1
        * linX g.1
      = PowerSeries.C (haloCharFunH 1 ψ (classicalPoint p k ζ) ω (g.1 1 1) * (g.1 1 1)⁻¹ ^ k)
        * linX g.1 ^ (k + 1) := by
  have hd0 : g.1 1 1 ≠ 0 := (levelBounds_M1Kh 1 ψ (classicalPoint p k ζ) hψ hT).d_ne_zero g.2
  have hlin : (1 : PowerSeries K) + PowerSeries.C (g.1 1 0 / g.1 1 1) * PowerSeries.X
      = PowerSeries.C (g.1 1 1)⁻¹ * linX g.1 := by
    simp only [linX, mul_add, ← map_mul, inv_mul_cancel₀ hd0, ← mul_assoc]
    rw [show (g.1 1 1)⁻¹ * g.1 1 0 = g.1 1 0 / g.1 1 1 by field_simp, map_one]
  rw [autFactor_haloWeightH 1 ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT g,
    haloExponentH_one_classicalPoint hp2 hζ (norm_natCast_p ψ hψ) k,
    mk_choose_natCast_mul_pow k (g.1 1 0 / g.1 1 1), hlin, mul_pow, ← map_pow, map_mul, pow_succ]
  ring

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (uu : ι → Fin p → U)

/-- **The classical shape of the halo weight at a classical point**, with the nebentypus
constants `u i t a = haloCharFunH(d)·d^{−k}` at the lower-right entry `d` of the disc conjugate. -/
theorem isClassicalShape_haloWeightH_classicalPoint (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖)
    (h1 : ‖classicalPoint p k ζ‖ < 1) (hT : ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹) :
    IsClassicalShape θG 1 ψ U hU vRep hvΔ uu
      (haloWeightH 1 ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT) k
      fun i t a => haloCharFunH 1 ψ (classicalPoint p k ζ) ω
          (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k :=
  fun i t a => autFactor_haloWeightH_classicalPoint ψ ω hp2 hψ hζ k h0 h1 hT
    (discConjK 1 (certM1 θG U hU vRep hvΔ uu i t) a ψ)

/-- **The classical datum at a classical point**: everything `Touching.lean`'s Step I asks of
`T_{χ_k}`, assembled. -/
def classicalData (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω (classicalPoint p k ζ) k where
  h0 := inv_lt_norm_classicalPoint hp2 hζ hpK k
  h1 := norm_classicalPoint_lt_one hp2 hζ hpK k
  hT := norm_TH_one_classicalPoint_sq_lt hp2 hζ hpK k
  hnorm := by rw [norm_classicalPoint_pow hp2 hζ hpK k, map_natCast]
  u := fun i t a => haloCharFunH 1 ψ (classicalPoint p k ζ) ω
      (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
    * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k
  shape := isClassicalShape_haloWeightH_classicalPoint ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ k _ _ _

end LWX

end
