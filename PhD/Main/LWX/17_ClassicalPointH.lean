/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«15_TouchingH»
import PhD.Main.LWX.«16_TargetPoint»

/-!
# Classical points of conductor `p^{h+1}`

[LWX, §2.1] (`lwx.txt:466–478`): "a continuous character `χ` of `ℤ_p^×` is classical if it
sends `x` to `x^k ψ(x)` for an integer `k ≥ 0` and a finite character `ψ` of conductor `p^m`
… `v(T_{(k,ψ)}) = 1/p^{m−2}(p−1)` if `m ≥ 2`".  With `m = h + 1`, `h ≥ 1`, and `q = p`:
the `T`-coordinate is `T_{(k,ψ)} = χ(exp p) − 1 = ζ·exp(pk) − 1` — **the same formula as at
level `1`** (`classicalPoint p k ζ`, `weightPoint p s ζ`), but now with `ζ = ψ(exp p)` a
primitive `p^h`-th root of unity, and `v(ζ − 1) = 1/(p^{h−1}(p−1)) = 1/ϕ(p^h)`.

This file supplies what `15_TouchingH.lean`'s `ClassicalDataH` asks of such a point:

* the norm of a primitive `p^h`-th root of unity minus one, `‖ζ − 1‖^{ϕ(p^h)} = ‖p‖`, from
  `Φ_{p^h}(1) = p` (`Polynomial.eval_one_cyclotomic_prime_pow`) and the equality of the norms
  `‖1 − ζ^i‖ = ‖1 − ζ‖` for `p ∤ i`;
* the halo conditions `p⁻¹ < ‖T‖ < 1` and the level-`h` analyticity `‖T'_h‖² < p⁻¹`, where
  `T'_h = (1 + T)^{p^h} − 1 = exp(p^{h+1}s) − 1` since `ζ^{p^h} = 1`;
* the level-`h` halo exponent `s_h = log(exp(p^{h+1}s))/p^{h+1} = s`, so the level-`h` halo
  weight at the classical point has the classical shape of exponent `k`
  (`isClassicalShape_haloWeightH_classicalPoint_prime_pow`), assembled as `classicalDataH`.

Everything is stated for the weight points `weightPoint p s ζ`, `s ∈ ℤ`, and specialised to
`classicalPoint p k ζ = weightPoint p k ζ` (`weightPoint_natCast`); the lemmas that only use
`ζ^{p^h} = 1` are stated with that hypothesis.  Nothing here depends on Jacquet–Langlands.
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### Roots of unity of prime-power order -/

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A root of unity has norm one. -/
theorem norm_eq_one_of_pow_eq_one {ζ : K} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, hζ, norm_one]
  rcases lt_trichotomy ‖ζ‖ 1 with hlt | heq | hgt
  · have := pow_lt_one₀ (norm_nonneg ζ) hlt hn
    linarith
  · exact heq
  · have := one_lt_pow₀ hgt hn
    linarith

omit [CompleteSpace K] [CharZero K] in
/-- **The inductive step of `‖ζ − 1‖ < 1`**: `(ζ − 1)^p ≡ ζ^p − 1 (mod p)` on the unit ball
(`add_pow` with `p ∣ C(p, i)` for `0 < i < p`), so `‖ζ^p − 1‖ < 1` forces `‖ζ − 1‖ < 1`. -/
theorem norm_sub_one_lt_one_of_norm_pow_sub_one_lt {ζ : K} (hζ : ‖ζ‖ ≤ 1)
    (hpK : ‖((p : ℕ) : K)‖ < 1) (h : ‖ζ ^ p - 1‖ < 1) : ‖ζ - 1‖ < 1 := by
  have hp0 : 0 < p := hp.out.pos
  set w : K := ζ - 1 with hw
  have hexp : ∑ i ∈ Finset.range (p + 1), (Nat.choose p i : K) * w ^ i = ζ ^ p := by
    have : (w + 1) ^ p = ζ ^ p := by rw [hw, sub_add_cancel]
    rw [add_pow] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [one_pow, mul_one, mul_comm]
  have hsplit : w ^ p = (ζ ^ p - 1) - ∑ i ∈ Finset.Ioo 0 p, (Nat.choose p i : K) * w ^ i := by
    have hrange : Finset.range (p + 1) = insert 0 (insert p (Finset.Ioo 0 p)) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
      omega
    rw [hrange, Finset.sum_insert (by simp [Finset.mem_Ioo]; omega),
      Finset.sum_insert (by simp [Finset.mem_Ioo])] at hexp
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul,
      Nat.choose_self] at hexp
    linear_combination hexp
  have hnormw : ‖w‖ ≤ 1 :=
    calc ‖w‖ = ‖ζ - 1‖ := rfl
      _ ≤ max ‖ζ‖ ‖(1 : K)‖ := norm_sub_le_max_norm ζ 1
      _ ≤ 1 := by rw [norm_one]; exact max_le hζ le_rfl
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
  have hsum : ‖∑ i ∈ Finset.Ioo 0 p, (Nat.choose p i : K) * w ^ i‖ < 1 :=
    lt_of_le_of_lt
      (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hterm) hpK
  have hwp : ‖w‖ ^ p < 1 := by
    rw [← norm_pow, hsplit]
    exact lt_of_le_of_lt (norm_sub_le_max_norm _ _) (max_lt h hsum)
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd hwp (not_lt.2 (one_le_pow₀ hcon))

omit [CompleteSpace K] [CharZero K] in
/-- A `p^h`-th root of unity is a `1`-unit (induction on `h` through
`norm_sub_one_lt_one_of_norm_pow_sub_one_lt`). -/
theorem norm_sub_one_lt_one_of_pow_prime_pow_eq_one {ζ : K} (hpK : ‖((p : ℕ) : K)‖ < 1) {h : ℕ}
    (hζ : ζ ^ p ^ h = 1) : ‖ζ - 1‖ < 1 := by
  induction h generalizing ζ with
  | zero =>
    rw [pow_zero, pow_one] at hζ
    rw [hζ, sub_self, norm_zero]
    exact one_pos
  | succ h ih =>
    have hζp : (ζ ^ p) ^ p ^ h = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hζ
    exact norm_sub_one_lt_one_of_norm_pow_sub_one_lt
      (norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp.out.ne_zero) hζ).le hpK (ih hζp)

omit [CompleteSpace K] [CharZero K] in
/-- `‖1 − ζ^i‖ = ‖1 − ζ‖` for `p ∤ i` and `ζ` a primitive `p^h`-th root of unity: `≤` by the
geometric sum `1 − ζ^i = (1 − ζ)(1 + ζ + ⋯ + ζ^{i−1})`, and `≥` by the same with `ζ = (ζ^i)^j`
for `ij ≡ 1 (mod p^h)` (`Nat.exists_mul_mod_eq_one_of_coprime`). -/
theorem norm_one_sub_pow_of_isPrimitiveRoot_prime_pow {ζ : K} {h : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (_hpK : ‖((p : ℕ) : K)‖ < 1) {i : ℕ} (hi : ¬ p ∣ i) :
    ‖1 - ζ ^ i‖ = ‖1 - ζ‖ := by
  have hpow : ∀ x : K, ‖x‖ ≤ 1 → ∀ j : ℕ, ‖x ^ j - 1‖ ≤ ‖x - 1‖ := by
    intro x hx j
    have hg : ‖∑ l ∈ Finset.range j, x ^ l‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    calc ‖x ^ j - 1‖ = ‖(∑ l ∈ Finset.range j, x ^ l) * (x - 1)‖ := by rw [geom_sum_mul]
      _ = ‖∑ l ∈ Finset.range j, x ^ l‖ * ‖x - 1‖ := norm_mul _ _
      _ ≤ 1 * ‖x - 1‖ := by gcongr
      _ = ‖x - 1‖ := one_mul _
  have hζn : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp.out.ne_zero) hζ.pow_eq_one
  rw [← norm_neg (1 - ζ ^ i), neg_sub, ← norm_neg (1 - ζ), neg_sub]
  refine le_antisymm (hpow ζ hζn.le i) ?_
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have h1 : ζ = 1 := by simpa using hζ.pow_eq_one
    simp [h1]
  · have hcop : Nat.Coprime i (p ^ h) :=
      Nat.Coprime.pow_right h ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hi).symm
    obtain ⟨m, -, hm⟩ :=
      Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hh.ne' hp.out.one_lt)
    have hζm : (ζ ^ i) ^ m = ζ := by
      rw [← pow_mul, ← pow_mod_orderOf, ← hζ.eq_orderOf, hm, pow_one]
    have hζin : ‖ζ ^ i‖ ≤ 1 := by rw [norm_pow, hζn, one_pow]
    calc ‖ζ - 1‖ = ‖(ζ ^ i) ^ m - 1‖ := by rw [hζm]
      _ ≤ ‖ζ ^ i - 1‖ := hpow (ζ ^ i) hζin m

omit [CompleteSpace K] [CharZero K] in
/-- **`v(ζ − 1) = v(p)/ϕ(p^h)`** for a primitive `p^h`-th root of unity, `h ≥ 1`:
`∏_{μ primitive} (1 − μ) = Φ_{p^h}(1) = p` (`Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`,
`Polynomial.eval_one_cyclotomic_prime_pow`), with `ϕ(p^h) = p^{h−1}(p−1)` factors
(`IsPrimitiveRoot.card_primitiveRoots`, `Nat.totient_prime_pow`), all of norm `‖1 − ζ‖`. -/
theorem norm_sub_one_pow_of_isPrimitiveRoot_prime_pow {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ < 1) :
    ‖ζ - 1‖ ^ (p ^ (h - 1) * (p - 1)) = ‖((p : ℕ) : K)‖ := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  haveI : NeZero (p ^ (h' + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hev : Polynomial.eval 1 (Polynomial.cyclotomic (p ^ (h' + 1)) K) = ((p : ℕ) : K) :=
    Polynomial.eval_one_cyclotomic_prime_pow h'
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  have hfac : ∀ μ ∈ primitiveRoots (p ^ (h' + 1)) K, ‖1 - μ‖ = ‖1 - ζ‖ := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ (p ^ (h' + 1)) :=
      (mem_primitiveRoots (pow_pos hp.out.pos _)).1 hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    have hcop : Nat.Coprime i (p ^ (h' + 1)) :=
      (hζ.pow_iff_coprime (pow_pos hp.out.pos _) i).1 hμ'
    have hi : ¬ p ∣ i :=
      (Nat.Prime.coprime_iff_not_dvd hp.out).1
        (Nat.Coprime.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero h')) hcop.symm)
    exact norm_one_sub_pow_of_isPrimitiveRoot_prime_pow hζ hpK hi
  have hprod : ‖((p : ℕ) : K)‖ = ∏ μ ∈ primitiveRoots (p ^ (h' + 1)) K, ‖1 - μ‖ := by
    rw [← norm_prod, hev]
  rw [hprod, Finset.prod_congr rfl hfac, Finset.prod_const, hζ.card_primitiveRoots,
    Nat.totient_prime_pow_succ hp.out, ← norm_neg (1 - ζ), neg_sub]

omit [CompleteSpace K] [CharZero K] in
/-- `p⁻¹ < ‖ζ − 1‖`: the exponent `p^{h−1}(p−1) ≥ 2` for odd `p`. -/
theorem inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ}
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) :
    (p : ℝ)⁻¹ < ‖ζ - 1‖ := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  have hpow := norm_sub_one_pow_of_isPrimitiveRoot_prime_pow hh hζ (by rw [hpK]; exact hp1)
  rw [hpK] at hpow
  have he : 2 ≤ p ^ (h - 1) * (p - 1) :=
    le_trans (by omega : 2 ≤ p - 1) (Nat.le_mul_of_pos_left (p - 1) (pow_pos hp.out.pos _))
  by_contra hcon
  rw [not_lt] at hcon
  have h2 : ((p : ℝ)⁻¹) ^ (p ^ (h - 1) * (p - 1)) ≤ ((p : ℝ)⁻¹) ^ 2 :=
    pow_le_pow_of_le_one h0.le hp1.le he
  have h3 : ‖ζ - 1‖ ^ (p ^ (h - 1) * (p - 1)) ≤ ((p : ℝ)⁻¹) ^ (p ^ (h - 1) * (p - 1)) := by
    gcongr
  rw [hpow] at h3
  nlinarith

/-! ### The weight points of conductor `p^{h+1}` -/

omit [CompleteSpace K] [CharZero K] in
/-- `0 < p⁻¹` (level-`h` copy of `16_TargetPoint.lean`'s private helper). -/
private theorem inv_p_posH : (0 : ℝ) < (p : ℝ)⁻¹ := by
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A `p`-adically small element lies in the exponential's disc: `‖w‖ ≤ p⁻¹` gives
`‖w‖² < ‖p‖`. -/
private theorem norm_sq_lt_of_le_invH (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {w : K}
    (hw : ‖w‖ ≤ (p : ℝ)⁻¹) : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_p_posH (p := p)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  calc ‖w‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := by gcongr
    _ < (p : ℝ)⁻¹ := by nlinarith
    _ = ‖((p : ℕ) : K)‖ := hpK.symm

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p·x‖ ≤ p⁻¹` for `‖x‖ ≤ 1`. -/
private theorem norm_p_mul_le_invH (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖((p : ℕ) : K) * x‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_mul, hpK]
  exact mul_le_of_le_one_right (inv_p_posH (p := p)).le hx

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p·x‖² < ‖p‖` for `‖x‖ ≤ 1`: the exponential's disc contains `p·x`. -/
private theorem norm_p_mul_sq_ltH (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖((p : ℕ) : K) * x‖ ^ 2 < ‖((p : ℕ) : K)‖ :=
  norm_sq_lt_of_le_invH hpK (norm_p_mul_le_invH hpK hx)

/-- `‖exp(p·x) − 1‖ ≤ p⁻¹` for `‖x‖ ≤ 1`. -/
private theorem norm_padicExp_p_mul_sub_one_leH (hp2 : p ≠ 2)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖PadicExpLog.padicExp (((p : ℕ) : K) * x) - 1‖ ≤ (p : ℝ)⁻¹ :=
  (PadicExpLog.norm_padicExp_sub_one_le (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2
    (norm_p_mul_sq_ltH hpK hx)).trans (norm_p_mul_le_invH hpK hx)

/-- `‖T_{(s,ψ)}‖ = ‖ζ − 1‖`: the factor `exp(ps)` is a `1`-unit closer to `1` than `ζ`
(`norm_weightPoint` with `inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow`). -/
theorem norm_weightPoint_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ = ‖ζ - 1‖ := by
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  have hE1 : ‖PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K)) - 1‖ ≤ (p : ℝ)⁻¹ :=
    norm_padicExp_p_mul_sub_one_leH hp2 hpK hs
  have hEn : ‖PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K))‖ = 1 :=
    norm_eq_one_of_norm_sub_le (p := p) norm_one hE1
  have hgt : (p : ℝ)⁻¹ < ‖ζ - 1‖ := inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow hp2 hh hζ hpK
  have hsplit : weightPoint p s ζ
      = (ζ - 1) * PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K))
        + (PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K)) - 1) := by
    rw [weightPoint]; ring
  have hne : ‖(ζ - 1) * PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K))‖
      ≠ ‖PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K)) - 1‖ := by
    rw [norm_mul, hEn, mul_one]
    exact fun hcon => absurd (hcon ▸ hE1) (not_le.2 hgt)
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_mul, hEn, mul_one,
    max_eq_left (hE1.trans hgt.le)]

/-- The classical norm condition at conductor `p^{h+1}`: `‖T_{(s,ψ)}‖^{p^{h−1}(p−1)} = ‖p‖`. -/
theorem norm_weightPoint_pow_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ ^ (p ^ (h - 1) * (p - 1)) = ‖((p : ℕ) : K)‖ := by
  rw [norm_weightPoint_prime_pow hp2 hh hζ hpK s]
  exact norm_sub_one_pow_of_isPrimitiveRoot_prime_pow hh hζ
    (by rw [hpK]; exact inv_lt_one_p (p := p))

/-- The weight point lies in the halo annulus: `p⁻¹ < ‖T_{(s,ψ)}‖`. -/
theorem inv_lt_norm_weightPoint_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    (p : ℝ)⁻¹ < ‖weightPoint p s ζ‖ := by
  rw [norm_weightPoint_prime_pow hp2 hh hζ hpK s]
  exact inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow hp2 hh hζ hpK

/-- The weight point lies in the halo annulus: `‖T_{(s,ψ)}‖ < 1`. -/
theorem norm_weightPoint_lt_one_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ < 1 := by
  rw [norm_weightPoint_prime_pow hp2 hh hζ hpK s]
  exact norm_sub_one_lt_one_of_pow_prime_pow_eq_one (by rw [hpK]; exact inv_lt_one_p (p := p))
    hζ.pow_eq_one

/-- At level `h` the wild part disappears: `(1 + T_{(s,ψ)})^{p^h} − 1 = exp(p^{h+1}s) − 1`,
since `ζ^{p^h} = 1` (`PadicExpLog.padicExp_natCast_mul`). -/
theorem TH_weightPoint (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    TH p h (weightPoint p s ζ)
      = PadicExpLog.padicExp (((p : ℕ) : K) ^ (h + 1) * (s : K)) - 1 := by
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  rw [TH, weightPoint, show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring,
    mul_pow, hζ, one_mul,
    ← PadicExpLog.padicExp_natCast_mul (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2
      (norm_p_mul_sq_ltH hpK hs) (p ^ h)]
  congr 2
  push_cast
  ring

/-- The level-`h` analyticity condition at the weight point: `‖T'_h‖ ≤ p^{−(h+1)}`. -/
theorem norm_TH_weightPoint_sq_lt (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖TH p h (weightPoint p s ζ)‖ ^ 2 < (p : ℝ)⁻¹ := by
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_p_posH (p := p)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  have hx : ‖((p : ℕ) : K) ^ h * ((s : ℤ) : K)‖ ≤ 1 := by
    rw [norm_mul, norm_pow, hpK]
    exact mul_le_one₀ (pow_le_one₀ h0.le hp1.le) (norm_nonneg _) hs
  have hle : ‖TH p h (weightPoint p s ζ)‖ ≤ (p : ℝ)⁻¹ := by
    rw [TH_weightPoint hp2 hζ hpK s,
      show ((p : ℕ) : K) ^ (h + 1) * ((s : ℤ) : K)
          = ((p : ℕ) : K) * (((p : ℕ) : K) ^ h * ((s : ℤ) : K)) from by ring]
    exact norm_padicExp_p_mul_sub_one_leH hp2 hpK hx
  calc ‖TH p h (weightPoint p s ζ)‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := by gcongr
    _ < (p : ℝ)⁻¹ := by nlinarith

/-- **The level-`h` halo exponent at the weight point is `s`**:
`s_h = log(exp(p^{h+1}s))/p^{h+1} = s`. -/
theorem haloExponentH_weightPoint (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    haloExponentH p h (weightPoint p s ζ) = (s : K) := by
  have h0 : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.pos.ne'
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  have hx : ‖((p : ℕ) : K) ^ h * ((s : ℤ) : K)‖ ≤ 1 := by
    rw [norm_mul, norm_pow, hpK]
    exact mul_le_one₀ (pow_le_one₀ (inv_p_posH (p := p)).le (inv_lt_one_p (p := p)).le)
      (norm_nonneg _) hs
  have hdisc : ‖((p : ℕ) : K) ^ (h + 1) * ((s : ℤ) : K)‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [show ((p : ℕ) : K) ^ (h + 1) * ((s : ℤ) : K)
        = ((p : ℕ) : K) * (((p : ℕ) : K) ^ h * ((s : ℤ) : K)) from by ring]
    exact norm_p_mul_sq_ltH hpK hx
  rw [haloExponentH, TH_weightPoint hp2 hζ hpK s,
    show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring,
    PadicExpLog.padicLog_padicExp (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2 hdisc]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ h0)

/-! ### The classical points, `s = k ≥ 0` -/

/-- The classical norm condition at the classical point of conductor `p^{h+1}`. -/
theorem norm_classicalPoint_pow_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ ^ (p ^ (h - 1) * (p - 1)) = ‖((p : ℕ) : K)‖ := by
  rw [← weightPoint_natCast]
  exact norm_weightPoint_pow_prime_pow hp2 hh hζ hpK k

/-- `p⁻¹ < ‖T_{χ_k}‖` at conductor `p^{h+1}`. -/
theorem inv_lt_norm_classicalPoint_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖ := by
  rw [← weightPoint_natCast]
  exact inv_lt_norm_weightPoint_prime_pow hp2 hh hζ hpK k

/-- `‖T_{χ_k}‖ < 1` at conductor `p^{h+1}`. -/
theorem norm_classicalPoint_lt_one_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ < 1 := by
  rw [← weightPoint_natCast]
  exact norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK k

/-- The level-`h` analyticity condition at the classical point. -/
theorem norm_TH_classicalPoint_sq_lt (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖TH p h (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹ := by
  rw [← weightPoint_natCast]
  exact norm_TH_weightPoint_sq_lt hp2 hζ hpK k

/-- **The level-`h` halo exponent at a classical point is `k`**. -/
theorem haloExponentH_classicalPoint (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    haloExponentH p h (classicalPoint p k ζ) = k := by
  rw [← weightPoint_natCast, haloExponentH_weightPoint hp2 hζ hpK k, Int.cast_natCast]

/-! ### The level-`h` halo weight at a classical point has the classical shape -/

variable (ψ : ℚ_[p] →+* K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **The automorphy factor of the level-`h` halo weight at a classical point** is
`haloCharFunH(d)·d^{−k}·(cz + d)^k` (`autFactor_haloWeightH` with the halo exponent `k`,
`haloExponentH_classicalPoint`, and `mk_choose_natCast_mul_pow`). -/
theorem autFactor_haloWeightH_classicalPoint_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {ζ : K} (h : ℕ) (hζ : ζ ^ p ^ h = 1) (k : ℕ) (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖)
    (h1 : ‖classicalPoint p k ζ‖ < 1) (hT : ‖TH p h (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹)
    (g : M1Kh h ψ) :
    (haloWeightH h ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1
        * linX g.1
      = PowerSeries.C (haloCharFunH h ψ (classicalPoint p k ζ) ω (g.1 1 1) * (g.1 1 1)⁻¹ ^ k)
        * linX g.1 ^ (k + 1) := by
  have hd0 : g.1 1 1 ≠ 0 := (levelBounds_M1Kh h ψ (classicalPoint p k ζ) hψ hT).d_ne_zero g.2
  have hlin : (1 : PowerSeries K) + PowerSeries.C (g.1 1 0 / g.1 1 1) * PowerSeries.X
      = PowerSeries.C (g.1 1 1)⁻¹ * linX g.1 := by
    simp only [linX, mul_add, ← map_mul, inv_mul_cancel₀ hd0, ← mul_assoc]
    rw [show (g.1 1 1)⁻¹ * g.1 1 0 = g.1 1 0 / g.1 1 1 by field_simp, map_one]
  rw [autFactor_haloWeightH h ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT g,
    haloExponentH_classicalPoint hp2 hζ (norm_natCast_p ψ hψ) k,
    mk_choose_natCast_mul_pow k (g.1 1 0 / g.1 1 1), hlin, mul_pow, ← map_pow, map_mul, pow_succ]
  ring

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (uu : ι → Fin p → U)

omit [Fintype ι] [DecidableEq ι] in
/-- **The classical shape of the level-`h` halo weight at a classical point**, with the
nebentypus constants `u i t a = haloCharFunH(d)·d^{−k}` at the lower-right entry `d` of the
disc conjugate. -/
theorem isClassicalShape_haloWeightH_classicalPoint_prime_pow (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} (h : ℕ) (hζ : ζ ^ p ^ h = 1) (k : ℕ)
    (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖) (h1 : ‖classicalPoint p k ζ‖ < 1)
    (hT : ‖TH p h (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹) :
    IsClassicalShape θG h ψ U hU vRep hvΔ uu
      (haloWeightH h ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT) k
      fun i t a => haloCharFunH h ψ (classicalPoint p k ζ) ω
          (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k :=
  fun i t a => autFactor_haloWeightH_classicalPoint_prime_pow ψ ω hp2 hψ h hζ k h0 h1 hT
    (discConjK h (certM1 θG U hU vRep hvΔ uu i t) a ψ)

/-- **The classical datum at a classical point of conductor `p^{h+1}`**: everything
`15_TouchingH.lean`'s Step I asks of `T_{χ_k}`, assembled. -/
def classicalDataH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω (classicalPoint p k ζ) k where
  h0 := inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k
  h1 := norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k
  hT := norm_TH_classicalPoint_sq_lt hp2 hζ.pow_eq_one hpK k
  hnorm := by rw [norm_classicalPoint_pow_prime_pow hp2 hh hζ hpK k, map_natCast]
  u := fun i t a => haloCharFunH h ψ (classicalPoint p k ζ) ω
      (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
    * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k
  shape := isClassicalShape_haloWeightH_classicalPoint_prime_pow ψ ω θG U hU vRep hvΔ uu hp2 hψ
    h hζ.pow_eq_one k _ _ _

end LWX

end
