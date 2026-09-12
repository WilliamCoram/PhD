/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Pochhammer
import PhD.Main.LWX.«00_PadicExpLog»

/-!
# The disc-restricted Colmez polynomials and their `p`-adic valuations — SKELETON

[Colmez, *Fonctions d'une variable p-adique*, Lemme 1.4.9] (the arithmetic heart of Amice's
theorem, [Colmez, Thm 1.4.7] = [LWX, §2.16 "Colm10, Théorème 1.29"]): for
`g_n = ⌊n/pʰ⌋!·(x choose n)` and a disc centre `a < pʰ`, the polynomial
`g_{n,a}(w) = g_n(a + pʰw)` has coefficients in `ℤ_p`, and its reduction modulo `p` is
controlled by the position of the disc `a` relative to the residue
`r(n) = n mod pʰ` and the degree `m(n) = ⌊n/pʰ⌋`.  Colmez centres the discs at `−j`
(`1 ≤ j ≤ pʰ`); we centre at the natural representative `a = n mod pʰ` — the translation
`w ↦ w + 1` of the unit disc does not change integrality, vanishing modulo `p`, or degrees.

The factorisation `g_{n,a} = c_{n,a}·f_{n,a}` ([Colmez, proof of 1.4.9]): each linear factor
`a − k + pʰw` is `pʰ(w − (k−a)/pʰ)` when `pʰ ∣ k − a` and `(a − k)(1 + pʰw/(a−k))` otherwise;
`f_{n,a}` (the product of the normalised factors) has `ℤ_p`-coefficients and reduces modulo `p`
to a monic polynomial of degree `|K_{n,a}|`, `K_{n,a} = {k < n : k ≡ a (pʰ)}`; the scalar
`c_{n,a}` has valuation `∑_{ℓ=1}^{h} [a mod pˡ < n mod pˡ] ≥ 0`.

## Main declarations

* `LWX.colmezPoly h n`, `LWX.discPoly h n a`, `LWX.discSupport`, `LWX.discFactor`,
  `LWX.discConst`, `LWX.discPoly_eq`.
* `LWX.norm_discConst`, `LWX.norm_coeff_discFactor_le`, `LWX.norm_coeff_discFactor_le_of_lt`,
  `LWX.norm_coeff_discFactor_card`.
* The three coefficient facts consumed by `08_AmiceBasis.lean`: `LWX.norm_coeff_discPoly_le`,
  `LWX.norm_coeff_discPoly_le_inv_of_lt`, `LWX.norm_coeff_discPoly_le_inv_of_res_lt`,
  `LWX.norm_coeff_discPoly_diag`.
-/

open Polynomial Finset

open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

section Counting

/-- The number of `k < n` with `k ≡ r (mod q)`, for `r < q`: `⌊n/q⌋ + [r < n mod q]`. -/
theorem card_filter_range_mod_eq (n r q : ℕ) (hq : 0 < q) (hr : r < q) :
    ((range n).filter fun k => k % q = r).card = n / q + if r < n % q then 1 else 0 := by
  classical
  have hdm : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have hb : n % q < q := Nat.mod_lt _ hq
  have key : ∀ m : ℕ, m * q + r < n ↔ m < n / q + if r < n % q then 1 else 0 := by
    intro m
    by_cases hrb : r < n % q
    · rw [if_pos hrb, Nat.lt_add_one_iff]
      constructor
      · intro h
        by_contra hcon
        push Not at hcon
        have h1 : (n / q + 1) * q ≤ m * q := Nat.mul_le_mul_right q hcon
        rw [add_mul, one_mul, mul_comm (n / q) q] at h1
        omega
      · intro h
        have h1 : m * q ≤ n / q * q := Nat.mul_le_mul_right q h
        rw [mul_comm (n / q) q] at h1
        omega
    · rw [if_neg hrb, add_zero]
      push Not at hrb
      constructor
      · intro h
        by_contra hcon
        push Not at hcon
        have h1 : n / q * q ≤ m * q := Nat.mul_le_mul_right q hcon
        rw [mul_comm (n / q) q] at h1
        omega
      · intro h
        have h1 : (m + 1) * q ≤ n / q * q := Nat.mul_le_mul_right q h
        rw [add_mul, one_mul, mul_comm (n / q) q] at h1
        omega
  have himg : (range n).filter (fun k => k % q = r)
      = (range (n / q + if r < n % q then 1 else 0)).image fun m => m * q + r := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, hkr⟩
      have hk2 : k / q * q + r = k := by
        conv_rhs => rw [← Nat.div_add_mod k q]
        rw [hkr, mul_comm]
      exact ⟨k / q, (key (k / q)).mp (by rw [hk2]; exact hk), hk2⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨(key m).mpr hm, by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt hr⟩
  rw [himg, Finset.card_image_of_injective _ fun a b h =>
    Nat.eq_of_mul_eq_mul_right hq (Nat.add_right_cancel h), Finset.card_range]

/-- Legendre's formula, truncated at `h`: `v_p(n!) − v_p(⌊n/pʰ⌋!) = ∑_{ℓ=1}^{h} ⌊n/pˡ⌋`. -/
theorem padicValNat_factorial_sub_factorial_div_pow (n h : ℕ) :
    padicValNat p (n !) = padicValNat p ((n / p ^ h)!) + ∑ ℓ ∈ Icc 1 h, n / p ^ ℓ := by
  have h1 : padicValNat p (n !) = ∑ i ∈ Ico 1 (Nat.log p n + 1 + h), n / p ^ i :=
    padicValNat_factorial (by omega)
  have h2 : padicValNat p ((n / p ^ h)!)
      = ∑ i ∈ Ico 1 (Nat.log p n + 1), n / p ^ h / p ^ i :=
    padicValNat_factorial (by
      have := Nat.log_mono_right (b := p) (Nat.div_le_self n (p ^ h))
      omega)
  have h4 : ∑ i ∈ Ico 1 (Nat.log p n + 1), n / p ^ h / p ^ i
      = ∑ j ∈ Ico (1 + h) (Nat.log p n + 1 + h), n / p ^ j := by
    rw [Finset.sum_congr rfl fun i _ => by rw [Nat.div_div_eq_div_mul, ← pow_add],
      Finset.sum_Ico_add (fun j => n / p ^ j) 1 (Nat.log p n + 1) h]
  have h5 : ∑ ℓ ∈ Icc 1 h, n / p ^ ℓ = ∑ ℓ ∈ Ico 1 (1 + h), n / p ^ ℓ := by
    rw [Nat.add_comm 1 h, Finset.Ico_add_one_right_eq_Icc]
  rw [h1, h2, h4, h5, ← Finset.sum_Ico_consecutive (fun j => n / p ^ j)
    (show (1 : ℕ) ≤ 1 + h from by omega)
    (show 1 + h ≤ Nat.log p n + 1 + h from by omega)]
  exact Nat.add_comm _ _

/-- `min(h, v_p(x)) = #{1 ≤ ℓ ≤ h : pˡ ∣ x}` for `x ≠ 0`. -/
theorem min_padicValNat_eq_card (h : ℕ) {x : ℕ} (hx : x ≠ 0) :
    min h (padicValNat p x) = ((Icc 1 h).filter fun ℓ => p ^ ℓ ∣ x).card := by
  classical
  have hset : (Icc 1 h).filter (fun ℓ => p ^ ℓ ∣ x) = Icc 1 (min h (padicValNat p x)) := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_Icc, padicValNat_dvd_iff_le hx, le_min_iff]
    tauto
  rw [hset, Nat.card_Icc]
  omega

end Counting

section Polynomials

/-- Colmez's rescaled binomial `g_n = ⌊n/pʰ⌋!·(X choose n)`, over `ℚ_p`. -/
def colmezPoly (h n : ℕ) : ℚ_[p][X] :=
  C (((n / p ^ h)! : ℚ_[p]) / (n ! : ℚ_[p])) * descPochhammer ℚ_[p] n

/-- `g_n(j) = ⌊n/pʰ⌋!·C(j, n)` at natural numbers. -/
theorem colmezPoly_eval_natCast (h n j : ℕ) :
    (colmezPoly (p := p) h n).eval (j : ℚ_[p]) = (((n / p ^ h)! * j.choose n : ℕ) : ℚ_[p]) := by
  have hfac : ((n ! : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [colmezPoly, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial ℚ_[p] j n, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

theorem natDegree_colmezPoly (h n : ℕ) : (colmezPoly (p := p) h n).natDegree = n := by
  have hne : (((n / p ^ h)! : ℕ) : ℚ_[p]) / ((n ! : ℕ) : ℚ_[p]) ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [colmezPoly, Polynomial.natDegree_C_mul hne, descPochhammer_natDegree]

/-- The disc-restricted polynomial `g_{n,a}(w) = g_n(a + pʰw)`. -/
def discPoly (h n a : ℕ) : ℚ_[p][X] :=
  (colmezPoly h n).comp (C (a : ℚ_[p]) + C ((p : ℚ_[p]) ^ h) * X)

theorem discPoly_eval (h n a : ℕ) (w : ℚ_[p]) :
    (discPoly (p := p) h n a).eval w
      = (colmezPoly h n).eval ((a : ℚ_[p]) + (p : ℚ_[p]) ^ h * w) := by
  rw [discPoly, Polynomial.eval_comp]
  simp

theorem natDegree_discPoly_le (h n a : ℕ) : (discPoly (p := p) h n a).natDegree ≤ n := by
  have hq : (C (a : ℚ_[p]) + C ((p : ℚ_[p]) ^ h) * X).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
  refine (Polynomial.natDegree_comp_le).trans ?_
  rw [natDegree_colmezPoly]
  calc n * (C (a : ℚ_[p]) + C ((p : ℚ_[p]) ^ h) * X).natDegree ≤ n * 1 :=
      Nat.mul_le_mul_left n hq
    _ = n := mul_one n

/-- Colmez's `K_{n,j}`: the indices `k < n` with `k ≡ a (mod pʰ)`. -/
def discSupport (h n a : ℕ) : Finset ℕ := (range n).filter fun k => k % p ^ h = a

theorem card_discSupport (h n a : ℕ) (ha : a < p ^ h) :
    (discSupport (p := p) h n a).card = n / p ^ h + if a < n % p ^ h then 1 else 0 :=
  card_filter_range_mod_eq n a (p ^ h) (pow_pos hp.out.pos h) ha

/-- The normalised linear factor of `a − k + pʰX`. -/
def discFactorTerm (h a k : ℕ) : ℚ_[p][X] :=
  if k % p ^ h = a then X - C (((k - a) / p ^ h : ℕ) : ℚ_[p])
  else 1 + C ((p : ℚ_[p]) ^ h / ((a : ℚ_[p]) - k)) * X

/-- The integral factor `f_{n,a} = ∏_{k<n} (normalised factor)`. -/
def discFactor (h n a : ℕ) : ℚ_[p][X] := ∏ k ∈ range n, discFactorTerm (p := p) h a k

/-- The scalar `c_{n,a} = (⌊n/pʰ⌋!/n!)·∏_{k∈K} pʰ·∏_{k∉K} (a − k)`. -/
def discConst (h n a : ℕ) : ℚ_[p] :=
  (((n / p ^ h)! : ℚ_[p]) / (n ! : ℚ_[p]))
    * ∏ k ∈ range n, if k % p ^ h = a then (p : ℚ_[p]) ^ h else (a : ℚ_[p]) - k

/-- `descPochhammer n` composed with `C a + C c * X` is the product of the shifted linear
factors. -/
theorem descPochhammer_comp_eq_prod (n : ℕ) (q : ℚ_[p][X]) :
    (descPochhammer ℚ_[p] n).comp q = ∏ k ∈ range n, (q - C (k : ℚ_[p])) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, Polynomial.mul_comp, ih, Finset.prod_range_succ]
    congr 1
    simp

/-- The factorisation `g_{n,a} = c_{n,a}·f_{n,a}` ([Colmez, proof of Lemme 1.4.9]). -/
theorem discPoly_eq (h n a : ℕ) (ha : a < p ^ h) :
    discPoly (p := p) h n a = C (discConst h n a) * discFactor h n a := by
  have hfac : ∀ k ∈ range n,
      C (a : ℚ_[p]) + C ((p : ℚ_[p]) ^ h) * X - C (k : ℚ_[p])
        = C (if k % p ^ h = a then (p : ℚ_[p]) ^ h else (a : ℚ_[p]) - k)
          * discFactorTerm (p := p) h a k := by
    intro k _
    have hsplit : C (a : ℚ_[p]) + C ((p : ℚ_[p]) ^ h) * X - C (k : ℚ_[p])
        = C ((a : ℚ_[p]) - k) + C ((p : ℚ_[p]) ^ h) * X := by
      rw [Polynomial.C_sub]
      ring
    rw [discFactorTerm]
    split_ifs with hk
    · have hle : a ≤ k := by
        by_contra hcon
        push Not at hcon
        rw [Nat.mod_eq_of_lt (hcon.trans ha)] at hk
        omega
      have hdvdk : p ^ h ∣ k - a :=
        (Nat.modEq_iff_dvd' hle).mp (by
          show a % p ^ h = k % p ^ h
          rw [hk, Nat.mod_eq_of_lt ha])
      have key : (a : ℚ_[p]) - (k : ℚ_[p])
          = -((p : ℚ_[p]) ^ h * (((k - a) / p ^ h : ℕ) : ℚ_[p])) := by
        rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.mul_div_cancel' hdvdk, Nat.cast_sub hle]
        ring
      rw [hsplit, key, mul_sub, Polynomial.C_neg, Polynomial.C_mul]
      ring
    · have hak : a ≠ k := fun hc => hk (by rw [← hc, Nat.mod_eq_of_lt ha])
      have hne : (a : ℚ_[p]) - k ≠ 0 :=
        sub_ne_zero.mpr fun hc => hak (Nat.cast_injective hc)
      have hcancel : ((a : ℚ_[p]) - k) * ((p : ℚ_[p]) ^ h / ((a : ℚ_[p]) - k))
          = (p : ℚ_[p]) ^ h := by field_simp
      rw [hsplit, mul_add, mul_one, ← mul_assoc, ← Polynomial.C_mul, hcancel]
  rw [discPoly, colmezPoly, Polynomial.mul_comp, Polynomial.C_comp,
    descPochhammer_comp_eq_prod, discConst, discFactor, Polynomial.C_mul, mul_assoc,
    map_prod, ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl hfac)

/-- Each normalised factor has integral coefficients. -/
private theorem norm_p_lt_one : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
  rw [Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

/-- `|a − k|` as a natural number. -/
private def sep (a k : ℕ) : ℕ := (a - k) + (k - a)

private theorem sep_eq_zero_iff (a k : ℕ) : sep a k = 0 ↔ a = k := by
  unfold sep
  omega

/-- The difference of two naturals, read in `ℚ_[p]`, has the norm of `|a − k|`. -/
private theorem norm_natCast_sub_eq_sep (a k : ℕ) :
    ‖(a : ℚ_[p]) - k‖ = ‖((sep a k : ℕ) : ℚ_[p])‖ := by
  unfold sep
  rcases le_total a k with hle | hle
  · rw [show a - k + (k - a) = k - a from by omega,
      show (a : ℚ_[p]) - k = -(((k - a : ℕ) : ℚ_[p])) from by rw [Nat.cast_sub hle]; ring, norm_neg]
  · rw [show a - k + (k - a) = a - k from by omega,
      show (a : ℚ_[p]) - k = ((a - k : ℕ) : ℚ_[p]) from by rw [Nat.cast_sub hle]]

omit hp in
/-- `pᵐ` divides `|a − k|` exactly when `a` and `k` are congruent modulo `pᵐ`. -/
private theorem dvd_sep_iff (m a k : ℕ) : p ^ m ∣ sep a k ↔ a % p ^ m = k % p ^ m := by
  unfold sep
  rcases le_total a k with hle | hle
  · rw [show a - k + (k - a) = k - a from by omega]
    exact ⟨fun hd => (Nat.modEq_iff_dvd' hle).mpr hd, fun hm => (Nat.modEq_iff_dvd' hle).mp hm⟩
  · rw [show a - k + (k - a) = a - k from by omega]
    exact ⟨fun hd => ((Nat.modEq_iff_dvd' hle).mpr hd).symm,
      fun hm => (Nat.modEq_iff_dvd' hle).mp hm.symm⟩

/-- If `k` is not congruent to `a` modulo `pʰ`, then `a − k` is not divisible by `pʰ`, so its
norm is at least `‖p‖ʰ` — the bound making the normalised factor integral. -/
private theorem norm_pow_le_norm_natCast_sub {h a k : ℕ} (ha : a < p ^ h) (hk : k % p ^ h ≠ a) :
    ‖((p : ℕ) : ℚ_[p])‖ ^ h ≤ ‖(a : ℚ_[p]) - (k : ℚ_[p])‖ := by
  have hane : a ≠ k := fun hc => hk (by rw [← hc, Nat.mod_eq_of_lt ha])
  have hd0 : sep a k ≠ 0 := fun hc => hane ((sep_eq_zero_iff a k).mp hc)
  have hnd : ¬p ^ h ∣ sep a k := fun hcon => hk (by
    have hmod := (dvd_sep_iff h a k).mp hcon
    rw [Nat.mod_eq_of_lt ha] at hmod
    exact hmod.symm)
  have hv : padicValNat p (sep a k) < h := by
    by_contra hcon
    push Not at hcon
    exact hnd ((padicValNat_dvd_iff_le hd0).mpr hcon)
  rw [norm_natCast_sub_eq_sep, PadicExpLog.norm_natCast_eq_pow_padicValNat norm_p_lt_one hd0]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_p_lt_one.le hv.le

theorem norm_coeff_discFactorTerm_le (h a k : ℕ) (ha : a < p ^ h) (i : ℕ) :
    ‖(discFactorTerm (p := p) h a k).coeff i‖ ≤ 1 := by
  rw [discFactorTerm]
  split_ifs with hk
  · have h1 : ‖(X : ℚ_[p][X]).coeff i‖ ≤ 1 := by
      rw [Polynomial.coeff_X]
      split_ifs <;> simp
    have h2 : ‖(C (((k - a) / p ^ h : ℕ) : ℚ_[p])).coeff i‖ ≤ 1 := by
      rw [Polynomial.coeff_C]
      split_ifs
      · exact IsUltrametricDist.norm_natCast_le_one _ _
      · simp
    rw [Polynomial.coeff_sub, sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
  · have hc : ‖(p : ℚ_[p]) ^ h / ((a : ℚ_[p]) - k)‖ ≤ 1 := by
      rw [norm_div, div_le_one_iff]
      left
      refine ⟨?_, ?_⟩
      · refine lt_of_lt_of_le ?_ (norm_pow_le_norm_natCast_sub ha hk)
        exact pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)) h
      · rw [norm_pow]
        exact norm_pow_le_norm_natCast_sub ha hk
    have h1 : ‖(1 : ℚ_[p][X]).coeff i‖ ≤ 1 := by
      rw [Polynomial.coeff_one]
      split_ifs <;> simp
    have h2 : ‖(C ((p : ℚ_[p]) ^ h / ((a : ℚ_[p]) - k)) * X).coeff i‖ ≤ 1 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X, norm_mul]
      split_ifs
      · simpa using hc
      · simp
    rw [Polynomial.coeff_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

/-- `f_{n,a}` has integral coefficients. -/
private theorem norm_coeff_mul_le {f g : ℚ_[p][X]} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i, ‖f.coeff i‖ ≤ c) (hg : ∀ i, ‖g.coeff i‖ ≤ 1) (i : ℕ) :
    ‖(f * g).coeff i‖ ≤ c := by
  rw [Polynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun x _ => ?_
  rw [norm_mul]
  calc ‖f.coeff x.1‖ * ‖g.coeff x.2‖ ≤ c * 1 := mul_le_mul (hf _) (hg _) (norm_nonneg _) hc
    _ = c := mul_one c

private theorem norm_coeff_mul_le_one {f g : ℚ_[p][X]} (hf : ∀ i, ‖f.coeff i‖ ≤ 1)
    (hg : ∀ i, ‖g.coeff i‖ ≤ 1) (i : ℕ) : ‖(f * g).coeff i‖ ≤ 1 :=
  norm_coeff_mul_le zero_le_one hf hg i

/-- A finite product of polynomials congruent to `1` modulo `c` is congruent to `1` modulo `c`. -/
private theorem norm_coeff_prod_sub_one {t : ℕ → ℚ_[p][X]} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (T : Finset ℕ) (ht : ∀ k ∈ T, ∀ i, ‖(t k - 1).coeff i‖ ≤ c) :
    ∀ i, ‖((∏ k ∈ T, t k) - 1).coeff i‖ ≤ c := by
  classical
  revert ht
  induction T using Finset.induction with
  | empty =>
    intro _ i
    simpa using hc0
  | insert k T hk ih =>
    intro ht i
    have h1 : ∀ j, ‖(t k - 1).coeff j‖ ≤ c := ht k (Finset.mem_insert_self k T)
    have h2 : ∀ j, ‖((∏ m ∈ T, t m) - 1).coeff j‖ ≤ c :=
      ih fun m hm => ht m (Finset.mem_insert_of_mem hm)
    rw [Finset.prod_insert hk, show t k * (∏ m ∈ T, t m) - 1
        = (t k - 1) + (((∏ m ∈ T, t m) - 1) + (t k - 1) * ((∏ m ∈ T, t m) - 1)) by ring,
      Polynomial.coeff_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 i) ?_)
    rw [Polynomial.coeff_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h2 i) ?_)
    exact norm_coeff_mul_le hc0 h1 (fun j => (h2 j).trans hc1) i

theorem norm_coeff_discFactor_le (h n a : ℕ) (ha : a < p ^ h) (i : ℕ) :
    ‖(discFactor (p := p) h n a).coeff i‖ ≤ 1 := by
  revert i
  induction n with
  | zero =>
    intro i
    rw [discFactor, Finset.range_zero, Finset.prod_empty, Polynomial.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    intro i
    rw [discFactor, Finset.prod_range_succ]
    exact norm_coeff_mul_le_one ih (norm_coeff_discFactorTerm_le h a n ha) i

/-- The reduction of `f_{n,a}` modulo `p` has degree `|K_{n,a}|`: coefficients beyond it are
divisible by `p` (the factors for `k ∉ K` reduce to `1`). -/
private theorem inv_p_le_one : ((p : ℝ))⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)

/-- The normalised factor at a disc other than the residue disc of `n` reduces to `1` modulo
`p`: its `X`-coefficient `pʰ/(a − k)` has norm `≤ p⁻¹` because `v_p(a − k) ≤ h − 1`. -/
private theorem norm_div_natCast_sub_le_inv {h a k : ℕ} (ha : a < p ^ h) (hk : k % p ^ h ≠ a) :
    ‖(p : ℚ_[p]) ^ h / ((a : ℚ_[p]) - k)‖ ≤ (p : ℝ)⁻¹ := by
  have hane : a ≠ k := fun hc => hk (by rw [← hc, Nat.mod_eq_of_lt ha])
  have hd0 : sep a k ≠ 0 := fun hc => hane ((sep_eq_zero_iff a k).mp hc)
  have hnd : ¬p ^ h ∣ sep a k := fun hcon => hk (by
    have hmod := (dvd_sep_iff h a k).mp hcon
    rw [Nat.mod_eq_of_lt ha] at hmod
    exact hmod.symm)
  have hv : padicValNat p (sep a k) < h := by
    by_contra hcon
    push Not at hcon
    exact hnd ((padicValNat_dvd_iff_le hd0).mpr hcon)
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hnorm : ‖(a : ℚ_[p]) - k‖ = ((p : ℝ)⁻¹) ^ padicValNat p (sep a k) := by
    rw [norm_natCast_sub_eq_sep, PadicExpLog.norm_natCast_eq_pow_padicValNat norm_p_lt_one hd0,
      Padic.norm_p]
  rw [norm_div, norm_pow, hnorm, Padic.norm_p, div_le_iff₀ (by positivity)]
  calc ((p : ℝ)⁻¹) ^ h ≤ ((p : ℝ)⁻¹) ^ (padicValNat p (sep a k) + 1) :=
      pow_le_pow_of_le_one hpos.le inv_p_le_one (by omega)
    _ = (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ padicValNat p (sep a k) := by ring

/-- The factorisation of `f_{n,a}` into its monic part (one factor per index of `K_{n,a}`) and a
part congruent to `1` modulo `p`. -/
private theorem exists_discFactor_eq_add (h n a : ℕ) (ha : a < p ^ h) :
    ∃ F G : ℚ_[p][X], F.Monic ∧ F.natDegree = (discSupport (p := p) h n a).card ∧
      (∀ i, ‖F.coeff i‖ ≤ 1) ∧ (∀ i, ‖G.coeff i‖ ≤ (p : ℝ)⁻¹) ∧
      discFactor (p := p) h n a = F + F * G := by
  classical
  refine ⟨∏ k ∈ (range n).filter (fun k => k % p ^ h = a),
      (X - C (((k - a) / p ^ h : ℕ) : ℚ_[p])),
    (∏ k ∈ (range n).filter (fun k => ¬k % p ^ h = a), discFactorTerm (p := p) h a k) - 1,
    Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _,
      Finset.sum_congr rfl fun x _ =>
        Polynomial.natDegree_X_sub_C (((x - a) / p ^ h : ℕ) : ℚ_[p])]
    simp [discSupport]
  · intro i
    refine Finset.prod_induction _ (fun f : ℚ_[p][X] => ∀ j, ‖f.coeff j‖ ≤ 1) ?_ ?_ ?_ i
    · exact fun f g hf hg => norm_coeff_mul_le_one hf hg
    · intro j
      rw [Polynomial.coeff_one]
      split_ifs <;> simp
    · intro k _ j
      rw [Polynomial.coeff_sub, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [Polynomial.coeff_X]
        split_ifs <;> simp
      · rw [norm_neg, Polynomial.coeff_C]
        split_ifs
        · exact IsUltrametricDist.norm_natCast_le_one _ _
        · simp
  · refine norm_coeff_prod_sub_one (by positivity) inv_p_le_one _ fun k hk j => ?_
    have hkk : ¬k % p ^ h = a := (Finset.mem_filter.mp hk).2
    rw [discFactorTerm, if_neg hkk, add_sub_cancel_left, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, norm_mul]
    split_ifs
    · simpa using norm_div_natCast_sub_le_inv ha hkk
    · simp
  · rw [discFactor, ← Finset.prod_filter_mul_prod_filter_not (range n) (fun k => k % p ^ h = a),
      Finset.prod_congr rfl fun k hk => by
        rw [discFactorTerm, if_pos (Finset.mem_filter.mp hk).2]]
    ring

theorem norm_coeff_discFactor_le_inv_of_lt (h n a : ℕ) (ha : a < p ^ h) {i : ℕ}
    (hi : (discSupport (p := p) h n a).card < i) :
    ‖(discFactor (p := p) h n a).coeff i‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨F, G, hmon, hdeg, hF, hG, heq⟩ := exists_discFactor_eq_add (p := p) h n a ha
  rw [heq, Polynomial.coeff_add,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hi), zero_add, mul_comm F G]
  exact norm_coeff_mul_le (by positivity) hG hF i

/-- The reduction of `f_{n,a}` modulo `p` is monic of degree `|K_{n,a}|`. -/
theorem norm_coeff_discFactor_card (h n a : ℕ) (ha : a < p ^ h) :
    ‖(discFactor (p := p) h n a).coeff (discSupport (p := p) h n a).card‖ = 1 := by
  obtain ⟨F, G, hmon, hdeg, hF, hG, heq⟩ := exists_discFactor_eq_add (p := p) h n a ha
  have hlead : F.coeff (discSupport (p := p) h n a).card = 1 := by
    rw [← hdeg]
    exact hmon.coeff_natDegree
  have hsmall : ‖(F * G).coeff (discSupport (p := p) h n a).card‖ ≤ (p : ℝ)⁻¹ := by
    rw [mul_comm F G]
    exact norm_coeff_mul_le (by positivity) hG hF _
  have hlt : ‖(F * G).coeff (discSupport (p := p) h n a).card‖ < 1 :=
    lt_of_le_of_lt hsmall (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  rw [heq, Polynomial.coeff_add, hlead,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'),
    norm_one, max_eq_left hlt.le]

/-- **The valuation of `c_{n,a}`** ([Colmez, proof of Lemme 1.4.9], in the residue-count form):
`‖c_{n,a}‖ = p^{−N}`, `N = #{1 ≤ ℓ ≤ h : a mod pˡ < n mod pˡ}`. -/
theorem norm_discConst (h n a : ℕ) (ha : a < p ^ h) :
    ‖discConst (p := p) h n a‖
      = (p : ℝ)⁻¹ ^ ((Icc 1 h).filter fun ℓ => a % p ^ ℓ < n % p ^ ℓ).card := by
  classical
  have hq0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  -- each factor of the product has the norm predicted by counting `p`-power congruences
  have hs : ∀ k ∈ range n,
      ‖(if k % p ^ h = a then (p : ℚ_[p]) ^ h else (a : ℚ_[p]) - k)‖
        = (p : ℝ)⁻¹ ^ ((Icc 1 h).filter fun ℓ => p ^ ℓ ∣ sep a k).card := by
    intro k _
    split_ifs with hk
    · have hall : (Icc 1 h).filter (fun ℓ => p ^ ℓ ∣ sep a k) = Icc 1 h := by
        refine Finset.filter_true_of_mem fun ℓ hℓ => ?_
        refine dvd_trans (pow_dvd_pow p (Finset.mem_Icc.mp hℓ).2) ?_
        exact (dvd_sep_iff h a k).mpr (by rw [hk, Nat.mod_eq_of_lt ha])
      rw [hall, Nat.card_Icc, norm_pow, Padic.norm_p, Nat.add_sub_cancel]
    · have hane : a ≠ k := fun hc => hk (by rw [← hc, Nat.mod_eq_of_lt ha])
      have hd0 : sep a k ≠ 0 := fun hc => hane ((sep_eq_zero_iff a k).mp hc)
      have hnd : ¬p ^ h ∣ sep a k := fun hcon => hk (by
        have hmod := (dvd_sep_iff h a k).mp hcon
        rw [Nat.mod_eq_of_lt ha] at hmod
        exact hmod.symm)
      have hv : padicValNat p (sep a k) < h := by
        by_contra hcon
        push Not at hcon
        exact hnd ((padicValNat_dvd_iff_le hd0).mpr hcon)
      rw [norm_natCast_sub_eq_sep, PadicExpLog.norm_natCast_eq_pow_padicValNat norm_p_lt_one hd0,
        Padic.norm_p, ← min_padicValNat_eq_card h hd0, min_eq_right hv.le]
  -- Fubini: summing the congruence counts along `k` or along `ℓ`
  have hfub : ∑ k ∈ range n, ((Icc 1 h).filter fun ℓ => p ^ ℓ ∣ sep a k).card
      = ((Icc 1 h).filter fun ℓ => a % p ^ ℓ < n % p ^ ℓ).card + ∑ ℓ ∈ Icc 1 h, n / p ^ ℓ := by
    have hinner : ∀ ℓ ∈ Icc 1 h, (∑ k ∈ range n, if p ^ ℓ ∣ sep a k then 1 else 0)
        = n / p ^ ℓ + (if a % p ^ ℓ < n % p ^ ℓ then 1 else 0) := by
      intro ℓ _
      rw [← Finset.card_filter,
        Finset.filter_congr (q := fun k => k % p ^ ℓ = a % p ^ ℓ)
          (fun k _ => by rw [dvd_sep_iff]; exact eq_comm),
        card_filter_range_mod_eq n (a % p ^ ℓ) (p ^ ℓ) (pow_pos hp.out.pos ℓ)
          (Nat.mod_lt _ (pow_pos hp.out.pos ℓ))]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
    exact add_comm _ _
  rw [discConst, norm_mul, norm_div, norm_prod, Finset.prod_congr rfl hs,
    Finset.prod_pow_eq_pow_sum, hfub,
    PadicExpLog.norm_natCast_eq_pow_padicValNat norm_p_lt_one (Nat.factorial_ne_zero _),
    PadicExpLog.norm_natCast_eq_pow_padicValNat norm_p_lt_one (Nat.factorial_ne_zero _),
    Padic.norm_p, padicValNat_factorial_sub_factorial_div_pow (p := p) n h, pow_add, pow_add]
  field_simp

theorem norm_discConst_le_one (h n a : ℕ) (ha : a < p ^ h) : ‖discConst (p := p) h n a‖ ≤ 1 := by
  rw [norm_discConst h n a ha]
  exact pow_le_one₀ (by positivity) inv_p_le_one

/-- On the disc of `n` itself (`a = n mod pʰ`), `c_{n,a}` is a unit. -/
theorem norm_discConst_res (h n : ℕ) : ‖discConst (p := p) h n (n % p ^ h)‖ = 1 := by
  have hlt : n % p ^ h < p ^ h := Nat.mod_lt _ (pow_pos hp.out.pos h)
  rw [norm_discConst h n _ hlt,
    Finset.filter_false_of_mem fun ℓ hℓ => by
      rw [Nat.mod_mod_of_dvd n (pow_dvd_pow p (Finset.mem_Icc.mp hℓ).2)]
      exact lt_irrefl _,
    Finset.card_empty, pow_zero]

/-- On a disc below the disc of `n` (`a < n mod pʰ`), `c_{n,a}` is divisible by `p`. -/
theorem norm_discConst_le_inv_of_lt (h n a : ℕ) (ha : a < n % p ^ h) :
    ‖discConst (p := p) h n a‖ ≤ (p : ℝ)⁻¹ := by
  have hmod : n % p ^ h < p ^ h := Nat.mod_lt _ (pow_pos hp.out.pos h)
  have hap : a < p ^ h := ha.trans hmod
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · simp only [pow_zero, Nat.mod_one] at ha
      omega
    · exact hpos
  have hmem : h ∈ (Icc 1 h).filter fun ℓ => a % p ^ ℓ < n % p ^ ℓ :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hh, le_rfl⟩, by rwa [Nat.mod_eq_of_lt hap]⟩
  have hcard : 1 ≤ ((Icc 1 h).filter fun ℓ => a % p ^ ℓ < n % p ^ ℓ).card :=
    Finset.card_pos.mpr ⟨h, hmem⟩
  rw [norm_discConst h n a hap]
  calc ((p : ℝ)⁻¹) ^ ((Icc 1 h).filter fun ℓ => a % p ^ ℓ < n % p ^ ℓ).card
      ≤ ((p : ℝ)⁻¹) ^ 1 := pow_le_pow_of_le_one (by positivity) inv_p_le_one hcard
    _ = (p : ℝ)⁻¹ := pow_one _

/-- (i) of [Colmez, Lemme 1.4.9]: `g_{n,a}` has integral coefficients. -/
theorem norm_coeff_discPoly_le (h n a : ℕ) (ha : a < p ^ h) (i : ℕ) :
    ‖(discPoly (p := p) h n a).coeff i‖ ≤ 1 := by
  rw [discPoly_eq h n a ha, Polynomial.coeff_C_mul, norm_mul]
  exact mul_le_one₀ (norm_discConst_le_one h n a ha) (norm_nonneg _)
    (norm_coeff_discFactor_le h n a ha i)

/-- (ii): coefficients of `g_{n,a}` of degree `> ⌊n/pʰ⌋` are divisible by `p`, on every disc. -/
theorem norm_coeff_discPoly_le_inv_of_lt (h n a : ℕ) (ha : a < p ^ h) {i : ℕ}
    (hi : n / p ^ h < i) : ‖(discPoly (p := p) h n a).coeff i‖ ≤ (p : ℝ)⁻¹ := by
  rw [discPoly_eq h n a ha, Polynomial.coeff_C_mul, norm_mul]
  by_cases hres : a < n % p ^ h
  · calc ‖discConst (p := p) h n a‖ * ‖(discFactor (p := p) h n a).coeff i‖
        ≤ (p : ℝ)⁻¹ * 1 := mul_le_mul (norm_discConst_le_inv_of_lt h n a hres)
          (norm_coeff_discFactor_le h n a ha i) (norm_nonneg _) (by positivity)
      _ = (p : ℝ)⁻¹ := mul_one _
  · have hcard : (discSupport (p := p) h n a).card < i := by
      rw [card_discSupport h n a ha, if_neg hres]
      simpa using hi
    calc ‖discConst (p := p) h n a‖ * ‖(discFactor (p := p) h n a).coeff i‖
        ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul (norm_discConst_le_one h n a ha)
          (norm_coeff_discFactor_le_inv_of_lt h n a ha hcard) (norm_nonneg _) zero_le_one
      _ = (p : ℝ)⁻¹ := one_mul _

/-- (ii): on a disc below the disc of `n`, the coefficient of degree `⌊n/pʰ⌋` is divisible by `p`
(`ḡ_{n,j} = 0` for `j > i(n)`). -/
theorem norm_coeff_discPoly_le_inv_of_res_lt (h n a : ℕ) (ha : a < n % p ^ h) :
    ‖(discPoly (p := p) h n a).coeff (n / p ^ h)‖ ≤ (p : ℝ)⁻¹ := by
  have hap : a < p ^ h := ha.trans (Nat.mod_lt _ (pow_pos hp.out.pos h))
  rw [discPoly_eq h n a hap, Polynomial.coeff_C_mul, norm_mul]
  calc ‖discConst (p := p) h n a‖ * ‖(discFactor (p := p) h n a).coeff (n / p ^ h)‖
      ≤ (p : ℝ)⁻¹ * 1 := mul_le_mul (norm_discConst_le_inv_of_lt h n a ha)
        (norm_coeff_discFactor_le h n a hap _) (norm_nonneg _) (by positivity)
    _ = (p : ℝ)⁻¹ := mul_one _

/-- (ii): on the disc of `n`, the coefficient of degree `⌊n/pʰ⌋` is a unit
(`deg ḡ_{n,i(n)} = m(n)`). -/
theorem norm_coeff_discPoly_diag (h n : ℕ) :
    ‖(discPoly (p := p) h n (n % p ^ h)).coeff (n / p ^ h)‖ = 1 := by
  have hlt : n % p ^ h < p ^ h := Nat.mod_lt _ (pow_pos hp.out.pos h)
  have hcard : (discSupport (p := p) h n (n % p ^ h)).card = n / p ^ h := by
    rw [card_discSupport h n _ hlt, if_neg (lt_irrefl _), Nat.add_zero]
  rw [discPoly_eq h n _ hlt, Polynomial.coeff_C_mul, norm_mul, norm_discConst_res, one_mul,
    ← hcard, norm_coeff_discFactor_card h n _ hlt]

end Polynomials

end LWX

end
