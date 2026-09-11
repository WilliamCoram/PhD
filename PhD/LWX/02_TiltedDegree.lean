/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PhD.LWX.UnitsLog

/-!
# Tilted degree: the Mahler calculus of [LWX] §3.3–§3.13 — SKELETON (lwx-halo board)

The computational core of [LWX] ("a mild `p`-adic analysis computation (which is the
core of our paper)", §1.11(3)).  `Δ̃` is mathlib's `fwdDiff 1` (`Δ_[1]`), the Mahler
coefficient `a_m(f) = Δ̃^m f(0)` is `fwdDiff_iter_eq_sum_shift`, and the binomial
function `z ↦ binom(z,n)` is `mahler n = Ring.choose · n`.

We define **tilted degree** by clause (1) of [LWX, Def-Prop 3.8] — *everywhere*
valuation bounds on iterated differences, `∀ m z, ‖Δ̃^m f z‖ ≤ p^{n−m}` — which needs
no Mahler expansion, is closed under pointwise limits, and specialises at `z = 0` to
the coefficient bounds the matrix entries consume.  Clause (2) (the Mahler-coefficient
form) is then not needed anywhere and is not stated.

Contents ([LWX] numbering): the Leibniz rule (3.5.1); `Δ̃`-of-`mahler` (3.5.2); the
Chu–Vandermonde input (3.5.3) is mathlib's binomial-ring `add_choose_eq`; degree
vanishing (Lemma 3.7(1)-analogue for polynomial functions); tilted-degree API
(Def-Prop 3.8, Lemma 3.10); the binomial-basis conversion (Lemma 3.11, norm form);
and the two binomial estimates (Lemma 3.12, Lemma 3.13 — `p` odd, cases (a)–(c)).
-/

open Filter Topology Finset
open scoped fwdDiff

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The difference-calculus identities of [LWX] §3.5 -/

/-- Iterated differences commute with the unit shift. -/
private theorem fwdDiff_iter_shift {R : Type*} [CommRing R] (f : R → R) (k : ℕ) (y : R) :
    Δ_[1]^[k] (fun z => f (z + 1)) y = Δ_[1]^[k] f (y + 1) := by
  induction k generalizing f y with
  | zero => simp
  | succ k IH =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hΔ : Δ_[1] (fun z => f (z + 1)) = fun z => (Δ_[1] f) (z + 1) := by
        funext z
        simp [fwdDiff]
      rw [hΔ, IH]

private theorem fwdDiff_iter_zero_fun {R : Type*} [CommRing R] (m : ℕ) :
    Δ_[1]^[m] (0 : R → R) = 0 := by
  induction m with
  | zero => rfl
  | succ m IH => rw [Function.iterate_succ_apply, show Δ_[1] (0 : R → R) = 0 by
      funext z; simp [fwdDiff], IH]

/-- [LWX, (3.5.1)], the discrete Leibniz rule:
`Δ̃^m(fg)(y) = ∑_{i≤m} binom(m,i)·Δ̃^{m−i}f(y+i)·Δ̃^i g(y)`.  Stated for functions on a
commutative ring into a commutative ring, step `1`. -/
theorem fwdDiff_iter_mul {R : Type*} [CommRing R] (f g : R → R) (m : ℕ) (y : R) :
    Δ_[1]^[m] (f * g) y =
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : R) * Δ_[1]^[m - i] f (y + i) * Δ_[1]^[i] g y := by
  induction m generalizing f g y with
  | zero => simp
  | succ m IH =>
      rw [Function.iterate_succ_apply]
      have hsplit : Δ_[1] (f * g) = (fun z => f (z + 1)) * Δ_[1] g + Δ_[1] f * g := by
        funext z
        simp only [fwdDiff, Pi.mul_apply, Pi.add_apply]
        ring
      have hadd : ∀ (F G : R → R), Δ_[1]^[m] (F + G) y = Δ_[1]^[m] F y + Δ_[1]^[m] G y := by
        intro F G
        have := fwdDiff_iter_add (1 : R) F G m
        exact congrFun this y
      rw [hsplit, hadd]
      -- first summand: shift `f`, differentiate `g` once more
      have h1 : Δ_[1]^[m] ((fun z => f (z + 1)) * Δ_[1] g) y
          = ∑ i ∈ Finset.range (m + 1),
            (m.choose i : R) * Δ_[1]^[m - i] f (y + i + 1) * Δ_[1]^[i + 1] g y := by
        rw [IH]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [fwdDiff_iter_shift, Function.iterate_succ_apply]
      -- second summand: differentiate `f` once more
      have h2 : Δ_[1]^[m] (Δ_[1] f * g) y
          = ∑ i ∈ Finset.range (m + 1),
            (m.choose i : R) * Δ_[1]^[m + 1 - i] f (y + i) * Δ_[1]^[i] g y := by
        rw [IH]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hmi : Δ_[1]^[m - i] (Δ_[1] f) = Δ_[1]^[m - i + 1] f :=
          (Function.iterate_succ_apply _ _ _).symm ▸ rfl
        have hexp : m - i + 1 = m + 1 - i := by
          rw [Finset.mem_range] at hi
          omega
        rw [show Δ_[1]^[m - i] (Δ_[1] f) (y + i) = Δ_[1]^[m + 1 - i] f (y + i) by
          rw [← hexp, ← Function.iterate_succ_apply]]
      rw [h1, h2]
      -- reindex the first sum by `j = i + 1` and recombine with Pascal
      have h1' : ∑ i ∈ Finset.range (m + 1),
            (m.choose i : R) * Δ_[1]^[m - i] f (y + i + 1) * Δ_[1]^[i + 1] g y
          = ∑ j ∈ Finset.range (m + 2), (if j = 0 then 0 else
            (m.choose (j - 1) : R) * Δ_[1]^[m + 1 - j] f (y + j) * Δ_[1]^[j] g y) := by
        rw [Finset.sum_range_succ' (fun j => if j = 0 then 0 else
          (m.choose (j - 1) : R) * Δ_[1]^[m + 1 - j] f (y + j) * Δ_[1]^[j] g y) (m + 1)]
        simp only [Nat.add_one_ne_zero, if_false, reduceIte, Nat.add_sub_cancel, add_zero]
        refine Finset.sum_congr rfl fun i hi => ?_
        have : y + (i + 1 : ℕ) = y + i + 1 := by push_cast; ring
        rw [this, show m + 1 - (i + 1) = m - i by omega]
      rw [h1']
      -- pad the second sum to `range (m + 2)`
      have h2' : ∑ i ∈ Finset.range (m + 1),
            (m.choose i : R) * Δ_[1]^[m + 1 - i] f (y + i) * Δ_[1]^[i] g y
          = ∑ j ∈ Finset.range (m + 2), (if j = m + 1 then 0 else
            (m.choose j : R) * Δ_[1]^[m + 1 - j] f (y + j) * Δ_[1]^[j] g y) := by
        rw [Finset.sum_range_succ (fun j => if j = m + 1 then 0 else
          (m.choose j : R) * Δ_[1]^[m + 1 - j] f (y + j) * Δ_[1]^[j] g y) (m + 1),
          if_pos (rfl : (m + 1 : ℕ) = m + 1), add_zero]
        exact Finset.sum_congr rfl fun i hi => by
          rw [if_neg (show i ≠ m + 1 by rw [Finset.mem_range] at hi; omega)]
      rw [h2', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rcases eq_or_ne j 0 with rfl | hj0
      · simp
      rcases eq_or_ne j (m + 1) with rfl | hjm
      · simp [Nat.choose_self]
      · rw [if_neg hj0, if_neg hjm]
        have hchoose : ((m + 1).choose j : R) = (m.choose (j - 1) : R) + (m.choose j : R) := by
          have := Nat.succ_sub_one j ▸ Nat.choose_succ_succ m (j - 1)
          rw [← Nat.cast_add]
          congr 1
          have hj1 : j - 1 + 1 = j := by omega
          calc (m + 1).choose j = (m + 1).choose (j - 1 + 1) := by rw [hj1]
            _ = m.choose (j - 1) + m.choose (j - 1 + 1) := Nat.choose_succ_succ m (j - 1)
            _ = m.choose (j - 1) + m.choose j := by rw [hj1]
        rw [hchoose]
        ring

/-- [LWX, (3.5.2)]: `Δ̃ binom(·, n+1) = binom(·, n)` — Pascal's rule for `Ring.choose`
on `ℤ_[p]`, via density of `ℕ`. -/
theorem fwdDiff_choose (n : ℕ) :
    Δ_[1] (fun z : ℤ_[p] => Ring.choose z (n + 1)) = fun z => Ring.choose z n := by
  refine PadicInt.denseRange_natCast.equalizer
    (((PadicInt.continuous_choose (n + 1)).comp
        (continuous_id.add continuous_const)).sub (PadicInt.continuous_choose (n + 1)))
    (PadicInt.continuous_choose n) ?_
  funext k
  simp only [Function.comp_apply, fwdDiff]
  rw [show ((k : ℤ_[p]) + 1) = ((k + 1 : ℕ) : ℤ_[p]) by push_cast; ring,
    Ring.choose_natCast, Ring.choose_natCast, Ring.choose_natCast,
    Nat.choose_succ_succ' k n]
  push_cast
  ring

/-- Iterated form of [LWX, (3.5.2)]: `Δ̃^m binom(·, n) = binom(·, n−m)` (`= 1` at
`n = m`, `= 0` for `m > n`). -/
theorem fwdDiff_iter_choose (m n : ℕ) :
    Δ_[1]^[m] (fun z : ℤ_[p] => Ring.choose z n) =
      if m ≤ n then (fun z => Ring.choose z (n - m)) else 0 := by
  induction m with
  | zero => simp
  | succ m IH =>
      rw [Function.iterate_succ_apply', IH]
      rcases le_or_gt (m + 1) n with h | h
      · rw [if_pos (show m ≤ n from Nat.le_of_succ_le h), if_pos h,
          show n - m = (n - (m + 1)) + 1 by omega, fwdDiff_choose]
      · rw [if_neg (show ¬(m + 1 ≤ n) by omega)]
        rcases le_or_gt m n with h' | h'
        · rw [if_pos h', show n - m = 0 by omega,
            show (fun z : ℤ_[p] => Ring.choose z 0) = fun _ => (1 : ℤ_[p]) from
              funext fun z => Ring.choose_zero_right z]
          funext z
          simp [fwdDiff]
        · rw [if_neg (show ¬(m ≤ n) by omega)]
          funext z
          simp [fwdDiff]

/-- Degree vanishing ([LWX, Lemma 3.7(1)], the direction used): the function of a
polynomial of degree `≤ n` has `Δ̃^{n+1} = 0`.  Finite differences drop polynomial
degree. -/
theorem fwdDiff_iter_eval_eq_zero {R : Type*} [CommRing R] (P : Polynomial R) {m : ℕ}
    (hdeg : P.natDegree < m) : Δ_[1]^[m] (fun z : R => P.eval z) = 0 := by
  induction m generalizing P with
  | zero => omega
  | succ m IH =>
      rw [Function.iterate_succ_apply]
      have hΔ : Δ_[1] (fun z : R => P.eval z)
          = fun z : R => (Polynomial.taylor 1 P - P).eval z := by
        funext z
        simp [fwdDiff, Polynomial.taylor_apply, Polynomial.eval_comp, add_comm z 1]
      rw [hΔ]
      rcases eq_or_ne (Polynomial.taylor 1 P - P) 0 with h0 | h0
      · rw [show (fun z : R => (Polynomial.taylor 1 P - P).eval z) = (0 : R → R) by
          funext z; rw [h0, Polynomial.eval_zero]; rfl]
        exact fwdDiff_iter_zero_fun m
      · refine IH _ ?_
        have hP0 : P ≠ 0 := by
          rintro rfl
          simp at h0
        have hdrop : (Polynomial.taylor 1 P - P).degree < P.degree :=
          Polynomial.degree_taylor P 1 ▸ Polynomial.degree_sub_lt
            (Polynomial.degree_taylor P 1) ((Polynomial.taylor_eq_zero 1 P).not.2 hP0)
            (Polynomial.leadingCoeff_taylor 1 P)
        have := Polynomial.natDegree_lt_natDegree h0 hdrop
        omega

/-! ### Tilted degree ([LWX, Definition-Proposition 3.8], clause (1)) -/

/-- Tilted degree `≤ n` ([LWX, Def-Prop 3.8(1)]): every iterated difference `Δ̃^m f`
takes values in `p^{m−n}ℤ_p`. -/
def TiltedDeg (n : ℕ) (f : ℤ_[p] → ℤ_[p]) : Prop :=
  ∀ (m : ℕ) (z : ℤ_[p]), ‖Δ_[1]^[m] f z‖ ≤ (p : ℝ) ^ ((n : ℤ) - m)

theorem TiltedDeg.norm_fwdDiff_iter_apply_le {n : ℕ} {f : ℤ_[p] → ℤ_[p]}
    (hf : TiltedDeg n f) (m : ℕ) (z : ℤ_[p]) :
    ‖Δ_[1]^[m] f z‖ ≤ (p : ℝ) ^ ((n : ℤ) - m) := hf m z

/-- Integral-valued functions have tilted degree `≤ n` for `m ≤ n` for free; the
content is `m > n`.  Any `ℤ_p`-valued function has tilted degree `≤ n` iff the bounds
hold for `m > n`. -/
theorem tiltedDeg_iff_of_forall_norm_le {n : ℕ} {f : ℤ_[p] → ℤ_[p]} :
    TiltedDeg n f ↔ ∀ (m : ℕ), n < m → ∀ z, ‖Δ_[1]^[m] f z‖ ≤ (p : ℝ) ^ ((n : ℤ) - m) := by
  refine ⟨fun hf m _ => hf m, fun hf m z => ?_⟩
  rcases lt_or_ge (n : ℕ) m with h | h
  · exact hf m h z
  · calc ‖Δ_[1]^[m] f z‖ ≤ 1 := PadicInt.norm_le_one _
      _ ≤ (p : ℝ) ^ ((n : ℤ) - m) := by
          rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℤ) by simp]
          exact zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega)

/-- [LWX, Lemma 3.10(1)], the direction used in Lemma 3.13(c): if `Δ̃f` has tilted
degree `≤ n − 1` (and `f` is `ℤ_p`-valued), then `f` has tilted degree `≤ n`
(`1 ≤ n`). -/
theorem TiltedDeg.of_fwdDiff {n : ℕ} (hn : 1 ≤ n) {f : ℤ_[p] → ℤ_[p]}
    (h : TiltedDeg (n - 1) (Δ_[1] f)) : TiltedDeg n f := by
  intro m z
  cases m with
  | zero =>
      calc ‖Δ_[1]^[0] f z‖ ≤ 1 := PadicInt.norm_le_one _
        _ ≤ (p : ℝ) ^ ((n : ℤ) - 0) := by
            rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℤ) by simp]
            exact zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega)
  | succ m =>
      rw [Function.iterate_succ_apply]
      calc ‖Δ_[1]^[m] (Δ_[1] f) z‖ ≤ (p : ℝ) ^ (((n - 1 : ℕ) : ℤ) - m) := h m z
        _ = (p : ℝ) ^ ((n : ℤ) - (m + 1)) := by
            congr 1
            omega

/-- [LWX, Lemma 3.10(2)]: tilted degrees add under products, via the Leibniz rule
(3.5.1). -/
theorem TiltedDeg.mul {m n : ℕ} {f g : ℤ_[p] → ℤ_[p]} (hf : TiltedDeg m f)
    (hg : TiltedDeg n g) : TiltedDeg (m + n) (f * g) := by
  intro r z
  rw [fwdDiff_iter_mul f g r z]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (zpow_nonneg (Nat.cast_nonneg p) _) fun i hi => ?_
  rw [Finset.mem_range] at hi
  calc ‖(r.choose i : ℤ_[p]) * Δ_[1]^[r - i] f (z + i) * Δ_[1]^[i] g z‖
      = ‖(r.choose i : ℤ_[p])‖ * ‖Δ_[1]^[r - i] f (z + i)‖ * ‖Δ_[1]^[i] g z‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ 1 * ((p : ℝ) ^ ((m : ℤ) - (r - i : ℕ)) * (p : ℝ) ^ ((n : ℤ) - i)) := by
        rw [mul_assoc]
        exact mul_le_mul (PadicInt.norm_le_one _)
          (mul_le_mul (hf _ _) (hg _ _) (norm_nonneg _) (zpow_nonneg (Nat.cast_nonneg p) _))
          (by positivity) zero_le_one
    _ = (p : ℝ) ^ (((m + n : ℕ) : ℤ) - r) := by
        rw [one_mul, ← zpow_add₀ (by exact_mod_cast hp.out.pos.ne' : (p : ℝ) ≠ 0)]
        congr 1
        omega

/-- Tilted degree is closed under pointwise limits (the "by approximation" step of
[LWX, Lemmas 3.12–3.13]): `Δ̃^m f z` is a finite signed sum of values of `f`. -/
theorem TiltedDeg.of_tendsto {n : ℕ} {F : ℕ → ℤ_[p] → ℤ_[p]} {f : ℤ_[p] → ℤ_[p]}
    (hF : ∀ N, TiltedDeg n (F N)) (h : ∀ z, Tendsto (fun N => F N z) atTop (𝓝 (f z))) :
    TiltedDeg n f := by
  intro m z
  have hlim : Tendsto (fun N => Δ_[1]^[m] (F N) z) atTop (𝓝 (Δ_[1]^[m] f z)) := by
    simp only [fwdDiff_iter_eq_sum_shift]
    exact tendsto_finsetSum _ fun k _ => (h (z + k • (1 : ℤ_[p]))).const_smul _
  exact le_of_tendsto hlim.norm (Eventually.of_forall fun N => hF N m z)

/-- Tilted degree is monotone in the degree bound. -/
theorem TiltedDeg.mono {n n' : ℕ} (h : n ≤ n') {f : ℤ_[p] → ℤ_[p]}
    (hf : TiltedDeg n f) : TiltedDeg n' f := fun m z =>
  (hf m z).trans (zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega))

/-- Constant functions have every tilted degree. -/
theorem tiltedDeg_const (n : ℕ) (c : ℤ_[p]) : TiltedDeg n fun _ => c := by
  intro m z
  cases m with
  | zero =>
      calc ‖Δ_[1]^[0] (fun _ : ℤ_[p] => c) z‖ ≤ 1 := PadicInt.norm_le_one _
        _ ≤ (p : ℝ) ^ ((n : ℤ) - 0) := by
            rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℤ) by simp]
            exact zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega)
  | succ m =>
      rw [Function.iterate_succ_apply,
        show Δ_[1] (fun _ : ℤ_[p] => c) = (0 : ℤ_[p] → ℤ_[p]) from
          funext fun w => by simp [fwdDiff], fwdDiff_iter_zero_fun]
      simpa using zpow_nonneg (Nat.cast_nonneg (α := ℝ) p) _

/-- Tilted degree is stable under finite sums (ultrametric). -/
theorem TiltedDeg.sum {n : ℕ} {ι : Type*} {s : Finset ι} {f : ι → ℤ_[p] → ℤ_[p]}
    (hf : ∀ i ∈ s, TiltedDeg n (f i)) :
    TiltedDeg n fun z => ∑ i ∈ s, f i z := by
  intro m z
  rw [show (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, f i from
    funext fun w => (Finset.sum_apply w s f).symm, fwdDiff_iter_finsetSum,
    Finset.sum_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (zpow_nonneg (Nat.cast_nonneg p) _) fun i hi => hf i hi m z

/-! ### The binomial-basis conversion ([LWX, Lemma 3.11], norm form) -/

/-- The binomial polynomial `binom(z, i) = z(z−1)⋯(z−i+1)/i!` over a field. -/
def binomialPoly (L : Type*) [Field L] (i : ℕ) : Polynomial L :=
  Polynomial.C ((i.factorial : L)⁻¹) * descPochhammer L i

/-- The triangular change of basis to falling factorials, [LWX, Lemma 3.11]'s core:
reverse induction peeling the top coefficient against the monic `descPochhammer`. -/
private theorem exists_descPochhammer_basis {L : Type*} [NontriviallyNormedField L]
    [IsUltrametricDist L] {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∀ (r : ℕ) (P : Polynomial L), P.natDegree ≤ r → (∀ i, ‖P.coeff i‖ ≤ ρ ^ i) →
    ∃ c : ℕ → L, (∀ i, ‖c i‖ ≤ ρ ^ i) ∧ (∀ i, r < i → c i = 0) ∧
      P = ∑ i ∈ Finset.range (r + 1), Polynomial.C (c i) * descPochhammer L i := by
  intro r
  induction r with
  | zero =>
      intro P hdeg hP
      refine ⟨fun i => if i = 0 then P.coeff 0 else 0, fun i => ?_, fun i hi => ?_, ?_⟩
      · rcases eq_or_ne i 0 with rfl | h
        · simpa using hP 0
        · simp [h, pow_nonneg hρ]
      · show (if i = 0 then P.coeff 0 else 0) = 0
        rw [if_neg (show i ≠ 0 by omega)]
      · rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        show P = Polynomial.C (if (0 : ℕ) = 0 then P.coeff 0 else 0) * descPochhammer L 0
        rw [if_pos (rfl : (0 : ℕ) = 0), descPochhammer_zero, mul_one]
        exact Polynomial.eq_C_of_natDegree_le_zero hdeg
  | succ r IH =>
      intro P hdeg hP
      set a := P.coeff (r + 1) with ha
      set Q := P - Polynomial.C a * descPochhammer L (r + 1) with hQ
      have hint : ∀ i, ‖(descPochhammer L (r + 1)).coeff i‖ ≤ 1 := by
        intro i
        rw [← descPochhammer_map (Int.castRingHom L) (r + 1), Polynomial.coeff_map]
        exact IsUltrametricDist.norm_intCast_le_one L _
      have htop : (descPochhammer L (r + 1)).coeff (r + 1) = 1 := by
        have := (monic_descPochhammer L (r + 1)).coeff_natDegree
        rwa [descPochhammer_natDegree] at this
      have hcoeffQ : ∀ i, ‖Q.coeff i‖ ≤ ρ ^ i := by
        intro i
        rcases le_or_gt i (r + 1) with hi | hi
        · rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul, sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP i) ?_)
          calc ‖-(a * (descPochhammer L (r + 1)).coeff i)‖
              = ‖a‖ * ‖(descPochhammer L (r + 1)).coeff i‖ := by rw [norm_neg, norm_mul]
            _ ≤ ρ ^ (r + 1) * 1 := mul_le_mul (hP (r + 1)) (hint i) (norm_nonneg _)
                (pow_nonneg hρ _)
            _ = ρ ^ (r + 1) := mul_one _
            _ ≤ ρ ^ i := pow_le_pow_of_le_one hρ hρ1 hi
        · rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hi),
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [descPochhammer_natDegree]; omega),
            mul_zero, sub_zero, norm_zero]
          positivity
      have hdegQ : Q.natDegree ≤ r := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro j hj
        rcases eq_or_ne j (r + 1) with rfl | hne
        · rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul, htop, mul_one, sub_self]
        · rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega)),
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [descPochhammer_natDegree]; omega),
            mul_zero, sub_zero]
      obtain ⟨c, hc, hcs, hrep⟩ := IH Q hdegQ hcoeffQ
      refine ⟨Function.update c (r + 1) a, fun i => ?_, fun i hi => ?_, ?_⟩
      · rcases eq_or_ne i (r + 1) with rfl | hne
        · rw [Function.update_self]
          exact hP (r + 1)
        · rw [Function.update_of_ne hne]
          exact hc i
      · rw [Function.update_of_ne (by omega)]
        exact hcs i (by omega)
      · rw [Finset.sum_range_succ,
          Finset.sum_congr rfl (fun i hi =>
            by rw [Function.update_of_ne (show i ≠ r + 1 by
              rw [Finset.mem_range] at hi; omega)]),
          ← hrep, Function.update_self, hQ]
        ring

/-- [LWX, Lemma 3.11] in norm form over an ultrametric field of characteristic zero
with weight `ρ ≤ 1`: a polynomial with `‖coeff i‖ ≤ ρ^i` is a combination
`∑ cᵢ·i!·binom(z,i)` with `‖cᵢ‖ ≤ ρ^i`.  (The source states it with a valuation
weight `s ∈ ℝ≥0`; `ρ = p^{−s} ≤ 1`, allowing the fractional `s` of Lemma 3.13's
proof without leaving `ℚ_p`.  `CharZero`/`ρ ≤ 1` are forced: in characteristic `p`
the `i ≥ p` terms all vanish, and for `ρ > 1` the triangular system violates the
bound — see the board's b2 log.) -/
theorem exists_binomial_basis {L : Type*} [NontriviallyNormedField L]
    [IsUltrametricDist L] [CharZero L] {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial L) (hP : ∀ i, ‖P.coeff i‖ ≤ ρ ^ i) :
    ∃ c : ℕ → L, (∀ i, ‖c i‖ ≤ ρ ^ i) ∧ (∀ i, P.natDegree < i → c i = 0) ∧
      P = ∑ i ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (c i * i.factorial) * binomialPoly L i := by
  obtain ⟨c, hc, hcs, hrep⟩ :=
    exists_descPochhammer_basis hρ hρ1 P.natDegree P le_rfl hP
  refine ⟨c, hc, hcs, hrep.trans (Finset.sum_congr rfl fun i _ => ?_)⟩
  simp only [binomialPoly]
  rw [← mul_assoc, ← Polynomial.C_mul,
    mul_assoc (c i) (i.factorial : L) (i.factorial : L)⁻¹,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)), mul_one]

/-! ### The two binomial estimates ([LWX, Lemmas 3.12 and 3.13]) -/

/-- The `ℕ`-valuation inequality inside [LWX, Lemma 3.12]:
for `k > ⌊n/p⌋`, `v(k!·p^k) ≥ k − ⌊n/p⌋ + v(n!)`. -/
theorem nat_ineq_3_12 {n k : ℕ} (h : n / p < k) :
    (k - n / p : ℕ) + (n.factorial.factorization p : ℕ) ≤
      k + k.factorial.factorization p := by
  set b := Nat.log p n + Nat.log p k + 2 with hb
  have hn : n.factorial.factorization p = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
    rw [Nat.factorization_def _ hp.out, padicValNat_factorial (b := b) (by omega)]
  have hk : k.factorial.factorization p = ∑ i ∈ Finset.Ico 1 b, k / p ^ i := by
    rw [Nat.factorization_def _ hp.out, padicValNat_factorial (b := b) (by omega)]
  have hpeel : ∑ i ∈ Finset.Ico 1 b, n / p ^ i
      = n / p + ∑ i ∈ Finset.Ico 2 b, n / p ^ i := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < b), pow_one]
  have htail : ∑ i ∈ Finset.Ico 2 b, n / p ^ i ≤ ∑ i ∈ Finset.Ico 1 b, k / p ^ i := by
    calc ∑ i ∈ Finset.Ico 2 b, n / p ^ i
        = ∑ r ∈ Finset.range (b - 2), n / p ^ (2 + r) :=
          Finset.sum_Ico_eq_sum_range (fun i => n / p ^ i) 2 b
      _ ≤ ∑ r ∈ Finset.range (b - 2), k / p ^ (1 + r) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [show (2 : ℕ) + r = (1 + r) + 1 by omega, pow_succ, mul_comm,
            ← Nat.div_div_eq_div_mul]
          exact Nat.div_le_div_right h.le
      _ ≤ ∑ r ∈ Finset.range (b - 1), k / p ^ (1 + r) :=
          Finset.sum_le_sum_of_subset (fun x hx => Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega)))
      _ = ∑ i ∈ Finset.Ico 1 b, k / p ^ i :=
          (Finset.sum_Ico_eq_sum_range (fun i => k / p ^ i) 1 b).symm
  omega

/-- `descPochhammer` evaluates to `n!·binom(x,n)` in any binomial ring (the
`eval` form of `Ring.descPochhammer_eq_factorial_smul_choose`). -/
private theorem descPochhammer_eval_eq_factorial_smul_choose {R : Type*} [CommRing R]
    [BinomialRing R] (x : R) (n : ℕ) :
    (descPochhammer R n).eval x = n.factorial • Ring.choose x n := by
  rw [← Ring.descPochhammer_eq_factorial_smul_choose,
    ← Polynomial.eval₂_smulOneHom_eq_smeval ℤ, ← descPochhammer_map (Int.castRingHom R) n,
    Polynomial.eval_map]
  congr 1
  exact Subsingleton.elim _ _

/-- `Ring.choose` on `ℤ_[p]` is computed by `Ring.choose` on `ℚ_[p]`. -/
private theorem coe_ringChoose (z : ℤ_[p]) (k : ℕ) :
    ((Ring.choose z k : ℤ_[p]) : ℚ_[p]) = Ring.choose (z : ℚ_[p]) k := by
  have hfac : (k.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  refine mul_left_cancel₀ hfac ?_
  calc (k.factorial : ℚ_[p]) * ((Ring.choose z k : ℤ_[p]) : ℚ_[p])
      = (((k.factorial • Ring.choose z k : ℤ_[p])) : ℚ_[p]) := by
        push_cast [nsmul_eq_mul]
        ring
    _ = (((descPochhammer ℤ_[p] k).eval z : ℤ_[p]) : ℚ_[p]) := by
        rw [descPochhammer_eval_eq_factorial_smul_choose]
    _ = (descPochhammer ℚ_[p] k).eval (z : ℚ_[p]) := by
        rw [← descPochhammer_map (PadicInt.Coe.ringHom (p := p)) k, Polynomial.eval_map,
          show ((z : ℚ_[p])) = PadicInt.Coe.ringHom (p := p) z from rfl,
          Polynomial.eval₂_at_apply]
        rfl
    _ = (k.factorial : ℚ_[p]) * Ring.choose (z : ℚ_[p]) k := by
        rw [descPochhammer_eval_eq_factorial_smul_choose, nsmul_eq_mul]

/-- Iterated differences of `ℤ_[p]`-valued functions commute with the (isometric)
inclusion into `ℚ_[p]`. -/
private theorem coe_fwdDiff_iter (m : ℕ) (φ : ℤ_[p] → ℤ_[p]) (z : ℤ_[p]) :
    ((Δ_[1]^[m] φ z : ℤ_[p]) : ℚ_[p]) = Δ_[1]^[m] (fun w => (φ w : ℚ_[p])) z := by
  induction m generalizing φ with
  | zero => rfl
  | succ m IH =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, IH (Δ_[1] φ),
        show (fun w => ((Δ_[1] φ w : ℤ_[p]) : ℚ_[p]))
            = Δ_[1] (fun w => ((φ w : ℤ_[p]) : ℚ_[p])) from funext fun w => by
          simp [fwdDiff]]

/-- The mixed-domain form of `fwdDiff_iter_choose`: iterated differences of
`z ↦ binom(z, k)` as a `ℚ_[p]`-valued function on `ℤ_[p]`. -/
private theorem fwdDiff_iter_choose_coe (m k : ℕ) (z : ℤ_[p]) :
    Δ_[1]^[m] (fun w : ℤ_[p] => Ring.choose (w : ℚ_[p]) k) z =
      if m ≤ k then Ring.choose (z : ℚ_[p]) (k - m) else 0 := by
  rw [show (fun w : ℤ_[p] => Ring.choose (w : ℚ_[p]) k)
      = fun w => ((Ring.choose w k : ℤ_[p]) : ℚ_[p]) from
    funext fun w => (coe_ringChoose w k).symm, ← coe_fwdDiff_iter, fwdDiff_iter_choose]
  split_ifs with h
  · exact coe_ringChoose z (k - m)
  · show ((0 : ℤ_[p]) : ℚ_[p]) = 0
    exact PadicInt.coe_zero

/-- The `ρ`-graded coefficient bound is closed under polynomial multiplication. -/
private theorem coeff_mul_le_of_coeff_le {P Q : Polynomial ℤ_[p]} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hP : ∀ k, ‖P.coeff k‖ ≤ ρ ^ k) (hQ : ∀ k, ‖Q.coeff k‖ ≤ ρ ^ k) (k : ℕ) :
    ‖(P * Q).coeff k‖ ≤ ρ ^ k := by
  rw [Polynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hρ _) ?_
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  calc ‖P.coeff i * Q.coeff j‖ = ‖P.coeff i‖ * ‖Q.coeff j‖ := norm_mul _ _
    _ ≤ ρ ^ i * ρ ^ j :=
        mul_le_mul (hP i) (hQ j) (norm_nonneg _) (pow_nonneg hρ _)
    _ = ρ ^ k := by rw [← pow_add, hij]

/-- The `p^{−k}`-graded bound survives composition with `descPochhammer`
(the "`g(z) ∈ ℤ_p[pz]`" step of [LWX, Lemma 3.12]). -/
private theorem coeff_descPochhammer_comp_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (n : ℕ) :
    ∀ P : Polynomial ℤ_[p], (∀ k, ‖P.coeff k‖ ≤ ρ ^ k) →
      ∀ k, ‖((descPochhammer ℤ_[p] n).comp P).coeff k‖ ≤ ρ ^ k := by
  induction n with
  | zero =>
      intro P _ k
      rw [descPochhammer_zero, Polynomial.one_comp, Polynomial.coeff_one]
      rcases eq_or_ne k 0 with rfl | h
      · simp
      · rw [if_neg h, norm_zero]
        exact pow_nonneg hρ0 _
  | succ n IH =>
      intro P hP k
      have hP1 : ∀ k, ‖(P - 1).coeff k‖ ≤ ρ ^ k := by
        intro k
        rcases eq_or_ne k 0 with rfl | h
        · simpa using PadicInt.norm_le_one ((P - 1).coeff 0)
        · rw [Polynomial.coeff_sub, Polynomial.coeff_one, if_neg h, sub_zero]
          exact hP k
      rw [descPochhammer_succ_left, Polynomial.mul_comp, Polynomial.X_comp,
        Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp]
      exact coeff_mul_le_of_coeff_le hρ0 hP (IH (P - 1) hP1) k

/-- The Mahler-expansion engine behind [LWX, Lemmas 3.12 and 3.13(a)–(b)]: a
`ρ`-graded coefficient bound on a polynomial `P`, together with a norm bound on the
falling-factorial coefficients `x·k!/n!` for `k > d`, gives `binom(P.eval ·, n)`
tilted degree `≤ d`. -/
private theorem tiltedDeg_choose_of_norm_bound (P : Polynomial ℤ_[p]) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hP : ∀ k, ‖P.coeff k‖ ≤ ρ ^ k) (n d : ℕ)
    (hd : ∀ k, d < k → k ≤ n * P.natDegree → ∀ x : ℚ_[p], ‖x‖ ≤ ρ ^ k →
      ‖x * (k.factorial : ℚ_[p]) / n.factorial‖ ≤ (p : ℝ) ^ ((d : ℤ) - k)) :
    TiltedDeg d fun z => Ring.choose (P.eval z) n := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  set g := (descPochhammer ℤ_[p] n).comp P with hg
  set Q := g.map (PadicInt.Coe.ringHom (p := p)) with hQdef
  have hQc : ∀ k, ‖Q.coeff k‖ ≤ ρ ^ k := by
    intro k
    rw [hQdef, Polynomial.coeff_map]
    rw [show PadicInt.Coe.ringHom (p := p) (g.coeff k) = ((g.coeff k : ℤ_[p]) : ℚ_[p])
      from rfl, PadicInt.padic_norm_e_of_padicInt]
    exact coeff_descPochhammer_comp_le hρ0 n P hP k
  obtain ⟨c, hc, hcsupp, hrep⟩ := exists_binomial_basis hρ0 hρ1 Q hQc
  have hQP : Q = (descPochhammer ℚ_[p] n).comp
      (P.map (PadicInt.Coe.ringHom (p := p))) := by
    rw [hQdef, hg, Polynomial.map_comp, descPochhammer_map]
  have hdegQ : Q.natDegree ≤ n * P.natDegree := by
    calc Q.natDegree ≤ g.natDegree := Polynomial.natDegree_map_le
      _ ≤ (descPochhammer ℤ_[p] n).natDegree * P.natDegree := Polynomial.natDegree_comp_le
      _ = n * P.natDegree := by rw [descPochhammer_natDegree]
  have hkey : ∀ z : ℤ_[p],
      (n.factorial : ℚ_[p]) * ((Ring.choose (P.eval z) n : ℤ_[p]) : ℚ_[p])
        = Q.eval (z : ℚ_[p]) := by
    intro z
    have h1 : ((P.eval z : ℤ_[p]) : ℚ_[p])
        = (P.map (PadicInt.Coe.ringHom (p := p))).eval (z : ℚ_[p]) := by
      rw [Polynomial.eval_map, show ((z : ℚ_[p])) = PadicInt.Coe.ringHom (p := p) z
        from rfl, Polynomial.eval₂_at_apply]
      rfl
    calc (n.factorial : ℚ_[p]) * ((Ring.choose (P.eval z) n : ℤ_[p]) : ℚ_[p])
        = (n.factorial : ℚ_[p]) * Ring.choose
            ((P.map (PadicInt.Coe.ringHom (p := p))).eval (z : ℚ_[p])) n := by
          rw [coe_ringChoose, h1]
      _ = (descPochhammer ℚ_[p] n).eval
            ((P.map (PadicInt.Coe.ringHom (p := p))).eval (z : ℚ_[p])) := by
          rw [descPochhammer_eval_eq_factorial_smul_choose, nsmul_eq_mul]
      _ = Q.eval (z : ℚ_[p]) := by rw [← Polynomial.eval_comp, ← hQP]
  have hψ : ∀ z : ℤ_[p], ((Ring.choose (P.eval z) n : ℤ_[p]) : ℚ_[p])
      = ∑ k ∈ Finset.range (Q.natDegree + 1),
          (c k * k.factorial / n.factorial) • Ring.choose (z : ℚ_[p]) k := by
    intro z
    have hn0 : (n.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    refine mul_left_cancel₀ hn0 ?_
    rw [hkey z]
    conv_lhs => rw [hrep]
    rw [Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hbp : (binomialPoly ℚ_[p] k).eval (z : ℚ_[p]) = Ring.choose (z : ℚ_[p]) k := by
      rw [binomialPoly, Polynomial.eval_mul, Polynomial.eval_C,
        descPochhammer_eval_eq_factorial_smul_choose, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero), one_mul]
    rw [Polynomial.eval_mul, Polynomial.eval_C, hbp, smul_eq_mul]
    field_simp
  -- the coefficient bound for the surviving basis terms, from the hypothesis
  have hbound : ∀ k : ℕ, d < k → k ≤ Q.natDegree →
      ‖c k * (k.factorial : ℚ_[p]) / n.factorial‖ ≤ (p : ℝ) ^ ((d : ℤ) - k) :=
    fun k hk hk2 => hd k hk (hk2.trans hdegQ) (c k) (hc k)
  -- assemble the clause-(1) bound
  rw [tiltedDeg_iff_of_forall_norm_le]
  intro m hm z
  have hfun : (fun w : ℤ_[p] => ((Ring.choose (P.eval w) n : ℤ_[p]) : ℚ_[p]))
      = ∑ k ∈ Finset.range (Q.natDegree + 1),
          fun w : ℤ_[p] => (c k * k.factorial / n.factorial) • Ring.choose (w : ℚ_[p]) k := by
    funext w
    rw [Finset.sum_apply]
    exact hψ w
  rw [PadicInt.norm_def, coe_fwdDiff_iter, hfun, fwdDiff_iter_finsetSum, Finset.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (zpow_nonneg (Nat.cast_nonneg p) _) fun k hkmem => ?_
  have hkQ : k ≤ Q.natDegree := by
    rw [Finset.mem_range] at hkmem
    omega
  have hsmul : Δ_[1]^[m]
      (fun w : ℤ_[p] => (c k * k.factorial / n.factorial) • Ring.choose (w : ℚ_[p]) k) z
      = (c k * k.factorial / n.factorial) •
          Δ_[1]^[m] (fun w : ℤ_[p] => Ring.choose (w : ℚ_[p]) k) z :=
    congrFun (fwdDiff_iter_const_smul (1 : ℤ_[p]) (c k * k.factorial / n.factorial)
      (fun w : ℤ_[p] => Ring.choose (w : ℚ_[p]) k) m) z
  rw [hsmul, fwdDiff_iter_choose_coe]
  rcases le_or_gt m k with h | h
  · rw [if_pos h, smul_eq_mul, norm_mul]
    have hchoose1 : ‖Ring.choose (z : ℚ_[p]) (k - m)‖ ≤ 1 := by
      rw [← coe_ringChoose, PadicInt.padic_norm_e_of_padicInt]
      exact PadicInt.norm_le_one _
    calc ‖c k * (k.factorial : ℚ_[p]) / n.factorial‖ * ‖Ring.choose (z : ℚ_[p]) (k - m)‖
        ≤ (p : ℝ) ^ ((d : ℤ) - k) * 1 :=
          mul_le_mul (hbound k (lt_of_lt_of_le hm h) hkQ) hchoose1 (norm_nonneg _)
            (zpow_nonneg (Nat.cast_nonneg p) _)
      _ = (p : ℝ) ^ ((d : ℤ) - k) := mul_one _
      _ ≤ (p : ℝ) ^ ((d : ℤ) - m) := zpow_le_zpow_right₀ hp1R.le (by omega)
  · rw [if_neg (by omega), smul_zero, norm_zero]
    exact zpow_nonneg (Nat.cast_nonneg p) _

private theorem tiltedDeg_choose_of_pMul_poly (P : Polynomial ℤ_[p])
    (hP : ∀ k, ‖P.coeff k‖ ≤ (p : ℝ)⁻¹ ^ k) (n : ℕ) :
    TiltedDeg (n / p) fun z => Ring.choose (P.eval z) n := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  refine tiltedDeg_choose_of_norm_bound P (inv_nonneg.mpr (Nat.cast_nonneg p))
    (inv_le_one_of_one_le₀ hp1R.le) hP n (n / p) ?_
  intro k hk _ x hx
  have hkf : (k.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnf : (n.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hnormk : ‖(k.factorial : ℚ_[p])‖
      = (p : ℝ) ^ (-(k.factorial.factorization p : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hkf, Padic.valuation_natCast,
      Nat.factorization_def _ hp.out]
  have hnormn : ‖(n.factorial : ℚ_[p])‖
      = (p : ℝ) ^ (-(n.factorial.factorization p : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hnf, Padic.valuation_natCast,
      Nat.factorization_def _ hp.out]
  have hcast : ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    refine hx.trans (le_of_eq ?_)
    rw [zpow_neg, ← inv_zpow, zpow_natCast]
  rw [norm_div, norm_mul, hnormk, hnormn]
  rw [div_le_iff₀ (zpow_pos (by exact_mod_cast hp.out.pos) _)]
  calc ‖x‖ * (p : ℝ) ^ (-(k.factorial.factorization p : ℤ))
      ≤ (p : ℝ) ^ (-(k : ℤ)) * (p : ℝ) ^ (-(k.factorial.factorization p : ℤ)) :=
        mul_le_mul_of_nonneg_right hcast (zpow_nonneg (Nat.cast_nonneg p) _)
    _ = (p : ℝ) ^ (-(k : ℤ) + -(k.factorial.factorization p : ℤ)) :=
        (zpow_add₀ hp0 _ _).symm
    _ ≤ (p : ℝ) ^ ((((n / p : ℕ) : ℤ) - k) + -(n.factorial.factorization p : ℤ)) := by
        refine zpow_le_zpow_right₀ hp1R.le ?_
        have := nat_ineq_3_12 (n := n) (k := k) hk
        omega
    _ = (p : ℝ) ^ (((n / p : ℕ) : ℤ) - k) * (p : ℝ) ^ (-(n.factorial.factorization p : ℤ)) :=
        zpow_add₀ hp0 _ _

/-- [LWX, Lemma 3.12]: if `F : ℤ_p → ℤ_p` is given by a power series with
`‖a_k‖ ≤ p^{−k}` (i.e. `F ∈ ℤ_p⟦pz⟧`), then `z ↦ binom(F z, n)` has tilted degree
`≤ ⌊n/p⌋`. -/
theorem tiltedDeg_choose_of_pMul {F : ℤ_[p] → ℤ_[p]} {a : ℕ → ℤ_[p]}
    (ha : ∀ k, ‖a k‖ ≤ (p : ℝ) ^ (-(k : ℤ)))
    (hF : ∀ z, HasSum (fun k => a k * z ^ k) (F z)) (n : ℕ) :
    TiltedDeg (n / p) fun z => Ring.choose (F z) n := by
  set P : ℕ → Polynomial ℤ_[p] :=
    fun N => ∑ k ∈ Finset.range N, Polynomial.C (a k) * Polynomial.X ^ k with hPdef
  have hcoeff : ∀ N k, ‖(P N).coeff k‖ ≤ (p : ℝ)⁻¹ ^ k := by
    intro N k
    rw [hPdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range N) k a]
    have hpk : (p : ℝ) ^ (-(k : ℤ)) = (p : ℝ)⁻¹ ^ k := by
      rw [zpow_neg, ← inv_zpow, zpow_natCast]
    split_ifs with h
    · rw [← hpk]
      exact ha k
    · rw [norm_zero]
      positivity
  refine TiltedDeg.of_tendsto (F := fun N z => Ring.choose ((P N).eval z) n)
    (fun N => tiltedDeg_choose_of_pMul_poly (P N) (hcoeff N) n) fun z => ?_
  have heval : ∀ N, (P N).eval z = ∑ k ∈ Finset.range N, a k * z ^ k := by
    intro N
    rw [hPdef, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have h1 : Tendsto (fun N => (P N).eval z) atTop (𝓝 (F z)) := by
    simp only [heval]
    exact (hF z).tendsto_sum_nat
  exact ((PadicInt.continuous_choose n).continuousAt.tendsto.comp h1)

omit hp in
/-- The `ℕ`-valuation inequality [LWX, (3.13.2)] in norm form, **case (a)** (`p ∤ n`):
for `m < k ≤ m·n`, `v(k!) + m ≥ v(m!) + k(1 + v(n))/n`.  (The board's original bare
hypothesis `2 ≤ n` is false at `n = p` — [LWX]'s case (c) — so the source's case
guards are the hypotheses; sanctioned edit recorded on ticket C4.) -/
theorem nat_ineq_3_13_2 {m n k : ℕ} (hpn : ¬ p ∣ n) (hmk : m < k) (hkn : k ≤ m * n) :
    (k : ℝ) * (1 + n.factorization p) / n ≤
      (k.factorial.factorization p : ℝ) + m - m.factorial.factorization p := by
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (dvd_zero p) hpn
    · exact h
  have hvn : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
  have hvm : m.factorial.factorization p ≤ k.factorial.factorization p :=
    Finsupp.le_def.mp
      ((Nat.factorization_le_iff_dvd m.factorial_ne_zero k.factorial_ne_zero).mpr
        (Nat.factorial_dvd_factorial hmk.le)) p
  have hkm : (k : ℝ) / n ≤ m := by
    rw [div_le_iff₀ (by exact_mod_cast hn0)]
    exact_mod_cast hkn
  have hvmR : (m.factorial.factorization p : ℝ) ≤ k.factorial.factorization p := by
    exact_mod_cast hvm
  rw [hvn]
  push_cast
  norm_num
  linarith

/-- The `ℕ`-valuation inequality [LWX, (3.13.2)] in norm form, **case (b)**
(`n ≥ 2p`, `p` odd — the source's exclusion `(p,n) ≠ (2,4)` is then automatic). -/
theorem nat_ineq_3_13_2' (hp2 : p ≠ 2) {m n k : ℕ} (hn : 2 * p ≤ n) (hmk : m < k)
    (hkn : k ≤ m * n) :
    (k : ℝ) * (1 + n.factorization p) / n ≤
      (k.factorial.factorization p : ℝ) + m - m.factorial.factorization p := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hn0 : 0 < n := by omega
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · omega
    · exact h
  -- the source's display `(1 + v(n))/n ≤ 1/p`, in the form `p·(1 + v(n)) ≤ n`
  have hkey : p * (1 + n.factorization p) ≤ n := by
    set a := n.factorization p with ha
    rcases Nat.lt_or_ge a 2 with h2 | h2
    · have := Nat.mul_le_mul_left p (show 1 + a ≤ 2 by omega)
      omega
    · have hle : p ^ a ≤ n := Nat.le_of_dvd hn0 (ha ▸ Nat.ordProj_dvd n p)
      have h3 : ∀ c : ℕ, c + 3 ≤ 3 ^ (c + 1) := by
        intro c
        induction c with
        | zero => norm_num
        | succ c IH => rw [pow_succ]; omega
      have hgrow : 1 + a ≤ p ^ (a - 1) :=
        calc 1 + a = (a - 2) + 3 := by omega
          _ ≤ 3 ^ ((a - 2) + 1) := h3 _
          _ = 3 ^ (a - 1) := by congr 1; omega
          _ ≤ p ^ (a - 1) := Nat.pow_le_pow_left hp3 _
      calc p * (1 + a) ≤ p * p ^ (a - 1) := Nat.mul_le_mul_left p hgrow
        _ = p ^ (a - 1 + 1) := (pow_succ' p (a - 1)).symm
        _ ≤ n := by rwa [show a - 1 + 1 = a by omega]
  -- the source's `v(k!/m!) ≥ ⌊(k−m)/p⌋`, via `k! = C(k,m)·m!·(k−m)!` and Legendre
  have hfac : m.factorial.factorization p + (k - m) / p
      ≤ k.factorial.factorization p := by
    have hv : k.factorial.factorization p
        = ((k.choose m).factorization p + m.factorial.factorization p)
          + (k - m).factorial.factorization p := by
      rw [← Nat.choose_mul_factorial_mul_factorial hmk.le,
        Nat.factorization_mul
          (Nat.mul_ne_zero (Nat.choose_pos hmk.le).ne' m.factorial_ne_zero)
          (k - m).factorial_ne_zero,
        Nat.factorization_mul (Nat.choose_pos hmk.le).ne' m.factorial_ne_zero]
      simp [Finsupp.add_apply]
    have hvkm : (k - m) / p ≤ (k - m).factorial.factorization p := by
      rcases Nat.eq_zero_or_pos ((k - m) / p) with h0 | h0
      · omega
      · have hple : p ≤ k - m := by
          by_contra hcon
          rw [not_le] at hcon
          rw [Nat.div_eq_of_lt hcon] at h0
          omega
        rw [Nat.factorization_def _ hp.out,
          padicValNat_factorial (Nat.lt_add_one _)]
        have h1mem : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log p (k - m) + 1) :=
          Finset.mem_Ico.mpr
            ⟨le_rfl, by have := Nat.log_pos hp.out.one_lt hple; omega⟩
        calc (k - m) / p = (k - m) / p ^ 1 := by rw [pow_one]
          _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p (k - m) + 1), (k - m) / p ^ i :=
            Finset.single_le_sum (f := fun i => (k - m) / p ^ i)
              (fun i _ => Nat.zero_le _) h1mem
    omega
  -- assemble over ℝ
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hstep1 : (k : ℝ) * (1 + n.factorization p) / n ≤ k / p := by
    rw [div_le_div_iff₀ hnR hpR]
    calc (k : ℝ) * (1 + n.factorization p) * p
        = k * (p * (1 + n.factorization p)) := by ring
      _ ≤ k * n :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hkey) (Nat.cast_nonneg k)
  have hfloor : ((k - m : ℕ) : ℝ) / p - 1 + 1 / p ≤ ((k - m) / p : ℕ) := by
    have hmod : (k - m) % p < p := Nat.mod_lt _ hp.out.pos
    rw [show ((k - m : ℕ) : ℝ) / p - 1 + 1 / p = (((k - m : ℕ) : ℝ) - p + 1) / p by
      field_simp, div_le_iff₀ hpR]
    have h1 : ((k - m : ℕ) : ℝ) + 1 ≤ p * (((k - m) / p : ℕ) : ℝ) + p := by
      exact_mod_cast (show (k - m : ℕ) + 1 ≤ p * ((k - m) / p) + p by
        have hdm := Nat.div_add_mod (k - m) p
        omega)
    linarith
  have hfacR : (m.factorial.factorization p : ℝ) + (((k - m) / p : ℕ) : ℝ)
      ≤ k.factorial.factorization p := by exact_mod_cast hfac
  have hsub : ((k - m : ℕ) : ℝ) = (k : ℝ) - m := by
    push_cast [Nat.cast_sub hmk.le]
    ring
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have haux : (0 : ℝ) ≤ ((m : ℝ) - 1) * (1 - 1 / p) := by
    refine mul_nonneg (by linarith) ?_
    rw [sub_nonneg, div_le_one hpR]
    exact_mod_cast hp.out.one_le
  have hexpand : ((m : ℝ) - 1) * (1 - 1 / p) = (m : ℝ) - 1 - m / p + 1 / p := by
    field_simp
    ring
  refine hstep1.trans ?_
  rw [hexpand] at haux
  have hsplit : (k : ℝ) / p = ((k - m : ℕ) : ℝ) / p + (m : ℝ) / p := by
    rw [hsub]
    ring
  linarith

/-- The monomial case `n = p` of [LWX, Lemma 3.13(c)]: `z ↦ binom(a·p^{p−2}·z^p, m)`
has tilted degree `≤ m`, by induction on `m` through Lemma 3.12 applied to
`a·p^{p−2}((z+1)^p − z^p) ∈ ℤ_p⟦pz⟧`. -/
theorem tiltedDeg_choose_monomial_p (hp2 : p ≠ 2) (a : ℤ_[p]) (m : ℕ) :
    TiltedDeg m fun z : ℤ_[p] =>
      Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * z ^ p) m := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [show (fun z : ℤ_[p] => Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * z ^ p) 0)
        = fun _ => (1 : ℤ_[p]) from funext fun z => Ring.choose_zero_right _]
    exact tiltedDeg_const 0 1
  refine TiltedDeg.of_fwdDiff hm ?_
  -- the increment `D z = a·p^{p−2}·((z+1)^p − z^p)` lies in `ℤ_p⟦pz⟧`
  have hD : ∀ j : ℕ, TiltedDeg (j / p) fun z : ℤ_[p] =>
      Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * ((z + 1) ^ p - z ^ p)) j := by
    intro j
    set d : ℕ → ℤ_[p] :=
      fun k => if k < p then a * (p : ℤ_[p]) ^ (p - 2) * (p.choose k : ℤ_[p]) else 0
      with hd
    refine tiltedDeg_choose_of_pMul (a := d) ?_ ?_ j
    · intro k
      simp only [hd]
      split_ifs with hk
      · rcases Nat.eq_zero_or_pos k with rfl | hk1
        · simpa using
            PadicInt.norm_le_one (a * (p : ℤ_[p]) ^ (p - 2) * (p.choose 0 : ℤ_[p]))
        · have hdvd : (p : ℤ_[p]) ∣ (p.choose k : ℤ_[p]) :=
            Nat.cast_dvd_cast (Nat.Prime.dvd_choose_self hp.out hk1.ne' hk)
          obtain ⟨u, hu⟩ := hdvd
          calc ‖a * (p : ℤ_[p]) ^ (p - 2) * (p.choose k : ℤ_[p])‖
              = ‖a‖ * ‖(p : ℤ_[p])‖ ^ (p - 2) * ((p : ℝ)⁻¹ * ‖u‖) := by
                rw [norm_mul, norm_mul, norm_pow, hu, norm_mul, PadicInt.norm_p]
            _ ≤ 1 * ((p : ℝ)⁻¹) ^ (p - 2) * ((p : ℝ)⁻¹ * 1) := by
                have h1 : ‖(p : ℤ_[p])‖ ^ (p - 2) = ((p : ℝ)⁻¹) ^ (p - 2) := by
                  rw [PadicInt.norm_p]
                rw [h1]
                refine mul_le_mul (mul_le_mul (PadicInt.norm_le_one a) le_rfl
                  (by positivity) zero_le_one) ?_ (by positivity) (by positivity)
                exact mul_le_mul le_rfl (PadicInt.norm_le_one u) (norm_nonneg _)
                  (by positivity)
            _ = (p : ℝ) ^ (-((p - 1 : ℕ) : ℤ)) := by
                rw [one_mul, mul_one, zpow_neg, ← inv_zpow, zpow_natCast, ← pow_succ]
                congr 1
                omega
            _ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
                refine zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) ?_
                omega
      · rw [norm_zero]
        exact zpow_nonneg (Nat.cast_nonneg p) _
    · intro z
      have hfin : ∀ k ∉ Finset.range p, d k * z ^ k = 0 := by
        intro k hk
        rw [Finset.mem_range, not_lt] at hk
        simp only [hd]
        rw [if_neg (by omega), zero_mul]
      have hsum : HasSum (fun k => d k * z ^ k) (∑ k ∈ Finset.range p, d k * z ^ k) :=
        hasSum_sum_of_ne_finset_zero hfin
      convert hsum using 1
      have hbin : (z + 1) ^ p = ∑ k ∈ Finset.range (p + 1),
          z ^ k * (1 : ℤ_[p]) ^ (p - k) * (p.choose k : ℤ_[p]) := add_pow z 1 p
      simp only [one_pow, mul_one] at hbin
      calc a * (p : ℤ_[p]) ^ (p - 2) * ((z + 1) ^ p - z ^ p)
          = a * (p : ℤ_[p]) ^ (p - 2)
              * (∑ k ∈ Finset.range p, z ^ k * (p.choose k : ℤ_[p])) := by
            rw [hbin, Finset.sum_range_succ, Nat.choose_self]
            push_cast
            ring
        _ = ∑ k ∈ Finset.range p, d k * z ^ k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k hk => ?_
            simp only [hd]
            rw [if_pos (Finset.mem_range.mp hk)]
            ring
  -- Chu–Vandermonde: `Δ̃(binom(f·,m))` as a sum of products over `i < m`
  have hstep : Δ_[1] (fun z : ℤ_[p] => Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * z ^ p) m)
      = fun z => ∑ i ∈ Finset.range m,
          Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * z ^ p) i *
          Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * ((z + 1) ^ p - z ^ p)) (m - i) := by
    funext z
    show Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * (z + 1) ^ p) m
        - Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * z ^ p) m = _
    rw [show a * (p : ℤ_[p]) ^ (p - 2) * (z + 1) ^ p
        = a * (p : ℤ_[p]) ^ (p - 2) * z ^ p
          + a * (p : ℤ_[p]) ^ (p - 2) * ((z + 1) ^ p - z ^ p) by ring,
      Ring.add_choose_eq m (Commute.all _ _),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * z ^ p) i *
          Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * ((z + 1) ^ p - z ^ p)) j) m,
      Finset.sum_range_succ, Nat.sub_self, Ring.choose_zero_right, mul_one,
      add_sub_cancel_right]
  rw [hstep]
  refine TiltedDeg.sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have h1 : TiltedDeg i fun z : ℤ_[p] =>
      Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * z ^ p) i := IH i (by omega)
  have h2 : TiltedDeg (m - i - 1) fun z : ℤ_[p] =>
      Ring.choose (a * (p : ℤ_[p]) ^ (p - 2) * ((z + 1) ^ p - z ^ p)) (m - i) := by
    refine (hD (m - i)).mono ?_
    have h3 : (m - i) / p ≤ (m - i) / 2 := Nat.div_le_div_left hp.out.two_le zero_lt_two
    omega
  have hmul := h1.mul h2
  rw [show i + (m - i - 1) = m - 1 by omega] at hmul
  exact hmul

/-- Iterated differences of a restriction to `ℤ_[p]` agree with the ambient ones. -/
private theorem fwdDiff_iter_comp_coe (G : ℚ_[p] → ℚ_[p]) (r : ℕ) (z : ℤ_[p]) :
    Δ_[1]^[r] (fun w : ℤ_[p] => G (w : ℚ_[p])) z = Δ_[1]^[r] G (z : ℚ_[p]) := by
  induction r generalizing G z with
  | zero => rfl
  | succ r IH =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← IH (Δ_[1] G) z]
      rfl

/-- `v(N) ≤ N − 1` for `N ≥ 1`. -/
private theorem factorization_le_pred {N : ℕ} (hN : 1 ≤ N) :
    N.factorization p ≤ N - 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have h1 : p ^ N ≤ p ^ (N.factorization p) :=
    Nat.pow_le_pow_right hp.out.pos (by omega)
  have h2 : p ^ (N.factorization p) ≤ N := Nat.le_of_dvd hN (Nat.ordProj_dvd N p)
  have h3 : N < 2 ^ N := Nat.lt_two_pow_self
  have h4 : 2 ^ N ≤ p ^ N := Nat.pow_le_pow_left hp.out.two_le N
  omega

/-- The `(a)`/`(b)` engine for a single log-shape monomial `a₀·z^N` (`N ≥ 2`), fed by
the applicable case of (3.13.2). -/
private theorem tiltedDeg_choose_logMonomial_engine {N : ℕ} (hN2 : 2 ≤ N) (a₀ : ℤ_[p])
    (ha : ‖a₀‖ ≤ (p : ℝ) ^ (-(N : ℤ) + 1 + (N.factorization p : ℤ)))
    (hineq : ∀ j k : ℕ, j < k → k ≤ j * N →
      (k : ℝ) * (1 + N.factorization p) / N ≤
        (k.factorial.factorization p : ℝ) + j - j.factorial.factorization p)
    (j : ℕ) : TiltedDeg j fun z => Ring.choose (a₀ * z ^ N) j := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0R : (0 : ℝ) < p := by positivity
  have hvN : N.factorization p ≤ N - 1 := factorization_le_pred (by omega)
  set s : ℝ := ((N : ℝ) - 1 - (N.factorization p : ℝ)) / N with hs
  have hs0 : 0 ≤ s := by
    refine div_nonneg ?_ (by positivity)
    have : (N.factorization p : ℝ) ≤ (N : ℝ) - 1 := by
      have h1 : ((N.factorization p : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast hvN
      have h2 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
        ring
      linarith
    linarith
  set ρ : ℝ := (p : ℝ) ^ (-s) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg hp0R.le _
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1R.le (by linarith)
  have hρpow : ∀ k : ℕ, ρ ^ k = (p : ℝ) ^ (-(s * k)) := by
    intro k
    rw [hρ, ← Real.rpow_natCast ((p : ℝ) ^ (-s)) k, ← Real.rpow_mul hp0R.le]
    congr 1
    ring
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hsN : s * N = (N : ℝ) - 1 - (N.factorization p : ℝ) := by
    rw [hs]
    field_simp
  set P : Polynomial ℤ_[p] := Polynomial.C a₀ * Polynomial.X ^ N with hP
  have hfun : (fun z : ℤ_[p] => Ring.choose (a₀ * z ^ N) j)
      = fun z => Ring.choose (P.eval z) j := by
    funext z
    rw [hP, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
  rw [hfun]
  refine tiltedDeg_choose_of_norm_bound P hρ0 hρ1 ?_ j j ?_
  · -- the coefficient bound
    intro k
    rw [hP, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hk
    · subst hk
      refine ha.trans (le_of_eq ?_)
      rw [hρpow, ← Real.rpow_intCast (p : ℝ) (-(k : ℤ) + 1 + (k.factorization p : ℤ))]
      congr 1
      have : s * k = (k : ℝ) - 1 - (k.factorization p : ℝ) := hsN
      push_cast
      linarith
    · rw [norm_zero]
      exact pow_nonneg hρ0 _
  · -- the falling-factorial coefficient bound, via (3.13.2)
    intro k hjk hkcap x hx
    have hkN : k ≤ j * N := by
      refine hkcap.trans (Nat.mul_le_mul_left j ?_)
      rw [hP]
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (le_of_eq (Polynomial.natDegree_X_pow N))
    have hkf : (k.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hjf : (j.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hnormk : ‖(k.factorial : ℚ_[p])‖
        = (p : ℝ) ^ (-(k.factorial.factorization p : ℤ)) := by
      rw [Padic.norm_eq_zpow_neg_valuation hkf, Padic.valuation_natCast,
        Nat.factorization_def _ hp.out]
    have hnormj : ‖(j.factorial : ℚ_[p])‖
        = (p : ℝ) ^ (-(j.factorial.factorization p : ℤ)) := by
      rw [Padic.norm_eq_zpow_neg_valuation hjf, Padic.valuation_natCast,
        Nat.factorization_def _ hp.out]
    -- move everything into `rpow`
    have hzr : ∀ n : ℤ, (p : ℝ) ^ n = (p : ℝ) ^ ((n : ℝ)) := fun n =>
      (Real.rpow_intCast (p : ℝ) n).symm
    rw [norm_div, norm_mul, hnormk, hnormj, div_le_iff₀
      (by rw [hzr]; exact Real.rpow_pos_of_pos hp0R _)]
    rw [hzr, hzr, hzr]
    push_cast
    calc ‖x‖ * (p : ℝ) ^ (-(k.factorial.factorization p : ℝ))
        ≤ (p : ℝ) ^ (-(s * k)) * (p : ℝ) ^ (-(k.factorial.factorization p : ℝ)) := by
          refine mul_le_mul_of_nonneg_right (hx.trans (le_of_eq ?_)) ?_
          · rw [hρpow k]
          · exact (Real.rpow_pos_of_pos hp0R _).le
      _ = (p : ℝ) ^ (-(s * k) + -(k.factorial.factorization p : ℝ)) :=
          (Real.rpow_add hp0R _ _).symm
      _ ≤ (p : ℝ) ^ (((j : ℝ) - k) + -(j.factorial.factorization p : ℝ)) := by
          rw [Real.rpow_le_rpow_left_iff hp1R]
          have hkey := hineq j k hjk hkN
          have hsid : s * k = (k : ℝ) - (k : ℝ) * (1 + (N.factorization p : ℝ)) / N := by
            rw [hs]
            field_simp
            ring
          linarith
      _ = (p : ℝ) ^ ((j : ℝ) - k) * (p : ℝ) ^ (-(j.factorial.factorization p : ℝ)) :=
          Real.rpow_add hp0R _ _

/-- The monomial case of [LWX, Lemma 3.13]: a single log-shape term `A·z^N`. -/
private theorem tiltedDeg_choose_logMonomial (hp2 : p ≠ 2) {A : ℚ_[p]} {N : ℕ}
    (hA1 : ‖A‖ ≤ 1) (hAN : 1 ≤ N → ‖A‖ * ‖(N : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ) + 1))
    (B : ℤ_[p] → ℤ_[p]) (hB : ∀ z, (B z : ℚ_[p]) = A * (z : ℚ_[p]) ^ N)
    (j : ℕ) : TiltedDeg j fun z => Ring.choose (B z) j := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rcases Nat.eq_zero_or_pos N with rfl | hN1
  · -- constant
    have hconst : ∀ z, B z = B 0 := fun z =>
      Subtype.ext (show ((B z : ℤ_[p]) : ℚ_[p]) = ((B 0 : ℤ_[p]) : ℚ_[p]) by
        rw [hB z, hB 0]
        simp)
    rw [show (fun z => Ring.choose (B z) j) = fun _ => Ring.choose (B 0) j from
      funext fun z => by rw [hconst z]]
    exact tiltedDeg_const j _
  set a₀ : ℤ_[p] := ⟨A, hA1⟩ with ha₀
  have hBa : B = fun z => a₀ * z ^ N := funext fun z =>
    Subtype.ext (show ((B z : ℤ_[p]) : ℚ_[p]) = ((a₀ * z ^ N : ℤ_[p]) : ℚ_[p]) by
      rw [hB z, PadicInt.coe_mul, PadicInt.coe_pow])
  -- the refined coefficient bound
  have hvN : (N : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnormN : ‖(N : ℚ_[p])‖ = (p : ℝ) ^ (-(N.factorization p : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hvN, Padic.valuation_natCast,
      Nat.factorization_def _ hp.out]
  have hAbound : ‖A‖ ≤ (p : ℝ) ^ (-(N : ℤ) + 1 + (N.factorization p : ℤ)) := by
    have h2 := hAN hN1
    rw [hnormN] at h2
    have ht : (0 : ℝ) < (p : ℝ) ^ (-(N.factorization p : ℤ)) :=
      zpow_pos (by positivity) _
    calc ‖A‖ ≤ (p : ℝ) ^ (-(N : ℤ) + 1) / (p : ℝ) ^ (-(N.factorization p : ℤ)) :=
          (le_div_iff₀ ht).mpr h2
      _ = (p : ℝ) ^ (-(N : ℤ) + 1 + (N.factorization p : ℤ)) := by
          rw [← zpow_sub₀ (by positivity : (p : ℝ) ≠ 0)]
          congr 1
          ring
  rcases eq_or_ne N 1 with rfl | hN2
  · -- `N = 1`: polynomial of degree `j`, vanishing differences
    rw [tiltedDeg_iff_of_forall_norm_le]
    intro r hr z
    set Qp : Polynomial ℚ_[p] :=
      (binomialPoly ℚ_[p] j).comp (Polynomial.C A * Polynomial.X) with hQp
    have hdeg : Qp.natDegree < r := by
      have h1 : Qp.natDegree ≤ (binomialPoly ℚ_[p] j).natDegree
          * (Polynomial.C A * Polynomial.X).natDegree := Polynomial.natDegree_comp_le
      have h2 : (binomialPoly ℚ_[p] j).natDegree ≤ j := by
        rw [binomialPoly]
        refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        rw [descPochhammer_natDegree]
      have h3 : (Polynomial.C A * Polynomial.X).natDegree ≤ 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans (le_of_eq Polynomial.natDegree_X)
      have := Nat.mul_le_mul h2 h3
      omega
    have hfeq : (fun w : ℤ_[p] => ((Ring.choose (B w) j : ℤ_[p]) : ℚ_[p]))
        = fun w : ℤ_[p] => (fun x : ℚ_[p] => Qp.eval x) (w : ℚ_[p]) := by
      funext w
      show ((Ring.choose (B w) j : ℤ_[p]) : ℚ_[p]) = Qp.eval (w : ℚ_[p])
      rw [coe_ringChoose, hB w, pow_one, hQp, Polynomial.eval_comp,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, binomialPoly,
        Polynomial.eval_mul, Polynomial.eval_C,
        descPochhammer_eval_eq_factorial_smul_choose, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr j.factorial_ne_zero), one_mul]
    rw [PadicInt.norm_def, coe_fwdDiff_iter, hfeq,
      fwdDiff_iter_comp_coe (fun x : ℚ_[p] => Qp.eval x) r z,
      show Δ_[1]^[r] (fun x : ℚ_[p] => Qp.eval x) = 0 from
        fwdDiff_iter_eval_eq_zero Qp hdeg]
    simpa using zpow_nonneg (Nat.cast_nonneg (α := ℝ) p) _
  -- now `N ≥ 2`
  have hN2' : 2 ≤ N := by omega
  have ha₀A : ‖a₀‖ ≤ (p : ℝ) ^ (-(N : ℤ) + 1 + (N.factorization p : ℤ)) := by
    rw [PadicInt.norm_def]
    exact hAbound
  rcases em ((p : ℕ) ∣ N) with hdvd | hndvd
  · rcases eq_or_ne N p with hNp | hNp
    · -- `N = p`: the direct induction, via `tiltedDeg_choose_monomial_p`
      have hfp : N.factorization p = 1 := by
        rw [hNp]
        exact Nat.Prime.factorization_self hp.out
      have hAp : ‖A‖ ≤ (p : ℝ) ^ (-((p : ℤ) - 2)) := by
        refine hAbound.trans (le_of_eq ?_)
        rw [hfp, hNp]
        congr 1
        push_cast
        ring
      have hpQ : ((p : ℚ_[p])) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
      have huval : ‖A * ((p : ℚ_[p]) ^ (p - 2))⁻¹‖ ≤ 1 := by
        rw [norm_mul, norm_inv, norm_pow, Padic.norm_p]
        have hppow : ((p : ℝ)⁻¹) ^ (p - 2) = (p : ℝ) ^ (-((p : ℤ) - 2)) := by
          rw [inv_pow, ← zpow_natCast, ← zpow_neg]
          congr 1
          have := hp.out.two_le
          push_cast [Nat.cast_sub (show 2 ≤ p from this)]
          ring
        rw [hppow, ← zpow_neg, neg_neg]
        calc ‖A‖ * (p : ℝ) ^ ((p : ℤ) - 2)
            ≤ (p : ℝ) ^ (-((p : ℤ) - 2)) * (p : ℝ) ^ ((p : ℤ) - 2) :=
              mul_le_mul_of_nonneg_right hAp (zpow_nonneg (Nat.cast_nonneg p) _)
          _ = 1 := by
              rw [← zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
              simp
      set u₀ : ℤ_[p] := ⟨A * ((p : ℚ_[p]) ^ (p - 2))⁻¹, huval⟩ with hu₀
      have hBu : B = fun z => u₀ * (p : ℤ_[p]) ^ (p - 2) * z ^ p := by
        funext z
        refine Subtype.ext ?_
        show ((B z : ℤ_[p]) : ℚ_[p])
            = ((u₀ * (p : ℤ_[p]) ^ (p - 2) * z ^ p : ℤ_[p]) : ℚ_[p])
        rw [hB z, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_pow,
          PadicInt.coe_pow, PadicInt.coe_natCast]
        rw [show ((u₀ : ℤ_[p]) : ℚ_[p]) = A * ((p : ℚ_[p]) ^ (p - 2))⁻¹ from rfl]
        rw [inv_mul_cancel_right₀ (pow_ne_zero _ hpQ), hNp]
      rw [hBu]
      exact tiltedDeg_choose_monomial_p hp2 u₀ j
    · -- `p ∣ N`, `N ≠ p` forces `2p ≤ N`: case (b)
      have h2p : 2 * p ≤ N := by
        obtain ⟨t, rfl⟩ := hdvd
        have ht2 : 2 ≤ t := by
          rcases t with _ | _ | t
          · omega
          · omega
          · omega
        calc 2 * p = p * 2 := by ring
          _ ≤ p * t := Nat.mul_le_mul_left p ht2
      rw [hBa]
      exact tiltedDeg_choose_logMonomial_engine hN2' a₀ ha₀A
        (fun j' k h1 h2 => nat_ineq_3_13_2' hp2 h2p h1 h2) j
  · -- case (a): `p ∤ N`
    rw [hBa]
    exact tiltedDeg_choose_logMonomial_engine hN2' a₀ ha₀A
      (fun j' k h1 h2 => nat_ineq_3_13_2 hndvd h1 h2) j

/-- [LWX, Lemma 3.13] (`p` odd; cases (a)–(c)): if `F : ℤ_p → ℤ_p` is given by a
series with coefficients of shape `p^{k−1}·a_k/k` (`IsLogShape`), then
`z ↦ binom(F z, m)` has tilted degree `≤ m`. -/
theorem tiltedDeg_choose_of_logShape (hp2 : p ≠ 2) {F : ℤ_[p] → ℤ_[p]} {A : ℕ → ℚ_[p]}
    (hA : IsLogShape A)
    (hF : ∀ z : ℤ_[p], HasSum (fun k => A k * (z : ℚ_[p]) ^ k) (F z : ℚ_[p]))
    (m : ℕ) : TiltedDeg m fun z => Ring.choose (F z) m := by
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  -- log-shape coefficients are integral
  have hAle : ∀ k, ‖A k‖ ≤ 1 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact hA.1
    · have hvk : (k : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hnormk : ‖(k : ℚ_[p])‖ = (p : ℝ) ^ (-(k.factorization p : ℤ)) := by
        rw [Padic.norm_eq_zpow_neg_valuation hvk, Padic.valuation_natCast,
          Nat.factorization_def _ hp.out]
      have h2 := hA.2 k hk
      rw [hnormk] at h2
      have ht : (0 : ℝ) < (p : ℝ) ^ (-(k.factorization p : ℤ)) :=
        zpow_pos (by positivity) _
      have h3 : ‖A k‖ ≤ (p : ℝ) ^ (-(k : ℤ) + 1 + (k.factorization p : ℤ)) := by
        calc ‖A k‖
            ≤ (p : ℝ) ^ (-(k : ℤ) + 1) / (p : ℝ) ^ (-(k.factorization p : ℤ)) :=
              (le_div_iff₀ ht).mpr h2
          _ = _ := by
              rw [← zpow_sub₀ (by positivity : (p : ℝ) ≠ 0)]
              congr 1
              ring
      refine h3.trans ?_
      rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℤ) by simp]
      refine zpow_le_zpow_right₀ hp1R.le ?_
      have := factorization_le_pred (p := p) (show 1 ≤ k by omega)
      omega
  -- integral truncations
  have hSle : ∀ (N : ℕ) (z : ℤ_[p]),
      ‖∑ k ∈ Finset.range N, A k * (z : ℚ_[p]) ^ k‖ ≤ 1 := by
    intro N z
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul, norm_pow]
    calc ‖A k‖ * ‖(z : ℚ_[p])‖ ^ k ≤ 1 * 1 ^ k := by
          refine mul_le_mul (hAle k) (pow_le_pow_left₀ (norm_nonneg _) ?_ k)
            (by positivity) zero_le_one
          rw [PadicInt.padic_norm_e_of_padicInt]
          exact PadicInt.norm_le_one z
      _ = 1 := by simp
  set S : ℕ → ℤ_[p] → ℤ_[p] :=
    fun N z => ⟨∑ k ∈ Finset.range N, A k * (z : ℚ_[p]) ^ k, hSle N z⟩ with hS
  -- each truncation satisfies the claim, by induction with Chu–Vandermonde
  have hSind : ∀ N j : ℕ, TiltedDeg j fun z => Ring.choose (S N z) j := by
    intro N
    induction N with
    | zero =>
        intro j
        have hzero : ∀ z, S 0 z = S 0 0 := fun z => Subtype.ext (by simp [hS])
        rw [show (fun z => Ring.choose (S 0 z) j) = fun _ => Ring.choose (S 0 0) j from
          funext fun z => by rw [hzero z]]
        exact tiltedDeg_const j _
    | succ N IH =>
        intro j
        have hTle : ∀ z : ℤ_[p], ‖A N * (z : ℚ_[p]) ^ N‖ ≤ 1 := by
          intro z
          rw [norm_mul, norm_pow]
          calc ‖A N‖ * ‖(z : ℚ_[p])‖ ^ N ≤ 1 * 1 ^ N := by
                refine mul_le_mul (hAle N) (pow_le_pow_left₀ (norm_nonneg _) ?_ N)
                  (by positivity) zero_le_one
                rw [PadicInt.padic_norm_e_of_padicInt]
                exact PadicInt.norm_le_one z
            _ = 1 := by simp
        set T : ℤ_[p] → ℤ_[p] := fun z => ⟨A N * (z : ℚ_[p]) ^ N, hTle z⟩ with hT
        have hsplit : ∀ z, S (N + 1) z = S N z + T z := by
          intro z
          refine Subtype.ext ?_
          show ((S (N + 1) z : ℤ_[p]) : ℚ_[p]) = ((S N z + T z : ℤ_[p]) : ℚ_[p])
          rw [PadicInt.coe_add]
          show ∑ k ∈ Finset.range (N + 1), A k * (z : ℚ_[p]) ^ k
              = (∑ k ∈ Finset.range N, A k * (z : ℚ_[p]) ^ k) + A N * (z : ℚ_[p]) ^ N
          exact Finset.sum_range_succ _ N
        have hTtilt : ∀ i, TiltedDeg i fun z => Ring.choose (T z) i := fun i =>
          tiltedDeg_choose_logMonomial hp2 (hAle N) (fun hN => hA.2 N hN) T
            (fun z => rfl) i
        have hCV : (fun z => Ring.choose (S (N + 1) z) j)
            = fun z => ∑ i ∈ Finset.range (j + 1),
                Ring.choose (S N z) i * Ring.choose (T z) (j - i) := by
          funext z
          rw [hsplit z, Ring.add_choose_eq j (Commute.all _ _),
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i l => Ring.choose (S N z) i * Ring.choose (T z) l) j]
        rw [hCV]
        refine TiltedDeg.sum fun i hi => ?_
        rw [Finset.mem_range] at hi
        have hmul := (IH i).mul (hTtilt (j - i))
        rw [show i + (j - i) = j by omega] at hmul
        exact hmul
  -- pass to the limit
  refine TiltedDeg.of_tendsto (F := fun N z => Ring.choose (S N z) m)
    (fun N => hSind N m) fun z => ?_
  have htend : Tendsto (fun N => S N z) atTop (𝓝 (F z)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h1 := (hF z).tendsto_sum_nat
    rw [tendsto_iff_dist_tendsto_zero] at h1
    convert h1 using 2 with N
    rw [dist_eq_norm, dist_eq_norm, PadicInt.norm_def, PadicInt.coe_sub]
  exact (PadicInt.continuous_choose m).continuousAt.tendsto.comp htend

end LWX
