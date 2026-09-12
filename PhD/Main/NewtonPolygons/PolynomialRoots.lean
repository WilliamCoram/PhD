/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import PhD.Main.NewtonPolygons.FirstBreak
import PhD.Main.ForMathlib.NumberTheory.NewtonPolygon.Construction
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassPrep
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.Units
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.Basic

/-!
# Roots of polynomials along the Newton polygon (blueprint §5.7–§5.11)

Skeleton of the root-counting layer of the `Test/test.lean` refactor (source lines 627–1920),
restated on the new APIs: the `coeffVal`/`negLogNorm` valuation bridge, `HasFirstBreak` on the
constructed polygon, and Martin Weierstrass preparation
(`PowerSeries.Restricted.weierstrassPreparation_polynomial_of_isMulDistinguished`) — every
`MemDivisibleValueGroup`/radius-density hypothesis of the old route is gone.

* **§5.7** factorisation at the first break (`exists_factorisation_of_firstBreak`): with the
  first break at `(i, m·i)` and `a₀ = 1`, `f = g·h` with `g` pure of slope `m` of degree `i`
  and `h` zero-free on the closed ball of radius `exp m`.
* **§5.8** the Gauss norm is `1` below the first slope (`gaussNorm_eq_one_of_lt_firstBreak`).
* **§5.9** no zeros below the first slope (`aeval_ne_zero_of_lt_firstBreak`).
* **§5.10** exactly `i` roots of absolute value `exp m` (`card_roots_firstBreak`).
* **§5.11** root counting along the whole polygon (`card_roots_slope`), assembled from the
  closed-ball count (`card_roots_le_slope`) and the open-ball count (`card_roots_lt_slope`);
  the convexity inputs are `vertex_line_le` / `vertex_line_lt`, phrased — like all public
  statements of this section — in the slope/length/vertex data of the constructed polygon
  `newtonPolygon₀OfPowerSeries negLogNorm f`.

Roots are measured in the algebraic closure `AlgebraicClosure K`, with a chosen valuation
`w : Valuation (AlgebraicClosure K) ℝ≥0` extending the norm (`hw`), exactly as in
`Test/test.lean`; generic zero-freeness statements take an arbitrary valued extension `L/K`.
-/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-! ### The unit factor of a Weierstrass preparation -/

/-- Micro-gap **G1**: a polynomial that is a *unit of the `c`-restricted power-series ring* has
strictly dominant constant coefficient — `‖eₖ‖ cᵏ < ‖e₀‖` for every `k ≥ 1`.
Polynomial-flavoured corollary of
`PowerSeries.Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit`; replaces
`dominant_const_of_isUnit_toRestricted` of `Test/test.lean` (consumed there at line 1038). -/
lemma norm_coeff_mul_pow_lt_of_isUnit_toRestricted {c : ℝ} [Fact (0 < c)] {e : Polynomial K}
    (he : IsUnit (Polynomial.toRestricted c e)) {k : ℕ} (hk : 1 ≤ k) :
    ‖e.coeff k‖ * c ^ k < ‖e.coeff 0‖ := by
  have h := PowerSeries.Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit c he
    (n := k) (by omega)
  rwa [PowerSeries.Restricted.constantCoeff_eq_coeff_zero, Polynomial.val_toRestricted,
    Polynomial.coeff_coe, Polynomial.coeff_coe] at h

/-- The restricted norm of a polynomial is read off from any coefficient attaining the bound:
if every Gauss term is at most `B` and the `n`-th one equals `B`, then `‖p‖ = B`. -/
private lemma norm_toRestricted_eq {c : ℝ} [Fact (0 < c)] (p : Polynomial K) {B : ℝ} {n : ℕ}
    (hle : ∀ k, ‖p.coeff k‖ * c ^ k ≤ B) (hn : ‖p.coeff n‖ * c ^ n = B) :
    ‖Polynomial.toRestricted c p‖ = B := by
  have hcoe : ∀ v : ℕ, PowerSeries.coeff v (Polynomial.toRestricted c p).1 = p.coeff v :=
    Polynomial.coeff_coe p
  refine le_antisymm ((PowerSeries.Restricted.norm_le_iff c _).mpr fun k => ?_) ?_
  · rw [hcoe]; exact hle k
  · have h := PowerSeries.Restricted.norm_coeff_mul_pow_le c (Polynomial.toRestricted c p) n
    rwa [hcoe, hn] at h

/-! ## §5.7 Factorisation at the first break -/

omit [IsUltrametricDist K] in
/-- **The dominant-term estimate.**  If at the point `x` the Gauss term of index `s` strictly
dominates every other one, then `p (x) ≠ 0`: all other terms of `p (x) - pₛ xˢ` are strictly
smaller than `‖pₛ‖ w(x)ˢ`, which is therefore the valuation of `p (x)` itself.  Shared core of
`aeval_ne_zero_of_dominant_const`, `aeval_ne_zero_of_dominant_lt` and
`aeval_ne_zero_of_dominant_top`, which only differ in how they verify the domination. -/
private lemma aeval_ne_zero_of_dominant {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (p : Polynomial K) {x : L} {s : ℕ}
    (hdom : ∀ k, k ≠ s → ‖p.coeff k‖ * (w x : ℝ) ^ k < ‖p.coeff s‖ * (w x : ℝ) ^ s) :
    Polynomial.aeval x p ≠ 0 := by
  have hpos : (0 : ℝ) < ‖p.coeff s‖ * (w x : ℝ) ^ s :=
    lt_of_le_of_lt (by positivity) (hdom (s + 1) (Nat.succ_ne_self s))
  have hne : (‖p.coeff s‖₊ * w x ^ s : NNReal) ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    push_cast
    exact hpos.ne'
  have hsub : w (Polynomial.aeval x p - algebraMap K L (p.coeff s) * x ^ s)
      < ‖p.coeff s‖₊ * w x ^ s := by
    rw [show Polynomial.aeval x p - algebraMap K L (p.coeff s) * x ^ s
        = Polynomial.aeval x (p - Polynomial.monomial s (p.coeff s)) by
      rw [_root_.map_sub, Polynomial.aeval_monomial], Polynomial.aeval_eq_sum_range]
    refine w.map_sum_lt hne fun k _ => ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_monomial]
    rcases eq_or_ne s k with rfl | hsk
    · rw [if_pos rfl, sub_self, zero_smul, w.map_zero]
      exact pos_iff_ne_zero.mpr hne
    · rw [if_neg hsk, sub_zero, Algebra.smul_def, w.map_mul, w.map_pow, hw, ← NNReal.coe_lt_coe]
      push_cast
      exact hdom k (Ne.symm hsk)
  intro h0
  rw [h0, zero_sub, w.map_neg, w.map_mul, w.map_pow, hw] at hsub
  exact lt_irrefl _ hsub

omit [IsUltrametricDist K] in
/-- **A polynomial whose constant term strictly dominates has no zeros in the closed ball of
radius `c`.**  This is the shape of the unit factor of a Weierstrass preparation
(`0`-distinguished); elementary ultrametric estimate, as in §5.9.
(`Test/test.lean` line 807.) -/
theorem aeval_ne_zero_of_dominant_const {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (e : Polynomial K) {c : ℝ}
    (hdom : ∀ k, 1 ≤ k → ‖e.coeff k‖ * c ^ k < ‖e.coeff 0‖)
    {x : L} (hx : (w x : ℝ) ≤ c) :
    Polynomial.aeval x e ≠ 0 := by
  refine aeval_ne_zero_of_dominant w hw e (s := 0) fun k hk => ?_
  rw [pow_zero, mul_one]
  calc ‖e.coeff k‖ * (w x : ℝ) ^ k
      ≤ ‖e.coeff k‖ * c ^ k := by gcongr
    _ < ‖e.coeff 0‖ := hdom k (Nat.one_le_iff_ne_zero.mpr hk)

omit [IsUltrametricDist K] in
/-- **A polynomial whose constant term (weakly) dominates every term has no zeros in the *open*
ball of radius `c`.**  This is the shape of the pure factor `g` of §5.7: its polygon starts at
`(0, ν(g₀))` with slope `m`, so `‖gₖ‖ cᵏ ≤ ‖g₀‖` at `c = exp m`, and strictness is recovered
from `w x < c`.  Used for the root count §5.10: no root of `g` lies strictly inside the ball.
(`Test/test.lean` line 845.) -/
theorem aeval_ne_zero_of_dominant_lt {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (g : Polynomial K) {c : ℝ} (hg0 : g.coeff 0 ≠ 0)
    (hdom : ∀ k, 1 ≤ k → ‖g.coeff k‖ * c ^ k ≤ ‖g.coeff 0‖)
    {x : L} (hx : (w x : ℝ) < c) :
    Polynomial.aeval x g ≠ 0 := by
  refine aeval_ne_zero_of_dominant w hw g (s := 0) fun k hk => ?_
  rw [pow_zero, mul_one]
  by_cases hgk : g.coeff k = 0
  · rw [hgk, norm_zero, zero_mul]
    exact norm_pos_iff.mpr hg0
  · calc ‖g.coeff k‖ * (w x : ℝ) ^ k
        < ‖g.coeff k‖ * c ^ k :=
          mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hx (w x).coe_nonneg hk) (norm_pos_iff.mpr hgk)
      _ ≤ ‖g.coeff 0‖ := hdom k (Nat.one_le_iff_ne_zero.mpr hk)

/-- If a multiset of `ℝ≥0` has all elements `≥ c` and product exactly `c ^ card`, every element
equals `c` (the pigeonhole behind "all roots of a pure polynomial have the same absolute
value").  (`Test/test.lean` line 884.) -/
private lemma eq_of_prod_eq_pow_card {S : Multiset NNReal} {c : NNReal} (hc : 0 < c)
    (hall : ∀ y ∈ S, c ≤ y) (hprod : S.prod = c ^ Multiset.card S)
    {y : NNReal} (hy : y ∈ S) : y = c := by
  obtain ⟨T, rfl⟩ : ∃ T, S = y ::ₘ T := ⟨S.erase y, (Multiset.cons_erase hy).symm⟩
  by_contra hne
  have hlt : c < y := lt_of_le_of_ne (hall y (Multiset.mem_cons_self y T)) (Ne.symm hne)
  have hle : c ^ Multiset.card T ≤ T.prod :=
    Multiset.pow_card_le_prod fun z hz => hall z (Multiset.mem_cons_of_mem hz)
  rw [Multiset.prod_cons, Multiset.card_cons, pow_succ'] at hprod
  have h1 : c * c ^ Multiset.card T < y * T.prod :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt (pow_pos hc _)) (mul_le_mul_right hle y)
  exact absurd hprod h1.ne'

/-- **Weierstrass preparation at radius `c`, unbundled into coefficient norms.**  An
`s`-distinguished polynomial factors as `f = e·ω` with `ω` monic of degree `s` whose Gauss
terms are all at most `cˢ`, and `e` with strictly dominant constant coefficient.

This threads `PowerSeries.Restricted.weierstrassPreparation_polynomial_of_isMulDistinguished`
(Martin §1.3) and `norm_coeff_mul_pow_lt_of_isUnit_toRestricted`.  (`Test/test.lean` line 1007,
with the `MemDivisibleValueGroup` hypothesis deleted: Martin preparation applies at every
positive radius, so the divisible-closure detour is gone.) -/
private theorem exists_factor_aux [CompleteSpace K] (f : Polynomial K) {c : ℝ} (hc : 0 < c)
    {s : ℕ} (hcs : f.coeff s ≠ 0)
    (hle : ∀ k, ‖f.coeff k‖ * c ^ k ≤ ‖f.coeff s‖ * c ^ s)
    (hlt : ∀ t, s < t → ‖f.coeff t‖ * c ^ t < ‖f.coeff s‖ * c ^ s) :
    ∃ ω e : Polynomial K,
      f = e * ω ∧ ω.natDegree = s ∧ ω.Monic ∧
      (∀ k, ‖ω.coeff k‖ * c ^ k ≤ c ^ s) ∧
      ∀ k, 1 ≤ k → ‖e.coeff k‖ * c ^ k < ‖e.coeff 0‖ := by
  haveI : Fact (0 < c) := ⟨hc⟩
  have hcoe : ∀ (p : Polynomial K) (v : ℕ),
      PowerSeries.coeff v (Polynomial.toRestricted c p).1 = p.coeff v :=
    fun p v => Polynomial.coeff_coe p v
  have hdist : PowerSeries.IsMulDistinguished c (Polynomial.toRestricted c f).1 s := by
    refine ⟨?_, ?_, fun t ht => ?_⟩
    · rw [hcoe]
      exact (isUnit_iff_ne_zero.mpr hcs).isNormMulUnit
    · rw [hcoe, ← PowerSeries.Restricted.norm_def c]
      exact norm_toRestricted_eq f hle rfl
    · rw [hcoe, hcoe]
      exact hlt t ht
  obtain ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hgeq⟩, -⟩, -⟩ :=
    PowerSeries.Restricted.weierstrassPreparation_polynomial_of_isMulDistinguished hdist
  refine ⟨ω, e, ?_, Polynomial.natDegree_eq_of_degree_eq_some ωd, ωm, fun k => ?_,
    fun k hk => norm_coeff_mul_pow_lt_of_isUnit_toRestricted he hk⟩
  · rw [← map_mul] at hgeq
    exact Polynomial.toRestricted_injective c hgeq
  · have h := PowerSeries.Restricted.norm_coeff_mul_pow_le c (Polynomial.toRestricted c ω) k
    rwa [hcoe, ωn] at h

/-- **Blueprint Theorem 5.7, valuation-free core.**  With the first break at `(i, mi)` and
`a₀ = 1`, `f = g · h` where `g` has degree `i` and is pure of slope `m`, and the constant
coefficient of `h` strictly dominates at `c = exp m` (whence `h` has no zeros in any closed
ball of radius `exp m`, in any valued extension — see `exists_factorisation_of_firstBreak`).
(`Test/test.lean` line 1051.) -/
theorem exists_factorisation_of_firstBreak' [CompleteSpace K] (f : Polynomial K)
    (hf0 : f.coeff 0 = 1)
    {i : ℕ} {m : ℝ} (hbreak : HasFirstBreak (f : PowerSeries K) i m) :
    ∃ g h : Polynomial K,
      f = g * h ∧ g.natDegree = i ∧ IsPureSeries (g : PowerSeries K) m ∧
      (∀ k, ‖g.coeff k‖ * Real.exp m ^ k ≤ ‖g.coeff 0‖) ∧
      ‖g.coeff g.natDegree‖ * Real.exp m ^ g.natDegree = ‖g.coeff 0‖ ∧
      ∀ k, 1 ≤ k → ‖h.coeff k‖ * Real.exp m ^ k < ‖h.coeff 0‖ := by
  haveI : Fact (0 < Real.exp m) := ⟨Real.exp_pos m⟩
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := (Polynomial.coeff_coe f 0).trans hf0
  have hipos : 0 < i := hbreak.1
  have hci : f.coeff i ≠ 0 := Polynomial.coeff_coe f i ▸ hbreak.coeff_break_ne_zero hf0'
  have hbreak_eq : ‖f.coeff i‖ * Real.exp m ^ i = 1 :=
    firstBreak_gaussTerm_break_eq f hf0 hbreak
  have hle : ∀ k, ‖f.coeff k‖ * Real.exp m ^ k ≤ ‖f.coeff i‖ * Real.exp m ^ i := fun k => by
    rw [hbreak_eq]; exact firstBreak_gaussTerm_le f hf0 hbreak k
  have hlt : ∀ t, i < t → ‖f.coeff t‖ * Real.exp m ^ t < ‖f.coeff i‖ * Real.exp m ^ i :=
    fun t ht => by rw [hbreak_eq]; exact firstBreak_gaussTerm_lt f hf0 hbreak ht
  obtain ⟨ω, e, hfeq, hωdeg, hωmonic, hωdom, hedom⟩ :=
    exists_factor_aux f (Real.exp_pos m) hci hle hlt
  -- Gauss multiplicativity pins the constant coefficient of `ω`: `‖ω₀‖ = exp m ^ i`, so the
  -- factor is normalised at both ends
  have hωs1 : ω.coeff i = 1 := by rw [← hωdeg]; exact hωmonic.coeff_natDegree
  have hnF : ‖Polynomial.toRestricted (Real.exp m) f‖ = 1 :=
    norm_toRestricted_eq f (firstBreak_gaussTerm_le f hf0 hbreak) (n := 0)
      (by rw [hf0, norm_one, pow_zero, mul_one])
  have hnE : ‖Polynomial.toRestricted (Real.exp m) e‖ = ‖e.coeff 0‖ :=
    norm_toRestricted_eq e (n := 0)
      (fun k => (Nat.eq_zero_or_pos k).elim (fun hk => by rw [hk, pow_zero, mul_one])
        fun hk => (hedom k hk).le) (by rw [pow_zero, mul_one])
  have hnW : ‖Polynomial.toRestricted (Real.exp m) ω‖ = Real.exp m ^ i :=
    norm_toRestricted_eq ω hωdom (n := i) (by rw [hωs1, norm_one, one_mul])
  have h1 : (1 : ℝ) = ‖e.coeff 0‖ * Real.exp m ^ i := by
    rw [← hnF, hfeq, map_mul, norm_mul, hnE, hnW]
  have hω0norm : ‖ω.coeff 0‖ = Real.exp m ^ i := by
    have h2 : ‖e.coeff 0‖ * ‖ω.coeff 0‖ = 1 := by
      rw [← norm_mul, ← Polynomial.mul_coeff_zero, ← hfeq, hf0, norm_one]
    exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h2) (h2.trans h1)
  have hω0 : ω.coeff 0 ≠ 0 :=
    norm_pos_iff.mp (by rw [hω0norm]; exact pow_pos (Real.exp_pos m) i)
  have hωle : ∀ k, ‖ω.coeff k‖ * Real.exp m ^ k ≤ ‖ω.coeff 0‖ := fun k => by
    rw [hω0norm]; exact hωdom k
  have hωtop : ‖ω.coeff i‖ * Real.exp m ^ i = ‖ω.coeff 0‖ := by
    rw [hωs1, norm_one, one_mul, hω0norm]
  exact ⟨ω, e, by rw [hfeq, mul_comm], hωdeg,
    isPureSeries_of_bounds ω hω0 (by rw [hωdeg]; exact hipos) m hωle
      (by rw [hωdeg]; exact hωtop),
    hωle, by rw [hωdeg]; exact hωtop, hedom⟩

/-- **Blueprint Theorem 5.7.**  With the first break at `(i, mi)` and `a₀ = 1` (the blueprint's
standing normalisation, added to the original statement as in §5.8–§5.10), `f = g · h` with `g`
pure of slope `m` of degree `i`, and `h` without zeros in the closed ball of radius
`c = exp m` of the algebraic closure.  (`Test/test.lean` line 1153.) -/
theorem exists_factorisation_of_firstBreak [CompleteSpace K] (f : Polynomial K)
    (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {i : ℕ} {m : ℝ} (hbreak : HasFirstBreak (f : PowerSeries K) i m)
    (c : ℝ) (hc : c = Real.exp m) :
    ∃ g h : Polynomial K,
      f = g * h ∧
      g.natDegree = i ∧
      IsPureSeries (g : PowerSeries K) m ∧
      (∀ x : AlgebraicClosure K, (w x : ℝ) ≤ c → Polynomial.aeval x h ≠ 0) := by
  subst hc
  obtain ⟨g, h, hfeq, hdeg, hpure, -, -, hdom⟩ :=
    exists_factorisation_of_firstBreak' f hf0 hbreak
  exact ⟨g, h, hfeq, hdeg, hpure, fun x hx => aeval_ne_zero_of_dominant_const w hw h hdom hx⟩

/-! ## §5.8 Gauss-norm bound below the first slope -/

/-- **Per-coefficient bound below the first slope.**  With the first break at `(i, mi)` and
`a₀ = 1`, for `0 < c < exp m` every coefficient with `k ≥ 1` satisfies
`‖aₖ‖ c^k ≤ exp (log c - m)` — a *uniform* bound `< 1`.  The analytic core of §5.8, extracted
so that §5.9 can reuse it term by term.  (`Test/test.lean` line 1237.) -/
theorem coeff_mul_pow_le_of_lt_firstBreak (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {i : ℕ} {m : ℝ} (hbreak : HasFirstBreak f i m)
    {c : ℝ} (hc0 : 0 < c) (hc : c < Real.exp m) {k : ℕ} (hk : 1 ≤ k) :
    ‖PowerSeries.coeff k f‖ * c ^ k ≤ Real.exp (Real.log c - m) := by
  have hL2 : Real.log c < m := (Real.log_lt_iff_lt_exp hc0).mpr hc
  by_cases hak : PowerSeries.coeff k f = 0
  · simp only [hak, norm_zero, zero_mul]
    exact (Real.exp_pos _).le
  · have hck : c ^ k = Real.exp ((k : ℝ) * Real.log c) := by
      rw [Real.exp_nat_mul, Real.exp_log hc0]
    have hprod : ‖PowerSeries.coeff k f‖ * c ^ k
        = Real.exp (Real.log ‖PowerSeries.coeff k f‖ + (k : ℝ) * Real.log c) := by
      rw [Real.exp_add, ← hck, Real.exp_log (norm_pos_iff.mpr hak)]
    rw [hprod, Real.exp_le_exp]
    have hL1 := hbreak.slope_mul_le hf0 hk hak
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [hL1, hL2, hk1]

/-- **Blueprint Proposition 5.8.**  With the first break at `(i, mi)` and `a₀ = 1`, for any
positive `c` strictly below `exp m` the Gauss norm is `1` and `f` differs from `1` by something
of Gauss norm `< 1`.  (`Test/test.lean` line 1258.) -/
theorem gaussNorm_eq_one_of_lt_firstBreak (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {i : ℕ} {m : ℝ} (hbreak : HasFirstBreak f i m)
    (c : ℝ) (hc0 : 0 < c) (hc : c < Real.exp m) :
    PowerSeries.gaussNorm norm c f = 1 ∧ PowerSeries.gaussNorm norm c (f - 1) < 1 := by
  set B : ℝ := Real.exp (Real.log c - m) with hB
  have hL2 : Real.log c < m := (Real.log_lt_iff_lt_exp hc0).mpr hc
  have hBlt : B < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hBpos : 0 < B := Real.exp_pos _
  -- per-coefficient bound for `k ≥ 1`
  have term_le_B : ∀ k, 1 ≤ k → ‖PowerSeries.coeff k f‖ * c ^ k ≤ B := fun k hk =>
    coeff_mul_pow_le_of_lt_firstBreak f hf0 hbreak hc0 hc hk
  have hsup1 : PowerSeries.gaussNorm norm c f = 1 := by
    rw [PowerSeries.gaussNorm_eq]
    have term_le_one : ∀ k, ‖PowerSeries.coeff k f‖ * c ^ k ≤ 1 := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [hf0]
      · exact (term_le_B k hk).trans hBlt.le
    have hbdd : BddAbove (Set.range fun k => ‖PowerSeries.coeff k f‖ * c ^ k) :=
      ⟨1, by rintro _ ⟨k, rfl⟩; exact term_le_one k⟩
    refine le_antisymm (ciSup_le term_le_one) ?_
    calc (1 : ℝ) = ‖PowerSeries.coeff 0 f‖ * c ^ 0 := by simp [hf0]
      _ ≤ _ := le_ciSup hbdd 0
  have hsup2 : PowerSeries.gaussNorm norm c (f - 1) < 1 := by
    rw [PowerSeries.gaussNorm_eq]
    have term_le : ∀ k, ‖PowerSeries.coeff k (f - 1)‖ * c ^ k ≤ B := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have h0 : PowerSeries.coeff 0 (f - 1) = 0 := by
          rw [_root_.map_sub, hf0, PowerSeries.coeff_one]; simp
        simp only [h0, norm_zero, zero_mul]
        exact hBpos.le
      · have hcoe : PowerSeries.coeff k (f - 1) = PowerSeries.coeff k f := by
          rw [_root_.map_sub, PowerSeries.coeff_one]; simp [hk.ne']
        rw [hcoe]
        exact term_le_B k hk
    calc (⨆ k, ‖PowerSeries.coeff k (f - 1)‖ * c ^ k) ≤ B := ciSup_le term_le
      _ < 1 := hBlt
  exact ⟨hsup1, hsup2⟩

/-! ## §5.9 No zeros below the first slope -/

/-- **Blueprint Proposition 5.9.**  With the first break at `(i, mi)` and `a₀ = 1`, `f` has no
zeros in the closed ball of radius `c`, for any positive `c` strictly below `exp m`.  Zeros are
measured in an arbitrary field extension `L/K` carrying a valuation `w` extending the norm.
(`Test/test.lean` line 1315.) -/
theorem aeval_ne_zero_of_lt_firstBreak {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    {i : ℕ} {m : ℝ} (hbreak : HasFirstBreak (f : PowerSeries K) i m)
    {c : ℝ} (hc0 : 0 < c) (hc : c < Real.exp m)
    {x : L} (hx : (w x : ℝ) ≤ c) :
    Polynomial.aeval x f ≠ 0 := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := (Polynomial.coeff_coe f 0).trans hf0
  have hBlt : Real.exp (Real.log c - m) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith [(Real.log_lt_iff_lt_exp hc0).mpr hc])
  -- `w (f(x) - 1) < 1`: every term of `f - 1` has valuation `< 1` on the closed ball
  have hsub : w (Polynomial.aeval x f - 1) < 1 := by
    have h1 : Polynomial.aeval x f - 1 = Polynomial.aeval x (f - 1) := by
      rw [_root_.map_sub, _root_.map_one]
    rw [h1, Polynomial.aeval_eq_sum_range]
    refine w.map_sum_lt one_ne_zero fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h00 : (f - 1).coeff 0 = 0 := by simp [hf0]
      simp [h00]
    · have hco : (f - 1).coeff k = f.coeff k := by
        simp [Polynomial.coeff_one, hk.ne']
      rw [hco, Algebra.smul_def, w.map_mul, w.map_pow, hw, ← NNReal.coe_lt_coe]
      push_cast
      have hterm : ‖f.coeff k‖ * c ^ k ≤ Real.exp (Real.log c - m) := by
        have h := coeff_mul_pow_le_of_lt_firstBreak (f : PowerSeries K) hf0' hbreak hc0 hc hk
        rwa [Polynomial.coeff_coe] at h
      calc ‖f.coeff k‖ * (w x : ℝ) ^ k
          ≤ ‖f.coeff k‖ * c ^ k := by gcongr
        _ ≤ Real.exp (Real.log c - m) := hterm
        _ < 1 := hBlt
  intro h0
  rw [h0, zero_sub, w.map_neg, w.map_one] at hsub
  exact lt_irrefl _ hsub

/-! ## §5.10 Root counting at the first slope -/

/-- **Blueprint Proposition 5.10, first half.**  No roots of absolute value strictly below
`exp m`.  (`Test/test.lean` line 1363.) -/
theorem aeval_ne_zero_of_norm_lt_firstBreak {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    {i : ℕ} {m : ℝ} (hbreak : HasFirstBreak (f : PowerSeries K) i m)
    {x : L} (hx : (w x : ℝ) < Real.exp m) :
    Polynomial.aeval x f ≠ 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, hf0]
  · have hc0 : (0 : ℝ) < (w x : ℝ) := by
      exact_mod_cast pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hx0)
    exact aeval_ne_zero_of_lt_firstBreak w hw f hf0 hbreak hc0 hx le_rfl

open Classical in
/-- **Blueprint Proposition 5.10, second half.**  `f` has exactly `i` roots of absolute value
`exp m`, counted with multiplicity in the algebraic closure.

Following the blueprint: `f = g · h` with `g` pure of degree `i` (§5.7); the roots of `h` all
lie strictly outside the closed ball (`aeval_ne_zero_of_dominant_const`); the roots of `g` lie
on the sphere — none inside (`aeval_ne_zero_of_dominant_lt`), and since the product of their
absolute values is `‖g₀/g_i‖ = (exp m)^i` while each is `≥ exp m`, all equal `exp m`
(`eq_of_prod_eq_pow_card`).  (`Test/test.lean` line 1384.) -/
theorem card_roots_firstBreak [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {i : ℕ} {m : ℝ} (hbreak : HasFirstBreak (f : PowerSeries K) i m) :
    (Multiset.filter (fun x => (w x : ℝ) = Real.exp m)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = i := by
  obtain ⟨g, h, hfeq, hdeg, -, hgle, hgtop, hdom⟩ :=
    exists_factorisation_of_firstBreak' f hf0 hbreak
  have hf_ne : f ≠ 0 := fun h0 => one_ne_zero (by rw [← hf0, h0, Polynomial.coeff_zero])
  have hg_ne : g ≠ 0 := fun h0 => hf_ne (by rw [hfeq, h0, zero_mul])
  have hh_ne : h ≠ 0 := fun h0 => hf_ne (by rw [hfeq, h0, mul_zero])
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h0
    have h1 := Polynomial.mul_coeff_zero g h
    rw [← hfeq, hf0, h0, zero_mul] at h1
    exact one_ne_zero h1
  set φ := algebraMap K (AlgebraicClosure K)
  have hφinj : Function.Injective φ := φ.injective
  have hgmap_ne : g.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hg_ne
  have hhmap_ne : h.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hh_ne
  have hroots : (f.map φ).roots = (g.map φ).roots + (h.map φ).roots := by
    rw [hfeq, Polynomial.map_mul, Polynomial.roots_mul (mul_ne_zero hgmap_ne hhmap_ne)]
  -- the roots of `h` lie strictly outside the closed ball of radius `exp m`
  have hh0 : Multiset.filter (fun x => (w x : ℝ) = Real.exp m) (h.map φ).roots = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx hxc
    exact aeval_ne_zero_of_dominant_const w hw h hdom hxc.le
      (Polynomial.mem_aroots'.mp (show x ∈ h.aroots (AlgebraicClosure K) from hx)).2
  -- no root of `g` lies strictly inside the ball …
  have hlow : ∀ x ∈ (g.map φ).roots, Real.exp m ≤ (w x : ℝ) := fun x hx =>
    not_lt.mp fun hlt => aeval_ne_zero_of_dominant_lt w hw g hg0 (fun k _ => hgle k) hlt
      (Polynomial.mem_aroots'.mp (show x ∈ g.aroots (AlgebraicClosure K) from hx)).2
  -- … and the product of the root norms is `(exp m) ^ deg g`, so all lie on the sphere
  have hsplits : (g.map φ).Splits := IsAlgClosed.splits _
  have hcards : Multiset.card (g.map φ).roots = g.natDegree := by
    rw [← Polynomial.natDegree_map φ (p := g)]
    exact hsplits.natDegree_eq_card_roots.symm
  have hlead_ne : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg_ne
  have hwid : ‖g.coeff 0‖₊ = ‖g.leadingCoeff‖₊ * ((g.map φ).roots.map w).prod := by
    calc ‖g.coeff 0‖₊ = w ((g.map φ).coeff 0) := by rw [Polynomial.coeff_map, hw]
      _ = w ((-1) ^ (g.map φ).natDegree) * w (g.map φ).leadingCoeff
            * w (g.map φ).roots.prod := by
          rw [hsplits.coeff_zero_eq_leadingCoeff_mul_prod_roots, w.map_mul, w.map_mul]
      _ = ‖g.leadingCoeff‖₊ * ((g.map φ).roots.map w).prod := by
          rw [w.map_pow, w.map_neg, w.map_one, one_pow, one_mul,
            Polynomial.leadingCoeff_map, hw, map_multiset_prod]
  have hexp0 : (0 : ℝ) ≤ Real.exp m := (Real.exp_pos m).le
  have hgtopn : ‖g.leadingCoeff‖₊ * Real.toNNReal (Real.exp m) ^ g.natDegree = ‖g.coeff 0‖₊ := by
    rw [← NNReal.coe_inj]
    push_cast
    rw [Real.coe_toNNReal _ hexp0]
    exact hgtop
  have hlcn : ‖g.leadingCoeff‖₊ ≠ 0 := by simpa using hlead_ne
  have hprodn : ((g.map φ).roots.map w).prod
      = Real.toNNReal (Real.exp m) ^ Multiset.card ((g.map φ).roots.map w) := by
    have h2 : ‖g.leadingCoeff‖₊ * ((g.map φ).roots.map w).prod
        = ‖g.leadingCoeff‖₊ * Real.toNNReal (Real.exp m) ^ g.natDegree := by rw [← hwid, ← hgtopn]
    rw [mul_left_cancel₀ hlcn h2, Multiset.card_map, hcards]
  have hall_roots : ∀ x ∈ (g.map φ).roots, (w x : ℝ) = Real.exp m := by
    intro x hx
    have hge : ∀ y ∈ (g.map φ).roots.map w, Real.toNNReal (Real.exp m) ≤ y := by
      intro y hy
      obtain ⟨x', hx', rfl⟩ := Multiset.mem_map.mp hy
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hexp0]
      exact hlow x' hx'
    have hxeq := eq_of_prod_eq_pow_card (Real.toNNReal_pos.mpr (Real.exp_pos m)) hge hprodn
      (Multiset.mem_map_of_mem w hx)
    rw [← Real.coe_toNNReal (Real.exp m) hexp0, ← hxeq]
  rw [hroots, Multiset.filter_add, Multiset.card_add, hh0, Multiset.card_zero, add_zero,
    Multiset.filter_eq_self.mpr hall_roots, hcards, hdeg]

/-! ## §5.11 Root counting along the whole polygon

The `k`-th-segment hypotheses of the public statements are phrased in the textbook data of the
constructed polygon `newtonPolygon₀OfPowerSeries negLogNorm f`: "the `k`-th segment has slope
`m`, projected length `l` and right endpoint `j₀`" is `.slopes k = m`, `.lengths k = l`,
`.vertexX (k + 1) = j₀` (each statement carrying only the components it uses).  For a
*polynomial* every segment of the polygon is genuine (the point set is finite), so this covers
all slopes; at `k = 0` with the normalisation `a₀ = 1` it specialises to §5.10.  The private
workhorses keep the raw step-algorithm form
`newtonPolygon (coeffVal f) k = some (.nextVertex j₀ j₁ l m)`, bridged by
`newtonPolygon_eq_nextVertex_of_segment_data`. -/

/-! ### Private infrastructure for the convexity statements

`newtonPolygon_eq_nextVertex_of_segment_data` is the intended bridge from the textbook segment
data to the step algorithm, but the two convexity statements below need less than it offers (no
length input), so they are served here by `step_of_segment_data`, proved directly from the
construction layer. -/

omit [IsUltrametricDist K] in
/-- Points to the right of a vertex lie on/above its outgoing line (`nextStep_slope_le` read
through `coeffVal`; refactor of `step_slope_le`, `Test/test.lean` line 184). -/
private lemma coeffVal_slope_le {f : PowerSeries K} {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m) {k : ℕ} (hk : i₀ < k)
    (hak : PowerSeries.coeff k f ≠ 0) :
    m * ((k : ℝ) - (i₀ : ℝ)) ≤ -Real.log ‖PowerSeries.coeff k f‖ - i₁ := by
  have h1 := nextStep_slope_le (coeffVal f) h hk (coeffVal_of_ne_zero hak)
  rwa [Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply] at h1

omit [IsUltrametricDist K] in
/-- Points beyond a vertex lie strictly above its incoming line (`nextStep_slope_lt` read through
`coeffVal`). -/
private lemma coeffVal_slope_lt {f : PowerSeries K} {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m) {k : ℕ} (hk : j₀ < k)
    (hak : PowerSeries.coeff k f ≠ 0) :
    m * ((k : ℝ) - (i₀ : ℝ)) < -Real.log ‖PowerSeries.coeff k f‖ - i₁ := by
  have h1 := nextStep_slope_lt (coeffVal f) h hk (coeffVal_of_ne_zero hak)
  rwa [Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply] at h1

omit [IsUltrametricDist K] in
/-- The output vertex of a step lies on the line of the step's slope through its input vertex. -/
private lemma coeffVal_vertex_line {f : PowerSeries K} {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m) :
    j₁ = i₁ + m * ((j₀ : ℝ) - (i₀ : ℝ)) := by
  have hijR : (0 : ℝ) < (j₀ : ℝ) - (i₀ : ℝ) := by
    rw [sub_pos]; exact_mod_cast nextVertex_lt _ h
  have hslope := nextVertex_slope_eq_sInf' _ h
  simp only [slopeReal, Algebra.algebraMap_self, RingHom.id_apply] at hslope
  rw [eq_div_iff hijR.ne'] at hslope
  linarith

omit [IsUltrametricDist K] in
/-- The output vertex of a step is a nonzero coefficient, carrying its height. -/
private lemma coeffVal_vertex_value {f : PowerSeries K} {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m) :
    PowerSeries.coeff j₀ f ≠ 0 ∧ j₁ = -Real.log ‖PowerSeries.coeff j₀ f‖ := by
  have h1 := nextVertex_j₁_eq (coeffVal f) h
  have hne : PowerSeries.coeff j₀ f ≠ 0 := fun h0 =>
    WithTop.top_ne_coe ((coeffVal_eq_top_iff.mpr h0).symm.trans h1)
  rw [coeffVal_of_ne_zero hne] at h1
  exact ⟨hne, by exact_mod_cast h1.symm⟩

omit [IsUltrametricDist K] in
/-- With `a₀ = 1` step `0` of the algorithm is the step out of the origin.
(`Test/test.lean` lines 156, 176.) -/
private lemma newtonPolygon_coeffVal_zero {f : PowerSeries K} (hf0 : PowerSeries.coeff 0 f = 1) :
    newtonPolygon (coeffVal f) 0 = some (nextStep (coeffVal f) 0 (0 : ℝ)) := by
  classical
  have hval : coeffVal f 0 = ((0 : ℝ) : WithTop ℝ) := coeffVal_zero_of_coeff_zero_eq_one hf0
  have hfin : finite (coeffVal f) 0 := show coeffVal f 0 ≠ ⊤ from hval.trans_ne WithTop.coe_ne_top
  have hex : ∃ i ≥ 0, finite (coeffVal f) i := ⟨0, le_refl _, hfin⟩
  have hzero : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr ⟨le_refl _, hfin⟩
  have hff : findFirstFinite (coeffVal f) 0 = some (0, (0 : ℝ)) := by
    have hchoose : (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose = (0 : ℝ) :=
      WithTop.coe_inj.mp ((Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose_spec.trans
        (by rw [hzero]; exact hval))
    unfold findFirstFinite
    rw [dif_pos hex, hchoose, hzero]
  simp only [newtonPolygon, hff]

omit [IsUltrametricDist K] in
/-- **The bridge, in its raw form**: a finite slope at index `a` excludes the `none`, `tail` and
`unboundedBelow` outputs (slope `⊤`/`⊥`) and a finite length excludes the two final rays, so the
algorithm outputs a `nextVertex` there, with that slope. -/
private lemma step_of_slope_of_lengths_ne_top {f : PowerSeries K} {a : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (m : WithBotTop ℝ))
    (hlen : (newtonPolygon₀OfPowerSeries negLogNorm f).lengths a ≠ ⊤) :
    ∃ (j₀ l : ℕ) (j₁ : ℝ), newtonPolygon (coeffVal f) a = some (.nextVertex j₀ j₁ l m) := by
  have hslopes : slopes' (newtonPolygon (coeffVal f) a) = (m : WithBotTop ℝ) := hm
  have hlengths : newtonPolygon_lengths (coeffVal f) a ≠ ⊤ := hlen
  cases hstep : newtonPolygon (coeffVal f) a with
  | none =>
      rw [hstep] at hslopes
      exact ((WithBotTop.coe_ne_top m) (show (m : WithBotTop ℝ) = ⊤ from hslopes.symm)).elim
  | some S =>
      rw [hstep] at hslopes
      cases S with
      | tail =>
          exact ((WithBotTop.coe_ne_top m) (show (m : WithBotTop ℝ) = ⊤ from hslopes.symm)).elim
      | unboundedBelow =>
          exact ((WithBotTop.coe_ne_bot m) (show (m : WithBotTop ℝ) = ⊥ from hslopes.symm)).elim
      | limitingRay m' => exact (hlengths (by simp only [newtonPolygon_lengths, hstep])).elim
      | infiniteRay m' => exact (hlengths (by simp only [newtonPolygon_lengths, hstep])).elim
      | nextVertex j₀ j₁ l m' =>
          obtain rfl : m' = m :=
            WithBotTop.coe_injective (show (m' : WithBotTop ℝ) = (m : WithBotTop ℝ) from hslopes)
          exact ⟨j₀, l, j₁, rfl⟩

omit [IsUltrametricDist K] in
/-- **The bridge**: a finite slope together with a finite right endpoint at index `a` forces the
algorithm to output a `nextVertex` there, with that endpoint and that slope.  (The two final rays
carry infinite length, so no vertex follows them.) -/
private lemma step_of_segment_data {f : PowerSeries K} {a j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (a + 1) = ((j₀ : ℤ) : WithTop ℤ)) :
    ∃ (j₁ : ℝ) (l : ℕ), newtonPolygon (coeffVal f) a = some (.nextVertex j₀ j₁ l m) := by
  obtain ⟨j₀', l, j₁, hstep⟩ := step_of_slope_of_lengths_ne_top hm fun hlen => by
    rw [NewtonPolygon₀.vertexX_succ, hlen, WithTop.map_top, add_top] at hj
    exact WithTop.coe_ne_top hj.symm
  obtain rfl : j₀' = j₀ := by
    exact_mod_cast (newtonPolygon₀OfSeq_vertexX (coeffVal f) hstep).symm.trans hj
  exact ⟨j₁, l, hstep⟩

omit [IsUltrametricDist K] in
/-- Two-position comparison of Gauss-norm terms at radius `c`:
`‖a‖ cᵗ ≤ ‖b‖ cˢ` iff `(t, ν(a))` lies on/above the line of slope `log c` through `(s, ν(b))`.
(`Test/test.lean` line 1514.) -/
private lemma term_le_term_iff' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {c : ℝ} (hc : 0 < c)
    (t s : ℕ) :
    ‖a‖ * c ^ t ≤ ‖b‖ * c ^ s ↔
      Real.log c * ((t : ℝ) - s) ≤ -Real.log ‖a‖ - -Real.log ‖b‖ := by
  rw [show c = Real.exp (Real.log c) from (Real.exp_log hc).symm,
    norm_mul_exp_pow_eq_exp ha _ t, norm_mul_exp_pow_eq_exp hb _ s, Real.exp_le_exp,
    Real.log_exp, mul_sub]
  constructor <;> intro h <;> linarith

omit [IsUltrametricDist K] in
/-- Strict variant of `term_le_term_iff'`.  (`Test/test.lean` line 1524.) -/
private lemma term_lt_term_iff' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {c : ℝ} (hc : 0 < c)
    (t s : ℕ) :
    ‖a‖ * c ^ t < ‖b‖ * c ^ s ↔
      Real.log c * ((t : ℝ) - s) < -Real.log ‖a‖ - -Real.log ‖b‖ := by
  rw [show c = Real.exp (Real.log c) from (Real.exp_log hc).symm,
    norm_mul_exp_pow_eq_exp ha _ t, norm_mul_exp_pow_eq_exp hb _ s, Real.exp_lt_exp,
    Real.log_exp, mul_sub]
  constructor <;> intro h <;> linarith

omit [IsUltrametricDist K] in
/-- **Backwards convexity, in algorithm data.**  Every finite point lies on/above the line of the
`a`-th slope through the `a`-th output vertex `(j₀, j₁)`; backwards along the polygon this is the
induction on the segment index (earlier segments have smaller slopes).
(`Test/test.lean` line 1537.) -/
private lemma vertex_line_le_step (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1) :
    ∀ (a : ℕ) {j₀ l : ℕ} {j₁ m : ℝ},
      newtonPolygon (coeffVal f) a = some (.nextVertex j₀ j₁ l m) →
      ∀ t, PowerSeries.coeff t f ≠ 0 →
        m * ((t : ℝ) - (j₀ : ℝ)) ≤ -Real.log ‖PowerSeries.coeff t f‖ - j₁ := by
  intro a
  induction a with
  | zero =>
      intro j₀ l j₁ m hseg t ht
      have hv : nextStep (coeffVal f) 0 (0 : ℝ) = .nextVertex j₀ j₁ l m :=
        Option.some_inj.mp ((newtonPolygon_coeffVal_zero hf0).symm.trans hseg)
      have hj₁ : j₁ = m * (j₀ : ℝ) := by simpa using coeffVal_vertex_line hv
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · have hν0 : -Real.log ‖PowerSeries.coeff 0 f‖ = 0 := by
          rw [hf0, norm_one, Real.log_one, neg_zero]
        have hexp : m * (((0 : ℕ) : ℝ) - (j₀ : ℝ)) = -(m * (j₀ : ℝ)) := by push_cast; ring
        rw [hν0, hexp, hj₁]
        linarith
      · have hfb : m * (t : ℝ) ≤ -Real.log ‖PowerSeries.coeff t f‖ := by
          simpa using coeffVal_slope_le hv htpos ht
        have hexp : m * ((t : ℝ) - (j₀ : ℝ)) = m * (t : ℝ) - m * (j₀ : ℝ) := by ring
        rw [hexp, hj₁]
        linarith
  | succ a ih =>
      intro j₀ l j₁ m hseg t ht
      obtain ⟨i₀, i₁, l', m', hprev⟩ := nextStep_nextVertex' _ hseg
      have hstep : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m :=
        nextStep_nextVertex'' _ hseg hprev
      have hline : j₁ = i₁ + m * ((j₀ : ℝ) - (i₀ : ℝ)) := coeffVal_vertex_line hstep
      have key : m * ((t : ℝ) - (i₀ : ℝ)) ≤ -Real.log ‖PowerSeries.coeff t f‖ - i₁ := by
        rcases Nat.lt_or_ge i₀ t with hti | hti
        · exact coeffVal_slope_le hstep hti ht
        · have h1 := ih hprev t ht
          have hts : ((t : ℝ) - (i₀ : ℝ)) ≤ 0 := by rw [sub_nonpos]; exact_mod_cast hti
          obtain ⟨p₀, p₁, hprevstep⟩ := nextStep_nextVertex _ hprev
          have hmm : m' < m := slopes_increasing_nextVertex _ hprevstep hstep
          nlinarith [h1, mul_nonneg (sub_nonneg.mpr hmm.le) (neg_nonneg.mpr hts)]
      have hexp : m * ((t : ℝ) - (j₀ : ℝ))
          = m * ((t : ℝ) - (i₀ : ℝ)) - m * ((j₀ : ℝ) - (i₀ : ℝ)) := by ring
      linarith [key, hline, hexp]

omit [IsUltrametricDist K] in
/-- **Backwards convexity of the polygon.**  Let `m` be the `a`-th slope of the Newton polygon
of `f` and `j₀` the right endpoint of its `a`-th segment.  Every finite point of the polygon —
before *or* after — lies on/above the line of slope `m` through the vertex
`(j₀, -log ‖f.coeff j₀‖)`.  Backwards this is by induction along the segments: the earlier
segments have smaller slopes, so walking back from the vertex the points rise relative to the
`m`-line.  (`Test/test.lean` line 1537.) -/
theorem vertex_line_le (f : Polynomial K) (hf0 : f.coeff 0 = 1) {a j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes a
      = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX (a + 1)
      = ((j₀ : ℤ) : WithTop ℤ)) :
    ∀ t, f.coeff t ≠ 0 →
      m * ((t : ℝ) - (j₀ : ℝ)) ≤ -Real.log ‖f.coeff t‖ - -Real.log ‖f.coeff j₀‖ := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := (Polynomial.coeff_coe f 0).trans hf0
  obtain ⟨j₁, l, hseg⟩ := step_of_segment_data hm hj
  obtain ⟨i₀, i₁, hstep⟩ := nextStep_nextVertex _ hseg
  obtain ⟨-, hj₁⟩ := coeffVal_vertex_value hstep
  rw [Polynomial.coeff_coe] at hj₁
  intro t ht
  have h := vertex_line_le_step (f : PowerSeries K) hf0' a hseg t (by rwa [Polynomial.coeff_coe])
  rw [Polynomial.coeff_coe] at h
  rwa [hj₁] at h

omit [IsUltrametricDist K] in
/-- Beyond the right endpoint `j₀` of the `a`-th segment the points lie **strictly** above the
`a`-th slope line (the next slope is strictly bigger).  (`Test/test.lean` line 1601.) -/
theorem vertex_line_lt (f : Polynomial K) {a j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes a
      = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX (a + 1)
      = ((j₀ : ℤ) : WithTop ℤ))
    {t : ℕ} (htj : j₀ < t) (hat : f.coeff t ≠ 0) :
    m * ((t : ℝ) - (j₀ : ℝ)) < -Real.log ‖f.coeff t‖ - -Real.log ‖f.coeff j₀‖ := by
  obtain ⟨j₁, l, hseg⟩ := step_of_segment_data hm hj
  obtain ⟨i₀, i₁, hstep⟩ := nextStep_nextVertex _ hseg
  obtain ⟨-, hj₁⟩ := coeffVal_vertex_value hstep
  rw [Polynomial.coeff_coe] at hj₁
  have hlt := coeffVal_slope_lt hstep htj (by rwa [Polynomial.coeff_coe] :
    PowerSeries.coeff t (f : PowerSeries K) ≠ 0)
  rw [Polynomial.coeff_coe] at hlt
  have hline : j₁ = i₁ + m * ((j₀ : ℝ) - (i₀ : ℝ)) := coeffVal_vertex_line hstep
  have hexp : m * ((t : ℝ) - (j₀ : ℝ))
      = m * ((t : ℝ) - (i₀ : ℝ)) - m * ((j₀ : ℝ) - (i₀ : ℝ)) := by ring
  linarith [hlt, hline, hexp, hj₁]

omit [IsUltrametricDist K] in
/-- **A polynomial whose top term dominates at radius `c` has no zeros outside the closed ball
of radius `c`** — the mirror of `aeval_ne_zero_of_dominant_const`, used for the Weierstrass
factor `ω` (its roots are exactly the small roots).  (`Test/test.lean` line 1617.) -/
theorem aeval_ne_zero_of_dominant_top {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (g : Polynomial K) {c : ℝ} (hc : 0 < c) {s : ℕ} (hdeg : g.natDegree = s)
    (hgs : g.coeff s ≠ 0)
    (hdom : ∀ t, ‖g.coeff t‖ * c ^ t ≤ ‖g.coeff s‖ * c ^ s)
    {x : L} (hx : c < (w x : ℝ)) :
    Polynomial.aeval x g ≠ 0 := by
  have hwx : (0 : ℝ) < (w x : ℝ) := lt_trans hc hx
  refine aeval_ne_zero_of_dominant w hw g (s := s) fun k hk => ?_
  by_cases hgk : g.coeff k = 0
  · rw [hgk, norm_zero, zero_mul]
    exact mul_pos (norm_pos_iff.mpr hgs) (pow_pos hwx s)
  · have hks : ((k : ℝ) - s) < 0 := by
      rw [sub_lt_zero]
      exact_mod_cast lt_of_le_of_ne (hdeg ▸ Polynomial.le_natDegree_of_ne_zero hgk) hk
    refine (term_lt_term_iff' hgk hgs hwx k s).mpr ?_
    have hd := (term_le_term_iff' hgk hgs hc k s).mp (hdom k)
    nlinarith [hd, mul_neg_of_pos_of_neg (sub_pos.mpr (Real.log_lt_log hc hx)) hks]

omit [IsUltrametricDist K] in
/-- **From slope and length to algorithm data.**  A finite slope together with a finite length at
index `k` forces a `nextVertex` output there — the other four outputs have slope `⊤`/`⊥` or
length `⊤` — whose right endpoint `j₀` is the `(k+1)`-st vertex of the constructed polygon and
satisfies `0 < l ≤ j₀`.  Companion of `step_of_segment_data`, which instead *reads* the endpoint
off the polygon; here it is produced, as needed by `card_roots_slope`. -/
private lemma step_of_slope_length {f : PowerSeries K} {k l : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hl : (newtonPolygon₀OfPowerSeries negLogNorm f).lengths k = (l : WithTop ℕ)) :
    ∃ (j₀ : ℕ) (j₁ : ℝ), newtonPolygon (coeffVal f) k = some (.nextVertex j₀ j₁ l m) ∧
      (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (k + 1) = ((j₀ : ℤ) : WithTop ℤ) ∧
      0 < l ∧ l ≤ j₀ := by
  obtain ⟨j₀, l', j₁, hstep⟩ :=
    step_of_slope_of_lengths_ne_top hm (hl.trans_ne WithTop.coe_ne_top)
  have hlengths : newtonPolygon_lengths (coeffVal f) k = (l : WithTop ℕ) := hl
  simp only [newtonPolygon_lengths, hstep] at hlengths
  obtain rfl : l' = l := by exact_mod_cast hlengths
  obtain ⟨i₀, i₁, hstp⟩ := nextStep_nextVertex _ hstep
  have h1 := nextVertex_l_eq _ hstp
  have h2 := nextVertex_lt _ hstp
  exact ⟨j₀, j₁, hstep, newtonPolygon₀OfSeq_vertexX (coeffVal f) hstep, by omega, by omega⟩

/-- **An intermediate radius above finitely many small values.**  Given a multiset `S` of points
and `μ < M`, there is a radius `c'` with `μ < c' < M` bounding every point of `S` of value
`< M`.  This replaces `exists_memDivisibleValueGroup_between` of `Test/test.lean` (line 1818):
Weierstrass preparation now applies at *every* positive radius, so `c'` no longer has to lie in
the divisible closure of the value group and plain density of `ℝ` suffices. -/
private lemma exists_radius_between {L : Type*} [Field L] (w : Valuation L NNReal)
    (S : Multiset L) {μ M : ℝ} (hμM : μ < M) :
    ∃ c', μ < c' ∧ c' < M ∧ ∀ x ∈ S, (w x : ℝ) < M → (w x : ℝ) ≤ c' := by
  classical
  obtain ⟨F, hFne, hFlt, hμF, hSF⟩ : ∃ F : Finset ℝ, F.Nonempty ∧ (∀ r ∈ F, r < M) ∧ μ ∈ F ∧
      ∀ x ∈ S, (w x : ℝ) < M → (w x : ℝ) ∈ F := by
    refine ⟨insert μ ((S.toFinset.image fun x => (w x : ℝ)).filter (fun r => r < M)),
      ⟨μ, Finset.mem_insert_self _ _⟩, ?_, Finset.mem_insert_self _ _, fun x hx hxM => ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hμM
      · exact (Finset.mem_filter.mp hr).2
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ (Multiset.mem_toFinset.mpr hx), hxM⟩)
  obtain ⟨c', h1, h2⟩ := exists_between (hFlt _ (F.max'_mem hFne))
  exact ⟨c', lt_of_le_of_lt (Finset.le_max' F _ hμF) h1, h2,
    fun x hx hxM => le_of_lt (lt_of_le_of_lt (Finset.le_max' F _ (hSF x hx hxM)) h1)⟩

open Classical in
/-- **The number of roots in the closed ball of radius `c` of an `s`-distinguished polynomial
is `s`.**  One application of Weierstrass preparation at radius `c`: `f = e·ω` with
`deg ω = s`; the roots of `e` lie strictly outside the ball, the roots of `ω` inside.
(`Test/test.lean` line 1670, with the `MemDivisibleValueGroup` hypothesis deleted.) -/
theorem card_roots_le_of_distinguished [CompleteSpace K] (f : Polynomial K)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {c : ℝ} (hc : 0 < c)
    {s : ℕ} (hcs : f.coeff s ≠ 0)
    (hle : ∀ k, ‖f.coeff k‖ * c ^ k ≤ ‖f.coeff s‖ * c ^ s)
    (hlt : ∀ t, s < t → ‖f.coeff t‖ * c ^ t < ‖f.coeff s‖ * c ^ s) :
    (Multiset.filter (fun x => (w x : ℝ) ≤ c)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = s := by
  obtain ⟨ω, e, hfeq, hωdeg, hωmonic, hωdom', hedom⟩ := exists_factor_aux f hc hcs hle hlt
  have hf_ne : f ≠ 0 := fun h0 => hcs (by rw [h0, Polynomial.coeff_zero])
  have hω_ne : ω ≠ 0 := fun h0 => hf_ne (by rw [hfeq, h0, mul_zero])
  have he_ne : e ≠ 0 := fun h0 => hf_ne (by rw [hfeq, h0, zero_mul])
  have hωs1 : ω.coeff s = 1 := hωdeg ▸ hωmonic.coeff_natDegree
  have hωs : ω.coeff s ≠ 0 := hωs1.trans_ne one_ne_zero
  have hωdom : ∀ t, ‖ω.coeff t‖ * c ^ t ≤ ‖ω.coeff s‖ * c ^ s := fun t => by
    rw [hωs1, norm_one, one_mul]
    exact hωdom' t
  set φ := algebraMap K (AlgebraicClosure K)
  have hφinj : Function.Injective φ := φ.injective
  have hωmap_ne : ω.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hω_ne
  have hemap_ne : e.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr he_ne
  have hroots : (f.map φ).roots = (e.map φ).roots + (ω.map φ).roots := by
    rw [hfeq, Polynomial.map_mul, Polynomial.roots_mul (mul_ne_zero hemap_ne hωmap_ne)]
  -- the roots of the unit factor `e` lie strictly outside the closed ball …
  have he0 : Multiset.filter (fun x => (w x : ℝ) ≤ c) (e.map φ).roots = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx hxc
    exact aeval_ne_zero_of_dominant_const w hw e hedom hxc
      (Polynomial.mem_aroots'.mp (show x ∈ e.aroots (AlgebraicClosure K) from hx)).2
  -- … and all `s` roots of the distinguished factor `ω` lie inside it
  have hωall : ∀ x ∈ (ω.map φ).roots, (w x : ℝ) ≤ c := fun x hx =>
    not_lt.mp fun hgt => aeval_ne_zero_of_dominant_top w hw ω hc hωdeg hωs hωdom hgt
      (Polynomial.mem_aroots'.mp (show x ∈ ω.aroots (AlgebraicClosure K) from hx)).2
  have hsplits : (ω.map φ).Splits := IsAlgClosed.splits _
  rw [hroots, Multiset.filter_add, Multiset.card_add, he0, Multiset.card_zero, zero_add,
    Multiset.filter_eq_self.mpr hωall, ← hsplits.natDegree_eq_card_roots,
    Polynomial.natDegree_map, hωdeg]

open Classical in
/-- **The closed-ball count at the `k`-th slope**: if `m` is the `k`-th slope of the Newton
polygon of `f` and `j₀` the right endpoint of its `k`-th segment, then `f` has exactly `j₀`
roots of absolute value `≤ exp m`.  By polygon convexity (`vertex_line_le`, `vertex_line_lt`),
`f` is `j₀`-distinguished at radius `exp m`.  (`Test/test.lean` line 1730.) -/
theorem card_roots_le_slope [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes k
      = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX (k + 1)
      = ((j₀ : ℤ) : WithTop ℤ)) :
    (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp m)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = j₀ := by
  obtain ⟨j₁, l, hseg⟩ := step_of_segment_data hm hj
  obtain ⟨i₀, i₁, hstep⟩ := nextStep_nextVertex _ hseg
  obtain ⟨hcj₀, -⟩ := coeffVal_vertex_value hstep
  rw [Polynomial.coeff_coe] at hcj₀
  refine card_roots_le_of_distinguished f w hw (Real.exp_pos m) hcj₀ (fun t => ?_) (fun t htj => ?_)
  · by_cases hat : f.coeff t = 0
    · rw [hat, norm_zero, zero_mul]
      positivity
    · refine (term_le_term_iff' hat hcj₀ (Real.exp_pos m) t j₀).mpr ?_
      rw [Real.log_exp]
      exact vertex_line_le f hf0 hm hj t hat
  · by_cases hat : f.coeff t = 0
    · rw [hat, norm_zero, zero_mul]
      exact mul_pos (norm_pos_iff.mpr hcj₀) (pow_pos (Real.exp_pos m) j₀)
    · refine (term_lt_term_iff' hat hcj₀ (Real.exp_pos m) t j₀).mpr ?_
      rw [Real.log_exp]
      exact vertex_line_lt f hm hj htj hat

open Classical in
/-- **The open-ball count at the `k`-th slope**: if `m` is the `k`-th slope of the Newton
polygon of `f`, `l` its length and `j₀` its right endpoint, then `f` has exactly `j₀ - l`
roots (the segment's *start*) of absolute value `< exp m`.  For `k = 0` this is §5.10's first
half; for `k ≥ 1`, pick a radius `c'` strictly between `exp m_{k-1}` and `exp m` lying above
the norms of the finitely many roots below the sphere: `f` is `i₀`-distinguished at `c'`
(strictly on both sides of `i₀`), and the closed `c'`-ball catches exactly the roots with
`w < exp m`.  (`Test/test.lean` line 1765; the intermediate radius no longer needs to lie in
the divisible closure of the value group, so the density detour is gone.) -/
theorem card_roots_lt_slope [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {k j₀ l : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes k
      = (m : WithBotTop ℝ))
    (hl : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).lengths k
      = (l : WithTop ℕ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX (k + 1)
      = ((j₀ : ℤ) : WithTop ℤ)) :
    (Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = j₀ - l := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := (Polynomial.coeff_coe f 0).trans hf0
  obtain ⟨j₀', j₁, hseg, hvx, hl0, -⟩ := step_of_slope_length hm hl
  have hjj : j₀' = j₀ := by exact_mod_cast WithTop.coe_inj.mp (hvx.symm.trans hj)
  rw [hjj] at hseg
  rcases k with _ | a
  · -- first segment: no roots below the first slope (§5.10, first half)
    have hv : nextStep (coeffVal (f : PowerSeries K)) 0 (0 : ℝ) = .nextVertex j₀ j₁ l m :=
      Option.some_inj.mp ((newtonPolygon_coeffVal_zero hf0').symm.trans hseg)
    have hlj₀ : l = j₀ := by have := nextVertex_l_eq _ hv; omega
    have hbreak : HasFirstBreak (f : PowerSeries K) l m := ⟨hl0, hm, hl⟩
    have hempty : Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
        ((f.map (algebraMap K (AlgebraicClosure K))).roots) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx hxc
      exact aeval_ne_zero_of_norm_lt_firstBreak w hw f hf0 hbreak hxc
        (Polynomial.mem_aroots'.mp (show x ∈ f.aroots (AlgebraicClosure K) from hx)).2
    rw [hempty, Multiset.card_zero]
    omega
  · -- later segment: count the closed ball at a radius just below `exp m`
    obtain ⟨i₀, i₁, l', m', hprev⟩ := nextStep_nextVertex' _ hseg
    have hstep : nextStep (coeffVal (f : PowerSeries K)) i₀ i₁ = .nextVertex j₀ j₁ l m :=
      nextStep_nextVertex'' _ hseg hprev
    obtain ⟨p₀, p₁, hprevstep⟩ := nextStep_nextVertex _ hprev
    have hmm : m' < m := slopes_increasing_nextVertex _ hprevstep hstep
    obtain ⟨hci₀, hi₁val⟩ := coeffVal_vertex_value hprevstep
    rw [Polynomial.coeff_coe] at hci₀ hi₁val
    have hi₀j₀ : i₀ < j₀ := nextVertex_lt _ hstep
    have hlen : l = j₀ - i₀ := nextVertex_l_eq _ hstep
    -- choose the intermediate radius `c'`, above the norms of the roots strictly inside
    obtain ⟨c', hm'c', hc'2, hroots_le⟩ := exists_radius_between w
      ((f.map (algebraMap K (AlgebraicClosure K))).roots) (Real.exp_lt_exp.mpr hmm)
    have hc'pos : 0 < c' := lt_trans (Real.exp_pos m') hm'c'
    have hμm : Real.log c' < m := (Real.log_lt_iff_lt_exp hc'pos).mpr hc'2
    have hm'μ : m' < Real.log c' := by
      have h := Real.log_lt_log (Real.exp_pos m') hm'c'
      rwa [Real.log_exp] at h
    -- `f` is `i₀`-distinguished at radius `c'`, strictly away from `i₀`
    have hstrict : ∀ t, f.coeff t ≠ 0 → t ≠ i₀ →
        Real.log c' * ((t : ℝ) - i₀) < -Real.log ‖f.coeff t‖ - -Real.log ‖f.coeff i₀‖ := by
      intro t hat htne
      rcases Nat.lt_or_ge t i₀ with hti | hti
      · have h1 := vertex_line_le_step (f : PowerSeries K) hf0' a hprev t
          (by rwa [Polynomial.coeff_coe])
        rw [Polynomial.coeff_coe, hi₁val] at h1
        have hts : ((t : ℝ) - i₀) < 0 := by rw [sub_lt_zero]; exact_mod_cast hti
        nlinarith [h1, mul_neg_of_pos_of_neg (sub_pos.mpr hm'μ) hts]
      · have hti' : i₀ < t := lt_of_le_of_ne hti (Ne.symm htne)
        have h1 := coeffVal_slope_le hstep hti' (by rwa [Polynomial.coeff_coe])
        rw [Polynomial.coeff_coe, hi₁val] at h1
        have hts : (0 : ℝ) < ((t : ℝ) - i₀) := by rw [sub_pos]; exact_mod_cast hti'
        nlinarith [h1, mul_pos (sub_pos.mpr hμm) hts]
    have key : ∀ t, t ≠ i₀ → ‖f.coeff t‖ * c' ^ t < ‖f.coeff i₀‖ * c' ^ i₀ := by
      intro t htne
      by_cases hat : f.coeff t = 0
      · rw [hat, norm_zero, zero_mul]
        exact mul_pos (norm_pos_iff.mpr hci₀) (pow_pos hc'pos i₀)
      · exact (term_lt_term_iff' hat hci₀ hc'pos t i₀).mpr (hstrict t hat htne)
    have hcount := card_roots_le_of_distinguished f w hw hc'pos hci₀
      (fun t => (eq_or_ne t i₀).elim (fun h => le_of_eq (by rw [h])) fun h => (key t h).le)
      fun t ht => key t ht.ne'
    have hfe : Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
        ((f.map (algebraMap K (AlgebraicClosure K))).roots)
        = Multiset.filter (fun x => (w x : ℝ) ≤ c')
          ((f.map (algebraMap K (AlgebraicClosure K))).roots) :=
      Multiset.filter_congr fun x hx =>
        ⟨fun h => hroots_le x hx h, fun h => lt_of_le_of_lt h hc'2⟩
    rw [hfe, hcount]
    omega

open Classical in
/-- **Blueprint Theorem 5.11.**  If the `k`-th segment of the Newton polygon of `f` has slope
`m` and projected length `l`, then `f` has exactly `l` roots of absolute value `exp m`, counted
with multiplicity in the algebraic closure: the closed-ball count minus the open-ball count.
(`Test/test.lean` line 1883.) -/
theorem card_roots_slope [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {k l : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes k
      = (m : WithBotTop ℝ))
    (hl : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).lengths k
      = (l : WithTop ℕ)) :
    (Multiset.filter (fun x => (w x : ℝ) = Real.exp m)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = l := by
  obtain ⟨j₀, j₁, hseg, hj, -, hlj⟩ := step_of_slope_length hm hl
  have hle_count := card_roots_le_slope f hf0 w hw hm hj
  have hlt_count := card_roots_lt_slope f hf0 w hw hm hl hj
  set R := (f.map (algebraMap K (AlgebraicClosure K))).roots
  have hsum : (Multiset.filter (fun x => (w x : ℝ) < Real.exp m) R).card
      + (Multiset.filter (fun x => (w x : ℝ) = Real.exp m) R).card
      = (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp m) R).card := by
    have h1 : Multiset.filter (fun x => (w x : ℝ) < Real.exp m ∨ (w x : ℝ) = Real.exp m) R
        = Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp m) R :=
      Multiset.filter_congr fun x _ => (le_iff_lt_or_eq (a := (w x : ℝ)) (b := Real.exp m)).symm
    have h2 : Multiset.filter (fun x => (w x : ℝ) < Real.exp m ∧ (w x : ℝ) = Real.exp m) R = 0 :=
      Multiset.filter_eq_nil.mpr fun x _ h => absurd h.2 (ne_of_lt h.1)
    have h := congrArg Multiset.card (Multiset.filter_add_filter
      (fun x => (w x : ℝ) < Real.exp m) (fun x => (w x : ℝ) = Real.exp m) R)
    rwa [Multiset.card_add, Multiset.card_add, h1, h2, Multiset.card_zero, add_zero] at h
  omega
