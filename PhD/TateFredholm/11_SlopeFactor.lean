/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.«10_Entire»
import PhD.TateFredholm.«00_Tate»

/-!
# The vertex (slope) factorisation of an entire series

[Bel] §II.3.2, Theorem II.3.6, existence half, over a Banach–Tate ring with the norm in place
of the pointwise conditions: if `N` is the *dominant index* of the entire `F` at radius `ρ`
— `‖aₖ‖ρᵏ ≤ ‖a_N‖ρ^N` for all `k`, strictly for `k > N` ([Bel] Definition II.2.3: "the
largest integer `N` such that `v_p(a_N) − Nν = inf_n (v_p(a_n) − nν)`") — and the dominant
coefficient `a_N` is a multiplicative unit, then `F = PG` with `P` a `ρ`-dominant polynomial of
degree `N` ([Bel] Definition II.2.4) and `G` entire with dominant index `0` at radius `ρ`
("`N(G_x, ν) = 0`").  The proof is the Newton iteration (II.3.1)–(II.3.6) of [Bel], driven by
the Euclidean-division estimates (II.2.1) — Martin's norm identity
`‖f‖ = max(‖g‖‖q‖, ‖r‖)` at radius `ρ`.

This is the "standard factorization argument" behind [LWX] Remark 3.25 ("see e.g. [Ke09,
Proposition 3.2.2] for the argument"; Kedlaya's proof is the same iteration
`P_{l+1} = P_l + X_l`, `Q_{l+1} = Q_l + Y_l`), and the norm-level form of [JN]
Definition 2.2.5's slope-`≤ h` factorisation.  The factors are relatively prime in `R{{T}}`
(the norm-level form of [JN] Lemma 2.2.7, proved here by Weierstrass division rather than by
resultants over the Gelfand spectrum), so [JN] Theorem 2.2.2 applies to them.

The proof given here is not [Bel]'s Newton iteration but Weierstrass preparation: `F` with
dominant index `N` and multiplicative dominant coefficient is Martin-distinguished of order `N`
at radius `ρ`, so `X^N` can be divided by `F`, and the monic factor is `X^N` minus the
remainder.

## Main definitions

* `PowerSeries.IsDominantIndex`, `PowerSeries.IsDominantPoly`: [Bel] Definitions II.2.3–II.2.4.
* `PowerSeries.IsDominantFactorization`: the conclusion of the factorisation, [Bel] Theorem
  II.3.6 (ii).

## Main results

* `PowerSeries.exists_isDominantPoly_of_isUnit_leadingCoeff`: [Bel] Lemma II.2.5.
* `PowerSeries.IsDominantPoly.isMulDistinguished`: dominance is Martin's distinguishedness.
* `PowerSeries.IsDominantPoly.mul`: dominant polynomials are closed under multiplication.
* `PowerSeries.norm_coeff_r_mul_pow_le_of_eq_mul_add`: the division estimate [Bel] (II.2.1).
* `PowerSeries.exists_isDominantFactorization`: the vertex factorisation.
* `PowerSeries.IsDominantFactorization.isEntireCoprime`: the factors are relatively prime.
-/

open Filter Topology Polynomial

noncomputable section

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]

/-- **[Bel] Definition II.2.3** (multiplicative form): `N` is the *dominant index* of `F` at
radius `ρ` if `‖aₖ‖ρᵏ ≤ ‖a_N‖ρ^N` for all `k`, with strict inequality for `k > N`. -/
def IsDominantIndex (ρ : ℝ) (F : PowerSeries R) (N : ℕ) : Prop :=
  (∀ k, ‖coeff k F‖ * ρ ^ k ≤ ‖coeff N F‖ * ρ ^ N) ∧
    ∀ k, N < k → ‖coeff k F‖ * ρ ^ k < ‖coeff N F‖ * ρ ^ N

/-- **[Bel] Definition II.2.4**: a polynomial is *`ρ`-dominant* if its degree is its dominant
index at radius `ρ` and its dominant (= leading) coefficient is invertible. -/
def IsDominantPoly (ρ : ℝ) (P : R[X]) : Prop :=
  IsDominantIndex ρ (P : PowerSeries R) P.natDegree ∧ IsUnit P.leadingCoeff

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- **[Bel] Lemma II.2.5**: a polynomial with invertible leading coefficient is `ρ`-dominant
for every sufficiently large radius. -/
theorem exists_isDominantPoly_of_isUnit_leadingCoeff (P : R[X]) (hP : IsUnit P.leadingCoeff) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ, ρ₀ ≤ ρ → IsDominantPoly ρ P := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨v, hv⟩ := hP
  have hlc : P.leadingCoeff ≠ 0 := by rw [← hv]; exact v.ne_zero
  have hlcpos : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.2 hlc
  have hinv : (1 : ℝ) ≤ ‖((v⁻¹ : Rˣ) : R)‖ * ‖P.leadingCoeff‖ := by
    have h := norm_mul_le ((v⁻¹ : Rˣ) : R) ((v : R))
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, norm_one, hv] at h
  set b : ℕ → ℝ := fun i ↦ ‖P.coeff i‖ * ‖((v⁻¹ : Rˣ) : R)‖ with hb
  have hbnn : ∀ i, 0 ≤ b i := fun i ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨1 + ∑ i ∈ Finset.range (P.natDegree + 1), b i,
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hbnn i)),
    fun ρ hρ ↦ ⟨⟨fun k ↦ ?_, fun k hk ↦ ?_⟩, hv ▸ v.isUnit⟩⟩
  · have h1ρ : (1 : ℝ) ≤ ρ :=
      le_trans (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hbnn i)) hρ
    have h0ρ : (0 : ℝ) ≤ ρ := zero_le_one.trans h1ρ
    rw [Polynomial.coeff_coe, Polynomial.coeff_coe]
    rcases lt_trichotomy k P.natDegree with hk | rfl | hk
    · have hbk : b k ≤ ρ :=
        le_trans (le_add_of_nonneg_of_le zero_le_one (Finset.single_le_sum
          (f := b) (fun i _ ↦ hbnn i) (Finset.mem_range.2 (Nat.lt_succ_of_le hk.le)))) hρ
      have hbound : ‖P.coeff k‖ ≤ ρ * ‖P.leadingCoeff‖ :=
        calc ‖P.coeff k‖ = ‖P.coeff k‖ * 1 := (mul_one _).symm
          _ ≤ ‖P.coeff k‖ * (‖((v⁻¹ : Rˣ) : R)‖ * ‖P.leadingCoeff‖) :=
              mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
          _ = b k * ‖P.leadingCoeff‖ := by rw [hb, mul_assoc]
          _ ≤ ρ * ‖P.leadingCoeff‖ := mul_le_mul_of_nonneg_right hbk hlcpos.le
      calc ‖P.coeff k‖ * ρ ^ k ≤ (ρ * ‖P.leadingCoeff‖) * ρ ^ k :=
            mul_le_mul_of_nonneg_right hbound (pow_nonneg h0ρ k)
        _ = ‖P.leadingCoeff‖ * ρ ^ (k + 1) := by rw [pow_succ]; ring
        _ ≤ ‖P.leadingCoeff‖ * ρ ^ P.natDegree :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1ρ hk) (norm_nonneg _)
    · exact le_rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, norm_zero, zero_mul]
      exact mul_nonneg (norm_nonneg _) (pow_nonneg h0ρ _)
  · have h1ρ : (1 : ℝ) ≤ ρ :=
      le_trans (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hbnn i)) hρ
    have h0ρ : (0 : ℝ) < ρ := zero_lt_one.trans_le h1ρ
    rw [Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt hk, norm_zero, zero_mul]
    exact mul_pos hlcpos (pow_pos h0ρ _)

omit [CompleteSpace R] [NormOneClass R] in
/-- The norm at radius `ρ` of a restricted series with dominant index `N` is its `N`-th Gauss
term. -/
theorem norm_of_isDominantIndex {ρ : ℝ} [Fact (0 < ρ)] {f : Restricted R ρ} {N : ℕ}
    (h : IsDominantIndex ρ f.1 N) : ‖f‖ = ‖coeff N f.1‖ * ρ ^ N :=
  le_antisymm ((Restricted.norm_le_iff ρ f).2 fun i ↦ h.1 i)
    (Restricted.norm_coeff_mul_pow_le ρ f N)

omit [CompleteSpace R] [NormOneClass R] in
/-- The Gauss norm at radius `ρ` of a polynomial with dominant index `N` is its `N`-th Gauss
term. -/
theorem norm_toRestricted_of_isDominantIndex {ρ : ℝ} [Fact (0 < ρ)] {P : R[X]} {N : ℕ}
    (h : IsDominantIndex ρ (P : PowerSeries R) N) :
    ‖Polynomial.toRestricted ρ P‖ = ‖coeff N (P : PowerSeries R)‖ * ρ ^ N :=
  norm_of_isDominantIndex (f := Polynomial.toRestricted ρ P) h

omit [CompleteSpace R] [NormOneClass R] in
/-- A `ρ`-dominant polynomial whose leading coefficient is multiplicative is Martin
distinguished of order its degree at radius `ρ` ([Mar16] Definition 1.24): the two notions
agree, dominance being the coefficientwise form of "the top Gauss term attains the Gauss norm
and strictly dominates the later ones". -/
theorem IsDominantPoly.isMulDistinguished {ρ : ℝ} (hρ : 0 < ρ) {P : R[X]}
    (hP : IsDominantPoly ρ P) (hm : TateFredholm.IsMultiplicative P.leadingCoeff) :
    IsMulDistinguished ρ (P : PowerSeries R) P.natDegree := by
  haveI : Fact (0 < ρ) := ⟨hρ⟩
  have hcoeff : coeff P.natDegree (P : PowerSeries R) = P.leadingCoeff := Polynomial.coeff_coe P _
  refine ⟨hcoeff ▸ ⟨hP.2, hm⟩, ?_, hP.1.2⟩
  exact norm_toRestricted_of_isDominantIndex hP.1

omit [CompleteSpace R] in
/-- **[JN] Lemma 2.2.9's polynomial input** ("if `Q₁` and `Q₂` are two multiplicative
polynomials of slope `≤ h`, then so is `Q₁Q₂`"), norm-level: `ρ`-dominant polynomials are
closed under multiplication (Martin's Lemma 1.26, `norm_mul_of_isMulDistinguished`).  The
leading coefficient of the first factor is assumed multiplicative — without it the norm of the
product of the leading coefficients can drop and the top term need not dominate. -/
theorem IsDominantPoly.mul {ρ : ℝ} (hρ : 0 < ρ) {P Q : R[X]} (hP : IsDominantPoly ρ P)
    (hQ : IsDominantPoly ρ Q) (hm : TateFredholm.IsMultiplicative P.leadingCoeff) :
    IsDominantPoly ρ (P * Q) := by
  have : Nontrivial R := NormOneClass.nontrivial
  haveI : Fact (0 < ρ) := ⟨hρ⟩
  have hlc : IsUnit (P.leadingCoeff * Q.leadingCoeff) := hP.2.mul hQ.2
  have hne : P.leadingCoeff * Q.leadingCoeff ≠ 0 := hlc.ne_zero
  have hdeg : (P * Q).natDegree = P.natDegree + Q.natDegree := Polynomial.natDegree_mul' hne
  have hlead : (P * Q).leadingCoeff = P.leadingCoeff * Q.leadingCoeff :=
    Polynomial.leadingCoeff_mul' hne
  have hPnorm : ‖Polynomial.toRestricted ρ P‖ = ‖P.leadingCoeff‖ * ρ ^ P.natDegree := by
    rw [norm_toRestricted_of_isDominantIndex hP.1, Polynomial.coeff_coe]
    rfl
  have hQnorm : ‖Polynomial.toRestricted ρ Q‖ = ‖Q.leadingCoeff‖ * ρ ^ Q.natDegree := by
    rw [norm_toRestricted_of_isDominantIndex hQ.1, Polynomial.coeff_coe]
    rfl
  have hlead' : (P * Q).coeff (P * Q).natDegree = P.leadingCoeff * Q.leadingCoeff := hlead
  have htop : ‖(P * Q).coeff (P * Q).natDegree‖ * ρ ^ (P * Q).natDegree =
      (‖P.leadingCoeff‖ * ρ ^ P.natDegree) * (‖Q.leadingCoeff‖ * ρ ^ Q.natDegree) := by
    rw [hlead', hdeg, hm Q.leadingCoeff, pow_add]
    ring
  refine ⟨⟨fun k ↦ ?_, fun k hk ↦ ?_⟩, hlead ▸ hlc⟩
  · rw [Polynomial.coeff_coe, Polynomial.coeff_coe, htop, ← hPnorm, ← hQnorm]
    calc ‖(P * Q).coeff k‖ * ρ ^ k ≤ ‖Polynomial.toRestricted ρ (P * Q)‖ := by
          have := Restricted.norm_coeff_mul_pow_le ρ (Polynomial.toRestricted ρ (P * Q)) k
          rwa [Polynomial.val_toRestricted, Polynomial.coeff_coe] at this
      _ = ‖Polynomial.toRestricted ρ P‖ * ‖Polynomial.toRestricted ρ Q‖ := by
          rw [map_mul, Restricted.norm_mul_of_isMulDistinguished (hP.isMulDistinguished hρ hm)]
  · rw [Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt hk, norm_zero, zero_mul]
    exact mul_pos (norm_pos_iff.2 (hlead' ▸ hne)) (pow_pos hρ _)

/-- The conclusion of the vertex factorisation ([Bel] Theorem II.3.6 (ii), norm level):
`F = PG` with `P` a `ρ`-dominant polynomial of degree `N` with `P(0) = 1` and `G` entire with
`G(0) = 1` and dominant index `0` at radius `ρ`. -/
structure IsDominantFactorization (ρ : ℝ) (N : ℕ) (F : PowerSeries R) (P : R[X])
    (G : PowerSeries R) : Prop where
  natDegree : P.natDegree = N
  coeff_zero : P.coeff 0 = 1
  dominant : IsDominantPoly ρ P
  mulLeadingCoeff : TateFredholm.IsMultiplicative P.leadingCoeff
  entire : IsEntire G
  coeff_zero_G : coeff 0 G = 1
  lt_one : ∀ k, 0 < k → ‖coeff k G‖ * ρ ^ k < 1
  eq : F = (P : PowerSeries R) * G

omit [CompleteSpace R] in
/-- **[Bel] Proposition II.2.8's estimates (II.2.1)** at radius `ρ`: in a Euclidean division
`F = BQ + S` by a polynomial `B` whose leading coefficient is a multiplicative unit, the
remainder and the quotient are controlled by the dividend, `‖S‖_ρ ≤ ‖F‖_ρ` and
`‖B‖_ρ ‖Q‖_ρ ≤ ‖F‖_ρ` (Martin's `norm_eq_max_of_eq_mul_add_of_isMulDistinguished`). -/
theorem norm_coeff_r_mul_pow_le_of_eq_mul_add {ρ : ℝ} (hρ : 0 < ρ) {B : R[X]}
    (hB : IsDominantPoly ρ B) (hmul : TateFredholm.IsMultiplicative B.leadingCoeff)
    {F q : PowerSeries R} {r : R[X]} (hF : IsEntire F) (hq : IsEntire q)
    (hr : r.degree < B.degree) (hdiv : F = (B : PowerSeries R) * q + r) {M : ℝ}
    (hM : ∀ k, ‖coeff k F‖ * ρ ^ k ≤ M) (k : ℕ) : ‖r.coeff k‖ * ρ ^ k ≤ M := by
  have : Nontrivial R := NormOneClass.nontrivial
  haveI : Fact (0 < ρ) := ⟨hρ⟩
  have hBne : B ≠ 0 := fun h0 ↦ hB.2.ne_zero (by rw [h0, Polynomial.leadingCoeff_zero])
  have hrdeg : r.degree < (B.natDegree : WithBot ℕ) :=
    hr.trans_le (Polynomial.degree_eq_natDegree hBne).le
  have hf : restrictedOf (hF ρ hρ) =
      Polynomial.toRestricted ρ B * restrictedOf (hq ρ hρ) + Polynomial.toRestricted ρ r :=
    Subtype.ext hdiv
  calc ‖r.coeff k‖ * ρ ^ k ≤ ‖Polynomial.toRestricted ρ r‖ := by
        have := Restricted.norm_coeff_mul_pow_le ρ (Polynomial.toRestricted ρ r) k
        rwa [Polynomial.val_toRestricted, Polynomial.coeff_coe] at this
    _ ≤ ‖restrictedOf (hF ρ hρ)‖ :=
        Restricted.norm_toRestricted_le_of_eq_mul_add_of_isMulDistinguished
          (hB.isMulDistinguished hρ hmul) hrdeg hf
    _ ≤ M := (Restricted.norm_le_iff ρ _).2 hM

omit [CompleteSpace R] in
-- The Gauss norm of `X ^ N` at radius `ρ` is `ρ ^ N`.
private theorem norm_toRestricted_X_pow {ρ : ℝ} [Fact (0 < ρ)] (N : ℕ) :
    ‖Polynomial.toRestricted ρ (Polynomial.X ^ N : R[X])‖ = ρ ^ N := by
  have hρ : (0 : ℝ) < ρ := Fact.out
  refine le_antisymm ((Restricted.norm_le_iff ρ _).2 fun i ↦ ?_) ?_
  · rw [Polynomial.val_toRestricted, Polynomial.coeff_coe, Polynomial.coeff_X_pow]
    rcases eq_or_ne i N with rfl | hi
    · rw [if_pos rfl, norm_one, one_mul]
    · rw [if_neg hi, norm_zero, zero_mul]
      exact pow_nonneg hρ.le _
  · have h := Restricted.norm_coeff_mul_pow_le ρ
      (Polynomial.toRestricted ρ (Polynomial.X ^ N : R[X])) N
    rwa [Polynomial.val_toRestricted, Polynomial.coeff_coe, Polynomial.coeff_X_pow, if_pos rfl,
      norm_one, one_mul] at h

omit [IsUltrametricDist R] [CompleteSpace R] in
-- `X ^ N − r` with `deg r < N` is monic of degree `N`.
private theorem natDegree_X_pow_sub {r : R[X]} {N : ℕ} (hrdeg : r.degree < (N : WithBot ℕ)) :
    (Polynomial.X ^ N - r : R[X]).natDegree = N := by
  have : Nontrivial R := NormOneClass.nontrivial
  have h := Polynomial.degree_sub_eq_left_of_degree_lt
    (p := (Polynomial.X ^ N : R[X])) (q := r) (by rwa [Polynomial.degree_X_pow])
  rw [Polynomial.degree_X_pow] at h
  exact Polynomial.natDegree_eq_of_degree_eq_some h

omit [CompleteSpace R] in
-- `‖X ^ N − r‖_ρ = ρ ^ N` when the remainder is bounded by `ρ ^ N`.
private theorem norm_toRestricted_X_pow_sub {ρ : ℝ} [Fact (0 < ρ)] {r : R[X]} {N : ℕ}
    (hrdeg : r.degree < (N : WithBot ℕ)) (hr : ‖Polynomial.toRestricted ρ r‖ ≤ ρ ^ N) :
    ‖Polynomial.toRestricted ρ (Polynomial.X ^ N - r : R[X])‖ = ρ ^ N := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hmon : (Polynomial.X ^ N - r).Monic := Polynomial.monic_X_pow_sub hrdeg
  have hcoeffN : (Polynomial.X ^ N - r : R[X]).coeff N = 1 := by
    have h := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, natDegree_X_pow_sub hrdeg] at h
  refine le_antisymm ?_ ?_
  · rw [map_sub, sub_eq_add_neg]
    refine le_trans (Restricted.isNonarchimedean_norm R ρ _ _)
      (max_le (norm_toRestricted_X_pow N).le ?_)
    rwa [norm_neg]
  · have h := Restricted.norm_coeff_mul_pow_le ρ
      (Polynomial.toRestricted ρ (Polynomial.X ^ N - r : R[X])) N
    rwa [Polynomial.val_toRestricted, Polynomial.coeff_coe, hcoeffN, norm_one, one_mul] at h

-- **Weierstrass preparation from division** ([Mar16, Proposition 1.27] applied to `X ^ N`):
-- an entire series distinguished of order `N` at radius `ρ` is a monic polynomial of degree
-- `N` and norm `ρ ^ N` times an entire series, and the constant term of the polynomial is
-- bounded by `‖a_N‖⁻¹` (it is the constant term of the Weierstrass quotient of `X ^ N`).
private theorem exists_monic_mul_eq_of_isMulDistinguished {ρ : ℝ} [Fact (0 < ρ)]
    {F : PowerSeries R} (hF : IsEntire F) (hF0 : coeff 0 F = 1) {N : ℕ}
    (hFd : IsMulDistinguished ρ F N) :
    ∃ (P₀ : R[X]) (G₀ : PowerSeries R), P₀.Monic ∧ P₀.natDegree = N ∧ IsEntire G₀ ∧
      F = (P₀ : PowerSeries R) * G₀ ∧ ‖Polynomial.toRestricted ρ P₀‖ = ρ ^ N ∧
      ‖P₀.coeff 0‖ * (‖coeff N F‖ * ρ ^ N) ≤ ρ ^ N := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hρ : (0 : ℝ) < ρ := Fact.out
  have hFnorm : ‖restrictedOf (hF ρ hρ)‖ = ‖coeff N F‖ * ρ ^ N := hFd.gaussNorm_eq
  obtain ⟨q, r, hrdeg, hdiv⟩ := Restricted.weierstrassDivision_exists_of_isMulDistinguished
    (g := restrictedOf (hF ρ hρ)) hFd (Polynomial.toRestricted ρ (Polynomial.X ^ N : R[X]))
  have hmon : (Polynomial.X ^ N - r).Monic := Polynomial.monic_X_pow_sub hrdeg
  have hdegP : (Polynomial.X ^ N - r : R[X]).natDegree = N := natDegree_X_pow_sub hrdeg
  have hPeq : Polynomial.toRestricted ρ (Polynomial.X ^ N - r) = restrictedOf (hF ρ hρ) * q := by
    rw [map_sub, hdiv]
    abel
  have hnormP : ‖Polynomial.toRestricted ρ (Polynomial.X ^ N - r : R[X])‖ = ρ ^ N := by
    refine norm_toRestricted_X_pow_sub hrdeg ?_
    rw [← norm_toRestricted_X_pow (R := R) (ρ := ρ) N]
    exact Restricted.norm_toRestricted_le_of_eq_mul_add_of_isMulDistinguished hFd hrdeg hdiv
  obtain ⟨G₀, r', hG₀, hr'deg, hdiv'⟩ := hF.exists_eq_mul_add
    (B := Polynomial.X ^ N - r) (by rw [hmon.leadingCoeff]; exact isUnit_one)
  have hr'N : r'.degree < (N : WithBot ℕ) := by
    rwa [Polynomial.degree_eq_natDegree hmon.ne_zero, hdegP] at hr'deg
  have hdivR : restrictedOf (hF ρ hρ) =
      restrictedOf (hF ρ hρ) * (q * restrictedOf (hG₀ ρ hρ)) + Polynomial.toRestricted ρ r' := by
    rw [← mul_assoc, ← hPeq]
    exact Subtype.ext hdiv'
  have hone : restrictedOf (hF ρ hρ) =
      restrictedOf (hF ρ hρ) * 1 + Polynomial.toRestricted ρ 0 := by
    rw [mul_one, map_zero, add_zero]
  have hr'0 : r' = 0 := Restricted.weierstrassDivision_r_unique_of_isMulDistinguished hFd hr'N
    hdivR (by rw [Polynomial.degree_zero]; exact bot_lt_iff_ne_bot.2 (by simp)) hone
  refine ⟨Polynomial.X ^ N - r, G₀, hmon, hdegP, hG₀, by rw [hdiv', hr'0, Polynomial.coe_zero,
    add_zero], hnormP, ?_⟩
  have hq0 : (Polynomial.X ^ N - r : R[X]).coeff 0 = coeff 0 q.1 := by
    have h : ((Polynomial.X ^ N - r : R[X]) : PowerSeries R) = F * q.1 := congrArg Subtype.val hPeq
    have h2 := congrArg (coeff 0) h
    rw [Polynomial.coeff_coe, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hF0, one_mul] at h2
    exact h2
  calc ‖(Polynomial.X ^ N - r : R[X]).coeff 0‖ * (‖coeff N F‖ * ρ ^ N)
      = (‖coeff 0 q.1‖ * ρ ^ 0) * ‖restrictedOf (hF ρ hρ)‖ := by
        rw [hq0, hFnorm, pow_zero, mul_one]
    _ ≤ ‖q‖ * ‖restrictedOf (hF ρ hρ)‖ :=
        mul_le_mul_of_nonneg_right (Restricted.norm_coeff_mul_pow_le ρ q 0) (norm_nonneg _)
    _ = ρ ^ N := by
        rw [mul_comm, ← Restricted.norm_mul_of_isMulDistinguished hFd q, ← hPeq, hnormP]

-- The cofactor of the Weierstrass preparation has dominant index `0`, with constant term of
-- norm `‖a_N‖`: if the greatest achieving index `k₀` of the cofactor were positive, the
-- product would achieve its Gauss norm at `N + k₀ > N` ([Mar16, Lemma 1.26(2)]), contradicting
-- the strict domination of the index `N` in `F`.
omit [CompleteSpace R] in
private theorem isDominantIndex_zero_of_monic_mul {ρ : ℝ} [Fact (0 < ρ)] {F : PowerSeries R}
    (hF : IsEntire F) {N : ℕ} (hFd : IsMulDistinguished ρ F N) {P₀ : R[X]} {G₀ : PowerSeries R}
    (hmon : P₀.Monic) (hdeg : P₀.natDegree = N) (hG₀ : IsEntire G₀)
    (hFeq : F = (P₀ : PowerSeries R) * G₀) (hnormP₀ : ‖Polynomial.toRestricted ρ P₀‖ = ρ ^ N) :
    IsDominantIndex ρ G₀ 0 ∧ ‖coeff 0 G₀‖ = ‖coeff N F‖ := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hρ : (0 : ℝ) < ρ := Fact.out
  have hcoeffN : P₀.coeff N = 1 := by
    have h := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at h
  have hP₀d : IsMulDistinguished ρ (Polynomial.toRestricted ρ P₀).1 N :=
    Restricted.isMulDistinguished_toRestricted_of_monic hmon
      (by rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg]) hnormP₀
  have hmulR : Polynomial.toRestricted ρ P₀ * restrictedOf (hG₀ ρ hρ) = restrictedOf (hF ρ hρ) :=
    Subtype.ext hFeq.symm
  have hFnorm : ‖restrictedOf (hF ρ hρ)‖ = ‖coeff N F‖ * ρ ^ N := hFd.gaussNorm_eq
  have haN : 0 < ‖coeff N F‖ := norm_pos_iff.2 hFd.isNormMulUnit_coeff.isUnit.ne_zero
  have hgnorm : ‖restrictedOf (hG₀ ρ hρ)‖ = ‖coeff N F‖ := by
    have h := Restricted.norm_mul_of_isMulDistinguished hP₀d (restrictedOf (hG₀ ρ hρ))
    rw [hmulR, hFnorm, hnormP₀] at h
    exact mul_left_cancel₀ (pow_pos hρ N).ne' (by rw [← h]; ring)
  have hgne : restrictedOf (hG₀ ρ hρ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hgnorm
    exact haN.ne hgnorm
  obtain ⟨k₀, hk₀, hk₀max⟩ := Restricted.exists_greatest_achievesGaussNorm
    (restrictedOf (hG₀ ρ hρ)) hgne
  have hk₀eq : ‖coeff k₀ G₀‖ * ρ ^ k₀ = ‖coeff N F‖ :=
    (hk₀.trans (Restricted.norm_def ρ _).symm).trans hgnorm
  have hk₀0 : k₀ = 0 := by
    by_contra hne
    have hcoeff := Restricted.norm_coeff_add_mul_of_isMulDistinguished hP₀d hk₀ hk₀max
    rw [hmulR, Polynomial.val_toRestricted, Polynomial.coeff_coe, hcoeffN, norm_one, one_mul]
      at hcoeff
    have hcoeff' : ‖coeff (N + k₀) F‖ = ‖coeff k₀ G₀‖ := hcoeff
    have hlt := hFd.gaussTerm_lt (N + k₀) (by omega)
    rw [hcoeff', pow_add, show ‖coeff k₀ G₀‖ * (ρ ^ N * ρ ^ k₀) =
      ‖coeff k₀ G₀‖ * ρ ^ k₀ * ρ ^ N from by ring, hk₀eq] at hlt
    exact absurd rfl hlt.ne
  subst hk₀0
  rw [pow_zero, mul_one] at hk₀eq
  refine ⟨⟨fun k ↦ ?_, fun k hk ↦ ?_⟩, hk₀eq⟩
  · rw [pow_zero, mul_one, hk₀eq, ← hgnorm]
    exact Restricted.norm_coeff_mul_pow_le ρ (restrictedOf (hG₀ ρ hρ)) k
  · rw [pow_zero, mul_one, hk₀eq, ← hgnorm]
    exact hk₀max k hk

-- The normalisation `P(0) = G(0) = 1` of a Weierstrass preparation `F = P₀ G₀`: multiply the
-- monic factor by `G₀(0)` and the cofactor by `P₀(0)`, which are mutually inverse.
omit [CompleteSpace R] in
-- Rescaling a monic polynomial of degree `N` and norm `ρ ^ N` by a unit keeps it `ρ`-dominant
-- of degree `N`, with the unit as leading coefficient.
private theorem isDominantPoly_C_mul {ρ : ℝ} [Fact (0 < ρ)] {P₀ : R[X]} {N : ℕ} {d : R}
    (hmon : P₀.Monic) (hdeg : P₀.natDegree = N)
    (hnormP₀ : ‖Polynomial.toRestricted ρ P₀‖ = ρ ^ N) (hd : IsUnit d) :
    (Polynomial.C d * P₀).natDegree = N ∧ (Polynomial.C d * P₀).leadingCoeff = d ∧
      IsDominantIndex ρ ((Polynomial.C d * P₀ : R[X]) : PowerSeries R) N := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hρ : (0 : ℝ) < ρ := Fact.out
  have hcoeffN : P₀.coeff N = 1 := by
    have h := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at h
  have hP₀bound : ∀ k, ‖P₀.coeff k‖ * ρ ^ k ≤ ρ ^ N := fun k ↦ by
    have h := Restricted.norm_coeff_mul_pow_le ρ (Polynomial.toRestricted ρ P₀) k
    rwa [Polynomial.val_toRestricted, Polynomial.coeff_coe, hnormP₀] at h
  have hPdeg : (Polynomial.C d * P₀).natDegree = N := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun M hM ↦ ?_) ?_
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ hM), mul_zero]
    · rw [Polynomial.coeff_C_mul, hcoeffN, mul_one]
      exact hd.ne_zero
  refine ⟨hPdeg, by rw [Polynomial.leadingCoeff, hPdeg, Polynomial.coeff_C_mul, hcoeffN, mul_one],
    fun k ↦ ?_, fun k hk ↦ ?_⟩
  · rw [Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, hcoeffN, mul_one]
    calc ‖d * P₀.coeff k‖ * ρ ^ k ≤ ‖d‖ * (‖P₀.coeff k‖ * ρ ^ k) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (pow_nonneg hρ.le k)
      _ ≤ ‖d‖ * ρ ^ N := mul_le_mul_of_nonneg_left (hP₀bound k) (norm_nonneg _)
  · rw [Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, hcoeffN, mul_one,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ hk), mul_zero, norm_zero, zero_mul]
    exact mul_pos (norm_pos_iff.2 hd.ne_zero) (pow_pos hρ N)

omit [CompleteSpace R] in
private theorem isDominantFactorization_C_mul {ρ : ℝ} [Fact (0 < ρ)] {F : PowerSeries R}
    {N : ℕ} {P₀ : R[X]} {G₀ : PowerSeries R} (hmon : P₀.Monic) (hdeg : P₀.natDegree = N)
    (hG₀ : IsEntire G₀) (hFeq : F = (P₀ : PowerSeries R) * G₀)
    (hnormP₀ : ‖Polynomial.toRestricted ρ P₀‖ = ρ ^ N) (hdom : IsDominantIndex ρ G₀ 0)
    (hG₀0 : ‖coeff 0 G₀‖ = ‖coeff N F‖) (hcd : P₀.coeff 0 * coeff 0 G₀ = 1)
    (hcnorm : ‖P₀.coeff 0‖ * ‖coeff N F‖ = 1) :
    IsDominantFactorization ρ N F (Polynomial.C (coeff 0 G₀) * P₀)
      (PowerSeries.C (P₀.coeff 0) * G₀) := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hρ : (0 : ℝ) < ρ := Fact.out
  have hcunit : IsUnit (P₀.coeff 0) :=
    isUnit_iff_exists.2 ⟨coeff 0 G₀, hcd, by rw [mul_comm]; exact hcd⟩
  have hdunit : IsUnit (coeff 0 G₀) :=
    isUnit_iff_exists.2 ⟨P₀.coeff 0, by rw [mul_comm]; exact hcd, hcd⟩
  obtain ⟨hPdeg, hlead, hPdom⟩ := isDominantPoly_C_mul hmon hdeg hnormP₀ hdunit
  have hmulP : TateFredholm.IsMultiplicative (Polynomial.C (coeff 0 G₀) * P₀).leadingCoeff := by
    rw [hlead]
    have hdc : coeff 0 G₀ * P₀.coeff 0 = 1 := by rw [mul_comm]; exact hcd
    have hnorm : ‖(((⟨coeff 0 G₀, P₀.coeff 0, hdc, hcd⟩ : Rˣ)⁻¹ : Rˣ) : R)‖ =
        ‖((⟨coeff 0 G₀, P₀.coeff 0, hdc, hcd⟩ : Rˣ) : R)‖⁻¹ := by
      show ‖P₀.coeff 0‖ = ‖coeff 0 G₀‖⁻¹
      rw [hG₀0]
      exact eq_inv_of_mul_eq_one_left hcnorm
    exact (isNormMulUnit_of_norm_coe_inv_units hnorm).2
  refine ⟨hPdeg, ?_, ⟨hPdeg ▸ hPdom, by rw [hlead]; exact hdunit⟩, hmulP,
    (isEntire_C _).mul hG₀, ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_C_mul, mul_comm]
    exact hcd
  · rw [PowerSeries.coeff_C_mul]
    exact hcd
  · intro k hk
    have hlt : ‖coeff k G₀‖ * ρ ^ k < ‖coeff N F‖ := by
      have h := hdom.2 k hk
      rwa [pow_zero, mul_one, hG₀0] at h
    calc ‖coeff k (PowerSeries.C (P₀.coeff 0) * G₀)‖ * ρ ^ k
        ≤ ‖P₀.coeff 0‖ * (‖coeff k G₀‖ * ρ ^ k) := by
          rw [PowerSeries.coeff_C_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (pow_nonneg hρ.le k)
      _ < ‖P₀.coeff 0‖ * ‖coeff N F‖ :=
          mul_lt_mul_of_pos_left hlt (norm_pos_iff.2 hcunit.ne_zero)
      _ = 1 := hcnorm
  · rw [Polynomial.coe_mul, Polynomial.coe_C, mul_comm (PowerSeries.C (coeff 0 G₀)),
      mul_assoc, ← mul_assoc (PowerSeries.C (coeff 0 G₀)), ← map_mul, mul_comm (coeff 0 G₀),
      hcd, map_one, one_mul, ← hFeq]

/-- **The vertex factorisation** ([Bel] Theorem II.3.6, existence; [Ke09] Proposition 3.2.2;
[LWX] Remark 3.25 "a standard factorization argument"): an entire Fredholm series whose
dominant coefficient at radius `ρ` is a multiplicative unit factors as `P·G` with `P` a
`ρ`-dominant polynomial of degree the dominant index and `G` of dominant index `0`.  Proved by
Weierstrass preparation — divide `T^N` by `F` ([Mar16] Proposition 1.27) — rather than by
[Bel]'s Newton iteration; the normalisation `P(0) = G(0) = 1` uses that the constant term of
the monic factor has norm exactly `‖a_N‖⁻¹`. -/
theorem exists_isDominantFactorization {ρ : ℝ} (hρ : 0 < ρ) {F : PowerSeries R}
    (hF : IsEntire F) (hF0 : coeff 0 F = 1) {N : ℕ} (hN : IsDominantIndex ρ F N)
    (hunit : IsUnit (coeff N F)) (hmul : TateFredholm.IsMultiplicative (coeff N F)) :
    ∃ (P : R[X]) (G : PowerSeries R), IsDominantFactorization ρ N F P G := by
  have : Nontrivial R := NormOneClass.nontrivial
  haveI : Fact (0 < ρ) := ⟨hρ⟩
  have hFd : IsMulDistinguished ρ F N :=
    ⟨⟨hunit, hmul⟩, norm_of_isDominantIndex (f := restrictedOf (hF ρ hρ)) hN, hN.2⟩
  obtain ⟨P₀, G₀, hmon, hdeg, hG₀, hFeq, hnormP₀, hbound⟩ :=
    exists_monic_mul_eq_of_isMulDistinguished hF hF0 hFd
  obtain ⟨hG₀dom, hG₀0⟩ := isDominantIndex_zero_of_monic_mul hF hFd hmon hdeg hG₀ hFeq hnormP₀
  have hcd : P₀.coeff 0 * coeff 0 G₀ = 1 := by
    have h : PowerSeries.constantCoeff F =
        PowerSeries.constantCoeff (P₀ : PowerSeries R) * PowerSeries.constantCoeff G₀ := by
      rw [hFeq, map_mul]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hF0] at h
    exact h.symm
  have hcnorm : ‖P₀.coeff 0‖ * ‖coeff N F‖ = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← mul_assoc] at hbound
      exact le_of_mul_le_mul_right (by rw [one_mul]; exact hbound) (pow_pos hρ N)
    · calc (1 : ℝ) = ‖P₀.coeff 0 * coeff 0 G₀‖ := by rw [hcd, norm_one]
        _ ≤ ‖P₀.coeff 0‖ * ‖coeff 0 G₀‖ := norm_mul_le _ _
        _ = ‖P₀.coeff 0‖ * ‖coeff N F‖ := by rw [hG₀0]
  exact ⟨_, _, isDominantFactorization_C_mul hmon hdeg hG₀ hFeq hnormP₀ hG₀dom hG₀0 hcd hcnorm⟩

/-- **Norm-level [JN] Lemma 2.2.7** ("Let `S` be a Fredholm series of slope `> h` and `Q` a
multiplicative polynomial of slope `≤ h`. Then `Q` and `S` are relatively prime"): the factors
of a dominant factorisation are relatively prime in `R{{T}}`.  Proof by Weierstrass division at
radius `ρ` instead of Coleman's resultant: `G` is a unit of `R⟨ρ⁻¹T⟩` (`‖G − 1‖_ρ < 1`), so its
remainder `r` modulo `P` satisfies `1 − rG = P·(entire)` — the cofactor is entire because the
entire division of `1 − rG` by `P` has the same quotient, by uniqueness at radius `ρ`. -/
theorem IsDominantFactorization.isEntireCoprime {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ}
    {F : PowerSeries R} {P : R[X]} {G : PowerSeries R} (h : IsDominantFactorization ρ N F P G) :
    IsEntireCoprime (P : PowerSeries R) G := by
  have : Nontrivial R := NormOneClass.nontrivial
  haveI : Fact (0 < ρ) := ⟨hρ⟩
  have hPne : P ≠ 0 := fun h0 ↦ h.dominant.2.ne_zero (by rw [h0, Polynomial.leadingCoeff_zero])
  have hPdegN : P.degree = (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hPne, h.natDegree]
  have hPd : IsMulDistinguished ρ (Polynomial.toRestricted ρ P).1 N :=
    h.natDegree ▸ h.dominant.isMulDistinguished hρ h.mulLeadingCoeff
  have hlt : ‖1 - restrictedOf (h.entire ρ hρ)‖ < 1 := by
    refine (Restricted.norm_lt_iff ρ _).2 fun i ↦ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h0 : coeff 0 ((1 : Restricted R ρ) - restrictedOf (h.entire ρ hρ)).1 = 0 := by
        show coeff 0 ((1 : PowerSeries R) - G) = 0
        rw [map_sub, PowerSeries.coeff_zero_one, h.coeff_zero_G, sub_self]
      rw [h0, norm_zero, zero_mul]
      exact zero_lt_one
    · have hc : coeff i ((1 : Restricted R ρ) - restrictedOf (h.entire ρ hρ)).1 = -coeff i G := by
        show coeff i ((1 : PowerSeries R) - G) = -coeff i G
        rw [map_sub, PowerSeries.coeff_one, if_neg hi.ne', zero_sub]
      rw [hc, norm_neg]
      exact h.lt_one i hi
  obtain ⟨u, hu⟩ : IsUnit (restrictedOf (h.entire ρ hρ)) := by
    simpa using isUnit_one_sub_of_norm_lt_one hlt
  obtain ⟨q, r, hrdeg, hdiv⟩ := Restricted.weierstrassDivision_exists_of_isMulDistinguished hPd
    ((u⁻¹ : (Restricted R ρ)ˣ) : Restricted R ρ)
  have hone : (1 : Restricted R ρ) = Polynomial.toRestricted ρ P * (q * restrictedOf
      (h.entire ρ hρ)) + Polynomial.toRestricted ρ r * restrictedOf (h.entire ρ hρ) := by
    rw [← mul_assoc, ← add_mul, ← hdiv, ← hu, Units.inv_mul]
  have hent : IsEntire ((1 : PowerSeries R) - (r : PowerSeries R) * G) :=
    isEntire_one.sub ((Polynomial.isEntire_coe r).mul h.entire)
  obtain ⟨c, sPoly, hc, hsdeg, hcs⟩ := hent.exists_eq_mul_add (B := P) h.dominant.2
  have hdiv₁ : restrictedOf (hent ρ hρ) =
      Polynomial.toRestricted ρ P * (q * restrictedOf (h.entire ρ hρ)) +
        Polynomial.toRestricted ρ 0 := by
    have hone' : (1 : PowerSeries R) =
      (P : PowerSeries R) * (q.1 * G) + (r : PowerSeries R) * G := congrArg Subtype.val hone
    refine Subtype.ext ?_
    show (1 : PowerSeries R) - (r : PowerSeries R) * G =
      ((P : PowerSeries R) * (q.1 * G) + ((0 : R[X]) : PowerSeries R))
    rw [Polynomial.coe_zero, add_zero, sub_eq_iff_eq_add]
    exact hone'
  have hdiv₂ : restrictedOf (hent ρ hρ) =
      Polynomial.toRestricted ρ P * restrictedOf (hc ρ hρ) + Polynomial.toRestricted ρ sPoly :=
    Subtype.ext hcs
  have hs0 : (0 : R[X]) = sPoly :=
    Restricted.weierstrassDivision_r_unique_of_isMulDistinguished hPd
      (by rw [Polynomial.degree_zero]; exact bot_lt_iff_ne_bot.2 (by simp)) hdiv₁
      (hPdegN ▸ hsdeg) hdiv₂
  refine ⟨c, (r : PowerSeries R), hc, Polynomial.isEntire_coe r, ?_⟩
  rw [← hs0, Polynomial.coe_zero, add_zero] at hcs
  rw [mul_comm c, ← hcs]
  ring

end PowerSeries

end
