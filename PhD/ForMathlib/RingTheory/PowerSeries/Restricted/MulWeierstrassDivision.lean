/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Martin.Distinguished
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.WeierstrassDivision

/-! # Weierstrass division at every radius over an ultrametric Banach ring

[Mar16, Proposition 1.27]: for `g` Martin-distinguished of order `s` in `A{c⁻¹T}` — `A`
any ultrametric complete normed ring, `c > 0` any radius — every `f` divides uniquely as
`f = g * q + r` with `deg r < s`, and `‖f‖ = max (‖g‖ * ‖q‖) ‖r‖`.

The proof is Martin's: the norm identity (1.8) follows from Lemma 1.26 and gives
uniqueness and the bounds; existence truncates the divisor to a polynomial `g'` with
invertible leading coefficient, divides Euclideanly, and iterates the resulting
one-step approximation (1.11), whose error contracts by the tail factor `θ < 1` —
strict dominance is needed **above** the distinguished degree only, so no hypothesis on
the radius ever enters.  The limit lives in `divisionSet g s`, which is closed by the
bounds (reusing the project's `NormMulClass`-free closure machinery).

Source: F. Martin, J. EMS 18 (2016), §1.3.
-/

namespace PowerSeries.Restricted

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] {c : ℝ} [Fact (0 < c)]

/-- The lower bound of [Mar16, (1.8)]: in a Weierstrass division `f = g * q + r` by a
Martin-distinguished `g`, the norm of `f` dominates both `‖g‖ * ‖q‖ = ‖g * q‖` and
`‖r‖`. -/
theorem max_norm_le_of_eq_mul_add_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) {f q : Restricted A c} {r : Polynomial A}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toRestricted c r) :
    max (‖g‖ * ‖q‖) ‖Polynomial.toRestricted c r‖ ≤ ‖f‖ := by
  by_cases hq0 : q = 0
  · subst hq0
    rw [mul_zero, zero_add] at hf
    rw [hf, norm_zero, mul_zero]
    exact max_le (norm_nonneg _) le_rfl
  obtain ⟨k₀, hk, hkmax⟩ := exists_greatest_achievesGaussNorm q hq0
  have h_peak : ‖coeff (s + k₀) (g * q).1‖ * c ^ (s + k₀) = ‖g‖ * ‖q‖ := by
    calc ‖coeff (s + k₀) (g * q).1‖ * c ^ (s + k₀)
        = (‖coeff s g.1‖ * ‖coeff k₀ q.1‖) * c ^ (s + k₀) := by
          rw [norm_coeff_add_mul_of_isMulDistinguished hg hk hkmax]
      _ = (‖coeff s g.1‖ * c ^ s) * (‖coeff k₀ q.1‖ * c ^ k₀) := by rw [pow_add]; ring
      _ = ‖g‖ * ‖q‖ := by
          rw [hg.toIsDistinguished.norm_coeff_mul_pow_eq, hk.trans (norm_def c q).symm]
  have h_toR_zero : coeff (s + k₀) (Polynomial.toRestricted c r).1 = 0 := by
    rw [Polynomial.val_toRestricted, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt (hr.trans_le (mod_cast Nat.le_add_right s k₀))
  have h_coeff_f : ‖coeff (s + k₀) f.1‖ * c ^ (s + k₀) = ‖g‖ * ‖q‖ := by
    rw [show f.1 = (g * q).1 + (Polynomial.toRestricted c r).1 from by rw [hf]; rfl,
      map_add, h_toR_zero, add_zero]
    exact h_peak
  have h_gq_bd : ‖g‖ * ‖q‖ ≤ ‖f‖ := by
    rw [← h_coeff_f]
    exact norm_coeff_mul_pow_le c f (s + k₀)
  have h_gq_bd' : ‖g * q‖ ≤ ‖f‖ := (norm_mul_of_isMulDistinguished hg q).le.trans h_gq_bd
  refine max_le h_gq_bd ?_
  rw [show Polynomial.toRestricted c r = f - g * q from by rw [hf]; abel]
  refine (?_ : ‖f - g * q‖ ≤ max ‖f‖ ‖g * q‖).trans (max_le le_rfl h_gq_bd')
  simpa [norm_neg, sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max f (-(g * q))

/-- **[Mar16, (1.8)]**: the norm identity of the Weierstrass division,
`‖f‖ = max (‖g‖ * ‖q‖) ‖r‖`. -/
theorem norm_eq_max_of_eq_mul_add_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) {f q : Restricted A c} {r : Polynomial A}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toRestricted c r) :
    ‖f‖ = max (‖g‖ * ‖q‖) ‖Polynomial.toRestricted c r‖ := by
  refine le_antisymm ?_ (max_norm_le_of_eq_mul_add_of_isMulDistinguished hg hr hf)
  rw [hf, ← norm_mul_of_isMulDistinguished hg q]
  exact IsUltrametricDist.norm_add_le_max _ _

/-- The quotient bound: `‖q‖ ≤ ‖g‖⁻¹ * ‖f‖`. -/
theorem norm_q_le_of_eq_mul_add_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) {f q : Restricted A c} {r : Polynomial A}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toRestricted c r) :
    ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by
  rw [le_inv_mul_iff₀ hg.toIsDistinguished.norm_pos]
  exact (le_max_left _ _).trans (max_norm_le_of_eq_mul_add_of_isMulDistinguished hg hr hf)

/-- The remainder bound: `‖r‖ ≤ ‖f‖`. -/
theorem norm_toRestricted_le_of_eq_mul_add_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) {f q : Restricted A c} {r : Polynomial A}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toRestricted c r) :
    ‖Polynomial.toRestricted c r‖ ≤ ‖f‖ :=
  (le_max_right _ _).trans (max_norm_le_of_eq_mul_add_of_isMulDistinguished hg hr hf)

/-- Uniqueness of the Weierstrass quotient.  Source: [Mar16, Proposition 1.27],
uniqueness paragraph. -/
theorem weierstrassDivision_q_unique_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) {f : Restricted A c}
    {q₁ q₂ : Restricted A c} {r₁ r₂ : Polynomial A}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + Polynomial.toRestricted c r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + Polynomial.toRestricted c r₂) :
    q₁ = q₂ := by
  have h0 : (0 : Restricted A c) = g * (q₁ - q₂) + Polynomial.toRestricted c (r₁ - r₂) := by
    rw [map_sub]
    linear_combination hf₁ - hf₂
  have h_bd := norm_q_le_of_eq_mul_add_of_isMulDistinguished hg
    ((Polynomial.degree_sub_le _ _).trans_lt (max_lt hr₁ hr₂)) h0
  rwa [norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] at h_bd

/-- Uniqueness of the Weierstrass remainder. -/
theorem weierstrassDivision_r_unique_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) {f : Restricted A c}
    {q₁ q₂ : Restricted A c} {r₁ r₂ : Polynomial A}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + Polynomial.toRestricted c r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + Polynomial.toRestricted c r₂) :
    r₁ = r₂ := by
  obtain rfl : q₁ = q₂ :=
    weierstrassDivision_q_unique_of_isMulDistinguished hg hr₁ hf₁ hr₂ hf₂
  exact Polynomial.toRestricted_injective c (add_left_cancel (hf₁.symm.trans hf₂))

/-- Euclidean division by a polynomial with invertible (not necessarily `1`) leading
coefficient, via `Polynomial.modByMonic` after unit-rescaling.  Source: [Mar16, proof of
Proposition 1.27], "one can carry out euclidean division by `g'` [Lan02, 4.1.1]". -/
theorem _root_.Polynomial.exists_eq_mul_add_of_isUnit_leadingCoeff {R : Type*} [CommRing R]
    [Nontrivial R] {g₀ : Polynomial R} (hu : IsUnit g₀.leadingCoeff) (f₀ : Polynomial R) :
    ∃ q r : Polynomial R, r.degree < g₀.degree ∧ f₀ = g₀ * q + r := by
  obtain ⟨u, hu_eq⟩ := hu
  have hb : (↑u⁻¹ : R) * g₀.leadingCoeff = 1 := by rw [← hu_eq]; exact u.inv_mul
  set h := Polynomial.C (↑u⁻¹ : R) * g₀ with hh_def
  have hmonic : h.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one hb
  have hdeg : h.degree ≤ g₀.degree := by
    rw [hh_def, ← Polynomial.smul_eq_C_mul]
    exact Polynomial.degree_smul_le _ _
  refine ⟨Polynomial.C (↑u⁻¹ : R) * (f₀ /ₘ h), f₀ %ₘ h, ?_, ?_⟩
  · exact lt_of_lt_of_le (Polynomial.degree_modByMonic_lt f₀ hmonic) hdeg
  · have hgq : g₀ * (Polynomial.C (↑u⁻¹ : R) * (f₀ /ₘ h)) = h * (f₀ /ₘ h) := by
      rw [hh_def]; ring
    rw [hgq, add_comm (h * (f₀ /ₘ h)) (f₀ %ₘ h)]
    exact (Polynomial.modByMonic_add_div f₀ h).symm

/-- The contraction factor: the tail of a Martin-distinguished series beyond the
distinguished degree is `θ`-small relative to `‖g‖`, for some `θ < 1`.  Source: [Mar16,
proof of Proposition 1.27], "`κ := max_{m>s}(‖g_m‖r^m)/‖g‖ < 1`; if `κ = 0` replace it
by `1/2`". -/
lemma exists_lt_one_norm_sub_toRestricted_trunc_le_of_isMulDistinguished
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ‖g - Polynomial.toRestricted c (trunc (s + 1) g.1)‖ ≤ θ * ‖g‖ := by
  set d := g - Polynomial.toRestricted c (trunc (s + 1) g.1) with hd_def
  have hg_pos : 0 < ‖g‖ := hg.toIsDistinguished.norm_pos
  have hd_coeff : ∀ k, coeff k d.1 = if k < s + 1 then 0 else coeff k g.1 := by
    intro k
    rw [hd_def, show (g - Polynomial.toRestricted c (trunc (s + 1) g.1)).1
        = g.1 - (Polynomial.toRestricted c (trunc (s + 1) g.1)).1 from rfl, map_sub,
      Polynomial.val_toRestricted, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hk
    · exact sub_self _
    · exact sub_zero _
  rcases eq_or_ne d 0 with hd | hd
  · exact ⟨1 / 2, by norm_num, by norm_num,
      by rw [hd, norm_zero]; exact mul_nonneg (by norm_num) (norm_nonneg g)⟩
  · obtain ⟨t, ht_ne, ht_eq⟩ := exists_coeff_ne_zero_norm_eq c d hd
    have ht_gt : s < t := by
      by_contra h
      exact ht_ne (by rw [hd_coeff t, if_pos (by omega)])
    have ht_coeff : coeff t d.1 = coeff t g.1 := by rw [hd_coeff t, if_neg (by omega)]
    have hd_lt : ‖d‖ < ‖g‖ := by
      rw [ht_eq, ht_coeff]
      exact (hg.gaussTerm_lt t ht_gt).trans_eq hg.toIsDistinguished.norm_coeff_mul_pow_eq
    refine ⟨max (1 / 2) (‖d‖ / ‖g‖), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
      max_lt (by norm_num) ((div_lt_one hg_pos).mpr hd_lt), ?_⟩
    calc ‖d‖ = ‖d‖ / ‖g‖ * ‖g‖ := (div_mul_cancel₀ ‖d‖ hg_pos.ne').symm
      _ ≤ max (1 / 2) (‖d‖ / ‖g‖) * ‖g‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg g)

/-- **[Mar16, (1.11)]**, the one-step approximate division: truncate `f`, divide
Euclideanly by the truncated divisor, and control the error by `θ * ‖f‖`. -/
lemma exists_approx_div_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) {θ : ℝ} (hθ0 : 0 < θ) (_hθ1 : θ < 1)
    (hθ : ‖g - Polynomial.toRestricted c (trunc (s + 1) g.1)‖ ≤ θ * ‖g‖)
    (f : Restricted A c) :
    ∃ (q : Restricted A c) (r : Polynomial A), r.degree < s ∧
      ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ ∧
      ‖f - (g * q + Polynomial.toRestricted c r)‖ ≤ θ * ‖f‖ := by
  haveI hntA : Nontrivial A := hg.toIsDistinguished.nontrivial
  have hg_pos : 0 < ‖g‖ := hg.toIsDistinguished.norm_pos
  by_cases hf0 : f = 0
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · simp
    · rw [norm_zero]; exact mul_nonneg (inv_nonneg.mpr (norm_nonneg g)) (norm_nonneg f)
    · simp [hf0]
  · have hf_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
    -- The truncated polynomial divisor `g'p` and its degree bookkeeping.
    set g'p : Polynomial A := trunc (s + 1) g.1 with hg'p_def
    have hcsp : g'p.coeff s = coeff s g.1 := by
      rw [hg'p_def, PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self s)]
    have hcsp_ne : g'p.coeff s ≠ 0 := by
      rw [hcsp]; exact hg.isNormMulUnit_coeff.isUnit.ne_zero
    have hg'p_deg : g'p.degree = (s : WithBot ℕ) := by
      refine le_antisymm ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm => ?_)
        (Polynomial.le_degree_of_ne_zero hcsp_ne)
      have hsm : s < m := by exact_mod_cast hm
      rw [hg'p_def, PowerSeries.coeff_trunc]
      exact if_neg (by omega)
    have hlead_unit : IsUnit g'p.leadingCoeff := by
      have hlead : g'p.leadingCoeff = coeff s g.1 :=
        (congrArg g'p.coeff (Polynomial.natDegree_eq_of_degree_eq_some hg'p_deg)).trans hcsp
      rw [hlead]; exact hg.isNormMulUnit_coeff.isUnit
    -- The truncated divisor as a restricted series: distinguished of the same order and norm.
    set g' : Restricted A c := Polynomial.toRestricted c g'p with hg'_def
    have hg'_dist : IsMulDistinguished c g'.1 s := by
      rw [hg'_def, hg'p_def]; exact isMulDistinguished_toRestricted_trunc hg
    have hg'_norm : ‖g'‖ = ‖g‖ := by
      have hcoeff_s : coeff s g'.1 = coeff s g.1 := by
        rw [hg'_def, hg'p_def, Polynomial.val_toRestricted, Polynomial.coeff_coe,
          PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self s)]
      rw [← hg'_dist.toIsDistinguished.norm_coeff_mul_pow_eq, hcoeff_s,
        hg.toIsDistinguished.norm_coeff_mul_pow_eq]
    -- Truncate the dividend to a polynomial `f'p` close to `f` in Gauss norm.
    obtain ⟨N, hN⟩ := exists_norm_sub_toRestricted_trunc_le f (mul_pos hθ0 hf_pos)
    set f'p : Polynomial A := trunc N f.1 with hf'p_def
    set f' : Restricted A c := Polynomial.toRestricted c f'p with hf'_def
    -- Euclidean division of the truncated dividend by the truncated divisor.
    obtain ⟨qp, rp, hrp_deg, heq⟩ :=
      Polynomial.exists_eq_mul_add_of_isUnit_leadingCoeff hlead_unit f'p
    have hrp_s : rp.degree < (s : WithBot ℕ) := by rw [← hg'p_deg]; exact hrp_deg
    set q : Restricted A c := Polynomial.toRestricted c qp with hq_def
    have hmap : f' = g' * q + Polynomial.toRestricted c rp := by
      rw [hf'_def, hg'_def, hq_def]
      have h := congrArg (Polynomial.toRestricted c) heq
      rwa [map_add, map_mul] at h
    -- The quotient bound `‖q‖ ≤ ‖g‖⁻¹ * ‖f‖`, via the divisor `g'` (same norm as `g`).
    have hq_bd : ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by
      have h1 := norm_q_le_of_eq_mul_add_of_isMulDistinguished hg'_dist hrp_s hmap
      rw [hg'_norm] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hg_pos.le))
      rw [hf'_def, hf'p_def]; exact norm_toRestricted_trunc_le f N
    -- The error `f - (g q + rp) = (f - f') + (g' - g) q`, both parts `θ`-small.
    have herr : ‖(g' - g) * q‖ ≤ θ * ‖f‖ := by
      have h1 : ‖g' - g‖ ≤ θ * ‖g‖ := by rw [norm_sub_rev]; exact hθ
      have h2 : ‖(g' - g) * q‖ ≤ (θ * ‖g‖) * (‖g‖⁻¹ * ‖f‖) :=
        (norm_mul_le _ _).trans (mul_le_mul h1 hq_bd (norm_nonneg _)
          (mul_nonneg hθ0.le (norm_nonneg g)))
      refine h2.trans_eq ?_
      rw [mul_assoc, ← mul_assoc ‖g‖, mul_inv_cancel₀ hg_pos.ne', one_mul]
    refine ⟨q, rp, by exact_mod_cast hrp_s, hq_bd, ?_⟩
    have halg : f - (g * q + Polynomial.toRestricted c rp) = (f - f') + (g' - g) * q := by
      rw [hmap]; ring
    rw [halg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hN herr)

/-- Iterating the one-step approximation: every `f` is in the closure of the division
set.  Source: [Mar16, proof of Proposition 1.27], the inductive construction of the
Cauchy sequences `(q_i)`, `(R_i)`. -/
lemma mem_closure_divisionSet_of_isMulDistinguished {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) (f : Restricted A c) :
    f ∈ closure (divisionSet g s) := by
  obtain ⟨θ, hθ0, hθ1, hθ⟩ :=
    exists_lt_one_norm_sub_toRestricted_trunc_le_of_isMulDistinguished hg
  suffices hdense : Dense (divisionSet g s) from hdense f
  refine AddSubgroup.dense_of_infDist_le (divisionAddSubgroup g s) θ hθ0 hθ1 fun x ↦ ?_
  by_cases hx : x = 0
  · subst hx
    rw [Metric.infDist_zero_of_mem (divisionAddSubgroup g s).zero_mem]
    exact mul_nonneg hθ0.le dist_nonneg
  · obtain ⟨q, r, hr, -, hbd⟩ := exists_approx_div_of_isMulDistinguished hg hθ0 hθ1 hθ x
    calc Metric.infDist x (divisionAddSubgroup g s)
        ≤ dist x (g * q + Polynomial.toRestricted c r) :=
          Metric.infDist_le_dist_of_mem ⟨q, r, hr, rfl⟩
      _ = ‖x - (g * q + Polynomial.toRestricted c r)‖ := by rw [dist_eq_norm]
      _ ≤ θ * ‖x‖ := hbd
      _ = θ * dist x 0 := by rw [dist_zero_right]

/-- A sequence is Cauchy if its consecutive differences are dominated (up to a fixed
constant `K`) by those of a Cauchy sequence.  Local mirror of the project's private
`cauchySeq_of_norm_sub_le`. -/
private lemma cauchySeq_of_norm_sub_le {X Y : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] {b : ℕ → Y} (hb : CauchySeq b) {x : ℕ → X} {K : ℝ}
    (hK : 0 ≤ K) (hbd : ∀ n m, ‖x n - x m‖ ≤ K * ‖b n - b m‖) : CauchySeq x := by
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hb (ε / (K + 1)) (div_pos hε hK1)
  refine ⟨N, fun n hn m hm ↦ ?_⟩
  have hb' : ‖b n - b m‖ * (K + 1) < ε := by
    rw [← lt_div_iff₀ hK1, ← dist_eq_norm]; exact hN n hn m hm
  rw [dist_eq_norm]
  exact (hbd n m).trans_lt (by nlinarith [norm_nonneg (b n - b m)])

omit [Fact (0 < c)] in
/-- A restricted series whose coefficients vanish from degree `s` on is the image of a
polynomial of degree `< s`.  Local mirror of the project's private
`exists_toRestricted_eq_of_coeff_eq_zero`. -/
private lemma exists_toRestricted_eq_of_coeff_eq_zero {r_T : Restricted A c} {s : ℕ}
    (h : ∀ v, s ≤ v → coeff v r_T.1 = 0) :
    ∃ r : Polynomial A, r.degree < s ∧ Polynomial.toRestricted c r = r_T := by
  refine ⟨PowerSeries.trunc s r_T.1, PowerSeries.degree_trunc_lt r_T.1 s, ?_⟩
  apply Subtype.ext
  ext v
  change coeff v ((PowerSeries.trunc s r_T.1 : Polynomial A) : PowerSeries A) = coeff v r_T.1
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hv
  · rfl
  · exact (h v (not_lt.mp hv)).symm

/-- The division set is closed: the division bounds make a convergent sequence of
divisions into Cauchy sequences of quotients and remainders.  (Martin-hypothesis version
of the project's `isClosed_divisionSet`.) -/
lemma isClosed_divisionSet_of_isMulDistinguished [CompleteSpace A]
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) :
    IsClosed (divisionSet g s) := by
  refine IsSeqClosed.isClosed ?_
  intro b_seq b hb_mem hb_lim
  choose q_seq r_seq hr_seq hb_eq using hb_mem
  have diff_eq : ∀ n m, b_seq n - b_seq m =
      g * (q_seq n - q_seq m) + Polynomial.toRestricted c (r_seq n - r_seq m) := fun n m ↦ by
    rw [hb_eq n, hb_eq m, map_sub, mul_sub]
    abel
  have diff_deg : ∀ n m, (r_seq n - r_seq m).degree < s := fun n m ↦
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt (hr_seq n) (hr_seq m))
  have hq_cauchy : CauchySeq q_seq :=
    cauchySeq_of_norm_sub_le hb_lim.cauchySeq (inv_nonneg.mpr hg.toIsDistinguished.norm_pos.le)
      fun n m ↦ norm_q_le_of_eq_mul_add_of_isMulDistinguished hg (diff_deg n m) (diff_eq n m)
  have hr_cauchy : CauchySeq fun n ↦ Polynomial.toRestricted c (r_seq n) :=
    cauchySeq_of_norm_sub_le hb_lim.cauchySeq zero_le_one fun n m ↦ by
      rw [one_mul, ← map_sub]
      exact norm_toRestricted_le_of_eq_mul_add_of_isMulDistinguished hg (diff_deg n m)
        (diff_eq n m)
  obtain ⟨q, hq_lim⟩ := cauchySeq_tendsto_of_complete hq_cauchy
  obtain ⟨r_T, hr_T_lim⟩ := cauchySeq_tendsto_of_complete hr_cauchy
  have h_r_T_in : r_T ∈ {f : Restricted A c | ∀ v, s ≤ v → coeff v f.1 = 0} := by
    refine (isClosed_setOf_coeff_eq_zero c s).mem_of_tendsto hr_T_lim
      (Filter.Eventually.of_forall fun n v hv ↦ ?_)
    simp only [Polynomial.val_toRestricted, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt ((hr_seq n).trans_le (mod_cast hv))
  obtain ⟨r, hr_deg, hr_toR⟩ := exists_toRestricted_eq_of_coeff_eq_zero h_r_T_in
  refine ⟨q, r, hr_deg, ?_⟩
  rw [hr_toR]
  exact tendsto_nhds_unique hb_lim
    (by simpa [funext hb_eq] using (hq_lim.const_mul g).add hr_T_lim)

/-- **[Mar16, Proposition 1.27], existence**: Weierstrass division by a
Martin-distinguished series, over any ultrametric complete normed ring, at any
radius. -/
theorem weierstrassDivision_exists_of_isMulDistinguished [CompleteSpace A]
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) (f : Restricted A c) :
    ∃ (q : Restricted A c) (r : Polynomial A), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r :=
  (isClosed_divisionSet_of_isMulDistinguished hg).closure_subset
    (mem_closure_divisionSet_of_isMulDistinguished hg f)

end PowerSeries.Restricted
