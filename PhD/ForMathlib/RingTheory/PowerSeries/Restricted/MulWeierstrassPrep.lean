/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Martin.WeierstrassDivision

/-! # Weierstrass preparation at every radius over an ultrametric Banach ring

[Mar16, Corollary 1.28]: a Martin-distinguished `g` of order `s` factors uniquely as
`g = e * ω` with `ω` monic of degree `s` and `e` a **multiplicative unit** of `A{c⁻¹T}`.

The proof divides `T^s` by `g` (Proposition 1.27), sets `ω := T^s − r = g * q`, and shows
`q` is a multiplicative unit: the greatest achieving index of `q` is `0` (Lemma 1.26(2)
forces `s + k₀ ≤ s`), the coefficient identity `1 = Σ g_i q_{s−i}` then exhibits
`g_s * q₀` as `1 −` (small), a multiplicative unit by Remark 1.22, and `q` factors as
`q₀ * (1 + small)` in `A{c⁻¹T}`.

The file closes with the `NormMulClass` bridge corollaries: over a multiplicatively
normed coefficient ring, Martin's theorems specialise to oracle-free division and
preparation for the project's `IsDistinguished`.

Source: F. Martin, J. EMS 18 (2016), §1.3.
-/

namespace PowerSeries.Restricted

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] {c : ℝ} [Fact (0 < c)]

section QuotientUnit

variable [NormOneClass A]

omit [Fact (0 < c)] [NormOneClass A] in
/-- The `k`-th coefficient of the restricted power series attached to `X ^ s`. -/
private lemma coeff_toRestricted_X_pow (s k : ℕ) :
    coeff k (Polynomial.toRestricted c ((Polynomial.X : Polynomial A) ^ s)).1
      = if k = s then 1 else 0 := by
  rw [Polynomial.val_toRestricted, Polynomial.coeff_coe, Polynomial.coeff_X_pow]

omit [Fact (0 < c)] [NormOneClass A] in
/-- The coefficient identity read off `X ^ s = g * q + r`: at every index, the coefficient of
`g * q` plus that of `r` is the coefficient of `X ^ s`. -/
private lemma coeff_mul_add_coeff_eq {g q : Restricted A c} {s : ℕ} {r : Polynomial A}
    (hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r)
    (k : ℕ) :
    coeff k (g * q).1 + r.coeff k = if k = s then 1 else 0 := by
  have h : coeff k (Polynomial.toRestricted c (Polynomial.X ^ s)).1
      = coeff k (g * q).1 + coeff k (Polynomial.toRestricted c r).1 := by
    rw [hEq, show (g * q + Polynomial.toRestricted c r).1
      = (g * q).1 + (Polynomial.toRestricted c r).1 from rfl, map_add]
  rw [coeff_toRestricted_X_pow, Polynomial.val_toRestricted, Polynomial.coeff_coe] at h
  exact h.symm

omit [Fact (0 < c)] [NormOneClass A] in
/-- Reading `X ^ s = g * q + r` (with `r.degree < s`) at index `s` gives `coeff s (g * q) = 1`. -/
private lemma coeff_mul_eq_one {g q : Restricted A c} {s : ℕ} {r : Polynomial A}
    (hr : r.degree < s)
    (hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r) :
    coeff s (g * q).1 = 1 := by
  have h := coeff_mul_add_coeff_eq hEq s
  rwa [if_pos rfl, Polynomial.coeff_eq_zero_of_degree_lt hr, add_zero] at h

omit [Fact (0 < c)] in
/-- If `X ^ s = g * q + r` with `r.degree < s`, then the quotient `q` is nonzero: otherwise
the `s`-th coefficients would give `1 = 0` in `A`. -/
private lemma q_ne_zero_of_eq_pow {g q : Restricted A c} {s : ℕ} {r : Polynomial A}
    (hr : r.degree < s)
    (hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r) :
    q ≠ 0 := by
  rintro rfl
  rw [mul_zero, zero_add] at hEq
  have h : coeff s (Polynomial.toRestricted c (Polynomial.X ^ s)).1
      = coeff s (Polynomial.toRestricted c r).1 := by rw [hEq]
  rw [coeff_toRestricted_X_pow, if_pos rfl, Polynomial.val_toRestricted, Polynomial.coeff_coe,
    Polynomial.coeff_eq_zero_of_degree_lt hr] at h
  have h1 : ‖(1 : A)‖ = 0 := by rw [h]; exact norm_zero
  rw [norm_one] at h1
  exact one_ne_zero h1

/-- In the division `X ^ s = g * q + r`, the greatest index achieving the Gauss norm of the
quotient is `0`: at any positive achieving index `k₀`, the coefficient of `g * q` at `s + k₀`
would be forced to `0` while being norm-multiplicatively nonzero. -/
private lemma greatest_achieves_eq_zero {g q : Restricted A c} {s : ℕ} {r : Polynomial A}
    (hg : IsMulDistinguished c g.1 s) (hr : r.degree < s)
    (hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r) :
    AchievesGaussNorm norm c q.1 0 ∧ ∀ k, 0 < k → ‖coeff k q.1‖ * c ^ k < ‖q‖ := by
  haveI hntr : Nontrivial A := hg.toIsDistinguished.nontrivial
  have hq0 : q ≠ 0 := q_ne_zero_of_eq_pow hr hEq
  obtain ⟨k₀, hk, hkmax⟩ := exists_greatest_achievesGaussNorm q hq0
  have hq_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hqk_eq : ‖coeff k₀ q.1‖ * c ^ k₀ = ‖q‖ := hk.trans (norm_def c q).symm
  have hk0eq : k₀ = 0 := by
    by_contra hne
    have hidx : coeff (s + k₀) (g * q).1 = 0 := by
      have h := coeff_mul_add_coeff_eq hEq (s + k₀)
      rw [if_neg (by omega), Polynomial.coeff_eq_zero_of_degree_lt
        (hr.trans_le (by exact_mod_cast Nat.le_add_right s k₀)), add_zero] at h
      exact h
    have hprod := norm_coeff_add_mul_of_isMulDistinguished hg hk hkmax
    rw [hidx, norm_zero] at hprod
    have hgs_pos : 0 < ‖coeff s g.1‖ :=
      norm_pos_iff.mpr hg.isNormMulUnit_coeff.isUnit.ne_zero
    have hqk_pos : 0 < ‖coeff k₀ q.1‖ :=
      lt_of_le_of_ne (norm_nonneg _) fun h => hq_pos.ne' (by rw [← hqk_eq, ← h, zero_mul])
    exact (mul_pos hgs_pos hqk_pos).ne' hprod.symm
  subst hk0eq
  exact ⟨hk, hkmax⟩

/-- In the division `T^s = g * q + r`, the constant coefficient of the quotient pairs
with the distinguished coefficient to norm `1`: `‖g_s‖ * ‖q₀‖ = 1`.
Source: [Mar16, proof of Corollary 1.28], "`‖g_s q_0‖ = ‖1‖ = 1`". -/
lemma norm_coeff_mul_norm_coeff_zero_of_eq_pow {g q : Restricted A c} {s : ℕ}
    {r : Polynomial A} (hg : IsMulDistinguished c g.1 s) (hr : r.degree < s)
    (hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r) :
    ‖coeff s g.1‖ * ‖coeff 0 q.1‖ = 1 := by
  obtain ⟨hk, hkmax⟩ := greatest_achieves_eq_zero hg hr hEq
  have hprod := norm_coeff_add_mul_of_isMulDistinguished hg hk hkmax
  rw [add_zero, coeff_mul_eq_one hr hEq, norm_one] at hprod
  exact hprod.symm

/-- In the division `T^s = g * q + r`, the greatest achieving index of the quotient is
`0`: every later Gauss term of `q` is strictly below `‖q₀‖`.
Source: [Mar16, proof of Corollary 1.28], "necessarily `s + k₀ = s` and `k₀ = 0`". -/
lemma gaussTerm_lt_norm_coeff_zero_of_eq_pow {g q : Restricted A c} {s : ℕ}
    {r : Polynomial A} (hg : IsMulDistinguished c g.1 s) (hr : r.degree < s)
    (hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r) :
    ∀ k, 0 < k → ‖coeff k q.1‖ * c ^ k < ‖coeff 0 q.1‖ := by
  obtain ⟨hk, hkmax⟩ := greatest_achieves_eq_zero hg hr hEq
  have hq_eq0 : ‖coeff 0 q.1‖ = ‖q‖ := by simpa using hk.trans (norm_def c q).symm
  exact fun k hk0 => hq_eq0 ▸ hkmax k hk0

omit [NormOneClass A] in
/-- Multiplication by the constant series `C c a` of a multiplicative unit `a : A` is
norm-multiplicative, so `C c a` is again a multiplicative unit of `A{c⁻¹T}`. -/
private lemma isNormMulUnit_C {a : A} (ha : IsNormMulUnit a) : IsNormMulUnit (C c a) := by
  refine ⟨ha.isUnit.map (C c), fun f => ?_⟩
  rw [norm_C]
  refine le_antisymm ((norm_le_iff _ _).mpr fun k => ?_) ?_
  · rw [show (C c a * f).1 = (C c a).1 * f.1 from rfl, val_C, PowerSeries.coeff_C_mul,
      ha.norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_coeff_mul_pow_le c f k) (norm_nonneg a)
  · rcases eq_or_ne f 0 with rfl | hf
    · simp only [mul_zero, norm_zero, le_refl]
    · obtain ⟨k, -, hk⟩ := exists_coeff_ne_zero_norm_eq c f hf
      calc ‖a‖ * ‖f‖ = ‖coeff k (C c a * f).1‖ * c ^ k := by
            rw [hk, show (C c a * f).1 = (C c a).1 * f.1 from rfl, val_C,
              PowerSeries.coeff_C_mul, ha.norm_mul, mul_assoc]
        _ ≤ ‖C c a * f‖ := norm_coeff_mul_pow_le c (C c a * f) k

/-- The constant coefficient of the quotient of `T^s` by a Martin-distinguished series is a
multiplicative unit of `A`: the coefficient identity exhibits `g_s * q_0` as `1 −` (small),
a multiplicative unit by [Mar16, Remark 1.22], and `q_0 = g_s⁻¹ * (g_s * q_0)`.
Source: [Mar16, proof of Corollary 1.28]. -/
private lemma isNormMulUnit_coeff_zero_of_eq_pow [CompleteSpace A] {g q : Restricted A c}
    {s : ℕ} {r : Polynomial A} (hg : IsMulDistinguished c g.1 s) (hr : r.degree < s)
    (hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r) :
    IsNormMulUnit (coeff 0 q.1) := by
  haveI : Nontrivial A := hg.toIsDistinguished.nontrivial
  have hc : (0 : ℝ) < c := Fact.out
  have hprod : ‖coeff s g.1‖ * ‖coeff 0 q.1‖ = 1 :=
    norm_coeff_mul_norm_coeff_zero_of_eq_pow hg hr hEq
  have hgs_pos : 0 < ‖coeff s g.1‖ :=
    norm_pos_iff.mpr hg.isNormMulUnit_coeff.isUnit.ne_zero
  have hexpand : coeff s (g * q).1
      = coeff s g.1 * coeff 0 q.1
        + ∑ p ∈ (Finset.antidiagonal s).erase (s, 0), coeff p.1 g.1 * coeff p.2 q.1 := by
    rw [show (g * q).1 = g.1 * q.1 from rfl, PowerSeries.coeff_mul]
    exact (Finset.add_sum_erase (Finset.antidiagonal s)
      (fun p => coeff p.1 g.1 * coeff p.2 q.1)
      (show (s, 0) ∈ Finset.antidiagonal s from Finset.mem_antidiagonal.mpr rfl)).symm
  have hlt : ‖coeff s g.1 * coeff 0 q.1 - 1‖ < 1 := by
    have hsub : coeff s g.1 * coeff 0 q.1 - 1
        = -(∑ p ∈ (Finset.antidiagonal s).erase (s, 0), coeff p.1 g.1 * coeff p.2 q.1) := by
      have h1 : coeff s g.1 * coeff 0 q.1
          + ∑ p ∈ (Finset.antidiagonal s).erase (s, 0), coeff p.1 g.1 * coeff p.2 q.1 = 1 := by
        rw [← hexpand]; exact coeff_mul_eq_one hr hEq
      linear_combination h1
    rw [hsub, norm_neg]
    rcases ((Finset.antidiagonal s).erase (s, 0)).eq_empty_or_nonempty with he | he
    · rw [he, Finset.sum_empty, norm_zero]; exact one_pos
    · obtain ⟨p, hp, hbound⟩ := IsNonarchimedean.finset_image_add_of_nonempty
        IsUltrametricDist.isNonarchimedean_norm
        (fun p : ℕ × ℕ => coeff p.1 g.1 * coeff p.2 q.1) he
      obtain ⟨m, k⟩ := p
      rw [Finset.mem_erase, Finset.mem_antidiagonal] at hp
      obtain ⟨hne, hmk⟩ := hp
      have hk1 : 0 < k := Nat.pos_of_ne_zero fun hk0 => hne (Prod.ext (show m = s by omega) hk0)
      refine hbound.trans_lt ((norm_mul_le _ _).trans_lt ?_)
      have hgm : ‖coeff m g.1‖ * c ^ m ≤ ‖coeff s g.1‖ * c ^ s :=
        (norm_coeff_mul_pow_le c g m).trans hg.toIsDistinguished.norm_coeff_mul_pow_eq.ge
      have hqk : ‖coeff k q.1‖ * c ^ k < ‖coeff 0 q.1‖ :=
        gaussTerm_lt_norm_coeff_zero_of_eq_pow hg hr hEq k hk1
      have hA₂ : 0 < ‖coeff s g.1‖ * c ^ s := mul_pos hgs_pos (pow_pos hc s)
      have hkey : ‖coeff m g.1‖ * ‖coeff k q.1‖ * c ^ s < 1 * c ^ s :=
        calc ‖coeff m g.1‖ * ‖coeff k q.1‖ * c ^ s
            = (‖coeff m g.1‖ * c ^ m) * (‖coeff k q.1‖ * c ^ k) := by
              rw [← hmk, pow_add]; ring
          _ < (‖coeff s g.1‖ * c ^ s) * ‖coeff 0 q.1‖ :=
              (mul_le_mul_of_nonneg_right hgm
                (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le k))).trans_lt
                (mul_lt_mul_of_pos_left hqk hA₂)
          _ = 1 * c ^ s := by rw [mul_right_comm, hprod]
      exact lt_of_mul_lt_mul_right hkey (pow_nonneg hc.le s)
  have hprod_unit : IsNormMulUnit (coeff s g.1 * coeff 0 q.1) := by
    have h := isNormMulUnit_one_add hlt
    rwa [show (1 : A) + (coeff s g.1 * coeff 0 q.1 - 1) = coeff s g.1 * coeff 0 q.1 by ring] at h
  obtain ⟨v, hv_spec⟩ := hg.isNormMulUnit_coeff.isUnit
  have hv : IsNormMulUnit (↑v : A) := by rw [hv_spec]; exact hg.isNormMulUnit_coeff
  have hq0_eq : coeff 0 q.1 = (↑v⁻¹ : A) * (coeff s g.1 * coeff 0 q.1) := by
    rw [← hv_spec, Units.inv_mul_cancel_left]
  rw [hq0_eq]
  exact hv.coe_inv_units.mul hprod_unit

/-- The quotient of `T^s` by a Martin-distinguished series is a multiplicative unit of
`A{c⁻¹T}`.  Source: [Mar16, proof of Corollary 1.28], "`q` is also a multiplicative
unit". -/
lemma isNormMulUnit_of_eq_pow [CompleteSpace A] {g q : Restricted A c} {s : ℕ}
    {r : Polynomial A} (hg : IsMulDistinguished c g.1 s) (hr : r.degree < s)
    (hEq : Polynomial.toRestricted c (Polynomial.X ^ s) = g * q + Polynomial.toRestricted c r) :
    IsNormMulUnit q := by
  haveI : Nontrivial A := hg.toIsDistinguished.nontrivial
  have hq0_unit : IsNormMulUnit (coeff 0 q.1) := isNormMulUnit_coeff_zero_of_eq_pow hg hr hEq
  have hd : IsNormMulUnit (C c (coeff 0 q.1)) := isNormMulUnit_C hq0_unit
  set d : Restricted A c := C c (coeff 0 q.1) with hd_def
  have hd_norm : ‖d‖ = ‖coeff 0 q.1‖ := by rw [hd_def, norm_C]
  have hd_pos : 0 < ‖d‖ := by rw [hd_norm]; exact norm_pos_iff.mpr hq0_unit.isUnit.ne_zero
  have hclose : ‖q - d‖ < ‖d‖ := by
    rw [hd_norm]
    refine (norm_lt_iff _ _).mpr fun k => ?_
    have hcoeff : coeff k (q - d).1 = if k = 0 then 0 else coeff k q.1 := by
      rw [hd_def, show (q - C c (coeff 0 q.1)).1 = q.1 - (C c (coeff 0 q.1)).1 from rfl,
        map_sub, val_C, PowerSeries.coeff_C]
      split_ifs with hk
      · rw [hk, sub_self]
      · rw [sub_zero]
    rw [hcoeff]
    split_ifs with hk
    · rw [norm_zero, zero_mul]; exact norm_pos_iff.mpr hq0_unit.isUnit.ne_zero
    · exact gaussTerm_lt_norm_coeff_zero_of_eq_pow hg hr hEq k (Nat.pos_of_ne_zero hk)
  obtain ⟨u, hu_spec⟩ := hd.isUnit
  have hu : IsNormMulUnit (↑u : Restricted A c) := by rw [hu_spec]; exact hd
  have hw : ‖(↑u⁻¹ : Restricted A c) * (q - d)‖ < 1 := by
    rw [hu.coe_inv_units.norm_mul, hu.norm_coe_inv_units, hu_spec]
    calc ‖d‖⁻¹ * ‖q - d‖ < ‖d‖⁻¹ * ‖d‖ :=
          mul_lt_mul_of_pos_left hclose (inv_pos.mpr hd_pos)
      _ = 1 := inv_mul_cancel₀ hd_pos.ne'
  have hfactor : d * (1 + (↑u⁻¹ : Restricted A c) * (q - d)) = q := by
    rw [mul_add, mul_one, ← hu_spec, Units.mul_inv_cancel_left]; abel
  have hq : IsNormMulUnit (d * (1 + (↑u⁻¹ : Restricted A c) * (q - d))) :=
    hd.mul (isNormMulUnit_one_add hw)
  rwa [hfactor] at hq

end QuotientUnit

/-- The Gauss norm of `X ^ s` is `c ^ s`: it is the monomial `c s 1`. -/
private lemma norm_toRestricted_X_pow [NormOneClass A] (s : ℕ) :
    ‖Polynomial.toRestricted c (Polynomial.X ^ s : Polynomial A)‖ = c ^ s := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.toRestricted_monomial,
    norm_monomial, norm_one, one_mul]

/-- If `deg r < s` and `‖r‖ ≤ c ^ s`, then `X ^ s - r` has Gauss norm `c ^ s`: the upper bound
is the ultrametric inequality against `‖X ^ s‖ = c ^ s` and `‖r‖`, the lower bound is the
`s`-th Gauss term, whose coefficient is `1`. -/
private lemma norm_toRestricted_X_pow_sub [NormOneClass A] {r : Polynomial A} {s : ℕ}
    (hr : r.degree < s) (hrn : ‖Polynomial.toRestricted c r‖ ≤ c ^ s) :
    ‖Polynomial.toRestricted c (Polynomial.X ^ s - r)‖ = c ^ s := by
  refine le_antisymm ?_ ?_
  · rw [map_sub]
    have h1 := IsUltrametricDist.norm_add_le_max
      (Polynomial.toRestricted c (Polynomial.X ^ s : Polynomial A))
      (-(Polynomial.toRestricted c r))
    rw [← sub_eq_add_neg, norm_neg] at h1
    exact h1.trans (max_le (norm_toRestricted_X_pow (A := A) s).le hrn)
  · have hcs : coeff s (Polynomial.toRestricted c (Polynomial.X ^ s - r)).1 = 1 := by
      rw [Polynomial.val_toRestricted, Polynomial.coeff_coe, Polynomial.coeff_sub,
        Polynomial.coeff_X_pow, if_pos rfl, Polynomial.coeff_eq_zero_of_degree_lt hr, sub_zero]
    have h2 := norm_coeff_mul_pow_le c (Polynomial.toRestricted c (Polynomial.X ^ s - r)) s
    rwa [hcs, norm_one, one_mul] at h2

/-- **[Mar16, Corollary 1.28], existence**: Weierstrass preparation over any ultrametric
complete normed ring at any radius: `g = e * ω` with `ω` monic of degree `s`, of norm
`c ^ s`, and `e` a multiplicative unit. -/
theorem weierstrassPreparation_exists_of_isMulDistinguished [CompleteSpace A]
    [NormOneClass A] {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) :
    ∃ (ω : Polynomial A) (e : Restricted A c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsNormMulUnit e ∧
      g = e * Polynomial.toRestricted c ω := by
  haveI : Nontrivial A := hg.toIsDistinguished.nontrivial
  obtain ⟨q, r, hr, hEq⟩ :=
    weierstrassDivision_exists_of_isMulDistinguished hg
      (Polynomial.toRestricted c (Polynomial.X ^ s))
  have hω_s : (Polynomial.X ^ s - r : Polynomial A).coeff s = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_eq_zero_of_degree_lt hr, sub_zero]
  have hω_deg : (Polynomial.X ^ s - r : Polynomial A).degree = s := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    rwa [Polynomial.degree_X_pow]
  have hω_monic : (Polynomial.X ^ s - r : Polynomial A).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff,
      Polynomial.natDegree_eq_of_degree_eq_some hω_deg]
    exact hω_s
  have hq_unit : IsNormMulUnit q := isNormMulUnit_of_eq_pow hg hr hEq
  have hωgq : Polynomial.toRestricted c (Polynomial.X ^ s - r) = g * q := by
    rw [map_sub, hEq]; abel
  have hrn : ‖Polynomial.toRestricted c r‖ ≤ c ^ s :=
    (norm_toRestricted_le_of_eq_mul_add_of_isMulDistinguished hg hr hEq).trans
      (norm_toRestricted_X_pow (A := A) s).le
  have hωn : ‖Polynomial.toRestricted c (Polynomial.X ^ s - r)‖ = c ^ s :=
    norm_toRestricted_X_pow_sub hr hrn
  obtain ⟨u, hu_spec⟩ := hq_unit.isUnit
  have hu : IsNormMulUnit (↑u : Restricted A c) := by rw [hu_spec]; exact hq_unit
  refine ⟨Polynomial.X ^ s - r, ↑u⁻¹, hω_monic, hω_deg, hωn, hu.coe_inv_units, ?_⟩
  rw [hωgq, ← hu_spec, mul_comm g (↑u : Restricted A c), Units.inv_mul_cancel_left]

omit [Fact (0 < c)] in
/-- Rearranging a preparation `g = e * ω` (with `↑u = e`) into a Weierstrass division of
`X ^ s` by `g`: the remainder is `X ^ s - ω` (degree `< s`) and the quotient is `↑u⁻¹`. -/
private lemma toRestricted_X_pow_eq_of_isUnit_mul [Nontrivial A] {g : Restricted A c} {s : ℕ}
    {ω : Polynomial A} {e : Restricted A c} {u : (Restricted A c)ˣ}
    (hm : ω.Monic) (hd : ω.degree = s) (hu : (↑u : Restricted A c) = e)
    (hg' : g = e * Polynomial.toRestricted c ω) :
    (Polynomial.X ^ s - ω : Polynomial A).degree < (s : WithBot ℕ) ∧
      Polynomial.toRestricted c (Polynomial.X ^ s)
        = g * (↑u⁻¹ : Restricted A c) + Polynomial.toRestricted c (Polynomial.X ^ s - ω) := by
  refine ⟨?_, ?_⟩
  · have hlt := Polynomial.degree_sub_lt
      ((Polynomial.degree_X_pow (R := A) s).trans hd.symm)
      (Polynomial.monic_X_pow (R := A) s).ne_zero
      ((Polynomial.monic_X_pow (R := A) s).leadingCoeff.trans hm.leadingCoeff.symm)
    rwa [Polynomial.degree_X_pow] at hlt
  · have h_e : g * (↑u⁻¹ : Restricted A c) = Polynomial.toRestricted c ω := by
      rw [hg', ← hu, mul_comm (↑u : Restricted A c) _, mul_assoc, u.mul_inv, mul_one]
    rw [h_e, map_sub]; abel

/-- **[Mar16, Corollary 1.28], uniqueness of the distinguished polynomial** (only
`IsUnit e` is needed): rearranging `g = e * ω` exhibits `T^s = g * e⁻¹ + (T^s − ω)` as a
Weierstrass division of `T^s` by `g`, pinned down by division uniqueness. -/
theorem weierstrassPreparation_omega_unique_of_isMulDistinguished
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s)
    {ω₁ ω₂ : Polynomial A} {e₁ e₂ : Restricted A c}
    (hm₁ : ω₁.Monic) (hd₁ : ω₁.degree = s) (he₁ : IsUnit e₁)
    (hg₁ : g = e₁ * Polynomial.toRestricted c ω₁)
    (hm₂ : ω₂.Monic) (hd₂ : ω₂.degree = s) (he₂ : IsUnit e₂)
    (hg₂ : g = e₂ * Polynomial.toRestricted c ω₂) :
    ω₁ = ω₂ := by
  haveI : Nontrivial A := hg.toIsDistinguished.nontrivial
  obtain ⟨u₁, hu₁⟩ := he₁
  obtain ⟨u₂, hu₂⟩ := he₂
  obtain ⟨hρ₁, hEq₁⟩ := toRestricted_X_pow_eq_of_isUnit_mul hm₁ hd₁ hu₁ hg₁
  obtain ⟨hρ₂, hEq₂⟩ := toRestricted_X_pow_eq_of_isUnit_mul hm₂ hd₂ hu₂ hg₂
  have h := weierstrassDivision_r_unique_of_isMulDistinguished hg hρ₁ hEq₁ hρ₂ hEq₂
  linear_combination -h

/-- **[Mar16, Corollary 1.28], uniqueness of the unit**. -/
theorem weierstrassPreparation_e_unique_of_isMulDistinguished
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s)
    {ω₁ ω₂ : Polynomial A} {e₁ e₂ : Restricted A c}
    (hm₁ : ω₁.Monic) (hd₁ : ω₁.degree = s) (he₁ : IsUnit e₁)
    (hg₁ : g = e₁ * Polynomial.toRestricted c ω₁)
    (hm₂ : ω₂.Monic) (hd₂ : ω₂.degree = s) (he₂ : IsUnit e₂)
    (hg₂ : g = e₂ * Polynomial.toRestricted c ω₂) :
    e₁ = e₂ := by
  haveI : Nontrivial A := hg.toIsDistinguished.nontrivial
  obtain ⟨u₁, hu₁⟩ := he₁
  obtain ⟨u₂, hu₂⟩ := he₂
  obtain ⟨hρ₁, hEq₁⟩ := toRestricted_X_pow_eq_of_isUnit_mul hm₁ hd₁ hu₁ hg₁
  obtain ⟨hρ₂, hEq₂⟩ := toRestricted_X_pow_eq_of_isUnit_mul hm₂ hd₂ hu₂ hg₂
  have hq := weierstrassDivision_q_unique_of_isMulDistinguished hg hρ₁ hEq₁ hρ₂ hEq₂
  rw [← hu₁, ← hu₂, inv_injective (Units.ext hq)]

/-! ## Bridge: over a multiplicatively normed ring, Martin subsumes the project's
oracle-free statements -/

/-- Weierstrass division over a `NormMulClass` coefficient ring, with the project's
`IsDistinguished` hypothesis — an oracle-free specialisation of Martin's theorem. -/
theorem weierstrassDivision_exists_of_normMulClass [NormMulClass A] [CompleteSpace A]
    {g : Restricted A c} {s : ℕ} (hg : IsDistinguished norm c g.1 s) (f : Restricted A c) :
    ∃ (q : Restricted A c) (r : Polynomial A), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r :=
  weierstrassDivision_exists_of_isMulDistinguished
    (isMulDistinguished_iff_isDistinguished.mpr hg) f

/-- Weierstrass preparation over a `NormMulClass` coefficient ring, with the project's
`IsDistinguished` hypothesis. -/
theorem weierstrassPreparation_exists_of_normMulClass [NormMulClass A] [NormOneClass A]
    [CompleteSpace A] {g : Restricted A c} {s : ℕ} (hg : IsDistinguished norm c g.1 s) :
    ∃ (ω : Polynomial A) (e : Restricted A c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toRestricted c ω := by
  obtain ⟨ω, e, hmon, hdeg, hnorm, hunit, heq⟩ :=
    weierstrassPreparation_exists_of_isMulDistinguished
      (isMulDistinguished_iff_isDistinguished.mpr hg)
  exact ⟨ω, e, hmon, hdeg, hnorm, hunit.isUnit, heq⟩

end PowerSeries.Restricted
