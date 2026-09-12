/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«05_Sharpness»
import PhD.Main.LWX.«05_UpperPolygon»

/-!
# The Claim of [LWX, §4.2]

For `T₀` in the smaller annulus `0 < v(T₀) < 8/((p²−1)t + 8)` ([LWX, Thm 1.5]'s radius
`λ = p^{−8/((p²−1)t+8)}`), [LWX, §4.2] proves:

> **Claim.** If `(l, v(c_l(T₀)))` lies strictly below the upper bound polygon for some `l` and
> `T₀`, then there is a unique integer `m(l) ≥ λ(l)` such that for every `T` in the annulus,
> `(l, v(c_l(T)))` lies strictly below the upper bound polygon and `v(c_l(T)) = m(l)·v(T)`.

Here `m(l)` is made explicit and `T`-free: `unitIndex D ω l` is the least `m` with
`b_{l,m} ∈ ℤ_p^×` (the proof shows `b_{l,m(l)}` is a unit and `b_{l,m} ∈ pℤ_p` for
`λ(l) ≤ m < m(l)`), and "strictly below the upper bound polygon" is the `T`-free predicate
`IsBelowUpper D ω l : 2·unitIndex < lwxUpperTwice l` (both polygons scale with `v(T)`).

* `exists_isUnit_and_coeffVal_eq` — the analytic core ((4.2.1)–(4.2.4));
* `isBelowUpper_of_coeffVal_lt` — strictly below at one `T₀` ⟹ `IsBelowUpper`;
* `coeffVal_specCharSeries_eq_unitIndex_mul` — `IsBelowUpper` ⟹ `v(c_l(T)) = m(l)v(T)` ∀ `T`;
* `le_coeffVal_specCharSeries_of_not_isBelowUpper` — otherwise `v(c_l(T)) ≥ upper(l)·v(T)`.
-/

open Filter Topology Finset TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The unit index `m(l)` -/

/-- `m(l)`: the least `m` with `b_{l,m} ∈ ℤ_p^×` ([LWX, §4.2 Claim]); `sInf`, so junk `0` if no
coefficient of `c_l` is a unit. -/
def unitIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (l : ℕ) : ℕ :=
  sInf {m : ℕ | IsUnit ((charCoeff (D.op ω) l) (m : ℤ))}

/-- **"Strictly below the upper bound polygon"**, `T`-free: some `b_{l,m}` is a unit and
`m(l) < upper(l)`, i.e. `2·m(l) < lwxUpperTwice l`.  The index set `{l_i}` of [LWX, §4.2]. -/
def IsBelowUpper (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (l : ℕ) : Prop :=
  (∃ m : ℕ, IsUnit ((charCoeff (D.op ω) l) (m : ℤ))) ∧
    2 * unitIndex D ω l < lwxUpperTwice p (Fintype.card ι) l

/-- Units only occur at `m ≥ λ(l)` (`v(b_{l,m}) ≥ λ(l) − m ≥ 1` otherwise,
[LWX, Cor 3.18 proof]). -/
theorem lwxLambda_le_of_isUnit (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    {l : ℕ} {m : ℤ} (hu : IsUnit ((charCoeff (D.op ω) l) m)) :
    (lwxLambda p (Fintype.card ι) l : ℤ) ≤ m := by
  by_contra hlt
  rw [not_le] at hlt
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpow : (p : ℝ) ^ (m - (lwxLambda p (Fintype.card ι) l : ℤ)) ≤ (p : ℝ) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ hp1.le (by omega)
  rw [zpow_neg_one] at hpow
  have hlt1 : ‖(charCoeff (D.op ω) l) m‖ < 1 :=
    lt_of_le_of_lt ((norm_coeff_charCoeff_upOp_le hp2 D ω l m).trans hpow)
      (inv_lt_one_of_one_lt₀ hp1)
  exact absurd (PadicInt.isUnit_iff.1 hu) hlt1.ne

/-- `b_{l,m(l)}` is a unit when some coefficient is. -/
theorem isUnit_unitIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {l : ℕ}
    (h : ∃ m : ℕ, IsUnit ((charCoeff (D.op ω) l) (m : ℤ))) :
    IsUnit ((charCoeff (D.op ω) l) (unitIndex D ω l : ℤ)) :=
  Nat.sInf_mem (s := {m : ℕ | IsUnit ((charCoeff (D.op ω) l) (m : ℤ))}) h

/-- No coefficient below `m(l)` is a unit. -/
theorem not_isUnit_of_lt_unitIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {l m : ℕ}
    (hm : m < unitIndex D ω l) : ¬ IsUnit ((charCoeff (D.op ω) l) (m : ℤ)) := fun hu ↦
  absurd hm (not_lt.2 (Nat.sInf_le (s := {m : ℕ | IsUnit ((charCoeff (D.op ω) l) (m : ℤ))}) hu))

/-- `m(l)` is below every unit index. -/
theorem unitIndex_le (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {l m : ℕ}
    (hu : IsUnit ((charCoeff (D.op ω) l) (m : ℤ))) : unitIndex D ω l ≤ m :=
  Nat.sInf_le (s := {m : ℕ | IsUnit ((charCoeff (D.op ω) l) (m : ℤ))}) hu

/-- `λ(l) ≤ m(l)` when some coefficient is a unit. -/
theorem lwxLambda_le_unitIndex (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    {l : ℕ} (h : ∃ m : ℕ, IsUnit ((charCoeff (D.op ω) l) (m : ℤ))) :
    lwxLambda p (Fintype.card ι) l ≤ unitIndex D ω l := by
  have := lwxLambda_le_of_isUnit hp2 D ω (isUnit_unitIndex D ω h)
  exact_mod_cast this

/-! ### The Claim -/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [DecidableEq ι] [IsUltrametricDist K] [CompleteSpace K] in
/-- The radius condition `v(T₀) < 8/((p²−1)t + 8)` in additive form:
`(p²−1)t·v(T₀) < 8·(1 − v(T₀))`, i.e. `(p²−1)t·v(T₀)/8 < 1 − v(T₀)` ([LWX, (4.2.1)]). -/
theorem kappa_lt (_hp2 : p ≠ 2) {T₀ : K} (_h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) :
    (((p ^ 2 - 1) * Fintype.card ι : ℕ) : ℝ) * (-Real.log ‖T₀‖) <
      8 * (Real.log p + Real.log ‖T₀‖) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp2' : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
  have hT0 : (0 : ℝ) < ‖T₀‖ := by
    rcases (norm_nonneg T₀).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_pow (by omega)] at hκ
      exact absurd hκ (not_lt.2 (pow_nonneg (inv_nonneg.2 hp0.le) _))
  have hlog := Real.log_lt_log (pow_pos (inv_pos.2 hp0) 8) hκ
  rw [Real.log_pow, Real.log_pow, Real.log_inv] at hlog
  push_cast [Nat.cast_sub hp2'] at hlog ⊢
  linarith

/-- **[LWX, §4.2 Claim], the analytic core** ((4.2.1)–(4.2.4)): if `(l, v(c_l(T₀)))` lies strictly
below the upper bound polygon at a point `T₀` of the small annulus, then some `b_{l,m}` is a
unit and `v(c_l(T₀)) = m·v(T₀)` for that `m` (the `T₀`-minimal dominant index, which is `m(l)`).
Shared-witness existential: the witness `m` carries both conclusions. -/
theorem exists_isUnit_and_coeffVal_eq (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) {l : ℕ}
    (hbelow : coeffVal (specCharSeries D ω ψ T₀) l <
      (((lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ)) :
    ∃ m : ℕ, IsUnit ((charCoeff (D.op ω) l) (m : ℤ)) ∧
      coeffVal (specCharSeries D ω ψ T₀) l = (((m : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr hp0) h0
  have hlogT : Real.log ‖T₀‖ < 0 := Real.log_neg hr0 h1
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  set L := lwxLambda p (Fintype.card ι) l with hL
  set term : ℤ → K := fun m ↦ ψ ((charCoeff (D.op ω) l) m) * T₀ ^ m with hterm
  have htend : Tendsto term cofinite (𝓝 0) :=
    (HaloInt.summable_specialize ψ hψ h0 h1 (charCoeff (D.op ω) l)).tendsto_cofinite_zero
  have hcsum : PowerSeries.coeff l (specCharSeries D ω ψ T₀) = ∑' m : ℤ, term m := by
    rw [specCharSeries, PowerSeries.coeff_mk, HaloInt.specialize]
  have hc : PowerSeries.coeff l (specCharSeries D ω ψ T₀) ≠ 0 := by
    intro h
    rw [coeffVal_eq_top_iff.2 h] at hbelow
    exact absurd hbelow (not_lt.2 le_top)
  have hcpos : 0 < ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ := norm_pos_iff.2 hc
  have hV := coeffVal_of_ne_zero hc
  rw [hV, WithTop.coe_lt_coe] at hbelow
  -- the gap of Lemma 4.1 and the radius condition
  have hgap : (lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 ≤
      L + (((p ^ 2 - 1) * Fintype.card ι : ℕ) : ℝ) / 8 := by
    have h10 := lwxUpperTwice_sub_two_mul_lwxLambda_le p (Fintype.card ι) l
      (hp.out.odd_of_ne_two hp2) Fintype.card_pos
    have h9 := two_mul_lwxLambda_le_lwxUpperTwice p (Fintype.card ι) l hp.out.pos Fintype.card_pos
    have h10' : ((4 * (lwxUpperTwice p (Fintype.card ι) l - 2 * L) : ℕ) : ℝ) ≤
        (((p ^ 2 - 1) * Fintype.card ι : ℕ) : ℝ) := by exact_mod_cast h10
    rw [Nat.cast_mul, Nat.cast_sub h9, ← hL] at h10'
    push_cast at h10' ⊢
    linarith
  have hκ' := kappa_lt hp2 h1 hκ
  have hstar : -Real.log ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ <
      (L : ℝ) * (-Real.log ‖T₀‖) + Real.log p + Real.log ‖T₀‖ := by
    have hvT : 0 < -Real.log ‖T₀‖ := by linarith
    have h1' := mul_le_mul_of_nonneg_right hgap hvT.le
    nlinarith
  -- terms below `λ(l)` are strictly smaller than the coefficient
  have hsmall : ∀ m : ℤ, m < L →
      ‖term m‖ < ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ := fun m hm ↦ by
    have hb := norm_coeff_mul_zpow_le_of_lt hp2 D ω ψ hψ h0 h1 l hm
    rcases eq_or_ne (term m) 0 with h | h
    · rw [h, norm_zero]
      exact hcpos
    · rw [← Real.log_lt_log_iff (norm_pos_iff.2 h) hcpos]
      have h2 := Real.log_le_log (norm_pos_iff.2 h) hb
      rw [Real.log_mul (pow_pos hr0 _).ne' (div_pos (inv_pos.2 hp0) hr0).ne', Real.log_pow,
        Real.log_div (inv_ne_zero hp0.ne') hr0.ne', Real.log_inv] at h2
      linarith
  -- a dominant index `m ≥ λ(l)` exists
  have hex : ∃ m : ℕ, L ≤ m ∧
      ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ ≤ ‖term (m : ℤ)‖ := by
    by_contra hcon
    have hall : ∀ m : ℤ, ‖term m‖ < ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ :=
      fun m ↦ by
        rcases lt_or_ge m L with hm | hm
        · exact hsmall m hm
        · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg L) hm)
          by_contra hle
          exact hcon ⟨n, by exact_mod_cast hm, not_lt.1 hle⟩
    have := norm_tsum_lt_of_forall_lt htend hcpos hall
    rw [← hcsum] at this
    exact lt_irrefl _ this
  -- the least dominant index is a unit
  set m₀ := Nat.find hex with hm₀def
  have hm₀ := Nat.find_spec hex
  have hunit : IsUnit ((charCoeff (D.op ω) l) (m₀ : ℤ)) := by
    by_contra hnu
    have hb1 : ‖(charCoeff (D.op ω) l) (m₀ : ℤ)‖ ≤ (p : ℝ)⁻¹ := by
      have hlt : ‖(charCoeff (D.op ω) l) (m₀ : ℤ)‖ < 1 :=
        lt_of_le_of_ne (PadicInt.norm_le_one _) (fun h ↦ hnu (PadicInt.isUnit_iff.2 h))
      have := (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one _ (-1)).2 (by simpa using hlt)
      simpa using this
    have h2 : ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ ≤ (p : ℝ)⁻¹ * ‖T₀‖ ^ L := by
      calc ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ ≤ ‖term (m₀ : ℤ)‖ := hm₀.2
        _ = ‖(charCoeff (D.op ω) l) (m₀ : ℤ)‖ * ‖T₀‖ ^ (m₀ : ℤ) := by
            rw [hterm]
            simp only
            rw [norm_mul, hψ, norm_zpow]
        _ ≤ (p : ℝ)⁻¹ * ‖T₀‖ ^ (L : ℤ) :=
            mul_le_mul hb1 (zpow_le_zpow_right_of_le_one₀ hr0 h1.le (by exact_mod_cast hm₀.1))
              (zpow_nonneg hr0.le _) (inv_nonneg.2 hp0.le)
        _ = (p : ℝ)⁻¹ * ‖T₀‖ ^ L := by rw [zpow_natCast]
    have h3 := Real.log_le_log hcpos h2
    rw [Real.log_mul (inv_pos.2 hp0).ne' (pow_pos hr0 _).ne', Real.log_inv, Real.log_pow] at h3
    linarith
  have hdiag : ‖term (m₀ : ℤ)‖ = ‖T₀‖ ^ m₀ := by
    rw [hterm]
    simp only
    rw [norm_mul, hψ, norm_zpow, PadicInt.isUnit_iff.1 hunit, one_mul, zpow_natCast]
  have hothers : ∀ m : ℤ, m ≠ m₀ → ‖term m‖ < ‖T₀‖ ^ m₀ := fun m hm ↦ by
    rcases lt_or_ge m L with hmL | hmL
    · exact (hsmall m hmL).trans_le (hm₀.2.trans hdiag.le)
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg L) hmL)
      rcases lt_trichotomy n m₀ with h | h | h
      · have hnot := Nat.find_min hex h
        have hlt : ‖term (n : ℤ)‖ < ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ :=
          not_le.1 fun hle ↦ hnot ⟨by exact_mod_cast hmL, hle⟩
        exact hlt.trans_le (hm₀.2.trans hdiag.le)
      · exact absurd (by rw [h]) hm
      · calc ‖term (n : ℤ)‖ ≤ 1 * ‖T₀‖ ^ (n : ℤ) := by
              rw [hterm]
              simp only
              rw [norm_mul, hψ, norm_zpow]
              exact mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (zpow_nonneg hr0.le _)
          _ = ‖T₀‖ ^ (n : ℤ) := one_mul _
          _ < ‖T₀‖ ^ (m₀ : ℤ) := zpow_lt_zpow_right_of_lt_one₀ hr0 h1 (by exact_mod_cast h)
          _ = ‖T₀‖ ^ m₀ := zpow_natCast _ _
  have hnorm : ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ = ‖T₀‖ ^ m₀ := by
    rw [hcsum]
    exact norm_tsum_eq_of_forall_lt htend hdiag hothers
  refine ⟨m₀, hunit, ?_⟩
  rw [hV, hnorm, Real.log_pow]
  congr 1
  ring

/-- Strictly below the upper bound polygon at one point of the small annulus ⟹ `IsBelowUpper`
(`m(l) ≤ m` and `m·v(T₀) = v(c_l(T₀)) < upper(l)·v(T₀)`). -/
theorem isBelowUpper_of_coeffVal_lt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) {l : ℕ}
    (hbelow : coeffVal (specCharSeries D ω ψ T₀) l <
      (((lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ)) :
    IsBelowUpper D ω l := by
  obtain ⟨m, hu, hv⟩ := exists_isUnit_and_coeffVal_eq hp2 D ω ψ hψ h0 h1 hκ hbelow
  refine ⟨⟨m, hu⟩, ?_⟩
  have hle : unitIndex D ω l ≤ m := unitIndex_le D ω hu
  rw [hv, WithTop.coe_lt_coe] at hbelow
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (by exact_mod_cast hp.out.pos)) h0
  have hvT : 0 < -Real.log ‖T₀‖ := by
    have := Real.log_neg hr0 h1
    linarith
  have h2 : (2 * m : ℝ) < lwxUpperTwice p (Fintype.card ι) l := by
    have := lt_of_mul_lt_mul_right hbelow hvT.le
    linarith
  have h3 : 2 * m < lwxUpperTwice p (Fintype.card ι) l := by exact_mod_cast h2
  omega

/-- **[LWX, §4.2 Claim], `T`-independence**: for `l` strictly below the upper bound polygon,
`v(c_l(T)) = m(l)·v(T)` at every point `T` of the small annulus. -/
theorem coeffVal_specCharSeries_eq_unitIndex_mul (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) {l : ℕ}
    (h : IsBelowUpper D ω l) :
    coeffVal (specCharSeries D ω ψ T₀) l =
      (((unitIndex D ω l : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) := by
  classical
  obtain ⟨hex, hlt⟩ := h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr hp0) h0
  have hlogT : Real.log ‖T₀‖ < 0 := Real.log_neg hr0 h1
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  set L := lwxLambda p (Fintype.card ι) l with hL
  set m₀ := unitIndex D ω l with hm₀
  have hunit := isUnit_unitIndex D ω hex
  have hLm : L ≤ m₀ := lwxLambda_le_unitIndex hp2 D ω hex
  set term : ℤ → K := fun m ↦ ψ ((charCoeff (D.op ω) l) m) * T₀ ^ m with hterm
  have htend : Tendsto term cofinite (𝓝 0) :=
    (HaloInt.summable_specialize ψ hψ h0 h1 (charCoeff (D.op ω) l)).tendsto_cofinite_zero
  have hcsum : PowerSeries.coeff l (specCharSeries D ω ψ T₀) = ∑' m : ℤ, term m := by
    rw [specCharSeries, PowerSeries.coeff_mk, HaloInt.specialize]
  have hgap : (lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 ≤
      L + (((p ^ 2 - 1) * Fintype.card ι : ℕ) : ℝ) / 8 := by
    have h10 := lwxUpperTwice_sub_two_mul_lwxLambda_le p (Fintype.card ι) l
      (hp.out.odd_of_ne_two hp2) Fintype.card_pos
    have h9 := two_mul_lwxLambda_le_lwxUpperTwice p (Fintype.card ι) l hp.out.pos Fintype.card_pos
    have h10' : ((4 * (lwxUpperTwice p (Fintype.card ι) l - 2 * L) : ℕ) : ℝ) ≤
        (((p ^ 2 - 1) * Fintype.card ι : ℕ) : ℝ) := by exact_mod_cast h10
    rw [Nat.cast_mul, Nat.cast_sub h9, ← hL] at h10'
    push_cast at h10' ⊢
    linarith
  have hκ' := kappa_lt hp2 h1 hκ
  have hvT : 0 < -Real.log ‖T₀‖ := by linarith
  have hm₀lt : (m₀ : ℝ) < (lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 := by
    have : (2 * m₀ : ℝ) < lwxUpperTwice p (Fintype.card ι) l := by exact_mod_cast hlt
    linarith
  have hkey : (m₀ : ℝ) * (-Real.log ‖T₀‖) <
      (L : ℝ) * (-Real.log ‖T₀‖) + Real.log p + Real.log ‖T₀‖ := by
    have h1' := mul_le_mul_of_nonneg_right hgap hvT.le
    have h2' := mul_lt_mul_of_pos_right hm₀lt hvT
    nlinarith
  have hdiag : ‖term (m₀ : ℤ)‖ = ‖T₀‖ ^ m₀ := by
    rw [hterm]
    simp only
    rw [norm_mul, hψ, norm_zpow, PadicInt.isUnit_iff.1 hunit, one_mul, zpow_natCast]
  have hothers : ∀ m : ℤ, m ≠ m₀ → ‖term m‖ < ‖T₀‖ ^ m₀ := fun m hm ↦ by
    have hpow : 0 < ‖T₀‖ ^ m₀ := pow_pos hr0 _
    rcases lt_or_ge m L with hmL | hmL
    · have hb := norm_coeff_mul_zpow_le_of_lt hp2 D ω ψ hψ h0 h1 l hmL
      rcases eq_or_ne (term m) 0 with h | h
      · rw [h, norm_zero]
        exact hpow
      · rw [← Real.log_lt_log_iff (norm_pos_iff.2 h) hpow, Real.log_pow]
        have h2 := Real.log_le_log (norm_pos_iff.2 h) hb
        rw [Real.log_mul (pow_pos hr0 _).ne' (div_pos (inv_pos.2 hp0) hr0).ne', Real.log_pow,
          Real.log_div (inv_ne_zero hp0.ne') hr0.ne', Real.log_inv] at h2
        linarith
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg L) hmL)
      rcases lt_trichotomy n m₀ with h | h | h
      · have hnu := not_isUnit_of_lt_unitIndex D ω h
        have hb1 : ‖(charCoeff (D.op ω) l) (n : ℤ)‖ ≤ (p : ℝ)⁻¹ := by
          have hlt1 : ‖(charCoeff (D.op ω) l) (n : ℤ)‖ < 1 :=
            lt_of_le_of_ne (PadicInt.norm_le_one _) (fun h ↦ hnu (PadicInt.isUnit_iff.2 h))
          have := (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one _ (-1)).2 (by simpa using hlt1)
          simpa using this
        have hb : ‖term (n : ℤ)‖ ≤ (p : ℝ)⁻¹ * ‖T₀‖ ^ L := by
          calc ‖term (n : ℤ)‖ = ‖(charCoeff (D.op ω) l) (n : ℤ)‖ * ‖T₀‖ ^ (n : ℤ) := by
                rw [hterm]
                simp only
                rw [norm_mul, hψ, norm_zpow]
            _ ≤ (p : ℝ)⁻¹ * ‖T₀‖ ^ (L : ℤ) :=
                mul_le_mul hb1 (zpow_le_zpow_right_of_le_one₀ hr0 h1.le (by exact_mod_cast hmL))
                  (zpow_nonneg hr0.le _) (inv_nonneg.2 hp0.le)
            _ = (p : ℝ)⁻¹ * ‖T₀‖ ^ L := by rw [zpow_natCast]
        rcases eq_or_ne (term (n : ℤ)) 0 with h0' | h0'
        · rw [h0', norm_zero]
          exact hpow
        · rw [← Real.log_lt_log_iff (norm_pos_iff.2 h0') hpow, Real.log_pow]
          have h2 := Real.log_le_log (norm_pos_iff.2 h0') hb
          rw [Real.log_mul (inv_pos.2 hp0).ne' (pow_pos hr0 _).ne', Real.log_inv,
            Real.log_pow] at h2
          linarith
      · exact absurd (by rw [h]) hm
      · calc ‖term (n : ℤ)‖ ≤ 1 * ‖T₀‖ ^ (n : ℤ) := by
              rw [hterm]
              simp only
              rw [norm_mul, hψ, norm_zpow]
              exact mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (zpow_nonneg hr0.le _)
          _ = ‖T₀‖ ^ (n : ℤ) := one_mul _
          _ < ‖T₀‖ ^ (m₀ : ℤ) := zpow_lt_zpow_right_of_lt_one₀ hr0 h1 (by exact_mod_cast h)
          _ = ‖T₀‖ ^ m₀ := zpow_natCast _ _
  have hnorm : ‖PowerSeries.coeff l (specCharSeries D ω ψ T₀)‖ = ‖T₀‖ ^ m₀ := by
    rw [hcsum]
    exact norm_tsum_eq_of_forall_lt htend hdiag hothers
  have hc : PowerSeries.coeff l (specCharSeries D ω ψ T₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact absurd hnorm.symm (pow_pos hr0 _).ne'
  rw [coeffVal_of_ne_zero hc, hnorm, Real.log_pow]
  congr 1
  ring

/-- The contrapositive of the Claim: if `l` is not strictly below the upper bound polygon, then
`v(c_l(T)) ≥ upper(l)·v(T)` at every point `T` of the small annulus. -/
theorem le_coeffVal_specCharSeries_of_not_isBelowUpper (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) {l : ℕ}
    (h : ¬ IsBelowUpper D ω l) :
    (((lwxUpperTwice p (Fintype.card ι) l : ℝ) / 2 * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) ≤
      coeffVal (specCharSeries D ω ψ T₀) l :=
  not_lt.1 fun hlt ↦ h (isBelowUpper_of_coeffVal_lt hp2 D ω ψ hψ h0 h1 hκ hlt)

end LWX

end
