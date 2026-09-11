/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«05_Sharpness»
import PhD.LWX.«05_UpperPolygon»
import PhD.NewtonPolygons.Support

/-!
# The vertex analysis of [LWX, Theorem 1.3, proof Step II]

[LWX, §3.23 Step II] turns the touching of the Newton polygon with the lower bound polygon
at `P_k = (n_k, λ(n_k)v(T))` into the **unit indices**

* `leftIndex D ω k` = `n_k^−`, the minimal `n ∈ [n_k − t, n_k]` with `b_{n,λ(n)} ∈ ℤ_p^×`,
* `rightIndex D ω k` = `n_k^+`, the maximal `n ∈ [n_k, n_k + t]` with `b_{n,λ(n)} ∈ ℤ_p^×`,

and then reads the polygon at **every** halo point `T`: `(n_k^−, λ(n_k^−)v(T))` and
`(n_k^+, λ(n_k^+)v(T))` are consecutive vertices, joined by the segment of slope `kφ(q)v(T)`
through `(n_k, λ(n_k)v(T))`.  The existence of the unit indices is the `T`-free
**touching hypothesis** `HasUnitBand D ω k` — exactly what [LWX, Step I] supplies from
Atkin–Lehner theory and classicality (out of scope here), and `hasUnitBand_of_height_eq`
shows it is implied by touching at any single halo point.

The main statements are height/unit-slope readings of the specialized polygon
`newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)`:
`height_specCharSeries_eq_bandLine` (on `[n_k^−, n_k^+]`), the strict inequalities outside,
and the **[LWX, Thm 1.3] slope statement** `unitSlope_specCharSeries_eq_iff` /
`unitSlope_specCharSeries_mem_Ioo`: the `j`-th slope is `kφ(q)v(T)` exactly for
`j ∈ [n_k^−, n_k^+)` (so `deg X_k = n_k^+ − n_k^−`) and lies strictly between `kφ(q)v(T)` and
`(k+1)φ(q)v(T)` for `j ∈ [n_k^+, n_{k+1}^−)` (so `deg X_{(k,k+1)} = n_{k+1}^− − n_k^+`).
-/

open Filter Topology Finset TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Unit coefficients and the unit indices -/

/-- `b_{n,λ(n)} ∈ ℤ_p^×`: the `T^{λ(n)}`-coefficient of `c_n` is a `p`-adic unit
([LWX, Cor 3.18 / (3.23.2)]). -/
def IsUnitCoeff (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) : Prop :=
  IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))

/-- `c₀ = 1`, so `b_{0,0} = 1` is a unit. -/
theorem isUnitCoeff_zero (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    IsUnitCoeff D ω 0 := by
  unfold IsUnitCoeff
  rw [charCoeff_zero]
  simp [lwxLambda, HaloInt.coeff_one]

/-- `n_k^−`: the minimal index in `[n_k − t, n_k]` with a unit coefficient ([LWX, p. 26]);
`sInf`, so junk `0` if there is none. -/
def leftIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) : ℕ :=
  sInf {n : ℕ | touchX p (Fintype.card ι) k ≤ n + Fintype.card ι ∧
    n ≤ touchX p (Fintype.card ι) k ∧ IsUnitCoeff D ω n}

/-- `n_k^+`: the maximal index in `[n_k, n_k + t]` with a unit coefficient ([LWX, p. 26]);
`sSup`, so junk `0` if there is none. -/
def rightIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) : ℕ :=
  sSup {n : ℕ | touchX p (Fintype.card ι) k ≤ n ∧
    n ≤ touchX p (Fintype.card ι) k + Fintype.card ι ∧ IsUnitCoeff D ω n}

/-- **The touching hypothesis** (`T`-free form of [LWX, Step I]'s conclusion at `n_k`): a unit
coefficient exists in `[n_k − t, n_k]` and one in `[n_k, n_k + t]`.  By
`hasUnitBand_of_height_eq` it is equivalent to the Newton polygon touching the lower bound
polygon at `(n_k, λ(n_k)v(T₀))` for one (equivalently every) halo point `T₀`. -/
def HasUnitBand (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) : Prop :=
  (∃ n, touchX p (Fintype.card ι) k ≤ n + Fintype.card ι ∧
    n ≤ touchX p (Fintype.card ι) k ∧ IsUnitCoeff D ω n) ∧
  (∃ n, touchX p (Fintype.card ι) k ≤ n ∧
    n ≤ touchX p (Fintype.card ι) k + Fintype.card ι ∧ IsUnitCoeff D ω n)

/-- The touching hypothesis holds at `k = 0` (`n₀^− = 0`, [LWX, p. 26]). -/
theorem hasUnitBand_zero (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    HasUnitBand D ω 0 :=
  ⟨⟨0, by simp [touchX], by simp [touchX], isUnitCoeff_zero D ω⟩,
    ⟨0, by simp [touchX], by simp [touchX], isUnitCoeff_zero D ω⟩⟩

/-- `n_k^−` lies in `[n_k − t, n_k]` and carries a unit coefficient. -/
theorem leftIndex_mem (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k : ℕ}
    (hb : HasUnitBand D ω k) :
    touchX p (Fintype.card ι) k ≤ leftIndex D ω k + Fintype.card ι ∧
      leftIndex D ω k ≤ touchX p (Fintype.card ι) k ∧ IsUnitCoeff D ω (leftIndex D ω k) :=
  Nat.sInf_mem (s := {n : ℕ | touchX p (Fintype.card ι) k ≤ n + Fintype.card ι ∧
    n ≤ touchX p (Fintype.card ι) k ∧ IsUnitCoeff D ω n}) hb.1

/-- Minimality of `n_k^−`: no unit coefficient in `[n_k − t, n_k^−)`. -/
theorem not_isUnitCoeff_of_lt_leftIndex (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k n : ℕ}
    (hb : HasUnitBand D ω k) (hn : touchX p (Fintype.card ι) k ≤ n + Fintype.card ι)
    (hlt : n < leftIndex D ω k) : ¬ IsUnitCoeff D ω n := fun hu ↦ by
  have hle := (leftIndex_mem D ω hb).2.1
  have hmem : n ∈ {n : ℕ | touchX p (Fintype.card ι) k ≤ n + Fintype.card ι ∧
      n ≤ touchX p (Fintype.card ι) k ∧ IsUnitCoeff D ω n} := ⟨hn, by omega, hu⟩
  exact absurd hlt (not_lt.2 (Nat.sInf_le hmem))

/-- `n_k^+` lies in `[n_k, n_k + t]` and carries a unit coefficient. -/
theorem rightIndex_mem (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k : ℕ}
    (hb : HasUnitBand D ω k) :
    touchX p (Fintype.card ι) k ≤ rightIndex D ω k ∧
      rightIndex D ω k ≤ touchX p (Fintype.card ι) k + Fintype.card ι ∧
      IsUnitCoeff D ω (rightIndex D ω k) :=
  Nat.sSup_mem (s := {n : ℕ | touchX p (Fintype.card ι) k ≤ n ∧
    n ≤ touchX p (Fintype.card ι) k + Fintype.card ι ∧ IsUnitCoeff D ω n}) hb.2
    ⟨touchX p (Fintype.card ι) k + Fintype.card ι, fun _ hn ↦ hn.2.1⟩

/-- Maximality of `n_k^+`: no unit coefficient in `(n_k^+, n_k + t]`. -/
theorem not_isUnitCoeff_of_rightIndex_lt (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k n : ℕ}
    (hb : HasUnitBand D ω k) (hn : n ≤ touchX p (Fintype.card ι) k + Fintype.card ι)
    (hlt : rightIndex D ω k < n) : ¬ IsUnitCoeff D ω n := fun hu ↦ by
  have hge := (rightIndex_mem D ω hb).1
  have hbdd : BddAbove {n : ℕ | touchX p (Fintype.card ι) k ≤ n ∧
      n ≤ touchX p (Fintype.card ι) k + Fintype.card ι ∧ IsUnitCoeff D ω n} :=
    ⟨touchX p (Fintype.card ι) k + Fintype.card ι, fun _ hn ↦ hn.2.1⟩
  have hmem : n ∈ {n : ℕ | touchX p (Fintype.card ι) k ≤ n ∧
      n ≤ touchX p (Fintype.card ι) k + Fintype.card ι ∧ IsUnitCoeff D ω n} :=
    ⟨by omega, hn, hu⟩
  exact absurd hlt (not_lt.2 (le_csSup hbdd hmem))

/-- The unit intervals are ordered: `n_k^+ ≤ n_{k+1}^−` (as `n_k + t ≤ n_{k+1} − t`). -/
theorem rightIndex_le_leftIndex_succ (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {k : ℕ}
    (hb : HasUnitBand D ω k) (hb' : HasUnitBand D ω (k + 1)) :
    rightIndex D ω k ≤ leftIndex D ω (k + 1) := by
  have h1 := (rightIndex_mem D ω hb).2.1
  have h2 := (leftIndex_mem D ω hb').1
  have h3 : touchX p
      (Fintype.card ι) (k + 1) = touchX p (Fintype.card ι) k + p * Fintype.card ι := by
    rw [touchX, touchX, Nat.succ_mul]
  have : 2 * Fintype.card ι ≤ p * Fintype.card ι := Nat.mul_le_mul_right _ hp.out.two_le
  omega

/-! ### The band line -/

/-- The line through `(n_k, λ(n_k)v(T))` of slope `k(p−1)v(T)` ([LWX, p. 26]: "the line segment
… has slope `kφ(q)v(T)`, and passes through the point `(n_k, λ(n_k)v(T))`"). -/
def bandLine (p t k : ℕ) (vT : ℝ) (x : ℤ) : ℝ :=
  ((lwxLambda p t (touchX p t k) : ℝ) + ((k * (p - 1) : ℕ) : ℝ) * ((x : ℝ) - (touchX p t k : ℝ)))
    * vT

@[simp] theorem bandLine_touchX (p t k : ℕ) (vT : ℝ) :
    bandLine p t k vT (touchX p t k) = (lwxLambda p t (touchX p t k) : ℝ) * vT := by
  simp [bandLine]

theorem bandLine_add_one (p t k : ℕ) (vT : ℝ) (x : ℤ) :
    bandLine p t k vT (x + 1) = bandLine p t k vT x + ((k * (p - 1) : ℕ) : ℝ) * vT := by
  simp only [bandLine]
  push_cast
  ring

/-- On the band the line is `λ(n)·v(T)` (the band identities of `05_UpperPolygon.lean`). -/
theorem bandLine_eq_of_mem_band (p t k : ℕ) (hp : 0 < p) (ht : 0 < t) (vT : ℝ) {n : ℕ}
    (h1 : touchX p t k ≤ n + t) (h2 : n ≤ touchX p t k + t) :
    bandLine p t k vT n = (lwxLambda p t n : ℝ) * vT := by
  rcases le_or_gt (touchX p t k) n with hn | hn
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hi : i ≤ t := by omega
    rw [lwxLambda_touchX_add p t k i hp ht hi, bandLine]
    push_cast
    ring
  · obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hn.le
    have hi' : i ≤ t := by omega
    have hn' : touchX p t k - i = n := by omega
    have hsub := lwxLambda_touchX_sub p t k i hp ht hi' (by omega)
    rw [hn'] at hsub
    have hc : ((n : ℤ) : ℝ) - (touchX p t k : ℝ) = -(i : ℝ) := by
      rw [hi]
      push_cast
      ring
    have hL : (lwxLambda p t (touchX p t k) : ℝ) =
        lwxLambda p t n + ((k * (p - 1) : ℕ) : ℝ) * i := by
      exact_mod_cast hsub.symm
    rw [bandLine, hc, hL]
    ring

/-! ### The specialized valuations in `negLogNorm` units -/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- [LWX, Cor 3.18] in `coeffVal` form: `v(c_n(T₀)) ≥ λ(n)·v(T₀)`. -/
theorem le_coeffVal_specCharSeries (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) :
    (((lwxLambda p (Fintype.card ι) n : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) ≤
      coeffVal (specCharSeries D ω ψ T₀) n := by
  by_cases hc : PowerSeries.coeff n (specCharSeries D ω ψ T₀) = 0
  · rw [coeffVal_eq_top_iff.2 hc]
    exact le_top
  · rw [coeffVal_of_ne_zero hc, WithTop.coe_le_coe]
    have h2 := Real.log_le_log (norm_pos_iff.2 hc)
      (norm_specCharSeries_coeff_le hp2 D ω ψ hψ h0 h1 n)
    rw [Real.log_pow] at h2
    linarith

/-- [LWX, (3.23.2)], unit case: `v(c_n(T₀)) = λ(n)·v(T₀)`. -/
theorem coeffVal_specCharSeries_of_isUnitCoeff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {n : ℕ} (hu : IsUnitCoeff D ω n) :
    coeffVal (specCharSeries D ω ψ T₀) n =
      (((lwxLambda p (Fintype.card ι) n : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithTop ℝ) := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (by exact_mod_cast hp.out.pos)) h0
  have heq := norm_specCharSeries_coeff_eq_of_isUnit hp2 D ω ψ hψ h0 h1 n hu
  have hc : PowerSeries.coeff n (specCharSeries D ω ψ T₀) ≠ 0 := by
    intro h
    rw [h, norm_zero] at heq
    exact absurd heq.symm (pow_pos hr0 _).ne'
  rw [coeffVal_of_ne_zero hc, heq, Real.log_pow]
  congr 1
  ring

/-- [LWX, Cor 3.18], the margin in `coeffVal` form: for a non-unit `b_{n,λ(n)}`,
`v(c_n(T₀)) ≥ λ(n)·v(T₀) + min{v(T₀), 1 − v(T₀)}`. -/
theorem le_coeffVal_specCharSeries_of_not_isUnitCoeff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {n : ℕ} (hu : ¬ IsUnitCoeff D ω n) :
    (((lwxLambda p (Fintype.card ι) n : ℝ) * (-Real.log ‖T₀‖) +
        min (-Real.log ‖T₀‖) (Real.log p + Real.log ‖T₀‖) : ℝ) : WithTop ℝ) ≤
      coeffVal (specCharSeries D ω ψ T₀) n := by
  by_cases hc : PowerSeries.coeff n (specCharSeries D ω ψ T₀) = 0
  · rw [coeffVal_eq_top_iff.2 hc]
    exact le_top
  · rw [coeffVal_of_ne_zero hc, WithTop.coe_le_coe]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr hp0) h0
    have h2 := Real.log_le_log (norm_pos_iff.2 hc)
      (norm_specCharSeries_coeff_le_of_not_isUnit hp2 D ω ψ hψ h0 h1 n hu)
    rw [Real.log_mul (pow_pos hr0 _).ne' (lt_max_of_lt_left hr0).ne', Real.log_pow] at h2
    rcases le_total ‖T₀‖ ((p : ℝ)⁻¹ / ‖T₀‖) with h | h
    · rw [max_eq_right h, Real.log_div (inv_ne_zero hp0.ne') hr0.ne', Real.log_inv] at h2
      have := min_le_right (-Real.log ‖T₀‖) (Real.log p + Real.log ‖T₀‖)
      linarith
    · rw [max_eq_left h] at h2
      have := min_le_left (-Real.log ‖T₀‖) (Real.log p + Real.log ‖T₀‖)
      linarith

/-! ### Helpers: the lower polygon lies above every band line, and the specialized polygon -/

omit [Fintype
    ι] [DecidableEq ι] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The band line through `(n_k, λ(n_k))` of slope `k(p−1)` is a supporting line of `λ`:
`bandLine n ≤ λ(n)·v(T)` for every `n` (equality on the band, [LWX, p. 25]). -/
theorem bandLine_le_lwxLambda_mul (p t k : ℕ) (hp : 1 < p) (ht : 0 < t) {vT : ℝ} (hvT : 0 ≤ vT)
    (n : ℕ) : bandLine p t k vT n ≤ (lwxLambda p t n : ℝ) * vT := by
  have hp0 : 0 < p := by omega
  rcases le_or_gt (touchX p t k + t) n with hr | hr
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right _ _) hr)
    have hi : t ≤ i := by omega
    have hge := lwxLambda_touchX_add_ge p t k i hp ht hi
    have hge' : ((lwxLambda p t (touchX p t k) : ℝ) + ((k * (p - 1) : ℕ) : ℝ) * i) ≤
        lwxLambda p t (touchX p t k + i) := by
      have : lwxLambda p t (touchX p t k) + k * (p - 1) * i ≤ lwxLambda p t (touchX p t k + i) := by
        omega
      exact_mod_cast this
    have hm := mul_le_mul_of_nonneg_right hge' hvT
    rw [bandLine]
    push_cast at hm ⊢
    linarith
  · rcases le_or_gt (touchX p t k) (n + t) with hl | hl
    · rw [bandLine_eq_of_mem_band p t k hp0 ht vT hl hr.le]
    · obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le (show n ≤ touchX p t k by omega)
      have hit : t ≤ i := by omega
      have hge := lwxLambda_touchX_sub_ge p t k i hp ht hit (by omega)
      have hn : touchX p t k - i = n := by omega
      rw [hn] at hge
      have hge' : (lwxLambda p t (touchX p t k) : ℝ) ≤
          lwxLambda p t n + ((k * (p - 1) : ℕ) : ℝ) * i := by
        have : lwxLambda p t (touchX p t k) ≤ lwxLambda p t n + k * (p - 1) * i := by omega
        exact_mod_cast this
      have hc : ((n : ℤ) : ℝ) - (touchX p t k : ℝ) = -(i : ℝ) := by
        rw [hi]
        push_cast
        ring
      have hm := mul_le_mul_of_nonneg_right hge' hvT
      rw [bandLine, hc]
      push_cast at hm ⊢
      linarith

omit [Fintype
    ι] [DecidableEq ι] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- Beyond the band on the right, `λ` exceeds the band line by at least `(n − n_k − t)·v(T)`. -/
theorem bandLine_add_le_lwxLambda_mul_of_le (p t k : ℕ) (hp : 1 < p) (ht : 0 < t) {vT : ℝ}
    (hvT : 0 ≤ vT) {n : ℕ} (hn : touchX p t k + t ≤ n) :
    bandLine p t k vT n + ((n - touchX p t k - t : ℕ) : ℝ) * vT ≤ (lwxLambda p t n : ℝ) * vT := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right _ _) hn)
  have hi : t ≤ i := by omega
  have hge := lwxLambda_touchX_add_ge p t k i hp ht hi
  have hge' : ((lwxLambda p t (touchX p t k) : ℝ) + ((k * (p - 1) : ℕ) : ℝ) * i +
      ((i - t : ℕ) : ℝ)) ≤ lwxLambda p t (touchX p t k + i) := by exact_mod_cast hge
  have e : touchX p t k + i - touchX p t k - t = i - t := by omega
  have hm := mul_le_mul_of_nonneg_right hge' hvT
  rw [e, bandLine]
  push_cast at hm ⊢
  linarith

omit [Fintype
    ι] [DecidableEq ι] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- Beyond the band on the left, `λ` exceeds the band line by at least `(n_k − t − n)·v(T)`. -/
theorem bandLine_add_le_lwxLambda_mul_of_ge (p t k : ℕ) (hp : 1 < p) (ht : 0 < t) {vT : ℝ}
    (hvT : 0 ≤ vT) {n : ℕ} (hn : n + t ≤ touchX p t k) :
    bandLine p t k vT n + ((touchX p t k - t - n : ℕ) : ℝ) * vT ≤ (lwxLambda p t n : ℝ) * vT := by
  obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le (show n ≤ touchX p t k by omega)
  have hit : t ≤ i := by omega
  have hge := lwxLambda_touchX_sub_ge p t k i hp ht hit (by omega)
  have hn' : touchX p t k - i = n := by omega
  rw [hn'] at hge
  have hge' : (lwxLambda p t (touchX p t k) : ℝ) + ((i - t : ℕ) : ℝ) ≤
      lwxLambda p t n + ((k * (p - 1) : ℕ) : ℝ) * i := by exact_mod_cast hge
  have e : touchX p t k - t - n = i - t := by omega
  have hc : ((n : ℤ) : ℝ) - (touchX p t k : ℝ) = -(i : ℝ) := by
    rw [hi]
    push_cast
    ring
  have hm := mul_le_mul_of_nonneg_right hge' hvT
  rw [e, bandLine, hc]
  push_cast at hm ⊢
  linarith

omit [Fintype
    ι] [DecidableEq ι] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- A lower bound on `coeffVal` transfers to `pointHeight`. -/
theorem le_pointHeight_of_le_coeffVal {v : ℕ → WithTop ℝ} {n : ℕ} {a : ℝ}
    (h : (a : WithTop ℝ) ≤ v n) : (a : WithBotTop ℝ) ≤ pointHeight v n := by
  cases hv : v n with
  | top => rw [pointHeight_eq_top_iff.2 hv]; exact le_top
  | coe b =>
    rw [pointHeight_coe hv, Algebra.algebraMap_self_apply]
    rw [hv, WithTop.coe_le_coe] at h
    exact WithBotTop.coe_le_coe.2 h

omit [Fintype
    ι] [DecidableEq ι] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `pointHeight` of a finite value. -/
theorem pointHeight_eq_of_coeffVal_eq {v : ℕ → WithTop ℝ} {n : ℕ} {a : ℝ}
    (h : v n = (a : WithTop ℝ)) : pointHeight v n = (a : WithBotTop ℝ) := by
  rw [pointHeight_coe h, Algebra.algebraMap_self_apply]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The specialized series has a finite coefficient valuation (`c₀ = 1`). -/
theorem exists_coeffVal_specCharSeries_ne_top (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (ψ : ℤ_[p] →+* K) (T₀ : K) : ∃ i, coeffVal (specCharSeries D ω ψ T₀) i ≠ ⊤ :=
  ⟨0, (coeffVal_zero_of_coeff_zero_eq_one (specCharSeries_coeff_zero D ω ψ T₀)).trans_ne
    WithTop.coe_ne_top⟩

/-- The coefficient valuations of the specialized series are admissible (all `≥ 0`). -/
theorem isAdmissible_coeffVal_specCharSeries (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0
        :
            (p
                : ℝ)⁻¹ < ‖T₀‖)
                    (h1 : ‖T₀‖ < 1) : IsAdmissible (coeffVal (specCharSeries D ω ψ T₀)) := by
  have hT0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 (by exact_mod_cast hp.out.pos)).trans h0
  refine isAdmissible_of_affine_bound (coeffVal (specCharSeries D ω ψ T₀)) (m := 0) (b := 0)
    fun k a hva ↦ ?_
  have hk : PowerSeries.coeff k (specCharSeries D ω ψ T₀) ≠ 0 := fun hcz ↦
    WithTop.coe_ne_top (hva.symm.trans (coeffVal_eq_top_iff.mpr hcz))
  have haeq : a = -Real.log ‖PowerSeries.coeff k (specCharSeries D ω ψ T₀)‖ :=
    WithTop.coe_inj.mp (hva.symm.trans (coeffVal_of_ne_zero hk))
  have hle1 : ‖PowerSeries.coeff k (specCharSeries D ω ψ T₀)‖ ≤ 1 :=
    (norm_specCharSeries_coeff_le hp2 D ω ψ hψ h0 h1 k).trans (pow_le_one₀ hT0.le h1.le)
  have := Real.log_nonpos (norm_nonneg _) hle1
  simp only [Algebra.algebraMap_self, RingHom.id_apply, haeq]
  linarith

/-- The specialized series has the Newton polygon of its coefficient valuations (the
`hex`/`hadm` block of `isBelow_newtonPolygon_specCharSeries`, made reusable). -/
theorem isNewtonPolygonOf_specCharSeries (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) :
    IsNewtonPolygonOf (coeffVal (specCharSeries D ω ψ T₀))
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)) :=
  isNewtonPolygonOf_powerSeries negLogNorm _ (exists_coeffVal_specCharSeries_ne_top D ω ψ T₀)
    (isAdmissible_coeffVal_specCharSeries hp2 D ω ψ hψ h0 h1)

/-- The specialized polygon has no `⊥` unit slope. -/
theorem unitSlope_specCharSeries_ne_bot (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j ≠ ⊥ :=
  newtonPolygon₀OfSeq_unitSlope_ne_bot _ (exists_coeffVal_specCharSeries_ne_top D ω ψ T₀)
    (isAdmissible_coeffVal_specCharSeries hp2 D ω ψ hψ h0 h1) j

omit [Fintype
    ι] [DecidableEq ι] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- A `WithBotTop ℝ` value that is neither `⊥` nor `⊤` is a real. -/
theorem exists_coe_of_ne_bot_of_ne_top {v : WithBotTop ℝ} (hb : v ≠ ⊥) (ht : v ≠ ⊤) :
    ∃ r : ℝ, v = (r : WithBotTop ℝ) := by
  induction v using WithBotTop.rec with
  | bot => exact absurd rfl hb
  | coe r => exact ⟨r, rfl⟩
  | top => exact absurd rfl ht

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The specialized polygon is anchored at `x = 0` (`c₀ = 1`). -/
theorem specCharSeries_starting_point_fst (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (ψ : ℤ_[p] →+* K) (T₀ : K) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).starting_point.1 = 0 := by
  rw [newtonPolygon₀_starting_point_of_coeff_zero_eq_one (specCharSeries_coeff_zero D ω ψ T₀)]

omit [Fintype
    ι] [DecidableEq ι] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The band line as an affine function of `x`. -/
theorem bandLine_eq_add_mul (p t k : ℕ) (vT : ℝ) (x : ℤ) :
    bandLine p t k vT x = bandLine p t k vT 0 + ((k * (p - 1) : ℕ) : ℝ) * vT * x := by
  simp only [bandLine]
  push_cast
  ring

/-- Every point of the specialized series lies on/above the band line. -/
theorem bandLine_le_pointHeight (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (k n : ℕ) :
    (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n : WithBotTop ℝ) ≤
      pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 (by exact_mod_cast hp.out.pos)).trans h0
  have hvT : 0 ≤ -Real.log ‖T₀‖ := by
    have := Real.log_neg hr0 h1
    linarith
  refine le_pointHeight_of_le_coeffVal
    (le_trans ?_ (le_coeffVal_specCharSeries hp2 D ω ψ hψ h0 h1 n))
  rw [WithTop.coe_le_coe]
  exact bandLine_le_lwxLambda_mul p (Fintype.card ι) k hp.out.one_lt Fintype.card_pos hvT n

/-- A non-unit point of the band lies at least `μ = min{v(T), 1 − v(T)}` above the band line. -/
theorem bandLine_add_min_le_pointHeight (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k n : ℕ}
    (hb1 : touchX p (Fintype.card ι) k ≤ n + Fintype.card ι)
    (hb2 : n ≤ touchX p (Fintype.card ι) k + Fintype.card ι) (hnu : ¬ IsUnitCoeff D ω n) :
    ((bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n +
        min (-Real.log ‖T₀‖) (Real.log p + Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) ≤
      pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := by
  refine le_pointHeight_of_le_coeffVal
    (le_trans ?_ (le_coeffVal_specCharSeries_of_not_isUnitCoeff hp2 D ω ψ hψ h0 h1 hnu))
  rw [WithTop.coe_le_coe,
    bandLine_eq_of_mem_band p (Fintype.card ι) k hp.out.pos Fintype.card_pos _ hb1 hb2]

/-- Left of the band every point lies at least `(n_k − t − n)·v(T)` above the band line. -/
theorem bandLine_add_le_pointHeight_of_ge (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k n : ℕ}
    (hn : n + Fintype.card ι ≤ touchX p (Fintype.card ι) k) :
    ((bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n +
        ((touchX p (Fintype.card ι) k - Fintype.card ι - n : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) :
        WithBotTop ℝ) ≤
      pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 (by exact_mod_cast hp.out.pos)).trans h0
  have hvT : 0 ≤ -Real.log ‖T₀‖ := by
    have := Real.log_neg hr0 h1
    linarith
  refine le_pointHeight_of_le_coeffVal
    (le_trans ?_ (le_coeffVal_specCharSeries hp2 D ω ψ hψ h0 h1 n))
  rw [WithTop.coe_le_coe]
  exact bandLine_add_le_lwxLambda_mul_of_ge p (Fintype.card ι) k hp.out.one_lt Fintype.card_pos
    hvT hn

/-- Right of the band every point lies at least `(n − n_k − t)·v(T)` above the band line. -/
theorem bandLine_add_le_pointHeight_of_le (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k n : ℕ}
    (hn : touchX p (Fintype.card ι) k + Fintype.card ι ≤ n) :
    ((bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n +
        ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) :
        WithBotTop ℝ) ≤
      pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 (by exact_mod_cast hp.out.pos)).trans h0
  have hvT : 0 ≤ -Real.log ‖T₀‖ := by
    have := Real.log_neg hr0 h1
    linarith
  refine le_pointHeight_of_le_coeffVal
    (le_trans ?_ (le_coeffVal_specCharSeries hp2 D ω ψ hψ h0 h1 n))
  rw [WithTop.coe_le_coe]
  exact bandLine_add_le_lwxLambda_mul_of_le p (Fintype.card ι) k hp.out.one_lt Fintype.card_pos
    hvT hn

/-! ### [LWX, Step II] at every halo point -/

/-- **[LWX, Step II]**, the segment: on `[n_k^−, n_k^+]` the Newton polygon of the specialized
series is the band line of slope `kφ(q)v(T)` through `(n_k, λ(n_k)v(T))`. -/
theorem height_specCharSeries_eq_bandLine (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {x : ℤ}
    (hx1 : (leftIndex D ω k : ℤ) ≤ x) (hx2 : x ≤ rightIndex D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height x =
      (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) x : WithBotTop ℝ) := by
  have hNP := isNewtonPolygonOf_specCharSeries hp2 D ω ψ hψ h0 h1
  have hx0 := specCharSeries_starting_point_fst D ω ψ T₀
  have hp1 : 1 < p := hp.out.one_lt
  have ht : 0 < Fintype.card ι := Fintype.card_pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 (by exact_mod_cast hp.out.pos)).trans h0
  have hvT : 0 ≤ -Real.log ‖T₀‖ := by
    have := Real.log_neg hr0 h1
    linarith
  have e : ∀ n : ℕ, bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
      ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * (n : ℝ) =
      bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n := fun n ↦ by
    rw [bandLine_eq_add_mul p (Fintype.card ι) k (-Real.log ‖T₀‖) n, Int.cast_natCast]
  -- every point lies on/above the band line
  have hpts : ∀ n : ℕ, ((bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
      ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * n : ℝ) : WithBotTop ℝ) ≤
      pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := fun n ↦ by
    refine le_pointHeight_of_le_coeffVal
      (le_trans ?_ (le_coeffVal_specCharSeries hp2 D ω ψ hψ h0 h1 n))
    rw [WithTop.coe_le_coe, e n]
    exact bandLine_le_lwxLambda_mul p (Fintype.card ι) k hp1 ht hvT n
  -- lower bound: the supporting line
  obtain ⟨xn, rfl⟩ : ∃ xn : ℕ, x = xn := ⟨x.toNat, by omega⟩
  have hlow : (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) xn : WithBotTop ℝ) ≤
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height xn := by
    have := hNP.line_le_height hx0 hpts xn
    rwa [e xn] at this
  -- upper bound: the chord between the two unit indices
  obtain ⟨hl1, hl2, hlu⟩ := leftIndex_mem D ω hb
  obtain ⟨hr1, hr2, hru⟩ := rightIndex_mem D ω hb
  have hleft : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
      (leftIndex D ω k) ≤
      (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) (leftIndex D ω k) : WithBotTop ℝ) := by
    refine (hNP.height_le _).trans (le_of_eq ?_)
    rw [pointHeight_eq_of_coeffVal_eq
      (coeffVal_specCharSeries_of_isUnitCoeff hp2 D ω ψ hψ h0 h1 hlu),
      bandLine_eq_of_mem_band p (Fintype.card ι) k hp.out.pos ht (-Real.log ‖T₀‖) hl1 (by omega)]
  have hright : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
      (rightIndex D ω k) ≤
      (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) (rightIndex D ω k) : WithBotTop ℝ) := by
    refine (hNP.height_le _).trans (le_of_eq ?_)
    rw [pointHeight_eq_of_coeffVal_eq
      (coeffVal_specCharSeries_of_isUnitCoeff hp2 D ω ψ hψ h0 h1 hru),
      bandLine_eq_of_mem_band p (Fintype.card ι) k hp.out.pos ht (-Real.log ‖T₀‖) (by omega) hr2]
  have hchord := (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height_le_chord
    (x := leftIndex D ω k) (y := xn) (z := rightIndex D ω k)
    (by rw [hx0]; exact Int.natCast_nonneg _) hx1 hx2 hleft hright
  have hline : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) (leftIndex D ω k) +
      (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) (rightIndex D ω k) -
        bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) (leftIndex D ω k)) /
        (((rightIndex D ω k : ℤ) : ℝ) - ((leftIndex D ω k : ℤ) : ℝ)) *
        (((xn : ℤ) : ℝ) - ((leftIndex D ω k : ℤ) : ℝ)) =
      bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) xn := by
    rcases eq_or_ne (rightIndex D ω k) (leftIndex D ω k) with heq | hne
    · have hxl : xn = leftIndex D ω k := by omega
      rw [heq, hxl]
      simp
    · have hne' : ((rightIndex D ω k : ℤ) : ℝ) - ((leftIndex D ω k : ℤ) : ℝ) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast hne
      rw [bandLine_eq_add_mul p (Fintype.card ι) k (-Real.log ‖T₀‖) (rightIndex D ω k),
        bandLine_eq_add_mul p (Fintype.card ι) k (-Real.log ‖T₀‖) (leftIndex D ω k),
        bandLine_eq_add_mul p (Fintype.card ι) k (-Real.log ‖T₀‖) xn]
      field_simp
      ring
  rw [hline] at hchord
  exact le_antisymm hchord hlow

/-- **[LWX, Step II]**, left vertex: strictly left of `n_k^−` the polygon lies strictly above
the band line (so `n_k^−` is a vertex). -/
theorem bandLine_lt_height_specCharSeries_of_lt_leftIndex (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {x : ℤ}
    (hx0 : 0 ≤ x) (hx : x < leftIndex D ω k) :
    (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) x : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height x := by
  have hNP := isNewtonPolygonOf_specCharSeries hp2 D ω ψ hψ h0 h1
  have hst := specCharSeries_starting_point_fst D ω ψ T₀
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 hp0).trans h0
  have hlogT := Real.log_neg hr0 h1
  have hvT : 0 < -Real.log ‖T₀‖ := by linarith
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  have hlpT : 0 < Real.log p + Real.log ‖T₀‖ := by
    have := Real.log_lt_log (inv_pos.2 hp0) h0
    rw [Real.log_inv] at this
    linarith
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = min (-Real.log ‖T₀‖) (Real.log p + Real.log ‖T₀‖) := ⟨_, rfl⟩
  have hμpos : 0 < μ := by rw [hμ]; exact lt_min hvT hlpT
  have hμle : μ ≤ -Real.log ‖T₀‖ := by rw [hμ]; exact min_le_left _ _
  obtain ⟨xn, rfl⟩ : ∃ xn : ℕ, x = xn := ⟨x.toNat, by omega⟩
  have hxN : xn < leftIndex D ω k := by exact_mod_cast hx
  have hNpos : (0 : ℝ) < leftIndex D ω k := by exact_mod_cast (show 0 < leftIndex D ω k by omega)
  obtain ⟨hl1, hl2, -⟩ := leftIndex_mem D ω hb
  have e : ∀ n : ℕ, bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
      ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * (n : ℝ) =
      bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n := fun n ↦ by
    rw [bandLine_eq_add_mul p (Fintype.card ι) k (-Real.log ‖T₀‖) n, Int.cast_natCast]
  -- the competitor: slope `b − μ/N` up to `N = n_k^−`, then `b`
  have hpts : ∀ n : ℕ, ((bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 + μ +
      (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) - μ / leftIndex D ω k) *
        min (n : ℝ) (leftIndex D ω k) +
      ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * max ((n : ℝ) - leftIndex D ω k) 0 : ℝ) :
        WithBotTop ℝ) ≤ pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := fun n ↦ by
    rcases le_or_gt (leftIndex D ω k) n with hnN | hnN
    · have hc : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 + μ +
          (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) - μ / leftIndex D ω k) *
            min (n : ℝ) (leftIndex D ω k) +
          ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * max ((n : ℝ) - leftIndex D ω k) 0 =
          bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n := by
        rw [min_eq_right (Nat.cast_le.2 hnN), max_eq_left (sub_nonneg.2 (Nat.cast_le.2 hnN)),
          ← e n]
        field_simp
        ring
      rw [hc]
      exact bandLine_le_pointHeight hp2 D ω ψ hψ h0 h1 k n
    · have hc : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 + μ +
          (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) - μ / leftIndex D ω k) *
            min (n : ℝ) (leftIndex D ω k) +
          ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * max ((n : ℝ) - leftIndex D ω k) 0 ≤
          bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n + μ := by
        rw [min_eq_left (Nat.cast_le.2 hnN.le), max_eq_right (sub_nonpos.2 (Nat.cast_le.2 hnN.le)),
          ← e n]
        have : 0 ≤ μ / leftIndex D ω k * n := by positivity
        nlinarith
      refine le_trans (WithBotTop.coe_le_coe.2 hc) ?_
      rcases le_or_gt (touchX p (Fintype.card ι) k) (n + Fintype.card ι) with hband | hbeyond
      · have hnu := not_isUnitCoeff_of_lt_leftIndex D ω hb hband hnN
        rw [hμ]
        exact bandLine_add_min_le_pointHeight hp2 D ω ψ hψ h0 h1 (k := k) hband (by omega) hnu
      · refine le_trans ?_
          (bandLine_add_le_pointHeight_of_ge hp2 D ω ψ hψ h0 h1 (k := k) (n := n) (by omega))
        rw [WithBotTop.coe_le_coe]
        have h1' : (1 : ℝ) ≤ ((touchX p (Fintype.card ι) k - Fintype.card ι - n : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ touchX p (Fintype.card ι) k - Fintype.card ι - n by omega)
        have := mul_le_mul_of_nonneg_right h1' hvT.le
        linarith
  have key := hNP.twoSlope_le_height hst
      (y₀ := bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 + μ)
    (s₁ := ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) - μ / leftIndex D ω k)
    (s₂ := ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖))
    (by have := div_pos hμpos hNpos; linarith) (N := leftIndex D ω k) hpts xn
  refine lt_of_lt_of_le ?_ key
  rw [WithBotTop.coe_lt_coe, min_eq_left (Nat.cast_le.2 hxN.le),
    max_eq_right (sub_nonpos.2 (Nat.cast_le.2 hxN.le)), ← e xn]
  have hlt : (xn : ℝ) < leftIndex D ω k := by exact_mod_cast hxN
  have : μ / leftIndex D ω k * xn < μ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hNpos]
    nlinarith
  nlinarith

/-- **[LWX, Step II]**, right vertex: strictly right of `n_k^+` the polygon lies strictly above
the band line (so `n_k^+` is a vertex). -/
theorem bandLine_lt_height_specCharSeries_of_rightIndex_lt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {x : ℤ}
    (hx : (rightIndex D ω k : ℤ) < x) :
    (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) x : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height x := by
  have hNP := isNewtonPolygonOf_specCharSeries hp2 D ω ψ hψ h0 h1
  have hst := specCharSeries_starting_point_fst D ω ψ T₀
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 hp0).trans h0
  have hlogT := Real.log_neg hr0 h1
  have hvT : 0 < -Real.log ‖T₀‖ := by linarith
  have hlpT : 0 < Real.log p + Real.log ‖T₀‖ := by
    have := Real.log_lt_log (inv_pos.2 hp0) h0
    rw [Real.log_inv] at this
    linarith
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = min (-Real.log ‖T₀‖) (Real.log p + Real.log ‖T₀‖) := ⟨_, rfl⟩
  have hμpos : 0 < μ := by rw [hμ]; exact lt_min hvT hlpT
  have hμle : μ ≤ -Real.log ‖T₀‖ := by rw [hμ]; exact min_le_left _ _
  have ht2 : (0 : ℝ) < (Fintype.card ι : ℝ) + 2 := by positivity
  obtain ⟨xn, rfl⟩ : ∃ xn : ℕ, x = xn := ⟨x.toNat, by omega⟩
  have hxN : rightIndex D ω k < xn := by exact_mod_cast hx
  obtain ⟨hr1, hr2, -⟩ := rightIndex_mem D ω hb
  have e : ∀ n : ℕ, bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
      ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * (n : ℝ) =
      bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n := fun n ↦ by
    rw [bandLine_eq_add_mul p (Fintype.card ι) k (-Real.log ‖T₀‖) n, Int.cast_natCast]
  -- the competitor: slope `b` up to `N = n_k^+`, then `b + μ/(t+2)`
  have hpts : ∀ n : ℕ, ((bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
      ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * min (n : ℝ) (rightIndex D ω k) +
      (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) + μ / ((Fintype.card ι : ℝ) + 2)) *
        max ((n : ℝ) - rightIndex D ω k) 0 : ℝ) : WithBotTop ℝ) ≤
      pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := fun n ↦ by
    rcases le_or_gt n (rightIndex D ω k) with hnN | hnN
    · have hc : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
          ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * min (n : ℝ) (rightIndex D ω k) +
          (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) + μ / ((Fintype.card ι : ℝ) + 2)) *
            max ((n : ℝ) - rightIndex D ω k) 0 =
          bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n := by
        rw [min_eq_left (Nat.cast_le.2 hnN), max_eq_right (sub_nonpos.2 (Nat.cast_le.2 hnN)),
          ← e n]
        ring
      rw [hc]
      exact bandLine_le_pointHeight hp2 D ω ψ hψ h0 h1 k n
    · have hc : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
          ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * min (n : ℝ) (rightIndex D ω k) +
          (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) + μ / ((Fintype.card ι : ℝ) + 2)) *
            max ((n : ℝ) - rightIndex D ω k) 0 =
          bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n +
            μ / ((Fintype.card ι : ℝ) + 2) * ((n : ℝ) - rightIndex D ω k) := by
        rw [min_eq_right (Nat.cast_le.2 hnN.le), max_eq_left (sub_nonneg.2 (Nat.cast_le.2 hnN.le)),
          ← e n]
        ring
      rw [hc]
      rcases le_or_gt n (touchX p (Fintype.card ι) k + Fintype.card ι) with hband | hbeyond
      · have hnu := not_isUnitCoeff_of_rightIndex_lt D ω hb hband hnN
        refine le_trans ?_
            (bandLine_add_min_le_pointHeight hp2 D ω ψ hψ h0 h1 (k := k) (by omega) hband hnu)
        rw [WithBotTop.coe_le_coe, ← hμ]
        have hd : (n : ℝ) - rightIndex D ω k ≤ Fintype.card ι := by
          have : n ≤ rightIndex D ω k + Fintype.card ι := by omega
          have := (Nat.cast_le (α := ℝ)).2 this
          push_cast at this
          linarith
        have hd0 : (0 : ℝ) ≤ (n : ℝ) - rightIndex D ω k := sub_nonneg.2 (Nat.cast_le.2 hnN.le)
        have : μ / ((Fintype.card ι : ℝ) + 2) * ((n : ℝ) - rightIndex D ω k) ≤ μ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ ht2]
          nlinarith
        linarith
      · refine le_trans ?_
          (bandLine_add_le_pointHeight_of_le hp2 D ω ψ hψ h0 h1 (k := k) (n := n) (by omega))
        rw [WithBotTop.coe_le_coe]
        have hm : (1 : ℝ) ≤ ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ n - touchX p (Fintype.card ι) k - Fintype.card ι by omega)
        have hd : (n : ℝ) - rightIndex D ω k ≤
            ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) + Fintype.card ι := by
          have : n ≤ (n - touchX p (Fintype.card ι) k - Fintype.card ι) + Fintype.card ι +
              rightIndex D ω k := by omega
          have := (Nat.cast_le (α := ℝ)).2 this
          push_cast at this
          linarith
        have hd0 : (0 : ℝ) ≤ (n : ℝ) - rightIndex D ω k := sub_nonneg.2 (Nat.cast_le.2 hnN.le)
        have : μ / ((Fintype.card ι : ℝ) + 2) * ((n : ℝ) - rightIndex D ω k) ≤
            ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) * (-Real.log ‖T₀‖) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ ht2]
          have hA := mul_le_mul_of_nonneg_left hd hμpos.le
          have hB := mul_le_mul_of_nonneg_right hμle
            (by
                positivity :
                    (0 : ℝ) ≤ ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) +
              Fintype.card ι)
          have hC : ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) + Fintype.card ι ≤
              ((n
                  - touchX p
                      (Fintype.card
                          ι) k - Fintype.card ι : ℕ) : ℝ) * ((Fintype.card ι : ℝ) + 2) := by
            nlinarith [mul_nonneg (sub_nonneg.2 hm) (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))]
          have hD := mul_le_mul_of_nonneg_left hC hvT.le
          linarith
        linarith
  have key := hNP.twoSlope_le_height hst (y₀ := bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0)
    (s₁ := ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖))
    (s₂ := ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) + μ / ((Fintype.card ι : ℝ) + 2))
    (by have := div_pos hμpos ht2; linarith) (N := rightIndex D ω k) hpts xn
  refine lt_of_lt_of_le ?_ key
  rw [WithBotTop.coe_lt_coe, min_eq_right (Nat.cast_le.2 hxN.le),
    max_eq_left (sub_nonneg.2 (Nat.cast_le.2 hxN.le)), ← e xn]
  have hlt : (rightIndex D ω k : ℝ) < xn := by exact_mod_cast hxN
  have : 0 < μ / ((Fintype.card ι : ℝ) + 2) * ((xn : ℝ) - rightIndex D ω k) :=
    mul_pos (div_pos hμpos ht2) (by linarith)
  nlinarith

/-- **Touching at every halo point**: under the touching hypothesis the Newton polygon passes
through `(n_k, λ(n_k)v(T))` ([LWX, §4]: "the Newton polygon … passes through the points
`(n_k, λ(n_k)v(T))` for all `k ≥ 0`"). -/
theorem height_specCharSeries_touchX (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        (touchX p (Fintype.card ι) k) =
      (((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) : ℝ) * (-Real.log ‖T₀‖) : ℝ) :
        WithBotTop ℝ) := by
  have h := height_specCharSeries_eq_bandLine hp2 D ω ψ hψ h0 h1 hb
    (x := touchX p (Fintype.card ι) k) (by exact_mod_cast (leftIndex_mem D ω hb).2.1)
    (by exact_mod_cast (rightIndex_mem D ω hb).1)
  rw [h, bandLine_touchX]

/-- **The bridge to [LWX, Step I]**: touching at a single halo point `T₀` forces unit coefficients
on both sides of `n_k` ([LWX, p. 25–26]: "It follows that `n_{k+1}^− ∈ [n_{k+1} − t, n_{k+1}]`
and `n_{k+1}^+ ∈ [n_{k+1}, n_{k+1} + t]`", via (3.23.2)). -/
theorem hasUnitBand_of_height_eq (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ}
    (h : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        (touchX p (Fintype.card ι) k) =
      (((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) : ℝ) * (-Real.log ‖T₀‖) : ℝ) :
        WithBotTop ℝ)) :
    HasUnitBand D ω k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hasUnitBand_zero D ω
  have hNP := isNewtonPolygonOf_specCharSeries hp2 D ω ψ hψ h0 h1
  have hst := specCharSeries_starting_point_fst D ω ψ T₀
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 hp0).trans h0
  have hlogT := Real.log_neg hr0 h1
  have hvT : 0 < -Real.log ‖T₀‖ := by linarith
  have hlpT : 0 < Real.log p + Real.log ‖T₀‖ := by
    have := Real.log_lt_log (inv_pos.2 hp0) h0
    rw [Real.log_inv] at this
    linarith
  have ht : 0 < Fintype.card ι := Fintype.card_pos
  have ht2 : (0 : ℝ) < (Fintype.card ι : ℝ) + 2 := by positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = min (-Real.log ‖T₀‖) (Real.log p + Real.log ‖T₀‖) := ⟨_, rfl⟩
  have hμpos : 0 < μ := by rw [hμ]; exact lt_min hvT hlpT
  have hμle : μ ≤ -Real.log ‖T₀‖ := by rw [hμ]; exact min_le_left _ _
  have htX : 1 ≤ touchX p (Fintype.card ι) k := Nat.mul_pos hk (Nat.mul_pos hp.out.pos ht)
  have e : ∀ n : ℕ, bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
      ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) * (n : ℝ) =
      bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n := fun n ↦ by
    rw [bandLine_eq_add_mul p (Fintype.card ι) k (-Real.log ‖T₀‖) n, Int.cast_natCast]
  have hh : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
      (touchX p (Fintype.card ι) k) =
      (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) (touchX p (Fintype.card ι) k) :
        WithBotTop ℝ) := by
    rw [h, bandLine_touchX]
  refine ⟨?_, ?_⟩
  · by_contra hno
    have hnu : ∀ n, touchX p (Fintype.card ι) k ≤ n + Fintype.card ι →
        n ≤ touchX p (Fintype.card ι) k → ¬ IsUnitCoeff D ω n :=
      fun n h1' h2' hu ↦ hno ⟨n, h1', h2', hu⟩
    have hNpos : (0 : ℝ) < ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ) := by positivity
    have hpts : ∀ n : ℕ, ((bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 + μ +
        (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) -
            μ / ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ)) *
          min (n : ℝ) ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ) +
        ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) *
          max ((n : ℝ) - ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ)) 0 : ℝ) : WithBotTop ℝ) ≤
        pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := fun n ↦ by
      rcases le_or_gt (touchX p (Fintype.card ι) k + 1) n with hnN | hnN
      · have hc : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 + μ +
            (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) -
                μ / ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ)) *
              min (n : ℝ) ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ) +
            ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) *
              max ((n : ℝ) - ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ)) 0 =
            bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n := by
          rw [min_eq_right (Nat.cast_le.2 hnN), max_eq_left (sub_nonneg.2 (Nat.cast_le.2 hnN)),
            ← e n]
          field_simp
          ring
        rw [hc]
        exact bandLine_le_pointHeight hp2 D ω ψ hψ h0 h1 k n
      · have hc : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 + μ +
            (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) -
                μ / ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ)) *
              min (n : ℝ) ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ) +
            ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) *
              max ((n : ℝ) - ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ)) 0 ≤
            bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n + μ := by
          rw [min_eq_left (Nat.cast_le.2 hnN.le),
            max_eq_right (sub_nonpos.2 (Nat.cast_le.2 hnN.le)), ← e n]
          have : 0 ≤ μ / ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ) * n := by positivity
          nlinarith
        refine le_trans (WithBotTop.coe_le_coe.2 hc) ?_
        rcases le_or_gt (touchX p (Fintype.card ι) k) (n + Fintype.card ι) with hband | hbeyond
        · rw [hμ]
          exact bandLine_add_min_le_pointHeight hp2 D ω ψ hψ h0 h1 (k := k) hband (by omega)
            (hnu n hband (by omega))
        · refine le_trans ?_
            (bandLine_add_le_pointHeight_of_ge hp2 D ω ψ hψ h0 h1 (k := k) (n := n) (by omega))
          rw [WithBotTop.coe_le_coe]
          have h1' : (1 : ℝ) ≤ ((touchX p (Fintype.card ι) k - Fintype.card ι - n : ℕ) : ℝ) := by
            exact_mod_cast (show 1 ≤ touchX p (Fintype.card ι) k - Fintype.card ι - n by omega)
          have := mul_le_mul_of_nonneg_right h1' hvT.le
          linarith
    have key := hNP.twoSlope_le_height hst
      (y₀ := bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 + μ)
      (s₁ := ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) -
        μ / ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ))
      (s₂ := ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖))
      (by have := div_pos hμpos hNpos; linarith) (N := touchX p (Fintype.card ι) k + 1) hpts
      (touchX p (Fintype.card ι) k)
    have hle :
        ((touchX p (Fintype.card ι) k : ℕ) : ℝ) ≤ ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ _
    rw [hh, WithBotTop.coe_le_coe, min_eq_left hle, max_eq_right (sub_nonpos.2 hle),
      ← e (touchX p (Fintype.card ι) k)] at key
    have hlt :
        ((touchX p (Fintype.card ι) k : ℕ) : ℝ) < ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self _
    have : μ /
        ((touchX p (Fintype.card ι) k + 1 : ℕ) : ℝ) * (touchX p (Fintype.card ι) k : ℝ) < μ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hNpos]
      nlinarith
    linarith
  · by_contra hno
    have hnu : ∀ n, touchX p (Fintype.card ι) k ≤ n →
        n ≤ touchX p (Fintype.card ι) k + Fintype.card ι → ¬ IsUnitCoeff D ω n :=
      fun n h1' h2' hu ↦ hno ⟨n, h1', h2', hu⟩
    have hcast :
        ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ) = (touchX p (Fintype.card ι) k : ℝ) - 1 := by
      rw [Nat.cast_sub htX, Nat.cast_one]
    have hpts : ∀ n : ℕ, ((bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
        ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) *
          min (n : ℝ) ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ) +
        (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) + μ / ((Fintype.card ι : ℝ) + 2)) *
          max ((n : ℝ) - ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ)) 0 : ℝ) : WithBotTop ℝ) ≤
        pointHeight (coeffVal (specCharSeries D ω ψ T₀)) n := fun n ↦ by
      rcases le_or_gt n (touchX p (Fintype.card ι) k - 1) with hnN | hnN
      · have hc : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
            ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) *
              min (n : ℝ) ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ) +
            (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) + μ / ((Fintype.card ι : ℝ) + 2)) *
              max ((n : ℝ) - ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ)) 0 =
            bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n := by
          rw [min_eq_left (Nat.cast_le.2 hnN), max_eq_right (sub_nonpos.2 (Nat.cast_le.2 hnN)),
            ← e n]
          ring
        rw [hc]
        exact bandLine_le_pointHeight hp2 D ω ψ hψ h0 h1 k n
      · have hc : bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0 +
            ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) *
              min (n : ℝ) ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ) +
            (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) + μ / ((Fintype.card ι : ℝ) + 2)) *
              max ((n : ℝ) - ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ)) 0 =
            bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) n +
              μ / ((Fintype.card ι : ℝ) + 2) *
                ((n : ℝ) - ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ)) := by
          rw [min_eq_right (Nat.cast_le.2 hnN.le),
            max_eq_left (sub_nonneg.2 (Nat.cast_le.2 hnN.le)), ← e n]
          ring
        rw [hc, hcast]
        have hnT : touchX p (Fintype.card ι) k ≤ n := by omega
        rcases le_or_gt n (touchX p (Fintype.card ι) k + Fintype.card ι) with hband | hbeyond
        · refine le_trans ?_
            (bandLine_add_min_le_pointHeight hp2 D ω ψ hψ h0 h1 (k := k) (by omega) hband
              (hnu n hnT hband))
          rw [WithBotTop.coe_le_coe, ← hμ]
          have hd : (n : ℝ) - ((touchX p (Fintype.card ι) k : ℝ) - 1) ≤ Fintype.card ι + 1 := by
            have := (Nat.cast_le (α := ℝ)).2 hband
            push_cast at this
            linarith
          have hd0 : (0 : ℝ) ≤ (n : ℝ) - ((touchX p (Fintype.card ι) k : ℝ) - 1) := by
            have := (Nat.cast_le (α := ℝ)).2 hnT
            linarith
          have : μ /
              ((Fintype.card
                  ι : ℝ) + 2) * ((n : ℝ) - ((touchX p (Fintype.card ι) k : ℝ) - 1)) ≤ μ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ ht2]
            nlinarith
          linarith
        · refine le_trans ?_
            (bandLine_add_le_pointHeight_of_le hp2 D ω ψ hψ h0 h1 (k := k) (n := n) (by omega))
          rw [WithBotTop.coe_le_coe]
          have hm : (1 : ℝ) ≤ ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) := by
            exact_mod_cast (show 1 ≤ n - touchX p (Fintype.card ι) k - Fintype.card ι by omega)
          have hd : (n : ℝ) - ((touchX p (Fintype.card ι) k : ℝ) - 1) =
              ((n
                  - touchX p
                      (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) + Fintype.card ι + 1 := by
            have : n = (n - touchX p (Fintype.card ι) k - Fintype.card ι) + Fintype.card ι +
                touchX p (Fintype.card ι) k := by omega
            have := congrArg (fun m : ℕ ↦ (m : ℝ)) this
            push_cast at this
            linarith
          have : μ /
              ((Fintype.card ι : ℝ) + 2) * ((n : ℝ) - ((touchX p (Fintype.card ι) k : ℝ) - 1)) ≤
              ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) * (-Real.log ‖T₀‖) := by
            rw [hd, div_mul_eq_mul_div, div_le_iff₀ ht2]
            have hA := mul_le_mul_of_nonneg_right hμle
              (by
                  positivity :
                      (0 : ℝ) ≤ ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) +
                Fintype.card ι + 1)
            have hC :
                ((n - touchX p (Fintype.card ι) k - Fintype.card ι : ℕ) : ℝ) + Fintype.card ι + 1 ≤
                ((n
                    - touchX p
                        (Fintype.card
                            ι) k - Fintype.card ι : ℕ) : ℝ) * ((Fintype.card ι : ℝ) + 2) := by
              nlinarith [mul_nonneg (sub_nonneg.2 hm) (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))]
            have hD := mul_le_mul_of_nonneg_left hC hvT.le
            linarith
          linarith
    have key := hNP.twoSlope_le_height hst
      (y₀ := bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) 0)
      (s₁ := ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖))
      (s₂ := ((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) + μ / ((Fintype.card ι : ℝ) + 2))
      (by have := div_pos hμpos ht2; linarith) (N := touchX p (Fintype.card ι) k - 1) hpts
      (touchX p (Fintype.card ι) k)
    have hle : ((touchX p (Fintype.card ι) k - 1 : ℕ) : ℝ) ≤ (touchX p (Fintype.card ι) k : ℝ) := by
      rw [hcast]; linarith
    rw [hh, WithBotTop.coe_le_coe, min_eq_right hle, max_eq_left (sub_nonneg.2 hle),
      ← e (touchX p (Fintype.card ι) k), hcast] at key
    have := div_pos hμpos ht2
    nlinarith

/-! ### The slope reading: [LWX, Theorem 1.3] at the polygon level -/

/-- The slopes over `[n_k^−, n_k^+)` are exactly `kφ(q)v(T)`. -/
theorem unitSlope_specCharSeries_eq_of_mem_band (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {j : ℕ}
    (hj1 : leftIndex D ω k ≤ j) (hj2 : j < rightIndex D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j =
      ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) := by
  have hst := specCharSeries_starting_point_fst D ω ψ T₀
  have hj := height_specCharSeries_eq_bandLine hp2 D ω ψ hψ h0 h1 hb (x := j)
    (by exact_mod_cast hj1) (by exact_mod_cast hj2.le)
  have hj' := height_specCharSeries_eq_bandLine hp2 D ω ψ hψ h0 h1 hb (x := ((j + 1 : ℕ) : ℤ))
    (by exact_mod_cast le_trans hj1 (Nat.le_succ j)) (by exact_mod_cast hj2)
  rw [(newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope_eq_of_height_eq
    hst (unitSlope_specCharSeries_ne_bot hp2 D ω ψ hψ h0 h1 j) hj hj']
  congr 1
  rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by push_cast; ring, bandLine_add_one]
  ring

/-- The slopes from `n_k^+` on are strictly larger than `kφ(q)v(T)`. -/
theorem lt_unitSlope_specCharSeries_of_rightIndex_le (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {j : ℕ}
    (hj : rightIndex D ω k ≤ j) :
    ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j := by
  have hst := specCharSeries_starting_point_fst D ω ψ T₀
  have hlr : leftIndex D ω k ≤ rightIndex D ω k := by
    have := (leftIndex_mem D ω hb).2.1
    have := (rightIndex_mem D ω hb).1
    omega
  have hN : ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope
        (rightIndex D ω k) := by
    have hh := height_specCharSeries_eq_bandLine hp2 D ω ψ hψ h0 h1 hb (x := rightIndex D ω k)
      (by exact_mod_cast hlr) le_rfl
    by_cases htop : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        ((rightIndex D ω k + 1 : ℕ) : ℤ) = ⊤
    · obtain ⟨-, -, htop'⟩ :=
        (newtonPolygon₀OfPowerSeries
            negLogNorm (specCharSeries D ω ψ T₀)).unitSlope_eq_top_of_height_eq_top
          htop
      rw [hst] at htop'
      have hidx : ((((rightIndex D ω k + 1 : ℕ) : ℤ) - 0).toNat - 1) = rightIndex D ω k := by
        simp
      rw [hidx] at htop'
      rw [htop']
      exact lt_top_iff_ne_top.2 (WithBotTop.coe_ne_top _)
    · have hbot : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
          ((rightIndex D ω k + 1 : ℕ) : ℤ) ≠ ⊥ := by
        rw [Ne, NewtonPolygon₀.height_eq_bot_iff, hst]
        omega
      obtain ⟨c, hc⟩ := exists_coe_of_ne_bot_of_ne_top hbot htop
      have hgt := bandLine_lt_height_specCharSeries_of_rightIndex_lt hp2 D ω ψ hψ h0 h1 hb
        (x := ((rightIndex D ω k + 1 : ℕ) : ℤ)) (by omega)
      rw [hc, WithBotTop.coe_lt_coe] at hgt
      rw [(newtonPolygon₀OfPowerSeries
          negLogNorm (specCharSeries D ω ψ T₀)).unitSlope_eq_of_height_eq
        hst (unitSlope_specCharSeries_ne_bot hp2 D ω ψ hψ h0 h1 _) hh hc, WithBotTop.coe_lt_coe]
      have e := bandLine_add_one p (Fintype.card ι) k (-Real.log ‖T₀‖) (rightIndex D ω k)
      rw [show
          ((rightIndex D ω k + 1 : ℕ) : ℤ) = (rightIndex D ω k : ℤ) + 1 by push_cast; ring] at hgt
      linarith
  exact lt_of_lt_of_le hN
    ((newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope_mono hj)

/-- The slopes before `n_k^−` are strictly smaller than `kφ(q)v(T)`. -/
theorem unitSlope_specCharSeries_lt_of_lt_leftIndex (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) {j : ℕ}
    (hj : j < leftIndex D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j <
      ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) := by
  have hNP := isNewtonPolygonOf_specCharSeries hp2 D ω ψ hψ h0 h1
  have hst := specCharSeries_starting_point_fst D ω ψ T₀
  have hL1 : 1 ≤ leftIndex D ω k := by omega
  have hlr : leftIndex D ω k ≤ rightIndex D ω k := by
    have := (leftIndex_mem D ω hb).2.1
    have := (rightIndex_mem D ω hb).1
    omega
  have hM : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope
      (leftIndex D ω k - 1) <
      ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) := by
    have hh := height_specCharSeries_eq_bandLine hp2 D ω ψ hψ h0 h1 hb (x := leftIndex D ω k)
      le_rfl (by exact_mod_cast hlr)
    have h0' : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        ((0 : ℕ) : ℤ) ≤ ((0 : ℝ) : WithBotTop ℝ) := by
      have := hNP.height_le 0
      rwa [pointHeight_eq_of_coeffVal_eq
        (coeffVal_zero_of_coeff_zero_eq_one (specCharSeries_coeff_zero D ω ψ T₀))] at this
    have hfin : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        ((leftIndex D ω k - 1 : ℕ) : ℤ) ≠ ⊤ := by
      have hchord :=
          (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height_le_chord
        (x := ((0 : ℕ) : ℤ)) (y := ((leftIndex D ω k - 1 : ℕ) : ℤ)) (z := leftIndex D ω k)
        (by rw [hst]; exact le_rfl) (by omega) (by omega) h0' hh.le
      exact ne_top_of_le_ne_top (WithBotTop.coe_ne_top _) hchord
    have hbot : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        ((leftIndex D ω k - 1 : ℕ) : ℤ) ≠ ⊥ := by
      rw [Ne, NewtonPolygon₀.height_eq_bot_iff, hst]
      omega
    obtain ⟨a, ha⟩ := exists_coe_of_ne_bot_of_ne_top hbot hfin
    have hgt := bandLine_lt_height_specCharSeries_of_lt_leftIndex hp2 D ω ψ hψ h0 h1 hb
      (x := ((leftIndex D ω k - 1 : ℕ) : ℤ)) (by omega) (by omega)
    rw [ha, WithBotTop.coe_lt_coe] at hgt
    have hh' : (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height
        (((leftIndex D ω k - 1) + 1 : ℕ) : ℤ) =
        (bandLine p (Fintype.card ι) k (-Real.log ‖T₀‖) (leftIndex D ω k) : WithBotTop ℝ) := by
      rw [Nat.sub_add_cancel hL1]
      exact hh
    rw [(newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope_eq_of_height_eq
      hst (unitSlope_specCharSeries_ne_bot hp2 D ω ψ hψ h0 h1 _) ha hh', WithBotTop.coe_lt_coe]
    have e := bandLine_add_one p (Fintype.card ι) k (-Real.log ‖T₀‖) ((leftIndex D ω k - 1 : ℕ) : ℤ)
    have hcast : ((leftIndex D ω k - 1 : ℕ) : ℤ) + 1 = (leftIndex D ω k : ℤ) := by omega
    rw [hcast] at e
    linarith
  exact lt_of_le_of_lt
    ((newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope_mono
      (show j ≤ leftIndex D ω k - 1 by omega)) hM

/-- **[LWX, Theorem 1.3], the integral components `X_k`**: the `j`-th slope equals `kφ(q)v(T)`
exactly for `j ∈ [n_k^−, n_k^+)`; so the multiplicity of the slope ratio `kφ(q)` is
`n_k^+ − n_k^−`, independently of `T` ([LWX, (3.23.3)–(3.23.4)]). -/
theorem unitSlope_specCharSeries_eq_iff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j =
        ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) ↔
      leftIndex D ω k ≤ j ∧ j < rightIndex D ω k := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩,
    fun h ↦ unitSlope_specCharSeries_eq_of_mem_band hp2 D ω ψ hψ h0 h1 hb h.1 h.2⟩
  · by_contra hj
    rw [not_le] at hj
    exact absurd h (ne_of_lt (unitSlope_specCharSeries_lt_of_lt_leftIndex hp2 D ω ψ hψ h0 h1 hb hj))
  · by_contra hj
    rw [not_lt] at hj
    exact absurd h
        (ne_of_gt (lt_unitSlope_specCharSeries_of_rightIndex_le hp2 D ω ψ hψ h0 h1 hb hj))

/-- **[LWX, Theorem 1.3], the components `X_{(k,k+1)}`**: for `j ∈ [n_k^+, n_{k+1}^−)` the
`j`-th slope lies strictly between `kφ(q)v(T)` and `(k+1)φ(q)v(T)`. -/
theorem unitSlope_specCharSeries_mem_Ioo (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k)
    (hb' : HasUnitBand D ω (k + 1)) {j : ℕ} (hj1 : rightIndex D ω k ≤ j)
    (hj2 : j < leftIndex D ω (k + 1)) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j ∈
      Set.Ioo ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ)
        (((((k + 1) * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) :=
  ⟨lt_unitSlope_specCharSeries_of_rightIndex_le hp2 D ω ψ hψ h0 h1 hb hj1,
    unitSlope_specCharSeries_lt_of_lt_leftIndex hp2 D ω ψ hψ h0 h1 hb' hj2⟩

end LWX

end
