/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Tate

/-!
# Comparison of norms on a Tate normed ring

Two norms on a ring are compared through a ring homomorphism `e : R → S` between two normed rings,
which avoids putting two norms on one type: "two norms on `R` inducing the same topology" is a ring
isomorphism `e : R ≃+* S` that is continuous in both directions. Over a Tate normed ring, continuity
already forces a *power* comparison (Johansson–Newton, Lemmas 2.1.6 and 2.1.7).

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.3.2. Tau Ceti home:
`TauCeti/Analysis/Normed/Ring/Ultra/NormComparison.lean`.

## Main results

* `NormedRing.exists_norm_le_of_norm_map_le_one`, `NormedRing.exists_norm_le_mul_rpow_norm_map` —
  Johansson–Newton, Lemma 2.1.6 (the corrected statement).
* `NormedRing.exists_norm_map_le_mul_rpow`, `NormedRing.exists_mul_rpow_le_norm_map` —
  Johansson–Newton, Lemma 2.1.7, with the exponent `Real.logb ‖ϖ‖ ‖e ϖ‖` explicit.
-/

open Filter Topology

namespace NormedRing

variable {R S : Type*} [NormedRing R] [NormOneClass R] [NormedRing S]

omit [NormOneClass R] in
/-- The constant of Johansson–Newton's Lemma 2.1.6: a power `ϖ ^ m`, `m ≥ 1`, whose image has
norm at most `1 / 2` and which pushes the preimage of the unit ball into the unit ball. -/
private theorem exists_pow_norm_map_le (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (ϖ : PseudoUniformizer R) :
    ∃ m : ℕ, 1 ≤ m ∧ ‖e ((ϖ : R) ^ m)‖ ≤ 1 / 2 ∧
      ∀ b : R, ‖e b‖ ≤ 1 → ‖(ϖ : R)‖ ^ m * ‖b‖ ≤ 1 := by
  obtain ⟨D, hD, hDsymm⟩ := Metric.continuousAt_iff.1 (he'.continuousAt (x := (0 : S))) 1 one_pos
  have ht : Tendsto (fun k : ℕ ↦ ‖e ((ϖ : R) ^ k)‖) atTop (𝓝 0) := by
    have := ((he.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ϖ.norm_lt_one)).norm
    rwa [map_zero, norm_zero] at this
  obtain ⟨m, hm, hm1⟩ :=
    ((ht.eventually (gt_mem_nhds (lt_min hD one_half_pos))).and (eventually_ge_atTop 1)).exists
  refine ⟨m, hm1, (hm.trans_le (min_le_right _ _)).le, fun b hb ↦ ?_⟩
  have h1 : ‖e ((ϖ : R) ^ m * b)‖ < D := by
    rw [map_mul]
    calc ‖e ((ϖ : R) ^ m) * e b‖ ≤ ‖e ((ϖ : R) ^ m)‖ * ‖e b‖ := _root_.norm_mul_le _ _
      _ ≤ ‖e ((ϖ : R) ^ m)‖ := mul_le_of_le_one_right (norm_nonneg _) hb
      _ < D := hm.trans_le (min_le_left _ _)
  have h2 := hDsymm (show dist (e ((ϖ : R) ^ m * b)) 0 < D by rwa [dist_zero_right])
  rw [map_zero, dist_zero_right, RingEquiv.symm_apply_apply] at h2
  rw [← ϖ.isMultiplicative.norm_pow_mul]
  exact h2.le

/-- Source: Johansson–Newton, Lemma 2.1.6 (first inequality): "if `|a|_π < 1`, `|a|_ϖ ≤ C₁`". -/
theorem exists_norm_le_of_norm_map_le_one (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (ϖ : PseudoUniformizer R) :
    ∃ C : ℝ, ∀ a : R, ‖e a‖ ≤ 1 → ‖a‖ ≤ C := by
  obtain ⟨m, -, -, hm⟩ := exists_pow_norm_map_le e he he' ϖ
  refine ⟨(‖(ϖ : R)‖ ^ m)⁻¹, fun a ha ↦ ?_⟩
  rw [← mul_one (‖(ϖ : R)‖ ^ m)⁻¹, le_inv_mul_iff₀ (pow_pos ϖ.norm_pos m)]
  exact hm a ha

/-- Source: Johansson–Newton, Lemma 2.1.6 (second inequality): "if `|a|_π ≥ 1`, then
`|a|_ϖ ≤ C₂ |a|_π ^ s`". -/
theorem exists_norm_le_mul_rpow_norm_map (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (ϖ : PseudoUniformizer R) :
    ∃ C s : ℝ, 0 < s ∧ ∀ a : R, 1 ≤ ‖e a‖ → ‖a‖ ≤ C * ‖e a‖ ^ s := by
  obtain ⟨m, hm1, hmhalf, hm⟩ := exists_pow_norm_map_le e he he' ϖ
  have hc₀ := ϖ.norm_pos
  have hq : 0 < ‖(ϖ : R)‖ ^ m := pow_pos hc₀ m
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (‖(ϖ : R)‖ ^ m)⁻¹ := ⟨_, rfl⟩
  have hK1 : 1 < K := hK ▸ (one_lt_inv₀ hq).2 (pow_lt_one₀ hc₀.le ϖ.norm_lt_one (by omega))
  have hK0 : 0 < K := one_pos.trans hK1
  refine ⟨K * K, Real.logb 2 K, Real.logb_pos one_lt_two hK1, fun a ha ↦ ?_⟩
  have hea : 0 < ‖e a‖ := one_pos.trans_le ha
  have hx0 : 0 ≤ Real.logb 2 ‖e a‖ := Real.logb_nonneg one_lt_two ha
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈Real.logb 2 ‖e a‖⌉₊ := ⟨_, rfl⟩
  have h2n : ‖e a‖ ≤ 2 ^ n := by
    calc ‖e a‖ = (2 : ℝ) ^ Real.logb 2 ‖e a‖ := (Real.rpow_logb two_pos (by norm_num) hea).symm
      _ ≤ (2 : ℝ) ^ (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (hn ▸ Nat.le_ceil _)
      _ = 2 ^ n := Real.rpow_natCast 2 n
  have hb : ‖e ((ϖ : R) ^ (m * n) * a)‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at h2n
      simpa [h0] using h2n
    rw [pow_mul, map_mul, map_pow]
    calc ‖e ((ϖ : R) ^ m) ^ n * e a‖ ≤ ‖e ((ϖ : R) ^ m) ^ n‖ * ‖e a‖ := _root_.norm_mul_le _ _
      _ ≤ ‖e ((ϖ : R) ^ m)‖ ^ n * ‖e a‖ :=
        mul_le_mul_of_nonneg_right (norm_pow_le' _ hpos) (norm_nonneg _)
      _ ≤ (1 / 2) ^ n * ‖e a‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hmhalf n) (norm_nonneg _)
      _ ≤ (1 / 2) ^ n * 2 ^ n := mul_le_mul_of_nonneg_left h2n (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hmain : ‖(ϖ : R)‖ ^ m * ((‖(ϖ : R)‖ ^ m) ^ n * ‖a‖) ≤ 1 := by
    rw [← pow_mul, ← ϖ.isMultiplicative.norm_pow_mul]
    exact hm _ hb
  have hKn : ‖a‖ ≤ K * K ^ n := by
    calc ‖a‖ = K * K ^ n * (‖(ϖ : R)‖ ^ m * ((‖(ϖ : R)‖ ^ m) ^ n * ‖a‖)) := by
          rw [hK, inv_pow]
          field_simp
      _ ≤ K * K ^ n * 1 := mul_le_mul_of_nonneg_left hmain (mul_pos hK0 (pow_pos hK0 n)).le
      _ = K * K ^ n := mul_one _
  have hkey : K ^ Real.logb 2 ‖e a‖ = ‖e a‖ ^ Real.logb 2 K := by
    rw [Real.rpow_def_of_pos hK0, Real.rpow_def_of_pos hea, Real.logb, Real.logb]
    congr 1
    ring
  have hKpow : K ^ n ≤ K * ‖e a‖ ^ Real.logb 2 K := by
    calc K ^ n = K ^ (n : ℝ) := (Real.rpow_natCast K n).symm
      _ ≤ K ^ (Real.logb 2 ‖e a‖ + 1) :=
        Real.rpow_le_rpow_of_exponent_le hK1.le (hn ▸ (Nat.ceil_lt_add_one hx0).le)
      _ = K * ‖e a‖ ^ Real.logb 2 K := by rw [Real.rpow_add hK0, Real.rpow_one, hkey, mul_comm]
  calc ‖a‖ ≤ K * K ^ n := hKn
    _ ≤ K * (K * ‖e a‖ ^ Real.logb 2 K) := mul_le_mul_of_nonneg_left hKpow hK0.le
    _ = K * K * ‖e a‖ ^ Real.logb 2 K := by ring

variable [NormOneClass S]

omit [NormOneClass R] in
/-- The image of a pseudo-uniformiser under a continuous ring homomorphism has norm less than
`1`, when it is multiplicative: its powers tend to `0`. -/
private theorem norm_map_lt_one (e : R →+* S) (he : Continuous e) (ϖ : PseudoUniformizer R)
    (hϖ : IsMultiplicative (e (ϖ : R))) : ‖e (ϖ : R)‖ < 1 := by
  have ht : Tendsto (fun k : ℕ ↦ ‖e (ϖ : R)‖ ^ k) atTop (𝓝 0) := by
    have := ((he.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ϖ.norm_lt_one)).norm
    rw [map_zero, norm_zero] at this
    refine this.congr fun k ↦ ?_
    simp only [Function.comp_apply, map_pow]
    exact hϖ.norm_pow k
  simpa [abs_norm] using tendsto_pow_atTop_nhds_zero_iff.1 ht

/-- Source: Johansson–Newton, Lemma 2.1.7 (the exponent `s` "is determined by
`|ϖ|₂ = |ϖ|₁ ^ s`"). -/
theorem logb_norm_map_pos (e : R →+* S) (he : Continuous e) (ϖ : PseudoUniformizer R)
    (hϖ : IsMultiplicative (e (ϖ : R))) : 0 < Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := by
  have h0 : 0 < ‖e (ϖ : R)‖ := IsMultiplicative.norm_pos (u := Units.map (e : R →* S) ϖ.unit) hϖ
  exact (Real.logb_pos_iff_of_base_lt_one ϖ.norm_pos ϖ.norm_lt_one h0).2
    (norm_map_lt_one e he ϖ hϖ)

/-- Source: Johansson–Newton, Lemma 2.1.7 (upper bound `|a|₂ ≤ C₂ |a|₁ ^ s`). -/
theorem exists_norm_map_le_mul_rpow (e : R →+* S) (he : Continuous e) (ϖ : PseudoUniformizer R)
    (hϖ : IsMultiplicative (e (ϖ : R))) :
    ∃ C : ℝ, ∀ a : R, ‖e a‖ ≤ C * ‖a‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := by
  have hs : 0 < Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := logb_norm_map_pos e he ϖ hϖ
  have hc₀ := ϖ.norm_pos
  obtain ⟨u, hu_def⟩ : ∃ u : Sˣ, u = Units.map (e : R →* S) ϖ.unit := ⟨_, rfl⟩
  have hu : IsMultiplicative (u : S) := hu_def ▸ hϖ
  have hue : (u : S) = e (ϖ : R) := by rw [hu_def]; rfl
  have ht₀ : 0 < ‖(u : S)‖ := hu.norm_pos
  have hts : ‖(ϖ : R)‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ = ‖(u : S)‖ := by
    rw [hue]
    exact Real.rpow_logb hc₀ ϖ.norm_lt_one.ne (hue ▸ ht₀)
  obtain ⟨D₁, hD₁, hD⟩ := Metric.continuousAt_iff.1 (he.continuousAt (x := (0 : R))) 1 one_pos
  have hD0 : 0 < D₁ / 2 := half_pos hD₁
  have hDle : ∀ b : R, ‖b‖ ≤ D₁ / 2 → ‖e b‖ ≤ 1 := fun b hb ↦ by
    have := hD (show dist b 0 < D₁ by rw [dist_zero_right]; linarith)
    rw [map_zero, dist_zero_right] at this
    exact this.le
  refine ⟨(D₁ / 2 * ‖(ϖ : R)‖) ^ (-Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖), fun a ↦ ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, norm_zero, norm_zero, Real.zero_rpow hs.ne', mul_zero]
  obtain ⟨n, ⟨hn₁, hn₂⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc hD0 ha
  have hen : e ((ϖ.unit ^ n : Rˣ) : R) = ((u ^ n : Sˣ) : S) := by
    rw [hu_def, ← map_zpow, Units.coe_map]
    rfl
  have h1 : ‖(u : S)‖ ^ n * ‖e a‖ ≤ 1 := by
    have := hDle _ hn₂
    rwa [smul_eq_mul, map_mul, hen, (hu.zpow n).norm_mul, hu.norm_zpow] at this
  rw [ϖ.norm_zpow_smul] at hn₁
  have h2 : ‖e a‖ ≤ (‖(u : S)‖ ^ n)⁻¹ := by
    rw [← mul_one (‖(u : S)‖ ^ n)⁻¹, le_inv_mul_iff₀ (zpow_pos ht₀ n)]
    exact h1
  have h3 : (‖(ϖ : R)‖ ^ n)⁻¹ < ‖a‖ / (D₁ / 2 * ‖(ϖ : R)‖) := by
    rw [lt_div_iff₀ (mul_pos hD0 hc₀), inv_mul_lt_iff₀ (zpow_pos hc₀ n)]
    exact hn₁
  have hmid : (‖(u : S)‖ ^ n)⁻¹ = ((‖(ϖ : R)‖ ^ n)⁻¹) ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := by
    rw [← hts, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hc₀.le,
      ← Real.rpow_neg hc₀.le, ← Real.rpow_neg hc₀.le, ← Real.rpow_mul hc₀.le]
    congr 1
    ring
  calc ‖e a‖ ≤ (‖(u : S)‖ ^ n)⁻¹ := h2
    _ = ((‖(ϖ : R)‖ ^ n)⁻¹) ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := hmid
    _ ≤ (‖a‖ / (D₁ / 2 * ‖(ϖ : R)‖)) ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ :=
      Real.rpow_le_rpow (inv_nonneg.2 (zpow_pos hc₀ n).le) h3.le hs.le
    _ = (D₁ / 2 * ‖(ϖ : R)‖) ^ (-Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖) *
        ‖a‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := by
      rw [Real.div_rpow (norm_nonneg _) (mul_pos hD0 hc₀).le,
        Real.rpow_neg (mul_pos hD0 hc₀).le, div_eq_inv_mul]

/-- Source: Johansson–Newton, Lemma 2.1.7 (lower bound `C₁ |a|₁ ^ s ≤ |a|₂`). -/
theorem exists_mul_rpow_le_norm_map (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm)
    (ϖ : PseudoUniformizer R) (hϖ : IsMultiplicative (e (ϖ : R))) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : R, C * ‖a‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ ≤ ‖e a‖ := by
  have hs : 0 < Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := logb_norm_map_pos (e : R →+* S) he ϖ hϖ
  let ϖ' : PseudoUniformizer S :=
    ⟨Units.map (e : R →* S) ϖ.unit, hϖ, norm_map_lt_one (e : R →+* S) he ϖ hϖ⟩
  have hϖ' : IsMultiplicative ((e.symm : S →+* R) (ϖ' : S)) := by
    change IsMultiplicative (e.symm (e (ϖ : R)))
    rw [RingEquiv.symm_apply_apply]
    exact ϖ.isMultiplicative
  obtain ⟨C', hC'⟩ := exists_norm_map_le_mul_rpow (e.symm : S →+* R) he' ϖ' hϖ'
  have hexp : Real.logb ‖(ϖ' : S)‖ ‖(e.symm : S →+* R) (ϖ' : S)‖ =
      (Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖)⁻¹ := by
    change Real.logb ‖e (ϖ : R)‖ ‖e.symm (e (ϖ : R))‖ = _
    rw [RingEquiv.symm_apply_apply, Real.inv_logb]
  have hK : 0 < max C' 1 := lt_max_of_lt_right one_pos
  have hKs : 0 < max C' 1 ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := Real.rpow_pos_of_pos hK _
  refine ⟨(max C' 1 ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖)⁻¹, inv_pos.2 hKs, fun a ↦ ?_⟩
  have h1 : ‖a‖ ≤ max C' 1 * ‖e a‖ ^ (Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖)⁻¹ := by
    have := hC' (e a)
    rw [hexp] at this
    change ‖e.symm (e a)‖ ≤ _ at this
    rw [RingEquiv.symm_apply_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  have h2 : ‖a‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ ≤
      max C' 1 ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ * ‖e a‖ := by
    calc ‖a‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖
        ≤ (max C' 1 * ‖e a‖ ^ (Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖)⁻¹) ^
            Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := Real.rpow_le_rpow (norm_nonneg _) h1 hs.le
      _ = max C' 1 ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ * ‖e a‖ := by
        rw [Real.mul_rpow hK.le (Real.rpow_nonneg (norm_nonneg _) _),
          Real.rpow_inv_rpow (norm_nonneg _) hs.ne']
  calc (max C' 1 ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖)⁻¹ * ‖a‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖
      ≤ (max C' 1 ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖)⁻¹ *
          (max C' 1 ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ * ‖e a‖) :=
        mul_le_mul_of_nonneg_left h2 (inv_pos.2 hKs).le
    _ = ‖e a‖ := by rw [← mul_assoc, inv_mul_cancel₀ hKs.ne', one_mul]

end NormedRing
