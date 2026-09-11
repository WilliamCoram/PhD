import PhD.TateFredholm.Residue

/-!
# Changing the norm, base change, and the classical specialisations
([JN] Lemmas 2.1.6–2.1.7, Proposition 2.1.8; [Buz07, Corollaries 2.9–2.10];
[Bel] Lemma II.1.23, matrix-wise; [Bel] Theorem II.1.13 (Serre).  See `Tate.lean` for
the development's overview and dictionary.)

The Tate-specific norm-comparison lemmas hold in the merged setting as stated by [JN];
the invariance and base-change statements lose their Noetherian hypotheses. -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

section BaseChangeAux

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]
variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [NormOneClass S]

private theorem isMult_norm_mul_pow {A : Type*} [NormedRing A] [NormOneClass A] {a : A}
    (ha : IsMultiplicative a) (n : ℕ) (x : A) : ‖a ^ n * x‖ = ‖a‖ ^ n * ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_assoc, ih (a * x), ha x]; ring

private theorem isMult_norm_pow {A : Type*} [NormedRing A] [NormOneClass A] {a : A}
    (ha : IsMultiplicative a) (n : ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by
  have := isMult_norm_mul_pow ha n 1; simpa using this

private theorem isMult_pow {A : Type*} [NormedRing A] [NormOneClass A] {a : A}
    (ha : IsMultiplicative a) (n : ℕ) : IsMultiplicative (a ^ n) := by
  intro x; rw [isMult_norm_mul_pow ha n x, isMult_norm_pow ha n]

private theorem npow_eq_rpow_npow {ρ τ s : ℝ} (hρ : 0 ≤ ρ) (h : τ = ρ ^ s) (n : ℕ) :
    τ ^ n = (ρ ^ n) ^ s := by
  rw [h, ← Real.rpow_natCast (ρ ^ s) n, ← Real.rpow_natCast ρ n, ← Real.rpow_mul hρ,
      ← Real.rpow_mul hρ, mul_comm]

private theorem zpow_eq_rpow_zpow {ρ τ s : ℝ} (hρ : 0 ≤ ρ) (h : τ = ρ ^ s) (n : ℤ) :
    τ ^ n = (ρ ^ n) ^ s := by
  rw [h, ← Real.rpow_intCast (ρ ^ s) n, ← Real.rpow_intCast ρ n, ← Real.rpow_mul hρ,
      ← Real.rpow_mul hρ, mul_comm]

private theorem norm_map_zpow_mul (e : R ≃+* S) (u : Rˣ)
    (hu : IsMultiplicative (e (u : R))) (n : ℤ) (x : S) :
    ‖e ((u ^ n : Rˣ) : R) * x‖ = ‖e (u : R)‖ ^ n * ‖x‖ := by
  have hSnt : Nontrivial S := NormOneClass.nontrivial
  have hτpos : 0 < ‖e (u : R)‖ := by
    rw [norm_pos_iff]
    intro h
    have hone : (e (u : R)) * e ((u⁻¹ : Rˣ) : R) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h, zero_mul] at hone
    exact zero_ne_one hone
  have hinv : ∀ y : S, ‖e ((u⁻¹ : Rˣ) : R) * y‖ = ‖e (u : R)‖⁻¹ * ‖y‖ := by
    intro y
    have key : e (u : R) * (e ((u⁻¹ : Rˣ) : R) * y) = y := by
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    have h2 := hu (e ((u⁻¹ : Rˣ) : R) * y)
    rw [key] at h2
    rw [h2, ← mul_assoc, inv_mul_cancel₀ hτpos.ne', one_mul]
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hu1 : (u ^ (k + 1 : ℤ) : Rˣ) = u * u ^ (k : ℤ) := by rw [zpow_add_one, mul_comm]
      rw [hu1, Units.val_mul, map_mul, mul_assoc, hu (e ((u ^ (k : ℤ) : Rˣ) : R) * x), ih,
          zpow_add_one₀ hτpos.ne']
      ring
  | pred k ih =>
      have hu1 : (u ^ (-(k : ℤ) - 1) : Rˣ) = u⁻¹ * u ^ (-(k : ℤ)) := by
        rw [zpow_sub_one, mul_comm]
      rw [hu1, Units.val_mul, map_mul, mul_assoc, hinv (e ((u ^ (-(k : ℤ)) : Rˣ) : R) * x), ih,
          zpow_sub_one₀ hτpos.ne']
      ring

private theorem exists_zpow_mul_mem_shell {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {ε : ℝ}
    (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    ∃ n : ℤ, τ ^ n * t < ε ∧ ε * τ ≤ τ ^ n * t := by
  have hb : 1 < τ⁻¹ := (one_lt_inv₀ hτ0).2 hτ1
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (div_pos ht hε) hb
  rw [inv_zpow] at hk1 hk2
  have hnpos : (0 : ℝ) < τ ^ (k + 1) := zpow_pos hτ0 _
  have hkpos : (0 : ℝ) < τ ^ k := zpow_pos hτ0 _
  refine ⟨k + 1, ?_, ?_⟩
  · have h2 := mul_lt_mul_of_pos_left hk2 hnpos
    rw [mul_inv_cancel₀ hnpos.ne'] at h2
    calc τ ^ (k + 1) * t = τ ^ (k + 1) * (t / ε) * ε := by
          rw [mul_assoc, div_mul_cancel₀ _ hε.ne']
    _ < 1 * ε := mul_lt_mul_of_pos_right h2 hε
    _ = ε := one_mul ε
  · have h1' : ε ≤ τ ^ k * t := by
      calc ε = τ ^ k * (τ ^ k)⁻¹ * ε := by rw [mul_inv_cancel₀ hkpos.ne', one_mul]
      _ ≤ τ ^ k * (t / ε) * ε := by
            apply mul_le_mul_of_nonneg_right _ hε.le
            exact mul_le_mul_of_nonneg_left hk1 hkpos.le
      _ = τ ^ k * t := by rw [mul_assoc, div_mul_cancel₀ _ hε.ne']
    calc ε * τ ≤ τ ^ k * t * τ := mul_le_mul_of_nonneg_right h1' hτ0.le
    _ = τ ^ (k + 1) * t := by rw [zpow_add_one₀ hτ0.ne']; ring

end BaseChangeAux

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section NormChange

variable {R}
variable (S : Type*) [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [NormOneClass S]

omit [IsUltrametricDist R] [CompleteSpace R] [IsUltrametricDist S] [CompleteSpace S] in
/-- **[JN] Lemma 2.1.6** (the erratum lemma): two equivalent Tate norms, with possibly
different pseudo-uniformizers, are *power*-comparable — `‖a‖ ≤ C₂‖a‖'^s` on `‖a‖' ≥ 1` —
but in general **not** bounded-equivalent.  (The target uniformizer `π` and the inverse
continuity `he'` are part of [JN]'s "equivalent Tate norms" data, kept for faithfulness even
though this direction does not consume them.) -/
@[nolint unusedArguments]
theorem norm_le_pow_of_equiv (e : R ≃+* S) (he : Continuous (e : R → S))
    (he' : Continuous (e.symm : S → R))
    (ϖ : PseudoUniformizer R) (π : PseudoUniformizer S) :
    ∃ C₁ C₂ s : ℝ, 0 < s ∧ (∀ a : R, ‖e a‖ < 1 → ‖a‖ ≤ C₁) ∧
      ∀ a : R, 1 ≤ ‖e a‖ → ‖a‖ ≤ C₂ * ‖e a‖ ^ s := by
  classical
  have hRnt : Nontrivial R := NormOneClass.nontrivial
  have hρ0 : 0 < ‖(ϖ : R)‖ := ϖ.norm_pos
  have hρ1 : ‖(ϖ : R)‖ < 1 := by rw [PseudoUniformizer.coe_eq]; exact ϖ.norm_lt_one
  obtain ⟨D, hDpos, hB⟩ : ∃ D > 0, ∀ a : R, ‖e a‖ ≤ D → ‖a‖ ≤ 1 := by
    have hc : ContinuousAt (e.symm : S → R) 0 := he'.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδpos, h⟩ := hc 1 zero_lt_one
    refine ⟨δ / 2, by positivity, fun a ha => ?_⟩
    have hlt : ‖e a‖ < δ := lt_of_le_of_lt ha (by linarith)
    have hd := h (show dist (e a) 0 < δ by rwa [dist_zero_right])
    rw [map_zero, RingEquiv.symm_apply_apply, dist_zero_right] at hd
    exact hd.le
  have htend0 : Tendsto (fun m : ℕ => (ϖ : R) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hρ1
  have htendE : Tendsto (fun m : ℕ => e ((ϖ : R) ^ m)) atTop (𝓝 0) := by
    have hce : Tendsto (e : R → S) (𝓝 0) (𝓝 (e 0)) := he.continuousAt
    rw [map_zero] at hce
    exact hce.comp htend0
  have htendN : Tendsto (fun m : ℕ => ‖e ((ϖ : R) ^ m)‖) atTop (𝓝 0) := by
    have := htendE.norm; rwa [norm_zero] at this
  have hmpos : (0 : ℝ) < min D (1 / 2) := by positivity
  rw [Metric.tendsto_atTop] at htendN
  obtain ⟨N, hN⟩ := htendN (min D (1 / 2)) hmpos
  set m : ℕ := max N 1 with hmdef
  have hm1 : 1 ≤ m := le_max_right _ _
  have hβsmall : ‖e ((ϖ : R) ^ m)‖ < min D (1 / 2) := by
    have := hN m (le_max_left _ _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  set β : ℝ := ‖e ((ϖ : R) ^ m)‖ with hβdef
  have hβD : β ≤ D := le_of_lt (lt_of_lt_of_le hβsmall (min_le_left _ _))
  have hβ1 : β < 1 := lt_of_lt_of_le hβsmall (le_trans (min_le_right _ _) (by norm_num))
  have hβ0 : 0 < β := by
    rw [hβdef, norm_pos_iff]
    intro h
    have hz : ((ϖ : R) ^ m) = 0 := e.injective (by rw [h, map_zero])
    have hne : ((ϖ : R) ^ m) ≠ 0 := by
      rw [PseudoUniformizer.coe_eq, ← Units.val_pow_eq_pow_val]; exact Units.ne_zero _
    exact hne hz
  set ρw : ℝ := ‖(ϖ : R) ^ m‖ with hρwdef
  have hρw0 : 0 < ρw := by rw [hρwdef, isMult_norm_pow ϖ.isMultiplicative m]; exact pow_pos hρ0 m
  have hρw1 : ρw < 1 := by
    rw [hρwdef, isMult_norm_pow ϖ.isMultiplicative m]; exact pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hwmul : IsMultiplicative ((ϖ : R) ^ m) := isMult_pow ϖ.isMultiplicative m
  have hlogρw : Real.log ρw < 0 := Real.log_neg hρw0 hρw1
  have hlogβ : Real.log β < 0 := Real.log_neg hβ0 hβ1
  set s : ℝ := Real.log ρw / Real.log β with hsdef
  have hs0 : 0 < s := by
    rw [hsdef, ← neg_div_neg_eq]; exact div_pos (neg_pos.2 hlogρw) (neg_pos.2 hlogβ)
  have hρws : ρw = β ^ s := by
    rw [hsdef, Real.rpow_def_of_pos hβ0, mul_comm, div_mul_cancel₀ _ hlogβ.ne, Real.exp_log hρw0]
  -- part 1
  have hpart1 : ∀ a : R, ‖e a‖ < 1 → ‖a‖ ≤ ρw⁻¹ := by
    intro a ha
    have hnorm_ea' : ‖e ((ϖ : R) ^ m * a)‖ ≤ D := by
      calc ‖e ((ϖ : R) ^ m * a)‖ = ‖e ((ϖ : R) ^ m) * e a‖ := by rw [map_mul]
      _ ≤ ‖e ((ϖ : R) ^ m)‖ * ‖e a‖ := norm_mul_le _ _
      _ = β * ‖e a‖ := by rw [hβdef]
      _ ≤ β * 1 := mul_le_mul_of_nonneg_left ha.le hβ0.le
      _ = β := mul_one β
      _ ≤ D := hβD
    have hb1 : ‖(ϖ : R) ^ m * a‖ ≤ 1 := hB _ hnorm_ea'
    have hb2 : ‖(ϖ : R) ^ m * a‖ = ρw * ‖a‖ := by
      rw [hwmul a, ← hρwdef]
    rw [hb2] at hb1
    calc ‖a‖ = ρw⁻¹ * (ρw * ‖a‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hρw0.ne', one_mul]
    _ ≤ ρw⁻¹ * 1 := mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = ρw⁻¹ := mul_one _
  refine ⟨ρw⁻¹, ρw⁻¹ * ρw⁻¹, s, hs0, hpart1, ?_⟩
  -- part 2
  intro a ha
  have hea0 : 0 < ‖e a‖ := lt_of_lt_of_le zero_lt_one ha
  have hex : ∃ n : ℕ, β ^ n * ‖e a‖ < 1 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hea0) hβ1
    exact ⟨n, by rw [← lt_div_iff₀ hea0, one_div]; exact hn⟩
  have hfind_pos : 1 ≤ Nat.find hex := by
    rw [Nat.one_le_iff_ne_zero]; intro h0
    have := Nat.find_spec hex; rw [h0, pow_zero, one_mul] at this; linarith
  obtain ⟨k, hk1, hkspec, hkmin⟩ :
      ∃ k : ℕ, 1 ≤ k ∧ β ^ k * ‖e a‖ < 1 ∧ 1 ≤ β ^ (k - 1) * ‖e a‖ :=
    ⟨Nat.find hex, hfind_pos, Nat.find_spec hex,
      not_lt.mp (Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega))⟩
  have heb : ‖e (((ϖ : R) ^ m) ^ k * a)‖ < 1 := by
    calc ‖e (((ϖ : R) ^ m) ^ k * a)‖ = ‖(e ((ϖ : R) ^ m)) ^ k * e a‖ := by rw [map_mul, map_pow]
    _ ≤ ‖(e ((ϖ : R) ^ m)) ^ k‖ * ‖e a‖ := norm_mul_le _ _
    _ ≤ ‖e ((ϖ : R) ^ m)‖ ^ k * ‖e a‖ :=
          mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _)
    _ = β ^ k * ‖e a‖ := by rw [hβdef]
    _ < 1 := hkspec
  have hble : ‖((ϖ : R) ^ m) ^ k * a‖ ≤ ρw⁻¹ := hpart1 _ heb
  have hbnorm : ‖((ϖ : R) ^ m) ^ k * a‖ = ρw ^ k * ‖a‖ := by
    rw [(isMult_pow hwmul k) a, isMult_norm_pow hwmul k, ← hρwdef]
  rw [hbnorm] at hble
  have hρwk0 : 0 < ρw ^ k := pow_pos hρw0 k
  have hanorm : ‖a‖ ≤ ρw⁻¹ * (ρw ^ k)⁻¹ := by
    rw [mul_comm]
    calc ‖a‖ = (ρw ^ k)⁻¹ * (ρw ^ k * ‖a‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hρwk0.ne', one_mul]
    _ ≤ (ρw ^ k)⁻¹ * ρw⁻¹ := mul_le_mul_of_nonneg_left hble (by positivity)
  have hea_s_pos : 0 < ‖e a‖ ^ s := Real.rpow_pos_of_pos hea0 s
  have hβk_lb : β / ‖e a‖ ≤ β ^ k := by
    rw [div_le_iff₀ hea0]
    calc β = β * 1 := (mul_one β).symm
    _ ≤ β * (β ^ (k - 1) * ‖e a‖) := mul_le_mul_of_nonneg_left hkmin hβ0.le
    _ = β ^ k * ‖e a‖ := by rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk1]
  have hstep1 : ρw / ‖e a‖ ^ s ≤ ρw ^ k := by
    have h1 : (β / ‖e a‖) ^ s ≤ (β ^ k) ^ s :=
      Real.rpow_le_rpow (by positivity) hβk_lb hs0.le
    rw [Real.div_rpow hβ0.le (norm_nonneg _), ← hρws, ← npow_eq_rpow_npow hβ0.le hρws k] at h1
    exact h1
  have hkey : (ρw ^ k)⁻¹ ≤ ρw⁻¹ * ‖e a‖ ^ s := by
    have hpos : 0 < ρw / ‖e a‖ ^ s := div_pos hρw0 hea_s_pos
    have hh := one_div_le_one_div_of_le hpos hstep1
    rw [one_div, one_div, inv_div, div_eq_inv_mul] at hh
    exact hh
  calc ‖a‖ ≤ ρw⁻¹ * (ρw ^ k)⁻¹ := hanorm
  _ ≤ ρw⁻¹ * (ρw⁻¹ * ‖e a‖ ^ s) := mul_le_mul_of_nonneg_left hkey (by positivity)
  _ = ρw⁻¹ * ρw⁻¹ * ‖e a‖ ^ s := by rw [mul_assoc]

/-- **[JN] Lemma 2.1.7**: with a common multiplicative pseudo-uniformizer, the comparison
is two-sided of pure power type, `C₁‖a‖^s ≤ ‖e a‖ ≤ C₂‖a‖^s` (`s` pinned by
`‖e ϖ‖ = ‖ϖ‖^s`). -/
theorem norm_comparison_of_common_uniformizer (e : R ≃+* S)
    (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (ϖ : PseudoUniformizer R)
    (hmul : IsMultiplicative (e (ϖ : R)))
    (hlt : ‖e (ϖ : R)‖ < 1) :
    ∃ C₁ C₂ s : ℝ, 0 < C₁ ∧ 0 < s ∧
      ∀ a : R, C₁ * ‖a‖ ^ s ≤ ‖e a‖ ∧ ‖e a‖ ≤ C₂ * ‖a‖ ^ s := by
  have hRnt : Nontrivial R := NormOneClass.nontrivial
  have hρ0 : 0 < ‖(ϖ : R)‖ := ϖ.norm_pos
  have hρ1 : ‖(ϖ : R)‖ < 1 := by rw [PseudoUniformizer.coe_eq]; exact ϖ.norm_lt_one
  have hτ0 : 0 < ‖e (ϖ : R)‖ := by
    rw [norm_pos_iff]; intro h
    have hz : (ϖ : R) = 0 := e.injective (by rw [h, map_zero])
    exact hρ0.ne' (by rw [hz, norm_zero])
  have hlogρ : Real.log ‖(ϖ : R)‖ < 0 := Real.log_neg hρ0 hρ1
  have hlogτ : Real.log ‖e (ϖ : R)‖ < 0 := Real.log_neg hτ0 hlt
  set s : ℝ := Real.log ‖e (ϖ : R)‖ / Real.log ‖(ϖ : R)‖ with hsdef
  have hs0 : 0 < s := by
    rw [hsdef, ← neg_div_neg_eq]; exact div_pos (neg_pos.2 hlogτ) (neg_pos.2 hlogρ)
  have hτρs : ‖e (ϖ : R)‖ = ‖(ϖ : R)‖ ^ s := by
    rw [hsdef, Real.rpow_def_of_pos hρ0, mul_comm, div_mul_cancel₀ _ hlogρ.ne, Real.exp_log hτ0]
  obtain ⟨δ, hδpos, he0⟩ : ∃ δ > 0, ∀ a : R, ‖a‖ ≤ δ → ‖e a‖ ≤ 1 := by
    have hc : ContinuousAt (e : R → S) 0 := he.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδpos, h⟩ := hc 1 zero_lt_one
    refine ⟨δ / 2, by positivity, fun a ha => ?_⟩
    have hlt' : ‖a‖ < δ := lt_of_le_of_lt ha (by linarith)
    have hd := h (show dist a 0 < δ by rwa [dist_zero_right])
    rw [map_zero, dist_zero_right] at hd
    exact hd.le
  obtain ⟨δ', hδ'pos, he'0⟩ : ∃ δ' > 0, ∀ a : R, ‖e a‖ ≤ δ' → ‖a‖ ≤ 1 := by
    have hc : ContinuousAt (e.symm : S → R) 0 := he'.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ', hδ'pos, h⟩ := hc 1 zero_lt_one
    refine ⟨δ' / 2, by positivity, fun a ha => ?_⟩
    have hlt' : ‖e a‖ < δ' := lt_of_le_of_lt ha (by linarith)
    have hd := h (show dist (e a) 0 < δ' by rwa [dist_zero_right])
    rw [map_zero, RingEquiv.symm_apply_apply, dist_zero_right] at hd
    exact hd.le
  refine ⟨δ' * ‖e (ϖ : R)‖, ((δ * ‖(ϖ : R)‖) ^ s)⁻¹, s,
    mul_pos hδ'pos hτ0, hs0, fun a => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha0
  · constructor <;> simp [Real.zero_rpow (ne_of_gt hs0)]
  · have hanorm0 : 0 < ‖a‖ := norm_pos_iff.2 ha0
    have hea0 : 0 < ‖e a‖ := by
      rw [norm_pos_iff]; exact fun h => ha0 (e.injective (by rw [h, map_zero]))
    constructor
    · -- lower bound
      obtain ⟨n, hn1, hn2⟩ := exists_zpow_mul_mem_shell hτ0 hlt hδ'pos hea0
      set b : R := ((ϖ.unit ^ n : Rˣ) : R) * a with hbdef
      have hebnorm : ‖e b‖ = ‖e (ϖ : R)‖ ^ n * ‖e a‖ := by
        rw [hbdef, map_mul, norm_map_zpow_mul e ϖ.unit hmul n (e a)]
      have hbRnorm : ‖b‖ = ‖(ϖ : R)‖ ^ n * ‖a‖ := by
        rw [hbdef, ← smul_eq_mul]; exact norm_pseudoUniformizer_zpow_smul ϖ n a
      have hb_le1 : ‖b‖ ≤ 1 := he'0 b (by rw [hebnorm]; exact hn1.le)
      have hρn0 : 0 < ‖(ϖ : R)‖ ^ n := zpow_pos hρ0 n
      have ha_le : ‖a‖ ≤ (‖(ϖ : R)‖ ^ n)⁻¹ := by
        rw [hbRnorm] at hb_le1
        calc ‖a‖ = (‖(ϖ : R)‖ ^ n)⁻¹ * (‖(ϖ : R)‖ ^ n * ‖a‖) := by
              rw [← mul_assoc, inv_mul_cancel₀ hρn0.ne', one_mul]
        _ ≤ (‖(ϖ : R)‖ ^ n)⁻¹ * 1 := mul_le_mul_of_nonneg_left hb_le1 (by positivity)
        _ = (‖(ϖ : R)‖ ^ n)⁻¹ := mul_one _
      have hτn0 : 0 < ‖e (ϖ : R)‖ ^ n := zpow_pos hτ0 n
      have has : ‖a‖ ^ s ≤ (‖e (ϖ : R)‖ ^ n)⁻¹ := by
        calc ‖a‖ ^ s ≤ ((‖(ϖ : R)‖ ^ n)⁻¹) ^ s := Real.rpow_le_rpow (norm_nonneg _) ha_le hs0.le
        _ = ((‖(ϖ : R)‖ ^ n) ^ s)⁻¹ := Real.inv_rpow (by positivity) s
        _ = (‖e (ϖ : R)‖ ^ n)⁻¹ := by rw [← zpow_eq_rpow_zpow hρ0.le hτρs n]
      have hea_ge : δ' * ‖e (ϖ : R)‖ * (‖e (ϖ : R)‖ ^ n)⁻¹ ≤ ‖e a‖ := by
        rw [← div_eq_mul_inv, div_le_iff₀ hτn0, mul_comm ‖e a‖ (‖e (ϖ : R)‖ ^ n)]
        exact hn2
      calc δ' * ‖e (ϖ : R)‖ * ‖a‖ ^ s
          ≤ δ' * ‖e (ϖ : R)‖ * (‖e (ϖ : R)‖ ^ n)⁻¹ :=
            mul_le_mul_of_nonneg_left has (by positivity)
      _ ≤ ‖e a‖ := hea_ge
    · -- upper bound
      obtain ⟨n, hn1, hn2⟩ := exists_zpow_mul_mem_shell hρ0 hρ1 hδpos hanorm0
      set b : R := ((ϖ.unit ^ n : Rˣ) : R) * a with hbdef
      have hebnorm : ‖e b‖ = ‖e (ϖ : R)‖ ^ n * ‖e a‖ := by
        rw [hbdef, map_mul, norm_map_zpow_mul e ϖ.unit hmul n (e a)]
      have hbRnorm : ‖b‖ = ‖(ϖ : R)‖ ^ n * ‖a‖ := by
        rw [hbdef, ← smul_eq_mul]; exact norm_pseudoUniformizer_zpow_smul ϖ n a
      have heb_le1 : ‖e b‖ ≤ 1 := he0 b (by rw [hbRnorm]; exact hn1.le)
      have hτn0 : 0 < ‖e (ϖ : R)‖ ^ n := zpow_pos hτ0 n
      have hρn0 : 0 < ‖(ϖ : R)‖ ^ n := zpow_pos hρ0 n
      have hea_le : ‖e a‖ ≤ (‖e (ϖ : R)‖ ^ n)⁻¹ := by
        rw [hebnorm] at heb_le1
        calc ‖e a‖ = (‖e (ϖ : R)‖ ^ n)⁻¹ * (‖e (ϖ : R)‖ ^ n * ‖e a‖) := by
              rw [← mul_assoc, inv_mul_cancel₀ hτn0.ne', one_mul]
        _ ≤ (‖e (ϖ : R)‖ ^ n)⁻¹ * 1 := mul_le_mul_of_nonneg_left heb_le1 (by positivity)
        _ = (‖e (ϖ : R)‖ ^ n)⁻¹ := mul_one _
      have hinv_le : (‖(ϖ : R)‖ ^ n)⁻¹ ≤ ‖a‖ / (δ * ‖(ϖ : R)‖) := by
        rw [le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hρn0,
            mul_comm ‖a‖ (‖(ϖ : R)‖ ^ n)]
        exact hn2
      calc ‖e a‖ ≤ (‖e (ϖ : R)‖ ^ n)⁻¹ := hea_le
      _ = ((‖(ϖ : R)‖ ^ n)⁻¹) ^ s := by
            rw [Real.inv_rpow (by positivity) s, ← zpow_eq_rpow_zpow hρ0.le hτρs n]
      _ ≤ (‖a‖ / (δ * ‖(ϖ : R)‖)) ^ s := Real.rpow_le_rpow (by positivity) hinv_le hs0.le
      _ = ((δ * ‖(ϖ : R)‖) ^ s)⁻¹ * ‖a‖ ^ s := by
            rw [Real.div_rpow (norm_nonneg _) (by positivity), div_eq_inv_mul]

variable {I : Type*} [DecidableEq I]

private theorem norm_matrixCoeff_le' [IsTate R] (u : c(I, R) →L[R] c(I, R)) (j i : I) :
    ‖matrixCoeff u j i‖ ≤ ‖u‖ :=
  calc ‖matrixCoeff u j i‖ ≤ ‖u (cSpace.single i 1)‖ := cSpace.norm_apply_le _ _
  _ ≤ ‖u‖ * ‖cSpace.single i (1 : R)‖ := le_opNorm _ _
  _ = ‖u‖ := by rw [cSpace.norm_single_one, mul_one]

private theorem norm_matrixCoeff_le_rowNorm' [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (j i : I) : ‖matrixCoeff u j i‖ ≤ rowNorm u j :=
  le_ciSup ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact norm_matrixCoeff_le' u j i⟩ i

/-- A norm-bounded ring homomorphism is continuous (Lipschitz). -/
private theorem continuous_of_norm_bound (ψ : R →+* S) (C : ℝ)
    (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖) : Continuous ψ := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal C) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  calc ‖ψ (x - y)‖ ≤ C * ‖x - y‖ := hψ _
  _ ≤ Real.toNNReal C * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)

/-- Coefficientwise transfer of the Fredholm determinant along any continuous ring
homomorphism relating the matrices. -/
private theorem charCoeff_map_of_continuous [IsTate R] [IsTate S]
    (ψ : R →+* S) (hψc : Continuous ψ)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) (n : ℕ) :
    charCoeff v n = ψ (charCoeff u n) := by
  rw [charCoeff, charCoeff, map_mul, map_pow, map_neg, map_one]
  congr 1
  have hminor : ∀ T : Finset I, minor v T = ψ (minor u T) := by
    intro T
    have hMeq : (Matrix.of fun j i : T => matrixCoeff v (j : I) (i : I))
        = ψ.mapMatrix (Matrix.of fun j i : T => matrixCoeff u (j : I) (i : I)) :=
      Matrix.ext fun j i => hv (j : I) (i : I)
    show (Matrix.of fun j i : T => matrixCoeff v (j : I) (i : I)).det = _
    rw [hMeq]
    exact (RingHom.map_det ψ _).symm
  rw [tsum_congr fun T : {T : Finset I // T.card = n} => hminor (T : Finset I)]
  exact ((summable_minor u hu n).hasSum.map ψ.toAddMonoidHom hψc).tsum_eq

/-- Norm-invariance of compactoidness ([JN] Proposition 2.1.8, genuinely
Noetherian-free): a bicontinuous ring isomorphism relating the matrices transfers row
decay (a topological statement).  (`he'` and `[IsTate S]` are [JN]'s hypotheses on the pair;
this direction of the proof does not consume them.) -/
@[nolint unusedArguments]
theorem isCompactoid_map_equiv [IsTate R] [IsTate S]
    (e : R ≃+* S) (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = e (matrixCoeff u j i)) :
    IsCompactoid v := by
  rw [IsCompactoid, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ r : R, ‖r‖ < δ → ‖e r‖ < ε / 2 := by
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuous_iff.1 he 0 (ε / 2) (half_pos hε)
    exact ⟨δ, hδ0, fun r hr => by
      have := hδ r (by rwa [dist_zero_right])
      rwa [map_zero, dist_zero_right] at this⟩
  filter_upwards [Metric.tendsto_nhds.1 hu δ hδ0] with j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg v j)]
  have hle : rowNorm v j ≤ ε / 2 := by
    refine Real.iSup_le (fun i => ?_) (half_pos hε).le
    rw [hv]
    exact (hδ _ ((norm_matrixCoeff_le_rowNorm' u j i).trans_lt hj)).le
  exact lt_of_le_of_lt hle (half_lt_self hε)

/-- Norm-invariance of the Fredholm determinant ([JN] Proposition 2.1.8,
Noetherian-free): `det(1 − Tv) = e(det(1 − Tu))` for a bicontinuous `e`.  Note this is a
*topological* statement (summability transfer) — `e` is only power-comparable
(`norm_le_pow_of_equiv`), not bounded, so it is **not** a special case of
`charPowerSeries_baseChange`.  (`he'` is part of "bicontinuous", kept for faithfulness.) -/
@[nolint unusedArguments]
theorem charPowerSeries_map_equiv [IsTate R] [IsTate S]
    (e : R ≃+* S) (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = e (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map (e : R →+* S) (charPowerSeries u) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, charPowerSeries_coeff, charPowerSeries_coeff]
  exact charCoeff_map_of_continuous (R := R) (S := S) (e : R →+* S) he u hu v hv n

/-- Base change along a bounded homomorphism, compactoid half
(`r_j(v) ≤ C·r_j(u) → 0`).  (`[IsTate S]` is carried for symmetry with the determinant
statements below, which do consume it.) -/
@[nolint unusedArguments]
theorem isCompactoid_baseChange [IsTate R] [IsTate S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) :
    IsCompactoid v := by
  have hbound : ∀ j, rowNorm v j ≤ max C 0 * rowNorm u j := fun j => by
    refine Real.iSup_le (fun i => ?_)
      (mul_nonneg (le_max_right _ _) (rowNorm_nonneg u j))
    rw [hv]
    calc ‖ψ (matrixCoeff u j i)‖ ≤ C * ‖matrixCoeff u j i‖ := hψ _
    _ ≤ max C 0 * ‖matrixCoeff u j i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max C 0 * rowNorm u j :=
        mul_le_mul_of_nonneg_left (norm_matrixCoeff_le_rowNorm' u j i) (le_max_right _ _)
  refine squeeze_zero (fun j => rowNorm_nonneg v j) hbound ?_
  simpa using hu.const_mul (max C 0)

/-- Base change along a bounded homomorphism, coefficientwise: `cₙ(v) = ψ(cₙ(u))`
(`ψ` commutes with finite determinants and, being continuous, with the `tsum`). -/
theorem charCoeff_baseChange [IsTate R] [IsTate S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) (n : ℕ) :
    charCoeff v n = ψ (charCoeff u n) :=
  charCoeff_map_of_continuous (R := R) (S := S) ψ (continuous_of_norm_bound (R := R) (S := S) ψ C hψ) u hu v hv n

/-- Base change, assembled: `det(1 − Tv) = ψ(det(1 − Tu))` in `S⟦T⟧`. -/
theorem charPowerSeries_baseChange [IsTate R] [IsTate S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map ψ (charPowerSeries u) := by
  ext n
  simp [charCoeff_baseChange S ψ C hψ u hu v hv n, PowerSeries.coeff_map]

variable {S}

/-- Base change along an **isometric** homomorphism, coefficientwise: `cₙ(v) = f(cₙ(u))`. -/
theorem charCoeff_map [IsTate R] [IsTate S] (f : R →+* S) (hf : ∀ x, ‖f x‖ = ‖x‖)
    {u : c(I, R) →L[R] c(I, R)} {v : c(I, S) →L[S] c(I, S)} (hu : IsCompactoid u)
    (hmatch : ∀ j i, matrixCoeff v j i = f (matrixCoeff u j i)) (n : ℕ) :
    charCoeff v n = f (charCoeff u n) :=
  charCoeff_baseChange S f 1 (fun r => by rw [hf, one_mul]) u hu v hmatch n

/-- Base change along an **isometric** homomorphism: `det(1 − Tv) = f(det(1 − Tu))`. -/
theorem charPowerSeries_map [IsTate R] [IsTate S] (f : R →+* S) (hf : ∀ x, ‖f x‖ = ‖x‖)
    {u : c(I, R) →L[R] c(I, R)} {v : c(I, S) →L[S] c(I, S)} (hu : IsCompactoid u)
    (hmatch : ∀ j i, matrixCoeff v j i = f (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map f (charPowerSeries u) :=
  charPowerSeries_baseChange S f 1 (fun r => by rw [hf, one_mul]) u hu v hmatch

end NormChange

/-! ## Classical specialisations

Statements that are intrinsically about the field case, phrased against the merged
definitions so that the parent files' versions are literal instances.  The residue
machinery feeding the proof lives in `Residue.lean`. -/

section Classical

section RescaledNorm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
  [CompleteSpace E]

/-- The "largest norm `< 1`" pseudo-uniformizer property, packaged so it can be carried
through `Fact` to equip the rescaled-norm instances on `Rescaled`. -/
private def uniformizerFact (π : K) : Prop :=
  0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖

/-- Type synonym carrying [Bel] Theorem II.1.13's rescaled norm `Residue.rescale π ·`.
Definitionally `E`, but equipped with a fresh norm/uniformity so the Serre machinery
(`isONable_of_discrete_norms`) applies to it. -/
private def Rescaled (_ : K) (E : Type*) : Type _ := E

private instance instAddCommGroupRescaled (π : K) : AddCommGroup (Rescaled π E) :=
  inferInstanceAs (AddCommGroup E)

private instance instModuleRescaled (π : K) : Module K (Rescaled π E) :=
  inferInstanceAs (Module K E)

/-- The identity `K`-linear equivalence `E ≃ₗ[K] Rescaled π E` (both directions the
identity map; only the norm changes). -/
private def toRescaledₗ (π : K) : E ≃ₗ[K] Rescaled π E where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl

private theorem rescale_zero (π : K) : rescale π (0 : E) = 0 := by
  rw [rescale, if_pos rfl]

private theorem rescale_pos (π : K) (hπ0 : 0 < ‖π‖) {m : E} (hm : m ≠ 0) :
    0 < rescale π m := by
  rw [rescale, if_neg hm]; exact zpow_pos hπ0 _

private theorem rescale_neg (π : K) (m : E) : rescale π (-m) = rescale π m := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [neg_zero]
  · rw [rescale, rescale, if_neg (neg_ne_zero.mpr hm), if_neg hm, norm_neg]

private theorem norm_le_rescale (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) (m : E) :
    ‖m‖ ≤ rescale π m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [rescale_zero]
  · exact (le_rescale_and_rescale_lt π hπ0 hπ1 m hm).1

private theorem rescale_le_inv_mul (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) (m : E) :
    rescale π m ≤ ‖π‖⁻¹ * ‖m‖ := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [rescale_zero]
  · exact (le_rescale_and_rescale_lt π hπ0 hπ1 m hm).2.le

/-- The rescaled norm makes `Rescaled π E` a normed group.  The axioms are the residue
lemmas of `Residue.lean`: `map_zero'`/definiteness from `rescale (0) = 0` and
`rescale_pos`, the (ultrametric, hence ordinary) triangle inequality from `rescale_add_le`,
and neg-invariance from `rescale_neg`. -/
private instance instNormedAddCommGroupRescaled (π : K) [h : Fact (uniformizerFact π)] :
    NormedAddCommGroup (Rescaled π E) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun m => rescale π ((toRescaledₗ π).symm m)
      map_zero' := by
        show rescale π ((toRescaledₗ π).symm (0 : Rescaled π E)) = 0
        rw [map_zero]; exact rescale_zero π
      add_le' := fun x y => by
        show rescale π ((toRescaledₗ π).symm (x + y))
          ≤ rescale π ((toRescaledₗ π).symm x) + rescale π ((toRescaledₗ π).symm y)
        rw [map_add]
        exact (rescale_add_le π h.out.1 h.out.2.1 _ _).trans
          (max_le_add_of_nonneg (rescale_nonneg π _) (rescale_nonneg π _))
      neg' := fun x => by
        show rescale π ((toRescaledₗ π).symm (-x)) = rescale π ((toRescaledₗ π).symm x)
        rw [map_neg, rescale_neg]
      eq_zero_of_map_eq_zero' := fun x hx => by
        have hx' : rescale π ((toRescaledₗ π).symm x) = 0 := hx
        have hm : (toRescaledₗ π).symm x = 0 := by
          by_contra hne; exact (rescale_pos π h.out.1 hne).ne' hx'
        rw [← map_zero (toRescaledₗ π).symm] at hm
        exact (toRescaledₗ π).symm.injective hm }

/-- Definitional unfolding of the rescaled norm. -/
private theorem norm_rescaled (π : K) [Fact (uniformizerFact π)] (m : Rescaled π E) :
    ‖m‖ = rescale π ((toRescaledₗ π).symm m) := rfl

private instance instIsUltrametricRescaled (π : K) [h : Fact (uniformizerFact π)] :
    IsUltrametricDist (Rescaled π E) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_
  simp only [norm_rescaled, map_add]
  exact rescale_add_le π h.out.1 h.out.2.1 _ _

private instance instNormedSpaceRescaled (π : K) [h : Fact (uniformizerFact π)] :
    NormedSpace K (Rescaled π E) where
  norm_smul_le c x := by
    simp only [norm_rescaled, map_smul]
    exact le_of_eq (rescale_smul π h.out.1 h.out.2.1 h.out.2.2 c _)

/-- The identity map is a continuous `K`-linear isomorphism `E ≃L[K] Rescaled π E`: the
norm sandwich `‖m‖ ≤ rescale π m ≤ ‖π‖⁻¹‖m‖` (`Residue.le_rescale_and_rescale_lt`) bounds it
in both directions. -/
private def rescaledCLE (π : K) [h : Fact (uniformizerFact π)] : E ≃L[K] Rescaled π E :=
  LinearEquiv.toContinuousLinearEquivOfBounds (toRescaledₗ π) ‖π‖⁻¹ 1
    (fun x => by
      simp only [norm_rescaled, LinearEquiv.symm_apply_apply]
      exact rescale_le_inv_mul π h.out.1 h.out.2.1 x)
    (fun x => by
      rw [one_mul]
      simp only [norm_rescaled]
      exact norm_le_rescale π h.out.1 h.out.2.1 _)

/-- Completeness transports along the bi-Lipschitz identity `rescaledCLE`. -/
private instance instCompleteSpaceRescaled (π : K) [Fact (uniformizerFact π)] :
    CompleteSpace (Rescaled π E) :=
  ((rescaledCLE π).isUniformEmbedding.toIsUniformInducing.completeSpace_congr
    (rescaledCLE π).surjective).mp inferInstance

end RescaledNorm

/-- **Serre's theorem** ([Bel] Theorem II.1.13 for `ℚ_p`; [Serre] Prop. 1; blueprint
Lemma 6.7): over a **discretely valued** nontrivially normed field `K`, every Banach
`K`-space is potentially ON-able.  Intrinsically a field statement: over a general
Banach–Tate ring not every Banach module is potentially ON-able (which is exactly why
property (Pr) exists).

*Proof sketch.*  Rescale the norm into `‖K‖` (`rescale`, lemmas R7a–R7c of
`Residue.lean`), then apply `isONable_of_discrete_norms` to the rescaled space and
transport along the identity homeomorphism. -/
theorem isPotentiallyONable_of_uniformizer (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K]
    (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    [CompleteSpace E] :
    IsPotentiallyONable K E := by
  obtain ⟨π, hπ0, hπ1, hπmax⟩ := hd
  haveI : Fact (uniformizerFact π) := ⟨⟨hπ0, hπ1, hπmax⟩⟩
  -- The norms of the rescaled space lie in `‖π‖^ℤ ∪ {0}`, by construction of `rescale`.
  have hdisc : ∀ m : Rescaled π E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n := by
    intro m hm
    have hmE : (toRescaledₗ π).symm m ≠ 0 := by
      rw [← map_zero (toRescaledₗ π).symm]
      exact (toRescaledₗ π).symm.injective.ne hm
    refine ⟨⌊Real.log ‖(toRescaledₗ π).symm m‖ / Real.log ‖π‖⌋, ?_⟩
    rw [norm_rescaled, rescale, if_neg hmE]
  -- Serre's theorem for the (discretely-normed) rescaled space, then transport the
  -- resulting isometry back along the identity homeomorphism `rescaledCLE`.
  obtain ⟨s, ⟨iso⟩⟩ := isONable_of_discrete_norms π hπ0 hπ1 hπmax hdisc
  exact ⟨s, ⟨(rescaledCLE π).trans iso.toContinuousLinearEquiv⟩⟩

end Classical

end TateFredholm

end
