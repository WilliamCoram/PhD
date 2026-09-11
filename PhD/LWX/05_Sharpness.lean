/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«04_Halo»

/-!
# Sharpness of the halo estimate: [LWX, Cor 3.18]'s equality clause

For the specialized characteristic series `∑ c_n(T₀) Xⁿ` at a halo point `p⁻¹ < ‖T₀‖ < 1`,
[LWX, Cor 3.18] refines `v(c_n(T₀)) ≥ λ(n)·v(T₀)` (proved as
`norm_specCharSeries_coeff_le` in `04_Halo.lean`) to

* equality **iff** `b_{n,λ(n)} ∈ ℤ_p^×` (`norm_specCharSeries_coeff_eq_iff`), and
* the margin `v(c_n(T₀)) ≥ λ(n)·v(T₀) + min{v(T₀), 1 − v(T₀)}` when `b_{n,λ(n)}` is not a
  unit (`norm_specCharSeries_coeff_le_of_not_isUnit`; in norm form the factor
  `max(‖T₀‖, p⁻¹/‖T₀‖)`).

The engine is the term-by-term estimate [LWX, (3.18.1)] (`norm_coeff_mul_zpow_le_of_lt` …)
together with the ultrametric "unique dominant term" principle
(`TateFredholm.norm_tsum_eq_of_forall_lt`).
-/

open Filter Topology Finset TateFredholm

noncomputable section

namespace TateFredholm

section UltrametricStrict

variable {ι E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]
  {f : ι → E}

/-- Strict ultrametric bound: if every term of a null family is `< B`, so is the sum
(all but finitely many terms are `< B/2`; the finitely many others have a maximum `< B`). -/
theorem norm_tsum_lt_of_forall_lt (hf : Tendsto f cofinite (𝓝 0)) {B : ℝ} (hB : 0 < B)
    (hlt : ∀ i, ‖f i‖ < B) : ‖∑' i, f i‖ < B := by
  have hev : ∀ᶠ i in cofinite, ‖f i‖ < B / 2 := by
    have := Metric.tendsto_nhds.1 hf (B / 2) (by positivity)
    simpa [dist_zero_right] using this
  have hS : {i | ¬ ‖f i‖ < B / 2}.Finite := Filter.eventually_cofinite.1 hev
  obtain ⟨M, hM, hMB⟩ : ∃ M : ℝ, (∀ i, ‖f i‖ ≤ M) ∧ M < B := by
    rcases hS.toFinset.eq_empty_or_nonempty with h | h
    · refine ⟨B / 2, fun i ↦ ?_, by linarith⟩
      by_contra hcon
      have hi : i ∈ hS.toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt]
        exact (not_le.1 hcon).le
      rw [h] at hi
      exact absurd hi (Finset.notMem_empty i)
    · obtain ⟨i₀, -, hmax⟩ := hS.toFinset.exists_max_image (fun i ↦ ‖f i‖) h
      refine ⟨max (B / 2) ‖f i₀‖, fun i ↦ ?_, max_lt (by linarith) (hlt i₀)⟩
      by_cases hi : ‖f i‖ < B / 2
      · exact hi.le.trans (le_max_left _ _)
      · exact (hmax i (by simpa using hi)).trans (le_max_right _ _)
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [tsum_empty, norm_zero]
    exact hB
  · exact lt_of_le_of_lt ((norm_tsum_le_iSup hf).trans (ciSup_le hM)) hMB

/-- **Unique dominant term**: a null family with one term of norm `B` and all others `< B`
has a sum of norm exactly `B`. -/
theorem norm_tsum_eq_of_forall_lt (hf : Tendsto f cofinite (𝓝 0)) {i₀ : ι} {B : ℝ}
    (hi₀ : ‖f i₀‖ = B) (hlt : ∀ i, i ≠ i₀ → ‖f i‖ < B) : ‖∑' i, f i‖ = B := by
  classical
  have hsum : Summable f := summable_of_tendsto_cofinite hf
  rw [hsum.tsum_eq_add_tsum_ite i₀]
  rcases eq_or_lt_of_le (norm_nonneg (f i₀)) with h0 | hpos
  · have hB0 : B = 0 := by rw [← hi₀, ← h0]
    have hg0 : (fun i ↦ if i = i₀ then 0 else f i) = fun _ ↦ (0 : E) := by
      funext i
      by_cases hi : i = i₀
      · simp [hi]
      · exact absurd (hlt i hi) (by rw [hB0]; exact not_lt.2 (norm_nonneg _))
    rw [hg0, tsum_zero, add_zero, hi₀]
  · have hgt : Tendsto (fun i ↦ if i = i₀ then 0 else f i) cofinite (𝓝 0) := by
      refine hf.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Set.finite_singleton i₀).subset fun i hi ↦ ?_
      by_contra h
      exact hi (by simp [show i ≠ i₀ from h])
    have hrest : ‖∑' i, (if i = i₀ then 0 else f i)‖ < B := by
      refine norm_tsum_lt_of_forall_lt hgt (hi₀ ▸ hpos) fun i ↦ ?_
      by_cases hi : i = i₀
      · simp [hi, hi₀ ▸ hpos]
      · simpa [hi] using hlt i hi
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hi₀]; exact hrest.ne'), hi₀,
      max_eq_left hrest.le]

end UltrametricStrict

end TateFredholm

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### The term-by-term estimate [LWX, (3.18.1)] -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- [LWX, (3.18.1)], `m < λ(n)`: `v(b_{n,m}T₀^m) ≥ λ(n)−m + m·v(T₀) ≥ λ(n)v(T₀) + (1 − v(T₀))`,
i.e. `‖b_{n,m}T₀^m‖ ≤ ‖T₀‖^{λ(n)}·(p⁻¹/‖T₀‖)`. -/
theorem norm_coeff_mul_zpow_le_of_lt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (_h1 : ‖T₀‖ < 1) (n : ℕ) {m : ℤ}
    (hm : m < lwxLambda p (Fintype.card ι) n) :
    ‖ψ ((charCoeff (D.op ω) n) m) * T₀ ^ m‖ ≤
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * ((p : ℝ)⁻¹ / ‖T₀‖) := by
  set L := lwxLambda p (Fintype.card ι) n with hL
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr hp0) h0
  have hpr : 1 < (p : ℝ) * ‖T₀‖ := by
    have := mul_lt_mul_of_pos_left h0 hp0
    rwa [mul_inv_cancel₀ hp0.ne'] at this
  have key : ((p : ℝ) * ‖T₀‖) ^ (m - L) ≤ ((p : ℝ) * ‖T₀‖) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ hpr.le (by omega)
  rw [mul_zpow, mul_zpow, zpow_neg_one, zpow_neg_one] at key
  rw [norm_mul, hψ, norm_zpow]
  calc ‖(charCoeff (D.op ω) n) m‖ * ‖T₀‖ ^ m
      ≤ (p : ℝ) ^ (m - L) * ‖T₀‖ ^ m :=
        mul_le_mul_of_nonneg_right (norm_coeff_charCoeff_upOp_le hp2 D ω n m)
          (zpow_nonneg hr0.le _)
    _ = (p : ℝ) ^ (m - L) * ‖T₀‖ ^ (m - L) * ‖T₀‖ ^ (L : ℤ) := by
        rw [mul_assoc, ← zpow_add₀ hr0.ne', sub_add_cancel]
    _ ≤ (p : ℝ)⁻¹ * ‖T₀‖⁻¹ * ‖T₀‖ ^ (L : ℤ) :=
        mul_le_mul_of_nonneg_right key (zpow_nonneg hr0.le _)
    _ = ‖T₀‖ ^ L * ((p : ℝ)⁻¹ / ‖T₀‖) := by
        rw [div_eq_mul_inv, mul_comm, zpow_natCast]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- [LWX, (3.18.1)], `m > λ(n)`: `v(b_{n,m}T₀^m) ≥ m·v(T₀) ≥ λ(n)v(T₀) + v(T₀)`. -/
theorem norm_coeff_mul_zpow_le_of_gt (_hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) {m : ℤ}
    (hm : (lwxLambda p (Fintype.card ι) n : ℤ) < m) :
    ‖ψ ((charCoeff (D.op ω) n) m) * T₀ ^ m‖ ≤ ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * ‖T₀‖ := by
  set L := lwxLambda p (Fintype.card ι) n with hL
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (by exact_mod_cast hp.out.pos)) h0
  rw [norm_mul, hψ, norm_zpow]
  calc ‖(charCoeff (D.op ω) n) m‖ * ‖T₀‖ ^ m ≤ 1 * ‖T₀‖ ^ m :=
        mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (zpow_nonneg hr0.le _)
    _ = ‖T₀‖ ^ m := one_mul _
    _ ≤ ‖T₀‖ ^ ((L : ℤ) + 1) := zpow_le_zpow_right_of_le_one₀ hr0 h1.le (by omega)
    _ = ‖T₀‖ ^ L * ‖T₀‖ := by rw [zpow_add_one₀ hr0.ne', zpow_natCast]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The diagonal term when `b_{n,λ(n)}` is a unit: `‖b_{n,λ(n)}T₀^{λ(n)}‖ = ‖T₀‖^{λ(n)}`. -/
theorem norm_coeff_mul_zpow_of_isUnit (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (T₀ : K) (n : ℕ)
    (hu : IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))) :
    ‖ψ ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ)) *
        T₀ ^ (lwxLambda p (Fintype.card ι) n : ℤ)‖ =
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := by
  rw [norm_mul, hψ, norm_zpow, PadicInt.isUnit_iff.1 hu, one_mul, zpow_natCast]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The diagonal term when `b_{n,λ(n)}` is not a unit: `v ≥ 1 + λ(n)v(T₀)`. -/
theorem norm_coeff_mul_zpow_le_of_not_isUnit (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (T₀ : K) (n : ℕ)
    (hu : ¬ IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))) :
    ‖ψ ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ)) *
        T₀ ^ (lwxLambda p (Fintype.card ι) n : ℤ)‖ ≤
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * (p : ℝ)⁻¹ := by
  set b := (charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ) with hb
  have hlt : ‖b‖ < 1 :=
    lt_of_le_of_ne (PadicInt.norm_le_one b) (fun h ↦ hu (PadicInt.isUnit_iff.2 h))
  have hle : ‖b‖ ≤ (p : ℝ)⁻¹ := by
    have := (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one b (-1)).2 (by simpa using hlt)
    simpa using this
  rw [norm_mul, hψ, norm_zpow, zpow_natCast, mul_comm]
  exact mul_le_mul_of_nonneg_left hle (pow_nonneg (norm_nonneg _) _)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Off the diagonal every term is strictly smaller than `‖T₀‖^{λ(n)}` ([LWX, Cor 3.18 proof]:
"the second equality holding if and only if `m = λ(n)`"). -/
theorem norm_coeff_mul_zpow_lt (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) {m : ℤ}
    (hm : m ≠ lwxLambda p (Fintype.card ι) n) :
    ‖ψ ((charCoeff (D.op ω) n) m) * T₀ ^ m‖ < ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (by exact_mod_cast hp.out.pos)) h0
  have hL : (0 : ℝ) < ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := pow_pos hr0 _
  rcases lt_or_gt_of_ne hm with h | h
  · exact (norm_coeff_mul_zpow_le_of_lt hp2 D ω ψ hψ h0 h1 n h).trans_lt
      (mul_lt_of_lt_one_right hL ((div_lt_one hr0).2 h0))
  · exact (norm_coeff_mul_zpow_le_of_gt hp2 D ω ψ hψ h0 h1 n h).trans_lt
      (mul_lt_of_lt_one_right hL h1)

/-! ### [LWX, Corollary 3.18], the sharpness clauses -/

/-- **[LWX, Cor 3.18], equality**: `v(c_n(T₀)) = λ(n)·v(T₀)` when `b_{n,λ(n)} ∈ ℤ_p^×`. -/
theorem norm_specCharSeries_coeff_eq_of_isUnit (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ)
    (hu : IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))) :
    ‖PowerSeries.coeff n (specCharSeries D ω ψ T₀)‖ = ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := by
  rw [specCharSeries, PowerSeries.coeff_mk, HaloInt.specialize]
  exact norm_tsum_eq_of_forall_lt
    (HaloInt.summable_specialize ψ hψ h0 h1 (charCoeff (D.op ω) n)).tendsto_cofinite_zero
    (norm_coeff_mul_zpow_of_isUnit D ω ψ hψ T₀ n hu)
    (fun m hm ↦ norm_coeff_mul_zpow_lt hp2 D ω ψ hψ h0 h1 n hm)

/-- **[LWX, Cor 3.18], the margin**: if `b_{n,λ(n)} ∉ ℤ_p^×` then
`v(c_n(T₀)) ≥ λ(n)·v(T₀) + min{v(T₀), 1 − v(T₀)}`, in norm form
`‖c_n(T₀)‖ ≤ ‖T₀‖^{λ(n)}·max(‖T₀‖, p⁻¹/‖T₀‖)`. -/
theorem norm_specCharSeries_coeff_le_of_not_isUnit (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ)
    (hu : ¬ IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ))) :
    ‖PowerSeries.coeff n (specCharSeries D ω ψ T₀)‖ ≤
      ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n * max ‖T₀‖ ((p : ℝ)⁻¹ / ‖T₀‖) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr hp0) h0
  have hL0 : (0 : ℝ) ≤ ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n := pow_nonneg hr0.le _
  rw [specCharSeries, PowerSeries.coeff_mk, HaloInt.specialize]
  refine (norm_tsum_le_iSup
    (HaloInt.summable_specialize ψ hψ h0 h1 (charCoeff (D.op ω) n)).tendsto_cofinite_zero).trans
    (ciSup_le fun m ↦ ?_)
  rcases lt_trichotomy m (lwxLambda p (Fintype.card ι) n : ℤ) with h | h | h
  · exact (norm_coeff_mul_zpow_le_of_lt hp2 D ω ψ hψ h0 h1 n h).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hL0)
  · subst h
    refine (norm_coeff_mul_zpow_le_of_not_isUnit D ω ψ hψ T₀ n hu).trans
      (mul_le_mul_of_nonneg_left (le_trans ?_ (le_max_right _ _)) hL0)
    rw [le_div_iff₀ hr0]
    exact mul_le_of_le_one_right (inv_nonneg.2 hp0.le) h1.le
  · exact (norm_coeff_mul_zpow_le_of_gt hp2 D ω ψ hψ h0 h1 n h).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hL0)

/-- **[LWX, Cor 3.18], the equality criterion**: `v(c_n(T₀)) = λ(n)·v(T₀)` iff
`b_{n,λ(n)} ∈ ℤ_p^×`. -/
theorem norm_specCharSeries_coeff_eq_iff (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) :
    ‖PowerSeries.coeff n (specCharSeries D ω ψ T₀)‖ = ‖T₀‖ ^ lwxLambda p (Fintype.card ι) n ↔
      IsUnit ((charCoeff (D.op ω) n) (lwxLambda p (Fintype.card ι) n : ℤ)) := by
  refine ⟨fun h ↦ ?_, norm_specCharSeries_coeff_eq_of_isUnit hp2 D ω ψ hψ h0 h1 n⟩
  by_contra hu
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (by exact_mod_cast hp.out.pos)) h0
  have hmax : max ‖T₀‖ ((p : ℝ)⁻¹ / ‖T₀‖) < 1 := max_lt h1 ((div_lt_one hr0).2 h0)
  refine absurd h (ne_of_lt ?_)
  exact (norm_specCharSeries_coeff_le_of_not_isUnit hp2 D ω ψ hψ h0 h1 n hu).trans_lt
    (mul_lt_of_lt_one_right (pow_pos hr0 _) hmax)

end LWX

end
