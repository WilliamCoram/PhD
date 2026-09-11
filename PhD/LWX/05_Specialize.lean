/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«04_IntegralModel»

/-!
# Specialization of `Λ^{>1/p}` at a halo point, as a continuous ring homomorphism

[LWX, Cor 3.18] evaluates the `T`-expansions of the coefficients `c_n ∈ Λ^{>1/p}` at a point
`T₀` of the halo annulus `p⁻¹ < ‖T₀‖ < 1`; `PhD/LWX/00_HaloRing.lean` defines that evaluation
`HaloInt.specialize ψ T₀ : Λ^{>1/p} → K` and proves the coefficient estimate.  [LWX, Prop
2.17] needs more: the specialization must be pushed through determinants (`Char(P)` is a
limit of determinants of minors of `P`) and through the convergent Mahler/entry sums of
[LWX, Prop 3.4].  This file upgrades `specialize` to a **continuous ring homomorphism**
(`specializeHom`) and records its values on the generators the seam uses: constants, `T`,
the binomial series `(1+T)^s` of [LWX, Notation 2.1] and the universal character
`[a] = ω(ā)·(1+T)^{ℓ⟨a⟩}`.

## Main declarations

* `LWX.HaloInt.specializeHom` — `f ↦ f(T₀)` as a ring homomorphism `Λ^{>1/p} →+* K`.
* `LWX.HaloInt.continuous_specialize`, `LWX.HaloInt.HasSum.specialize` — continuity, so the
  evaluation commutes with convergent sums.
* `LWX.oneAddPow`, `LWX.specialize_oneAddTPow`, `LWX.specialize_univChar` — the values of the
  specialization on `(1+T)^s` and on the universal character.
-/

open Filter Topology

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace HaloInt

variable (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K} (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
  (h1 : ‖T₀‖ < 1)

include hψ h0 h1 in
/-- The specialization is additive (termwise, by `summable_specialize`). -/
theorem specialize_add (f g : HaloInt p) :
    specialize ψ T₀ (f + g) = specialize ψ T₀ f + specialize ψ T₀ g := by
  unfold specialize
  rw [← (summable_specialize ψ hψ h0 h1 f).tsum_add (summable_specialize ψ hψ h0 h1 g)]
  exact tsum_congr fun j => by rw [coeff_add, map_add, add_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The specialization of `0` is `0`. -/
theorem specialize_zero : specialize ψ T₀ (0 : HaloInt p) = 0 := by
  simp [specialize]

omit [IsUltrametricDist K] [CompleteSpace K] in
include hψ h0 h1 in
/-- Every term of the specialization series has norm at most `1` on the annulus
(`‖f_j‖ ≤ p^{min(0,j)}`, `‖T₀‖ < 1`, `p‖T₀‖ > 1`). -/
theorem norm_specialize_term_le_one (f : HaloInt p) (j : ℤ) : ‖ψ (f j) * T₀ ^ j‖ ≤ 1 := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (by exact_mod_cast hp.out.pos)) h0
  rw [norm_mul, hψ, norm_zpow]
  rcases le_or_gt 0 j with hj | hj
  · calc ‖f j‖ * ‖T₀‖ ^ j ≤ 1 * ‖T₀‖ ^ j :=
          mul_le_mul_of_nonneg_right ((f.bound j).trans_eq (by rw [min_eq_left hj, zpow_zero]))
            (zpow_nonneg hr0.le _)
      _ = ‖T₀‖ ^ j := one_mul _
      _ ≤ ‖T₀‖ ^ (0 : ℤ) := zpow_le_zpow_right_of_le_one₀ hr0 h1.le hj
      _ = 1 := zpow_zero _
  · have hpr : 1 < (p : ℝ) * ‖T₀‖ := by
      calc (1 : ℝ) = (p : ℝ) * (p : ℝ)⁻¹ :=
            (mul_inv_cancel₀ (by exact_mod_cast hp.out.ne_zero)).symm
        _ < (p : ℝ) * ‖T₀‖ := mul_lt_mul_of_pos_left h0 (by exact_mod_cast hp.out.pos)
    calc ‖f j‖ * ‖T₀‖ ^ j ≤ (p : ℝ) ^ j * ‖T₀‖ ^ j :=
          mul_le_mul_of_nonneg_right ((f.bound j).trans_eq (by rw [min_eq_right hj.le]))
            (zpow_nonneg hr0.le _)
      _ = ((p : ℝ) * ‖T₀‖) ^ j := (mul_zpow _ _ _).symm
      _ ≤ ((p : ℝ) * ‖T₀‖) ^ (0 : ℤ) := zpow_le_zpow_right₀ hpr.le hj.le
      _ = 1 := zpow_zero _

include hψ h0 h1 in
/-- The specialization is multiplicative: the Cauchy product of the two-sided series
`∑ ψ(f_i)T₀^i` and `∑ ψ(g_j)T₀^j` is the series of the convolution `f * g`. -/
theorem specialize_mul (f g : HaloInt p) :
    specialize ψ T₀ (f * g) = specialize ψ T₀ f * specialize ψ T₀ g := by
  have hr0 : (0 : ℝ) < ‖T₀‖ := lt_trans (inv_pos.mpr (by exact_mod_cast hp.out.pos)) h0
  have hT0 : T₀ ≠ 0 := norm_pos_iff.mp hr0
  have hψc : Continuous ψ :=
    AddMonoidHomClass.continuous_of_bound ψ 1 fun x => by rw [hψ, one_mul]
  set a : ℤ → K := fun i => ψ (f i) * T₀ ^ i with ha
  set b : ℤ → K := fun j => ψ (g j) * T₀ ^ j with hb
  have hsa : Summable a := summable_specialize ψ hψ h0 h1 f
  have hsb : Summable b := summable_specialize ψ hψ h0 h1 g
  have ha1 : ∀ i, ‖a i‖ ≤ 1 := fun i => norm_specialize_term_le_one ψ hψ h0 h1 f i
  have hb1 : ∀ j, ‖b j‖ ≤ 1 := fun j => norm_specialize_term_le_one ψ hψ h0 h1 g j
  have hab : Summable fun x : ℤ × ℤ => a x.1 * b x.2 := by
    refine TateFredholm.summable_of_tendsto_cofinite ?_
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hfa : {i : ℤ | ¬ ‖a i‖ < ε}.Finite := by
      have h := hsa.tendsto_cofinite_zero
      rw [NormedAddGroup.tendsto_nhds_zero] at h
      exact Filter.eventually_cofinite.mp (h ε hε)
    have hfb : {j : ℤ | ¬ ‖b j‖ < ε}.Finite := by
      have h := hsb.tendsto_cofinite_zero
      rw [NormedAddGroup.tendsto_nhds_zero] at h
      exact Filter.eventually_cofinite.mp (h ε hε)
    rw [Filter.eventually_cofinite]
    refine (hfa.prod hfb).subset fun x hx => ?_
    have hx' : ε ≤ ‖a x.1 * b x.2‖ := not_lt.mp hx
    refine Set.mem_prod.mpr ⟨fun hlt => ?_, fun hlt => ?_⟩
    · have : ‖a x.1 * b x.2‖ ≤ ‖a x.1‖ * 1 :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hb1 _) (norm_nonneg _))
      linarith
    · have : ‖a x.1 * b x.2‖ ≤ 1 * ‖b x.2‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (ha1 _) (norm_nonneg _))
      linarith
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun x => (x.2, x.1 - x.2)
      invFun := fun y => (y.1 + y.2, y.1)
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  have hab' : Summable fun x : ℤ × ℤ => a x.2 * b (x.1 - x.2) :=
    (e.summable_iff (f := fun x : ℤ × ℤ => a x.1 * b x.2)).mpr hab
  have hslice : ∀ k : ℤ, Summable fun i : ℤ => a i * b (k - i) := fun k => hab'.prod_factor k
  calc specialize ψ T₀ (f * g) = ∑' k : ℤ, ψ ((f * g) k) * T₀ ^ k := rfl
    _ = ∑' k : ℤ, ∑' i : ℤ, a i * b (k - i) := by
        refine tsum_congr fun k => ?_
        rw [coeff_mul, ← ((summable_mul_coeff f g k).hasSum.map ψ hψc).tsum_eq,
          ← tsum_mul_right]
        refine tsum_congr fun i => ?_
        show ψ (f i * g (k - i)) * T₀ ^ k = ψ (f i) * T₀ ^ i * (ψ (g (k - i)) * T₀ ^ (k - i))
        rw [map_mul, show T₀ ^ k = T₀ ^ i * T₀ ^ (k - i) by
          rw [← zpow_add₀ hT0]; congr 1; ring]
        ring
    _ = ∑' x : ℤ × ℤ, a x.2 * b (x.1 - x.2) := (hab'.tsum_prod' hslice).symm
    _ = ∑' x : ℤ × ℤ, a x.1 * b x.2 := e.tsum_eq (fun x : ℤ × ℤ => a x.1 * b x.2)
    _ = specialize ψ T₀ f * specialize ψ T₀ g := (hsa.tsum_mul_tsum hsb hab).symm

/-- **Specialization as a ring homomorphism** `Λ^{>1/p} →+* K` at a halo point
`p⁻¹ < ‖T₀‖ < 1` ([LWX, Cor 3.18]'s evaluation, bundled). -/
def specializeHom : HaloInt p →+* K where
  toFun := specialize ψ T₀
  map_one' := specialize_one ψ T₀
  map_mul' := specialize_mul ψ hψ h0 h1
  map_zero' := specialize_zero ψ
  map_add' := specialize_add ψ hψ h0 h1

@[simp] theorem specializeHom_apply (f : HaloInt p) :
    specializeHom ψ hψ h0 h1 f = specialize ψ T₀ f := rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The specialization of a constant is its image under `ψ`. -/
theorem specialize_const (x : ℤ_[p]) : specialize ψ T₀ (const x) = ψ x := by
  unfold specialize
  rw [tsum_eq_single 0 fun j hj => by simp [hj]]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The specialization sends `T` to `T₀`. -/
theorem specialize_T : specialize ψ T₀ (T : HaloInt p) = T₀ := by
  unfold specialize
  rw [tsum_eq_single 1 fun j hj => by simp [hj]]
  simp

include hψ h0 h1 in
/-- **Continuity of the specialization** on the halo annulus: `‖f‖ ≤ p^{-k}` forces
`‖f(T₀)‖ ≤ ‖T₀‖^k` (`norm_specialize_le`), so the additive map is continuous at `0`. -/
theorem continuous_specialize : Continuous (specialize ψ T₀ : HaloInt p → K) := by
  refine continuous_of_continuousAt_zero (specializeHom ψ hψ h0 h1) ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε h1
  refine ⟨(p : ℝ) ^ (-(k : ℤ)), zpow_pos (by exact_mod_cast hp.out.pos) _, fun x hx => ?_⟩
  rw [dist_zero_right] at hx
  rw [dist_eq_norm, map_zero, sub_zero, specializeHom_apply]
  exact (norm_specialize_le ψ hψ h0 h1 hx.le).trans_lt hk

include hψ h0 h1 in
/-- The specialization commutes with convergent sums. -/
theorem HasSum.specialize {ι : Type*} {f : ι → HaloInt p} {a : HaloInt p}
    (hf : HasSum f a) : HasSum (fun i => specialize ψ T₀ (f i)) (specialize ψ T₀ a) := by
  exact hf.map (specializeHom ψ hψ h0 h1) (continuous_specialize ψ hψ h0 h1)

end HaloInt

section Character

variable [CharZero K]

/-- The binomial series `(1+T₀)^u = ∑_r C(u, r)·T₀^r` over `K` — the value of
[LWX, Notation 2.1]'s `(1+T)^s` at the halo point. -/
def oneAddPow (T₀ : K) (u : K) : K := ∑' r : ℕ, Ring.choose u r * T₀ ^ r

variable (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K} (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
  (h1 : ‖T₀‖ < 1)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The specialization of `(1+T)^s` is the binomial series `(1+T₀)^{ψ s}`
(`coeff_oneAddTPow`, `ψ` commutes with `Ring.choose`). -/
theorem specialize_oneAddTPow (T₀ : K) (s : ℤ_[p]) :
    HaloInt.specialize ψ T₀ (oneAddTPow p s) = oneAddPow T₀ (ψ s) := by
  unfold HaloInt.specialize oneAddPow
  rw [← Nat.cast_injective.tsum_eq (f := fun j : ℤ => ψ ((oneAddTPow p s) j) * T₀ ^ j) ?_]
  · refine tsum_congr fun r => ?_
    rw [coeff_oneAddTPow, if_pos (Int.natCast_nonneg r), Int.toNat_natCast, zpow_natCast,
      Ring.map_choose]
  · intro j hj
    rw [Function.mem_support] at hj
    rcases le_or_gt 0 j with h | h
    · exact ⟨j.toNat, Int.toNat_of_nonneg h⟩
    · exact absurd (by rw [coeff_oneAddTPow, if_neg (not_le.mpr h), map_zero, zero_mul]) hj

include hψ h0 h1 in
/-- The specialization of the universal character: `[a](T₀) = ψ(ω(ā))·(1+T₀)^{ψ(ℓ⟨a⟩)}`. -/
theorem specialize_univChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (a : ℤ_[p]ˣ) :
    HaloInt.specialize ψ T₀ (univChar ω a)
      = ψ (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
        * oneAddPow T₀ (ψ (logQuot a)) := by
  rw [univChar, HaloInt.specialize_mul ψ hψ h0 h1, HaloInt.specialize_const,
    specialize_oneAddTPow ψ T₀]

end Character

end LWX

end
