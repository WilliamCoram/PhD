/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«16_TargetPoint»

/-!
# The nebentypus character at a classical point 

At the classical point `T_{χ_k}` of the weight `χ_k = (k, ψ)` ([LWX, §3.23]) the halo character
is `κ(a) = a^k ψ(a)` ([LWX, §2.1]: "a continuous character `χ` of `ℤ_p^×` is classical if it
sends `x` to `x^k ψ(x)`"), so the **nebentypus** `ψ` is recovered as `a ↦ κ(a)·a^{−k}` — the
constants `u = haloCharFunH(d)·d^{−k}` of `15_ClassicalPoint.lean`'s classical shape, now read as
a character of `ℤ_p^×`.  This file establishes what the Atkin–Lehner argument needs of it:

* it is multiplicative (`nebChar_mul`) and trivial on `1 + p²ℤ_p` (`nebChar_of_norm_sub_one_le_sq`)
  — the conductor divides `p²`;
* it is **non-trivial on `1 + pℤ_p`**, indeed `nebChar (1 + p)` is a primitive `p`-th root of unity
  (`isPrimitiveRoot_nebChar_oneAddPMul_one`) — the conductor is exactly `p²`, which is [LWX]'s
  "conductor `q²`" and is what kills the non-central terms of `U_p ∘ U'_p`
  (`sum_nebChar_oneAddPMul_mul_eq_zero`);
* the **partner nebentypus** `ω' = ω⁻¹ω₀^{2k}` ([LWX, §3.23 Step III], `lwx.txt:2028–2036`:
  "`ψ⁻¹|_Δ · ω₀^k = χ_k⁻¹|_Δ · ω₀^{2k} = ω⁻¹ω₀^{2k}`") at the classical point of `ζ⁻¹` has
  nebentypus `ψ⁻¹` (`nebChar_partnerChar`) — the other half of the old gap AG-ω₀; under the shift
  `(k, ω) ↦ (k + 1, ωω₀²)` of [LWX, Cor 1.4] it is unchanged (`partnerChar_mul_teichChar_sq_succ`).

No Jacquet–Langlands input; see `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The units `1 + p·x` -/

/-- `1 + p·x` is a unit of `ℤ_p`. -/
theorem isUnit_one_add_p_mul (x : ℤ_[p]) : IsUnit (1 + (p : ℤ_[p]) * x) := by
  rw [PadicInt.isUnit_iff]
  have hlt : ‖(p : ℤ_[p]) * x‖ < 1 := by
    rw [norm_mul, PadicInt.norm_p]
    calc (p : ℝ)⁻¹ * ‖x‖ ≤ (p : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one x) (by positivity)
      _ < 1 := by rw [mul_one]; exact inv_lt_one_p (p := p)
  rw [PadicInt.norm_add_eq_max_of_ne (by rw [norm_one]; exact hlt.ne'), norm_one,
    max_eq_left hlt.le]

variable (p) in
/-- The unit `1 + p·x` of `ℤ_p`. -/
def oneAddPMul (x : ℤ_[p]) : ℤ_[p]ˣ := (isUnit_one_add_p_mul x).unit

@[simp] theorem coe_oneAddPMul (x : ℤ_[p]) : (oneAddPMul p x : ℤ_[p]) = 1 + (p : ℤ_[p]) * x :=
  (isUnit_one_add_p_mul x).unit_spec

/-! ### The nebentypus -/

variable (ψ : ℚ_[p] →+* K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K)

/-- The nebentypus function on `K`: `x ↦ κ_{T_{χ_k}}(x) · x^{−k}`. -/
def nebCharK (x : K) : K := haloCharFunH 1 ψ (classicalPoint p k ζ) ω x * x⁻¹ ^ k

/-- **The nebentypus character** `ψ_neb : ℤ_p^× → K` of the classical point: the constant
`u = haloCharFunH(d)·d^{−k}` of the classical shape, as a function of the unit `d`. -/
def nebChar (a : ℤ_[p]ˣ) : K := nebCharK ψ ω k ζ (intHom ψ (a : ℤ_[p]))

theorem nebChar_apply (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebChar ψ ω k ζ a
      = HaloInt.specialize (intHom ψ) (classicalPoint p k ζ) (univChar ω a)
        * (intHom ψ (a : ℤ_[p]))⁻¹ ^ k := by
  rw [nebChar, nebCharK, haloCharFunH_psi 1 ψ (classicalPoint p k ζ) ω hp2 hψ
    (inv_lt_norm_classicalPoint hp2 hζ hpK k) (norm_classicalPoint_lt_one hp2 hζ hpK k)
    (norm_TH_one_classicalPoint_sq_lt hp2 hζ hpK k) a]

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (uu : ι → Fin p → U)

/-- The classical datum's constants are the nebentypus at the `d`-entries of the disc conjugates
(`certConj_apply_one_one`). -/
theorem classicalData_u_eq_nebChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (i : ι) (t : Fin p)
    (a : ZMod (p ^ 1)) :
    (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k).u i t a
      = nebChar ψ ω k ζ (M1.toLocalMat (discConj 1 (certM1 θG U hU vRep hvΔ uu i t) a)).d := by
  show haloCharFunH 1 ψ (classicalPoint p k ζ) ω (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
      * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k = _
  rw [certConj_apply_one_one]
  rfl

/-- The shape constant of the halo weight at the classical point, at an arbitrary `g ∈ M1Kh`,
is the nebentypus at its `d`-entry: `autFactor g · L = C (nebCharK (g 1 1)) · L^{k+1}`. -/
theorem autFactor_haloWeightH_classicalPoint_eq_nebCharK (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖) (h1 : ‖classicalPoint p k ζ‖ < 1)
    (hT : ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh 1 ψ) :
    (haloWeightH 1 ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1
        * linX g.1
      = PowerSeries.C (nebCharK ψ ω k ζ (g.1 1 1)) * linX g.1 ^ (k + 1) :=
  autFactor_haloWeightH_classicalPoint ψ ω hp2 hψ hζ k h0 h1 hT g

/-! ### Multiplicativity and the conductor -/

theorem nebChar_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a b : ℤ_[p]ˣ) :
    nebChar ψ ω k ζ (a * b) = nebChar ψ ω k ζ a * nebChar ψ ω k ζ b := by
  rw [nebChar_apply ψ ω k ζ hp2 hψ hζ hpK, nebChar_apply ψ ω k ζ hp2 hψ hζ hpK,
    nebChar_apply ψ ω k ζ hp2 hψ hζ hpK, univChar_mul hp2 ω a b,
    HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ) (inv_lt_norm_classicalPoint hp2 hζ hpK k)
      (norm_classicalPoint_lt_one hp2 hζ hpK k), Units.val_mul, map_mul, mul_inv, mul_pow]
  ring

theorem nebChar_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) : nebChar ψ ω k ζ 1 = 1 := by
  rw [nebChar_apply ψ ω k ζ hp2 hψ hζ hpK, univChar_one hp2 ω, HaloInt.specialize_one,
    Units.val_one, map_one, inv_one, one_pow, one_mul]

theorem nebChar_ne_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) : nebChar ψ ω k ζ a ≠ 0 := by
  intro h
  have hmul := nebChar_mul ψ ω k ζ hp2 hψ hζ hpK a a⁻¹
  rw [mul_inv_cancel, nebChar_one ψ ω k ζ hp2 hψ hζ hpK, h, zero_mul] at hmul
  exact one_ne_zero hmul

/-- **The conductor divides `p²`**: the nebentypus is trivial on `1 + p²ℤ_p`
(`specialize_univChar_eq_padicExp` at level `1`, with the halo exponent `k`). -/
theorem nebChar_of_norm_sub_one_le_sq (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {a : ℤ_[p]ˣ}
    (ha : ‖(a : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ 2) : nebChar ψ ω k ζ a = 1 := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hsq : (p : ℝ)⁻¹ ^ 2 < (p : ℝ)⁻¹ := by
    rw [sq]
    exact mul_lt_of_lt_one_left (inv_pos.mpr (by exact_mod_cast hp.out.pos)) (inv_lt_one_p (p := p))
  have hu1 : ‖intHom ψ (a : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 := by
    rw [show intHom ψ (a : ℤ_[p]) - 1 = intHom ψ ((a : ℤ_[p]) - 1) by rw [map_sub, map_one],
      norm_intHom ψ hψ]
    exact ha
  have hu : ‖intHom ψ (a : ℤ_[p]) - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [hpK]
    calc ‖intHom ψ (a : ℤ_[p]) - 1‖ ^ 2 ≤ ‖intHom ψ (a : ℤ_[p]) - 1‖ := by
          rw [sq]
          exact mul_le_of_le_one_left (norm_nonneg _) (hu1.trans (hsq.le.trans hp1))
      _ ≤ (p : ℝ)⁻¹ ^ 2 := hu1
      _ < (p : ℝ)⁻¹ := hsq
  have hL : ‖PadicExpLog.padicLog (intHom ψ (a : ℤ_[p]))‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [PadicExpLog.norm_padicLog_eq h3 hp2 hu]; exact hu
  have hne : intHom ψ (a : ℤ_[p]) ≠ 0 := by
    intro h0
    have hn := norm_intHom ψ hψ (a : ℤ_[p])
    rw [h0, norm_zero, PadicInt.norm_units] at hn
    exact zero_ne_one hn
  rw [nebChar_apply ψ ω k ζ hp2 hψ hζ hpK,
    specialize_univChar_eq_padicExp 1 ψ (classicalPoint p k ζ) ω hp2 hψ
      (inv_lt_norm_classicalPoint hp2 hζ hpK k) (norm_classicalPoint_lt_one hp2 hζ hpK k)
      (norm_TH_one_classicalPoint_sq_lt hp2 hζ hpK k) ha,
    haloExponentH_one_classicalPoint hp2 hζ hpK k, PadicExpLog.padicExp_natCast_mul h3 hp2 hL k,
    PadicExpLog.padicExp_padicLog h3 hp2 hu, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hne)]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ℓ ↦ ζ^{ℓ mod p}` is locally constant on `ℤ_p`, hence continuous. -/
theorem continuous_zeta_pow_toZMod (ζ : K) :
    Continuous fun ℓ : ℤ_[p] => ζ ^ (PadicInt.toZMod ℓ).val := by
  refine continuous_iff_continuousAt.2 fun ℓ₀ => ?_
  refine ContinuousAt.congr (f := fun _ => ζ ^ (PadicInt.toZMod ℓ₀).val) continuousAt_const ?_
  filter_upwards [Metric.ball_mem_nhds ℓ₀ one_pos] with ℓ hℓ
  rw [Metric.mem_ball, dist_eq_norm] at hℓ
  have hres : PadicInt.toZMod ℓ = PadicInt.toZMod ℓ₀ := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact hℓ
  rw [hres]

/-- **`(1 + T)^ℓ` at `T = ζ − 1` is `ζ^{ℓ mod p}`**: both sides are continuous in `ℓ ∈ ℤ_p`
and agree on `ℕ` (`oneAddPow_natCast`, `hζ.pow_eq_one`). -/
theorem oneAddPow_sub_one_intHom (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (ℓ : ℤ_[p]) :
    oneAddPow (ζ - 1) (intHom ψ ℓ) = ζ ^ (PadicInt.toZMod ℓ).val := by
  have hw0 : weightPoint p 0 ζ = ζ - 1 := by
    rw [weightPoint, Int.cast_zero, mul_zero, PadicExpLog.padicExp_zero, mul_one]
  have hT : ‖ζ - 1‖ < 1 := hw0 ▸ norm_weightPoint_lt_one hp2 hζ hpK 0
  refine congrFun (PadicInt.denseRange_natCast.equalizer
    (continuous_oneAddPow_intHom ψ hψ hT) (continuous_zeta_pow_toZMod ζ)
    (funext fun n => ?_)) ℓ
  simp only [Function.comp_apply, map_natCast]
  rw [oneAddPow_natCast, show (1 : K) + (ζ - 1) = ζ by ring, ZMod.val_natCast]
  conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

/-- The one-unit part of `1 + p·x` is itself. -/
theorem oneUnitPart_oneAddPMul (x : ℤ_[p]) : oneUnitPart (oneAddPMul p x) = 1 + (p : ℤ_[p]) * x := by
  have hle : ‖((oneAddPMul p x : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [coe_oneAddPMul, add_sub_cancel_left, norm_mul, PadicInt.norm_p]
    exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (PadicInt.norm_le_one x)
  rw [oneUnitPart, teichmuller_eq_one_of_norm_sub_one_le hle, inv_one, mul_one, coe_oneAddPMul]

/-- **The nebentypus on `1 + pℤ_p`** is `ζ^{ℓ⟨a⟩ mod p}` (`oneAddPow_weightPoint_mul_padicExp` at
`(s, t) = (0, k)`, `intHom_oneUnitPart_eq_padicExp`, `oneAddPow_sub_one_intHom`). -/
theorem nebChar_oneAddPMul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (x : ℤ_[p]) :
    nebChar ψ ω k ζ (oneAddPMul p x)
      = ζ ^ (PadicInt.toZMod (logQuot (oneAddPMul p x))).val := by
  set a := oneAddPMul p x with ha
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hLle : ‖intHom ψ (logQuot a)‖ ≤ 1 := by
    rw [norm_intHom ψ hψ]; exact PadicInt.norm_le_one _
  have hpL : ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    have hle : ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ ≤ (p : ℝ)⁻¹ := by
      rw [norm_mul, hpK]; exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) hLle
    rw [hpK, sq]
    calc ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ * ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖
        ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := mul_le_mul hle hle (norm_nonneg _) (inv_nonneg.2 (Nat.cast_nonneg _))
      _ < (p : ℝ)⁻¹ := mul_lt_of_lt_one_left (inv_pos.2 (by exact_mod_cast hp.out.pos))
          (inv_lt_one_p (p := p))
  have hw0 : weightPoint p 0 ζ = ζ - 1 := by
    rw [weightPoint, Int.cast_zero, mul_zero, PadicExpLog.padicExp_zero, mul_one]
  have hbin := oneAddPow_weightPoint_mul_padicExp ψ hp2 hψ hζ hpK 0 (k : ℤ) (logQuot a)
  rw [weightPoint_natCast k ζ, hw0] at hbin
  have hle : ‖((a : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [ha, coe_oneAddPMul, add_sub_cancel_left, norm_mul, PadicInt.norm_p]
    exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (PadicInt.norm_le_one x)
  have hne : intHom ψ (a : ℤ_[p]) ≠ 0 := by
    intro h0
    have hn := norm_intHom ψ hψ (a : ℤ_[p])
    rw [h0, norm_zero, PadicInt.norm_units] at hn
    exact zero_ne_one hn
  have hexp : PadicExpLog.padicExp (((p : ℕ) : K) * (((k : ℤ) - 0 : ℤ) : K) * intHom ψ (logQuot a))
      = intHom ψ (a : ℤ_[p]) ^ k := by
    rw [show ((p : ℕ) : K) * (((k : ℤ) - 0 : ℤ) : K) * intHom ψ (logQuot a)
        = (k : K) * (((p : ℕ) : K) * intHom ψ (logQuot a)) by push_cast; ring,
      PadicExpLog.padicExp_natCast_mul h3 hp2 hpL k, ← intHom_oneUnitPart_eq_padicExp ψ hp2 hψ a,
      ha, oneUnitPart_oneAddPMul, coe_oneAddPMul]
  rw [nebChar_apply ψ ω k ζ hp2 hψ hζ hpK,
    specialize_univChar (intHom ψ) (norm_intHom ψ hψ) (inv_lt_norm_classicalPoint hp2 hζ hpK k)
      (norm_classicalPoint_lt_one hp2 hζ hpK k) ω a,
    unitsMap_toZMod_eq_one_of_norm_sub_one_le hle, map_one, Units.val_one, map_one, one_mul,
    ← hbin, hexp, oneAddPow_sub_one_intHom ψ ζ hp2 hψ hζ hpK, inv_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hne), mul_one]

/-- `ℓ⟨1 + p⟩ = log(1+p)/p` is a unit (`norm_padicLog_eq`). -/
theorem norm_logQuot_oneAddPMul_one (hp2 : p ≠ 2) :
    ‖(logQuot (oneAddPMul p 1) : ℤ_[p])‖ = 1 := by
  have hnp : ‖((p : ℕ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have h3 : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by rw [hnp]; exact inv_lt_one_p (p := p)
  have hsub : (((oneAddPMul p 1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1 = (p : ℚ_[p]) := by
    rw [coe_oneAddPMul]; push_cast; ring
  have hle : ‖((oneAddPMul p 1 : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, hsub, hnp]
  have hu2 : ‖(((oneAddPMul p 1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1‖ ^ 2 < ‖((p : ℕ) : ℚ_[p])‖ := by
    rw [hsub, hnp, sq]
    exact mul_lt_of_lt_one_left (inv_pos.2 (by exact_mod_cast hp.out.pos)) (inv_lt_one_p (p := p))
  rw [PadicInt.norm_def, coe_logQuot_of_norm_sub_one_le hle, norm_div,
    PadicExpLog.norm_padicLog_eq h3 hp2 hu2, hsub, hnp,
    div_self (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))]

/-- **The conductor is exactly `p²`**: `nebChar (1 + p)` is a primitive `p`-th root of unity. -/
theorem isPrimitiveRoot_nebChar_oneAddPMul_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) :
    IsPrimitiveRoot (nebChar ψ ω k ζ (oneAddPMul p 1)) p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [nebChar_oneAddPMul ψ ω k ζ hp2 hψ hζ hpK]
  refine hζ.pow_of_coprime _ ?_
  have hne : PadicInt.toZMod (logQuot (oneAddPMul p 1)) ≠ 0 := by
    intro h0
    have hmem : logQuot (oneAddPMul p 1) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact h0
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, norm_logQuot_oneAddPMul_one hp2] at hmem
    exact lt_irrefl _ hmem
  have hlt : (PadicInt.toZMod (logQuot (oneAddPMul p 1))).val < p := ZMod.val_lt _
  have hpos : 0 < (PadicInt.toZMod (logQuot (oneAddPMul p 1))).val :=
    Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2
    (Nat.not_dvd_of_pos_of_lt hpos hlt))

/-- `nebChar (1 + p n) = nebChar (1 + p)^n`: `(1+p)^n ≡ 1 + pn (mod p²)` and the conductor. -/
theorem nebChar_oneAddPMul_natCast (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (n : ℕ) :
    nebChar ψ ω k ζ (oneAddPMul p n) = nebChar ψ ω k ζ (oneAddPMul p 1) ^ n := by
  induction n with
  | zero =>
    have h1 : oneAddPMul p ((0 : ℕ) : ℤ_[p]) = 1 := Units.ext (by simp)
    rw [h1, nebChar_one ψ ω k ζ hp2 hψ hζ hpK, pow_zero]
  | succ n ih =>
    set u := oneAddPMul p (n : ℤ_[p]) * oneAddPMul p 1 with hu
    set w : ℤ_[p]ˣ := u⁻¹ * oneAddPMul p ((n + 1 : ℕ) : ℤ_[p]) with hw
    have hsplit : oneAddPMul p ((n + 1 : ℕ) : ℤ_[p]) = u * w := by rw [hw, mul_inv_cancel_left]
    have hw1 : ‖(w : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 := by
      have hu' : (u : ℤ_[p]) = (1 + (p : ℤ_[p]) * n) * (1 + (p : ℤ_[p]) * 1) := by
        rw [hu, Units.val_mul, coe_oneAddPMul, coe_oneAddPMul]
      have hdiff : (w : ℤ_[p]) - 1
          = ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (((oneAddPMul p ((n + 1 : ℕ) : ℤ_[p])) : ℤ_[p]) - u) := by
        rw [hw, Units.val_mul, mul_sub, Units.inv_mul]
      rw [hdiff, coe_oneAddPMul, hu',
        show (1 + (p : ℤ_[p]) * ((n + 1 : ℕ) : ℤ_[p])) - (1 + (p : ℤ_[p]) * n) * (1 + (p : ℤ_[p]) * 1)
          = -((p : ℤ_[p]) ^ 2 * n) by push_cast; ring,
        norm_mul, PadicInt.norm_units, one_mul, norm_neg, norm_mul, norm_pow, PadicInt.norm_p]
      exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
    rw [hsplit, nebChar_mul ψ ω k ζ hp2 hψ hζ hpK, hu, nebChar_mul ψ ω k ζ hp2 hψ hζ hpK, ih,
      nebChar_of_norm_sub_one_le_sq ψ ω k ζ hp2 hψ hζ hpK hw1, mul_one, pow_succ]

/-- **The character sum**: for `p ∤ b`, `∑_{c < p} ψ_neb(1 + p b c) = 0`
(`IsPrimitiveRoot.geom_sum_eq_zero` at the primitive root `nebChar (1+p)^b`). -/
theorem sum_nebChar_oneAddPMul_mul_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ} (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, nebChar ψ ω k ζ (oneAddPMul p ((b : ℤ_[p]) * c)) = 0 := by
  have hξ := (isPrimitiveRoot_nebChar_oneAddPMul_one ψ ω k ζ hp2 hψ hζ hpK).pow_of_coprime b
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hb))
  rw [← hξ.geom_sum_eq_zero hp.out.one_lt]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show (b : ℤ_[p]) * c = ((b * c : ℕ) : ℤ_[p]) by push_cast; ring,
    nebChar_oneAddPMul_natCast ψ ω k ζ hp2 hψ hζ hpK, pow_mul]

/-- **The character sum, inverted** (the form the identity computation consumes: the `d`-entry of
`ℓQ b c` is `1 + bcp`, and its nebentypus enters inverted through the level-equivariance at
`ℓ⁻¹`): for `p ∤ b`, `∑_{c < p} ψ_neb(1 + p b c)⁻¹ = 0`. -/
theorem sum_inv_nebChar_oneAddPMul_mul_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ} (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, (nebChar ψ ω k ζ (oneAddPMul p ((b : ℤ_[p]) * c)))⁻¹ = 0 := by
  have hξ := (isPrimitiveRoot_nebChar_oneAddPMul_one ψ ω k ζ hp2 hψ hζ hpK).inv.pow_of_coprime b
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hb))
  rw [← hξ.geom_sum_eq_zero hp.out.one_lt]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show (b : ℤ_[p]) * c = ((b * c : ℕ) : ℤ_[p]) by push_cast; ring,
    nebChar_oneAddPMul_natCast ψ ω k ζ hp2 hψ hζ hpK, pow_mul, inv_pow, inv_pow]

/-- The same in terms of `nebCharK` at `ψ(1 + b c p)`, the spelling that appears in the
identity computation. -/
theorem sum_inv_nebCharK_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ} (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, (nebCharK ψ ω k ζ (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ = 0 := by
  rw [← sum_inv_nebChar_oneAddPMul_mul_eq_zero ψ ω k ζ hp2 hψ hζ hpK hb]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [nebChar, intHom_apply, coe_oneAddPMul,
    show (((1 + (p : ℤ_[p]) * ((b : ℤ_[p]) * c) : ℤ_[p]) : ℚ_[p])) = 1 + (b : ℚ_[p]) * c * p by
      push_cast; ring]

/-! ### The three abstract hypotheses of `18_AtkinLehnerMap.lean`, discharged -/

/-- `hmul`: `nebCharK` is multiplicative on `ψ`-images of `p`-adic units (`nebChar_mul` at the
units `⟨x, _⟩`, `⟨y, _⟩` of `ℤ_p`). -/
theorem nebCharK_psi_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x y : ℚ_[p]} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    nebCharK ψ ω k ζ (ψ (x * y)) = nebCharK ψ ω k ζ (ψ x) * nebCharK ψ ω k ζ (ψ y) := by
  obtain ⟨ux, hux⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = x := by
    let z : ℤ_[p] := ⟨x, hx.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hx)
    exact ⟨hz.unit, rfl⟩
  obtain ⟨uy, huy⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = y := by
    let z : ℤ_[p] := ⟨y, hy.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hy)
    exact ⟨hz.unit, rfl⟩
  have h := nebChar_mul ψ ω k ζ hp2 hψ hζ hpK ux uy
  simp only [nebChar, intHom_apply, Units.val_mul, PadicInt.coe_mul, hux, huy] at h
  exact h

/-- `hne`: `nebCharK` does not vanish on `ψ`-images of `p`-adic units. -/
theorem nebCharK_psi_ne_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : ℚ_[p]} (hx : ‖x‖ = 1) :
    nebCharK ψ ω k ζ (ψ x) ≠ 0 := by
  obtain ⟨ux, hux⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = x := by
    let z : ℤ_[p] := ⟨x, hx.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hx)
    exact ⟨hz.unit, rfl⟩
  have h := nebChar_ne_zero ψ ω k ζ hp2 hψ hζ hpK ux
  simp only [nebChar, intHom_apply, hux] at h
  exact h

/-- `hcond`: `nebCharK` is trivial on `ψ(1 + p²ℤ_p)`. -/
theorem nebCharK_psi_of_norm_sub_one_le_sq (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2) : nebCharK ψ ω k ζ (ψ x) = 1 := by
  have hsq : (p : ℝ)⁻¹ ^ 2 ≤ (p : ℝ)⁻¹ := by
    rw [sq]
    exact mul_le_of_le_one_left (inv_nonneg.2 (Nat.cast_nonneg _))
      (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
  have hx1 : ‖x‖ = 1 := norm_eq_one_of_norm_sub_le (p := p) norm_one (hx.trans hsq)
  obtain ⟨ux, hux⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = x := by
    let z : ℤ_[p] := ⟨x, hx1.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hx1)
    exact ⟨hz.unit, rfl⟩
  have h := nebChar_of_norm_sub_one_le_sq ψ ω k ζ hp2 hψ hζ hpK (a := ux)
    (by rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, hux]; exact hx)
  simp only [nebChar, intHom_apply, hux] at h
  exact h

/-! ### The partner nebentypus `ω⁻¹ω₀^{2k}` -/

variable (p) in
/-- **The partner nebentypus** `ω' = ω⁻¹·ω₀^{2k}` ([LWX, §3.23 Step III]: "`ψ⁻¹|_Δ · ω₀^k =
χ_k⁻¹|_Δ · ω₀^{2k} = ω⁻¹ω₀^{2k}`"). -/
def partnerChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) : (ZMod p)ˣ →* ℤ_[p]ˣ :=
  invChar ω * teichChar p ^ (2 * k)

theorem partnerChar_apply (r : (ZMod p)ˣ) :
    partnerChar p ω k r = (ω r)⁻¹ * teichRes r ^ (2 * k) := by
  rw [partnerChar, MonoidHom.mul_apply, MonoidHom.pow_apply, teichChar_apply]
  rfl

/-- The partner nebentypus of `(ωω₀², k+1)` is that of `(ω, k)`:
`(ωω₀²)⁻¹ω₀^{2(k+1)} = ω⁻¹ω₀^{2k}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
theorem partnerChar_mul_teichChar_sq_succ :
    partnerChar p (ω * teichChar p ^ 2) (k + 1) = partnerChar p ω k := by
  refine MonoidHom.ext fun r => ?_
  rw [partnerChar_apply, partnerChar_apply, MonoidHom.mul_apply, MonoidHom.pow_apply,
    teichChar_apply, mul_inv, show 2 * (k + 1) = 2 + 2 * k by ring, pow_add (teichRes r) 2 (2 * k),
    mul_assoc, inv_mul_cancel_left]

/-- `(1+T)^ℓ` at `T = ζ⁻¹ − 1` and at `T = ζ − 1` are inverse to each other. -/
theorem oneAddPow_inv_sub_one_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (ℓ : ℤ_[p]) :
    oneAddPow (ζ⁻¹ - 1) (intHom ψ ℓ) * oneAddPow (ζ - 1) (intHom ψ ℓ) = 1 := by
  rw [oneAddPow_sub_one_intHom ψ ζ⁻¹ hp2 hψ hζ.inv hpK, oneAddPow_sub_one_intHom ψ ζ hp2 hψ hζ hpK,
    inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (hζ.ne_zero hp.out.ne_zero))]

/-- **`nebChar` in closed form**: `ψ_neb(a) = ω(ā) · ζ^{ℓ⟨a⟩ mod p} · ω₀(ā)^{−k}` — the `oneUnitPart`
factors `(oneUnitPart a)^k · a^{−k}` collapse to `teichmüller(a)^{−k}`
(`nebChar_apply`, `specialize_univChar`, `oneAddPow_weightPoint_mul_padicExp` at `(0, k)`,
`intHom_oneUnitPart_eq_padicExp`, `oneAddPow_sub_one_intHom`, `coe_eq_teichRes_mul_oneUnitPart`). -/
theorem nebChar_eq (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebChar ψ ω k ζ a
      = intHom ψ (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
        * ζ ^ (PadicInt.toZMod (logQuot a)).val
        * (intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]))⁻¹ ^ k := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hLle : ‖intHom ψ (logQuot a)‖ ≤ 1 := by
    rw [norm_intHom ψ hψ]; exact PadicInt.norm_le_one _
  have hpL : ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    have hle : ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ ≤ (p : ℝ)⁻¹ := by
      rw [norm_mul, hpK]; exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) hLle
    rw [hpK, sq]
    calc ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ * ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖
        ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := mul_le_mul hle hle (norm_nonneg _) (inv_nonneg.2 (Nat.cast_nonneg _))
      _ < (p : ℝ)⁻¹ := mul_lt_of_lt_one_left (inv_pos.2 (by exact_mod_cast hp.out.pos))
          (inv_lt_one_p (p := p))
  have hw0 : weightPoint p 0 ζ = ζ - 1 := by
    rw [weightPoint, Int.cast_zero, mul_zero, PadicExpLog.padicExp_zero, mul_one]
  have hbin := oneAddPow_weightPoint_mul_padicExp ψ hp2 hψ hζ hpK 0 (k : ℤ) (logQuot a)
  rw [weightPoint_natCast k ζ, hw0] at hbin
  have hexp : PadicExpLog.padicExp (((p : ℕ) : K) * (((k : ℤ) - 0 : ℤ) : K) * intHom ψ (logQuot a))
      = intHom ψ (oneUnitPart a) ^ k := by
    rw [show ((p : ℕ) : K) * (((k : ℤ) - 0 : ℤ) : K) * intHom ψ (logQuot a)
        = (k : K) * (((p : ℕ) : K) * intHom ψ (logQuot a)) by push_cast; ring,
      PadicExpLog.padicExp_natCast_mul h3 hp2 hpL k, ← intHom_oneUnitPart_eq_padicExp ψ hp2 hψ a]
  have ha : intHom ψ (a : ℤ_[p])
      = intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
        * intHom ψ (oneUnitPart a) := by
    rw [← map_mul, ← coe_eq_teichRes_mul_oneUnitPart a]
  have ht0 : intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]) ≠ 0 :=
    ((teichRes _).isUnit.map (intHom ψ)).ne_zero
  have ho0 : intHom ψ (oneUnitPart a) ≠ 0 := by
    intro h0
    have hn : ‖intHom ψ (oneUnitPart a)‖ = 1 := by
      rw [norm_intHom ψ hψ, oneUnitPart, PadicInt.norm_units]
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rw [nebChar_apply ψ ω k ζ hp2 hψ hζ hpK,
    specialize_univChar (intHom ψ) (norm_intHom ψ hψ) (inv_lt_norm_classicalPoint hp2 hζ hpK k)
      (norm_classicalPoint_lt_one hp2 hζ hpK k) ω a, ← hbin, hexp,
    oneAddPow_sub_one_intHom ψ ζ hp2 hψ hζ hpK, ha]
  simp only [mul_pow, inv_pow, mul_inv]
  field_simp

/-- **The partner point carries the inverse nebentypus** (the other half of AG-ω₀):
at `T_{χ_k}(ζ⁻¹)` with tame character `ω⁻¹ω₀^{2k}`, the nebentypus is `ψ_neb⁻¹`. -/
theorem nebChar_partnerChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebChar ψ (partnerChar p ω k) k ζ⁻¹ a = (nebChar ψ ω k ζ a)⁻¹ := by
  have hω : intHom ψ (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]) ≠ 0 :=
    ((ω _).isUnit.map (intHom ψ)).ne_zero
  have ht : intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]) ≠ 0 :=
    ((teichRes _).isUnit.map (intHom ψ)).ne_zero
  have hz : ζ ≠ 0 := hζ.ne_zero hp.out.ne_zero
  rw [nebChar_eq ψ (partnerChar p ω k) k ζ⁻¹ hp2 hψ hζ.inv hpK, nebChar_eq ψ ω k ζ hp2 hψ hζ hpK,
    partnerChar_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, map_units_inv]
  simp only [inv_pow, mul_inv, inv_inv]
  field_simp
  ring

/-- The partner nebentypus function on `K`, at the image of a unit: `nebCharK` at
`(ω⁻¹ω₀^{2k}, ζ⁻¹)` is the inverse of `nebCharK` at `(ω, ζ)` (the spelling `hκ'` consumes:
every `g ∈ M1Kh 1 ψ` has `g 1 1 = intHom ψ d` for a unit `d`). -/
theorem nebCharK_partnerChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharK ψ (partnerChar p ω k) k ζ⁻¹ (intHom ψ (a : ℤ_[p]))
      = (nebCharK ψ ω k ζ (intHom ψ (a : ℤ_[p])))⁻¹ :=
  nebChar_partnerChar ψ ω k ζ hp2 hψ hζ hpK a

/-- The shape constant of the partner halo weight at `g ∈ M1Kh` is `nebCharK(g 1 1)⁻¹`
(`autFactor_haloWeightH_classicalPoint_eq_nebCharK` at the partner point, `nebCharK_partnerChar`,
and `g 1 1 = intHom ψ d` with `d` a unit: `mem_M1Kh` gives `g 1 1 = ψ (δ 1 1)` for `δ ∈ Mh`). -/
theorem autFactor_haloWeightH_partner_eq_inv_nebCharK (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ⁻¹‖) (h1 : ‖classicalPoint p k ζ⁻¹‖ < 1)
    (hT : ‖TH p 1 (classicalPoint p k ζ⁻¹)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh 1 ψ) :
    (haloWeightH 1 ψ (classicalPoint p k ζ⁻¹) (partnerChar p ω k) hp2 hψ h0 h1 hT).toWeightSeries.autFactor
          g.1 * linX g.1
      = PowerSeries.C (nebCharK ψ ω k ζ (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1) := by
  rw [autFactor_haloWeightH_classicalPoint_eq_nebCharK ψ (partnerChar p ω k) k ζ⁻¹ hp2 hψ hζ.inv
    h0 h1 hT g]
  obtain ⟨δ, hδ, hδg⟩ := (mem_M1Kh_iff 1 ψ).1 g.2
  have hd : ‖δ 1 1‖ = 1 := (mem_Mh_iff.1 hδ).2.2.1
  obtain ⟨d, hd'⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = δ 1 1 := by
    let z : ℤ_[p] := ⟨δ 1 1, hd.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hd)
    exact ⟨hz.unit, rfl⟩
  have hg11 : g.1 1 1 = intHom ψ (d : ℤ_[p]) := by
    rw [← hδg, RingHom.mapMatrix_apply, Matrix.map_apply, intHom_apply, hd']
  rw [hg11, nebCharK_partnerChar ψ ω k ζ hp2 hψ hζ (norm_natCast_p ψ hψ) d]

/-- The constants of the partner classical datum are the inverses of the datum's. -/
theorem classicalData_partnerChar_u (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (i : ι) (t : Fin p)
    (a : ZMod (p ^ 1)) :
    (classicalData ψ (partnerChar p ω k) θG U hU vRep hvΔ uu hp2 hψ hζ.inv hpK k).u i t a
      = ((classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k).u i t a)⁻¹ := by
  rw [classicalData_u_eq_nebChar ψ (partnerChar p ω k) k ζ⁻¹ θG U hU vRep hvΔ uu hp2 hψ hζ.inv hpK,
    classicalData_u_eq_nebChar ψ ω k ζ θG U hU vRep hvΔ uu hp2 hψ hζ hpK,
    nebChar_partnerChar ψ ω k ζ hp2 hψ hζ hpK]

end LWX

end
