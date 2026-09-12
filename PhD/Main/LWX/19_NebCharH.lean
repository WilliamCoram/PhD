/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«18_TargetPointH»
import PhD.Main.LWX.«17_NebChar»

/-!
# The nebentypus character at a classical point of conductor `p^{h+1}`

`17_NebChar.lean` at level `h`.  At the classical point `T_{χ_k}` of the weight `χ_k = (k, ψ)`,
`ψ` of conductor `p^{h+1}` ([LWX, §2.1]: "a finite character of conductor `p^m` if it factors
through `(ℤ/p^m)^×` but not `(ℤ/p^{m−1})^×`"), the level-`h` halo character is
`κ(a) = a^k ψ(a)`, so the nebentypus is `a ↦ κ(a)·a^{−k}`, the constants of the level-`h`
classical shape.  What the Atkin–Lehner argument at level `h` needs of it:

* multiplicative, and trivial on `1 + p^{h+1}ℤ_p` (`nebCharH_of_norm_sub_one_le_pow`) — the
  conductor divides `p^{h+1}`;
* **non-trivial on `1 + p^hℤ_p`**: `nebCharH (1 + p^h)` is a primitive `p`-th root of unity
  (`isPrimitiveRoot_nebCharH_oneAddPPowMul_one`) — the conductor is exactly `p^{h+1}`, which
  kills the non-central terms of `U_p ∘ U'_p` through the character sum
  `∑_{c<p} ψ_neb(1 + bcp^h)⁻¹ = 0` for `p ∤ b` (`sum_inv_nebCharKH_eq_zero`);
* the partner nebentypus `ω' = ω⁻¹ω₀^{2k}` at the classical point of `ζ⁻¹` has nebentypus
  `ψ⁻¹` (`nebCharH_partnerChar`).

The wild part of the character is `ζ^{ℓ⟨a⟩ mod p^h}` (`oneAddPow_sub_one_intHom_prime_pow`,
through `PadicInt.toZModPow h`), in place of `ζ^{ℓ⟨a⟩ mod p}` at level `1`.
No Jacquet–Langlands input.
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The units `1 + p^h x` -/

variable (p) in
/-- The unit `1 + p^h·x` of `ℤ_p`, as `oneAddPMul p (p^{h−1} x)`. -/
def oneAddPPowMul (h : ℕ) (x : ℤ_[p]) : ℤ_[p]ˣ := oneAddPMul p ((p : ℤ_[p]) ^ (h - 1) * x)

theorem coe_oneAddPPowMul (h : ℕ) (hh : 0 < h) (x : ℤ_[p]) :
    (oneAddPPowMul p h x : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ h * x := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [oneAddPPowMul, coe_oneAddPMul, Nat.add_sub_cancel, pow_succ]
  ring

@[simp] theorem oneAddPPowMul_one (x : ℤ_[p]) : oneAddPPowMul p 1 x = oneAddPMul p x := by
  rw [oneAddPPowMul, Nat.sub_self, pow_zero, one_mul]

/-! ### The nebentypus -/

variable (h : ℕ) (ψ : ℚ_[p] →+* K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K)

/-- The nebentypus function on `K` at level `h`: `x ↦ κ_{T_{χ_k},h}(x) · x^{−k}`. -/
def nebCharKH (x : K) : K := haloCharFunH h ψ (classicalPoint p k ζ) ω x * x⁻¹ ^ k

/-- **The nebentypus character** `ψ_neb : ℤ_p^× → K` of the classical point of conductor
`p^{h+1}`. -/
def nebCharH (a : ℤ_[p]ˣ) : K := nebCharKH h ψ ω k ζ (intHom ψ (a : ℤ_[p]))

theorem nebCharH_apply (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharH h ψ ω k ζ a
      = HaloInt.specialize (intHom ψ) (classicalPoint p k ζ) (univChar ω a)
        * (intHom ψ (a : ℤ_[p]))⁻¹ ^ k := by
  rw [nebCharH, nebCharKH, haloCharFunH_psi h ψ (classicalPoint p k ζ) ω hp2 hψ
    (inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k)
    (norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k)
    (norm_TH_classicalPoint_sq_lt hp2 hζ.pow_eq_one hpK k) a]

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (uu : ι → Fin p → U)

omit [Fintype ι] [DecidableEq ι] in
/-- The level-`h` classical datum's constants are the nebentypus at the `d`-entries of the disc
conjugates (`certConj_apply_one_one`). -/
theorem classicalDataH_u_eq_nebCharH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (i : ι) (t : Fin p)
    (a : ZMod (p ^ h)) :
    (classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k).u i t a
      = nebCharH h ψ ω k ζ (M1.toLocalMat (discConj h (certM1 θG U hU vRep hvΔ uu i t) a)).d := by
  show haloCharFunH h ψ (classicalPoint p k ζ) ω (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
      * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k = _
  rw [certConj_apply_one_one]
  rfl

/-- The shape constant of the level-`h` halo weight at the classical point, at an arbitrary
`g ∈ M1Kh h ψ`, is the nebentypus at its `d`-entry. -/
theorem autFactor_haloWeightH_classicalPoint_eq_nebCharKH (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : ζ ^ p ^ h = 1)
    (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖) (h1 : ‖classicalPoint p k ζ‖ < 1)
    (hT : ‖TH p h (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh h ψ) :
    (haloWeightH h ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1
        * linX g.1
      = PowerSeries.C (nebCharKH h ψ ω k ζ (g.1 1 1)) * linX g.1 ^ (k + 1) :=
  autFactor_haloWeightH_classicalPoint_prime_pow ψ ω hp2 hψ h hζ k h0 h1 hT g

/-! ### Multiplicativity and the conductor -/

theorem nebCharH_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a b : ℤ_[p]ˣ) :
    nebCharH h ψ ω k ζ (a * b) = nebCharH h ψ ω k ζ a * nebCharH h ψ ω k ζ b := by
  rw [nebCharH_apply h ψ ω k ζ hp2 hψ hh hζ hpK, nebCharH_apply h ψ ω k ζ hp2 hψ hh hζ hpK,
    nebCharH_apply h ψ ω k ζ hp2 hψ hh hζ hpK, univChar_mul hp2 ω a b,
    HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ)
      (inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k)
      (norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k), Units.val_mul, map_mul, mul_inv,
    mul_pow]
  ring

theorem nebCharH_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) :
    nebCharH h ψ ω k ζ 1 = 1 := by
  rw [nebCharH_apply h ψ ω k ζ hp2 hψ hh hζ hpK, univChar_one hp2 ω, HaloInt.specialize_one,
    Units.val_one, map_one, inv_one, one_pow, one_mul]

theorem nebCharH_ne_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharH h ψ ω k ζ a ≠ 0 := by
  intro h0
  have hmul := nebCharH_mul h ψ ω k ζ hp2 hψ hh hζ hpK a a⁻¹
  rw [mul_inv_cancel, nebCharH_one h ψ ω k ζ hp2 hψ hh hζ hpK, h0, zero_mul] at hmul
  exact one_ne_zero hmul

/-- **The conductor divides `p^{h+1}`**: the nebentypus is trivial on `1 + p^{h+1}ℤ_p`
(`specialize_univChar_eq_padicExp` at level `h`, with the halo exponent `k`). -/
theorem nebCharH_of_norm_sub_one_le_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {a : ℤ_[p]ˣ}
    (ha : ‖(a : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) : nebCharH h ψ ω k ζ a = 1 := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hsq : (p : ℝ)⁻¹ ^ (h + 1) < (p : ℝ)⁻¹ := by
    calc (p : ℝ)⁻¹ ^ (h + 1) ≤ (p : ℝ)⁻¹ ^ 2 :=
          pow_le_pow_of_le_one (by positivity) hp1 (by omega)
      _ < (p : ℝ)⁻¹ := by
          rw [sq]
          exact mul_lt_of_lt_one_left (inv_pos.mpr (by exact_mod_cast hp.out.pos))
            (inv_lt_one_p (p := p))
  have hu1 : ‖intHom ψ (a : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [show intHom ψ (a : ℤ_[p]) - 1 = intHom ψ ((a : ℤ_[p]) - 1) by rw [map_sub, map_one],
      norm_intHom ψ hψ]
    exact ha
  have hu : ‖intHom ψ (a : ℤ_[p]) - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [hpK]
    calc ‖intHom ψ (a : ℤ_[p]) - 1‖ ^ 2 ≤ ‖intHom ψ (a : ℤ_[p]) - 1‖ := by
          rw [sq]
          exact mul_le_of_le_one_left (norm_nonneg _) (hu1.trans (hsq.le.trans hp1))
      _ ≤ (p : ℝ)⁻¹ ^ (h + 1) := hu1
      _ < (p : ℝ)⁻¹ := hsq
  have hL : ‖PadicExpLog.padicLog (intHom ψ (a : ℤ_[p]))‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [PadicExpLog.norm_padicLog_eq h3 hp2 hu]; exact hu
  have hne : intHom ψ (a : ℤ_[p]) ≠ 0 := by
    intro h0
    have hn := norm_intHom ψ hψ (a : ℤ_[p])
    rw [h0, norm_zero, PadicInt.norm_units] at hn
    exact zero_ne_one hn
  rw [nebCharH_apply h ψ ω k ζ hp2 hψ hh hζ hpK,
    specialize_univChar_eq_padicExp h ψ (classicalPoint p k ζ) ω hp2 hψ
      (inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k)
      (norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k)
      (norm_TH_classicalPoint_sq_lt hp2 hζ.pow_eq_one hpK k) ha,
    haloExponentH_classicalPoint hp2 hζ.pow_eq_one hpK k,
    PadicExpLog.padicExp_natCast_mul h3 hp2 hL k, PadicExpLog.padicExp_padicLog h3 hp2 hu, inv_pow,
    mul_inv_cancel₀ (pow_ne_zero _ hne)]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ℓ ↦ ζ^{ℓ mod p^h}` is locally constant on `ℤ_p`, hence continuous. -/
theorem continuous_zeta_pow_toZModPow (h : ℕ) (ζ : K) :
    Continuous fun ℓ : ℤ_[p] => ζ ^ (PadicInt.toZModPow h ℓ).val := by
  have hr : (0 : ℝ) < (p : ℝ)⁻¹ ^ h := pow_pos (inv_pos.2 (Nat.cast_pos.2 hp.out.pos)) h
  refine continuous_iff_continuousAt.2 fun ℓ₀ => ?_
  refine ContinuousAt.congr (f := fun _ => ζ ^ (PadicInt.toZModPow h ℓ₀).val) continuousAt_const ?_
  filter_upwards [Metric.ball_mem_nhds ℓ₀ hr] with ℓ hℓ
  rw [Metric.mem_ball, dist_eq_norm] at hℓ
  have hres : PadicInt.toZModPow h ℓ = PadicInt.toZModPow h ℓ₀ := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
      ← PadicInt.norm_le_pow_iff_mem_span_pow, zpow_neg, zpow_natCast, ← inv_pow]
    exact hℓ.le
  rw [hres]

/-- **`(1 + T)^ℓ` at `T = ζ − 1` is `ζ^{ℓ mod p^h}`** for a primitive `p^h`-th root of unity:
both sides are continuous in `ℓ ∈ ℤ_p` and agree on `ℕ`. -/
theorem oneAddPow_sub_one_intHom_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (ℓ : ℤ_[p]) :
    oneAddPow (ζ - 1) (intHom ψ ℓ) = ζ ^ (PadicInt.toZModPow h ℓ).val := by
  have hw0 : weightPoint p 0 ζ = ζ - 1 := by
    rw [weightPoint, Int.cast_zero, mul_zero, PadicExpLog.padicExp_zero, mul_one]
  have hT : ‖ζ - 1‖ < 1 := hw0 ▸ norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK 0
  refine congrFun (PadicInt.denseRange_natCast.equalizer
    (continuous_oneAddPow_intHom ψ hψ hT) (continuous_zeta_pow_toZModPow h ζ)
    (funext fun n => ?_)) ℓ
  simp only [Function.comp_apply, map_natCast]
  rw [oneAddPow_natCast, show (1 : K) + (ζ - 1) = ζ by ring, ZMod.val_natCast]
  conv_lhs => rw [← Nat.div_add_mod n (p ^ h), pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

/-- **The nebentypus on `1 + p^hℤ_p`** is `ζ^{ℓ⟨a⟩ mod p^h}`. -/
theorem nebCharH_oneAddPPowMul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (x : ℤ_[p]) :
    nebCharH h ψ ω k ζ (oneAddPPowMul p h x)
      = ζ ^ (PadicInt.toZModPow h (logQuot (oneAddPPowMul p h x))).val := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hLle : ‖intHom ψ (logQuot (oneAddPPowMul p h x))‖ ≤ 1 := by
    rw [norm_intHom ψ hψ]; exact PadicInt.norm_le_one _
  have hpL : ‖((p : ℕ) : K) * intHom ψ (logQuot (oneAddPPowMul p h x))‖ ^ 2
      < ‖((p : ℕ) : K)‖ := by
    have hle : ‖((p : ℕ) : K) * intHom ψ (logQuot (oneAddPPowMul p h x))‖ ≤ (p : ℝ)⁻¹ := by
      rw [norm_mul, hpK]; exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) hLle
    rw [hpK, sq]
    calc ‖((p : ℕ) : K) * intHom ψ (logQuot (oneAddPPowMul p h x))‖
          * ‖((p : ℕ) : K) * intHom ψ (logQuot (oneAddPPowMul p h x))‖
        ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ :=
          mul_le_mul hle hle (norm_nonneg _) (inv_nonneg.2 (Nat.cast_nonneg _))
      _ < (p : ℝ)⁻¹ := mul_lt_of_lt_one_left (inv_pos.2 (by exact_mod_cast hp.out.pos))
          (inv_lt_one_p (p := p))
  have hw0 : weightPoint p 0 ζ = ζ - 1 := by
    rw [weightPoint, Int.cast_zero, mul_zero, PadicExpLog.padicExp_zero, mul_one]
  have hbin := oneAddPow_weightPoint_mul_padicExp_prime_pow ψ hp2 hψ hh hζ hpK 0 (k : ℤ)
    (logQuot (oneAddPPowMul p h x))
  rw [weightPoint_natCast k ζ, hw0] at hbin
  have hle : ‖((oneAddPPowMul p h x : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [coe_oneAddPPowMul h hh, add_sub_cancel_left, norm_mul, norm_pow, PadicInt.norm_p]
    calc (p : ℝ)⁻¹ ^ h * ‖x‖ ≤ (p : ℝ)⁻¹ ^ h * 1 := by gcongr; exact PadicInt.norm_le_one x
      _ ≤ (p : ℝ)⁻¹ := by
          rw [mul_one]
          exact pow_le_of_le_one (by positivity)
            (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)) hh.ne'
  have hne : intHom ψ ((oneAddPPowMul p h x : ℤ_[p]ˣ) : ℤ_[p]) ≠ 0 := by
    intro h0
    have hn := norm_intHom ψ hψ ((oneAddPPowMul p h x : ℤ_[p]ˣ) : ℤ_[p])
    rw [h0, norm_zero, PadicInt.norm_units] at hn
    exact zero_ne_one hn
  have hexp : PadicExpLog.padicExp (((p : ℕ) : K) * (((k : ℤ) - 0 : ℤ) : K)
        * intHom ψ (logQuot (oneAddPPowMul p h x)))
      = intHom ψ ((oneAddPPowMul p h x : ℤ_[p]ˣ) : ℤ_[p]) ^ k := by
    rw [show ((p : ℕ) : K) * (((k : ℤ) - 0 : ℤ) : K) * intHom ψ (logQuot (oneAddPPowMul p h x))
        = (k : K) * (((p : ℕ) : K) * intHom ψ (logQuot (oneAddPPowMul p h x))) by push_cast; ring,
      PadicExpLog.padicExp_natCast_mul h3 hp2 hpL k,
      ← intHom_oneUnitPart_eq_padicExp ψ hp2 hψ (oneAddPPowMul p h x), oneAddPPowMul,
      oneUnitPart_oneAddPMul, coe_oneAddPMul]
  rw [nebCharH_apply h ψ ω k ζ hp2 hψ hh hζ hpK,
    specialize_univChar (intHom ψ) (norm_intHom ψ hψ)
      (inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k)
      (norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k) ω (oneAddPPowMul p h x),
    unitsMap_toZMod_eq_one_of_norm_sub_one_le hle, map_one, Units.val_one, map_one, one_mul,
    ← hbin, hexp, oneAddPow_sub_one_intHom_prime_pow h ψ ζ hp2 hψ hh hζ hpK, inv_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hne), mul_one]

/-- `ℓ⟨1 + p^h⟩ = log(1 + p^h)/p` has norm `p^{−(h−1)}` (`norm_padicLog_eq`). -/
theorem norm_logQuot_oneAddPPowMul_one (hp2 : p ≠ 2) (hh : 0 < h) :
    ‖(logQuot (oneAddPPowMul p h 1) : ℤ_[p])‖ = (p : ℝ)⁻¹ ^ (h - 1) := by
  have hnp : ‖((p : ℕ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have h3 : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by rw [hnp]; exact inv_lt_one_p (p := p)
  have hsub : (((oneAddPPowMul p h 1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1 = (p : ℚ_[p]) ^ h := by
    rw [coe_oneAddPPowMul h hh]; push_cast; ring
  have hpow : ‖(p : ℚ_[p]) ^ h‖ = (p : ℝ)⁻¹ ^ h := by rw [norm_pow, Padic.norm_p]
  have hpowle : (p : ℝ)⁻¹ ^ h ≤ (p : ℝ)⁻¹ :=
    pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
      hh.ne'
  have hle : ‖((oneAddPPowMul p h 1 : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, hsub, hpow]; exact hpowle
  have hu2 : ‖(((oneAddPPowMul p h 1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1‖ ^ 2
      < ‖((p : ℕ) : ℚ_[p])‖ := by
    rw [hsub, hpow, hnp, sq]
    calc (p : ℝ)⁻¹ ^ h * (p : ℝ)⁻¹ ^ h ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ :=
          mul_le_mul hpowle hpowle (by positivity) (by positivity)
      _ < (p : ℝ)⁻¹ := mul_lt_of_lt_one_left (inv_pos.2 (by exact_mod_cast hp.out.pos))
          (inv_lt_one_p (p := p))
  rw [PadicInt.norm_def, coe_logQuot_of_norm_sub_one_le hle, norm_div,
    PadicExpLog.norm_padicLog_eq h3 hp2 hu2, hsub, hpow, hnp]
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ,
    mul_div_cancel_right₀ _ (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))]

/-- **The conductor is exactly `p^{h+1}`**: `nebCharH (1 + p^h)` is a primitive `p`-th root of
unity (`ℓ⟨1 + p^h⟩ ≡ p^{h−1}·u (mod p^h)` with `p ∤ u`, and `ζ^{p^{h−1}}` is a primitive `p`-th
root, `IsPrimitiveRoot.pow_of_dvd`). -/
theorem isPrimitiveRoot_nebCharH_oneAddPPowMul_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) :
    IsPrimitiveRoot (nebCharH h ψ ω k ζ (oneAddPPowMul p h 1)) p := by
  rw [nebCharH_oneAddPPowMul h ψ ω k ζ hp2 hψ hh hζ hpK]
  have hnorm := norm_logQuot_oneAddPPowMul_one h hp2 hh
  generalize logQuot (oneAddPPowMul p h 1) = ℓ at hnorm ⊢
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hnorm
  haveI : NeZero (p ^ (h' + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpinv0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hp.out.pos)
  -- the residue `v` of `ℓ` modulo `p^{h'+1}` is non-zero
  have hv0 : (PadicInt.toZModPow (h' + 1) ℓ).val ≠ 0 := by
    intro h0
    have hz : PadicInt.toZModPow (h' + 1) ℓ = 0 := (ZMod.val_eq_zero _).1 h0
    have hmem : ℓ ∈ Ideal.span {(p : ℤ_[p]) ^ (h' + 1)} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]; exact hz
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, hnorm, zpow_neg, zpow_natCast, ← inv_pow] at hmem
    have hlt : (p : ℝ)⁻¹ ^ (h' + 1) < (p : ℝ)⁻¹ ^ h' :=
      pow_lt_pow_right_of_lt_one₀ hpinv0 (inv_lt_one_p (p := p)) (Nat.lt_succ_self h')
    linarith
  -- `p^{h'}` divides it
  have hdvd : p ^ h' ∣ (PadicInt.toZModPow (h' + 1) ℓ).val := by
    have hcast : (((PadicInt.toZModPow (h' + 1) ℓ).val : ℕ) : ZMod (p ^ h'))
        = PadicInt.toZModPow h' ℓ := by
      rw [ZMod.natCast_val, PadicInt.cast_toZModPow h' (h' + 1) (Nat.le_succ h')]
    have hz : PadicInt.toZModPow h' ℓ = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow,
        hnorm, zpow_neg, zpow_natCast, inv_pow]
    rw [← ZMod.natCast_eq_zero_iff, hcast, hz]
  obtain ⟨u, hu⟩ := hdvd
  have hvlt : (PadicInt.toZModPow (h' + 1) ℓ).val < p ^ (h' + 1) := ZMod.val_lt _
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · exact absurd (by rw [hu, mul_zero]) hv0
    · exact hpos
  have hult : u < p := by
    rw [hu, pow_succ] at hvlt
    exact Nat.lt_of_mul_lt_mul_left hvlt
  have hprim := hζ.pow_of_dvd (pow_ne_zero h' hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ h'))
  rw [Nat.pow_div (Nat.le_succ h') hp.out.pos, show h'.succ - h' = 1 by omega, pow_one] at hprim
  rw [hu, pow_mul]
  exact hprim.pow_of_coprime u (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2
    (Nat.not_dvd_of_pos_of_lt hu0 hult)))

/-- `nebCharH (1 + p^h n) = nebCharH (1 + p^h)^n`: `(1 + p^h)^n ≡ 1 + p^h n (mod p^{h+1})`. -/
theorem nebCharH_oneAddPPowMul_natCast (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (n : ℕ) :
    nebCharH h ψ ω k ζ (oneAddPPowMul p h n)
      = nebCharH h ψ ω k ζ (oneAddPPowMul p h 1) ^ n := by
  induction n with
  | zero =>
    have h1 : oneAddPPowMul p h ((0 : ℕ) : ℤ_[p]) = 1 :=
      Units.ext (by rw [coe_oneAddPPowMul h hh]; simp)
    rw [h1, nebCharH_one h ψ ω k ζ hp2 hψ hh hζ hpK, pow_zero]
  | succ n ih =>
    have hw1 : ‖(((oneAddPPowMul p h (n : ℤ_[p]) * oneAddPPowMul p h 1)⁻¹
        * oneAddPPowMul p h ((n + 1 : ℕ) : ℤ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) - 1‖
        ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
      have hdiff : (((oneAddPPowMul p h (n : ℤ_[p]) * oneAddPPowMul p h 1)⁻¹
          * oneAddPPowMul p h ((n + 1 : ℕ) : ℤ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) - 1
          = (((oneAddPPowMul p h (n : ℤ_[p]) * oneAddPPowMul p h 1)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
            * (((oneAddPPowMul p h ((n + 1 : ℕ) : ℤ_[p])) : ℤ_[p])
              - ((oneAddPPowMul p h (n : ℤ_[p]) * oneAddPPowMul p h 1 : ℤ_[p]ˣ) : ℤ_[p])) := by
        rw [Units.val_mul _ (oneAddPPowMul p h ((n + 1 : ℕ) : ℤ_[p])), mul_sub, Units.inv_mul]
      rw [hdiff, Units.val_mul, coe_oneAddPPowMul h hh, coe_oneAddPPowMul h hh,
        coe_oneAddPPowMul h hh,
        show (1 + (p : ℤ_[p]) ^ h * ((n + 1 : ℕ) : ℤ_[p]))
            - (1 + (p : ℤ_[p]) ^ h * n) * (1 + (p : ℤ_[p]) ^ h * 1)
          = -((p : ℤ_[p]) ^ (2 * h) * n) by push_cast; ring,
        norm_mul, PadicInt.norm_units, one_mul, norm_neg, norm_mul, norm_pow, PadicInt.norm_p]
      calc (p : ℝ)⁻¹ ^ (2 * h) * ‖(n : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (2 * h) * 1 := by
            gcongr; exact PadicInt.norm_le_one _
        _ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
            rw [mul_one]
            exact pow_le_pow_of_le_one (by positivity)
              (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)) (by omega)
    have hsplit : oneAddPPowMul p h ((n + 1 : ℕ) : ℤ_[p])
        = (oneAddPPowMul p h (n : ℤ_[p]) * oneAddPPowMul p h 1)
          * ((oneAddPPowMul p h (n : ℤ_[p]) * oneAddPPowMul p h 1)⁻¹
            * oneAddPPowMul p h ((n + 1 : ℕ) : ℤ_[p])) := by
      rw [mul_inv_cancel_left]
    rw [hsplit, nebCharH_mul h ψ ω k ζ hp2 hψ hh hζ hpK, nebCharH_mul h ψ ω k ζ hp2 hψ hh hζ hpK,
      ih, nebCharH_of_norm_sub_one_le_pow h ψ ω k ζ hp2 hψ hh hζ hpK hw1, mul_one, pow_succ]

/-- **The character sum**: for `p ∤ b`, `∑_{c < p} ψ_neb(1 + p^h b c) = 0`
(`IsPrimitiveRoot.geom_sum_eq_zero` at the primitive root `nebCharH (1 + p^h)^b`). -/
theorem sum_nebCharH_oneAddPPowMul_mul_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ}
    (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, nebCharH h ψ ω k ζ (oneAddPPowMul p h ((b : ℤ_[p]) * c)) = 0 := by
  have hξ := (isPrimitiveRoot_nebCharH_oneAddPPowMul_one h ψ ω k ζ hp2 hψ hh hζ hpK).pow_of_coprime
    b (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hb))
  rw [← hξ.geom_sum_eq_zero hp.out.one_lt]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show (b : ℤ_[p]) * c = ((b * c : ℕ) : ℤ_[p]) by push_cast; ring,
    nebCharH_oneAddPPowMul_natCast h ψ ω k ζ hp2 hψ hh hζ hpK, pow_mul]

/-- **The character sum, inverted**: for `p ∤ b`, `∑_{c < p} ψ_neb(1 + p^h b c)⁻¹ = 0`. -/
theorem sum_inv_nebCharH_oneAddPPowMul_mul_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ}
    (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, (nebCharH h ψ ω k ζ (oneAddPPowMul p h ((b : ℤ_[p]) * c)))⁻¹ = 0 := by
  have hξ :=
    (isPrimitiveRoot_nebCharH_oneAddPPowMul_one h ψ ω k ζ hp2 hψ hh hζ hpK).inv.pow_of_coprime
      b (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hb))
  rw [← hξ.geom_sum_eq_zero hp.out.one_lt]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show (b : ℤ_[p]) * c = ((b * c : ℕ) : ℤ_[p]) by push_cast; ring,
    nebCharH_oneAddPPowMul_natCast h ψ ω k ζ hp2 hψ hh hζ hpK, pow_mul, inv_pow, inv_pow]

/-- The same in terms of `nebCharKH` at `ψ(1 + b c p^h)`, the spelling that appears in the
identity computation (the `d`-entry of `ℓQH b c` is `1 + bcp^h`). -/
theorem sum_inv_nebCharKH_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ}
    (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p,
      (nebCharKH h ψ ω k ζ (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ = 0 := by
  rw [← sum_inv_nebCharH_oneAddPPowMul_mul_eq_zero h ψ ω k ζ hp2 hψ hh hζ hpK hb]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [nebCharH, intHom_apply, coe_oneAddPPowMul h hh,
    show (((1 + (p : ℤ_[p]) ^ h * ((b : ℤ_[p]) * c) : ℤ_[p]) : ℚ_[p]))
        = 1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h by push_cast; ring]

/-! ### The three abstract hypotheses of `20_AtkinLehnerMapH.lean`, discharged -/

/-- `hmul`: `nebCharKH` is multiplicative on `ψ`-images of `p`-adic units. -/
theorem nebCharKH_psi_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x y : ℚ_[p]}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    nebCharKH h ψ ω k ζ (ψ (x * y)) = nebCharKH h ψ ω k ζ (ψ x) * nebCharKH h ψ ω k ζ (ψ y) := by
  obtain ⟨ux, hux⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = x := by
    let z : ℤ_[p] := ⟨x, hx.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hx)
    exact ⟨hz.unit, rfl⟩
  obtain ⟨uy, huy⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = y := by
    let z : ℤ_[p] := ⟨y, hy.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hy)
    exact ⟨hz.unit, rfl⟩
  have hres := nebCharH_mul h ψ ω k ζ hp2 hψ hh hζ hpK ux uy
  simp only [nebCharH, intHom_apply, Units.val_mul, PadicInt.coe_mul, hux, huy] at hres
  exact hres

/-- `hne`: `nebCharKH` does not vanish on `ψ`-images of `p`-adic units. -/
theorem nebCharKH_psi_ne_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : ℚ_[p]}
    (hx : ‖x‖ = 1) : nebCharKH h ψ ω k ζ (ψ x) ≠ 0 := by
  obtain ⟨ux, hux⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = x := by
    let z : ℤ_[p] := ⟨x, hx.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hx)
    exact ⟨hz.unit, rfl⟩
  have hres := nebCharH_ne_zero h ψ ω k ζ hp2 hψ hh hζ hpK ux
  simp only [nebCharH, intHom_apply, hux] at hres
  exact hres

/-- `hcond`: `nebCharKH` is trivial on `ψ(1 + p^{h+1}ℤ_p)`. -/
theorem nebCharKH_psi_of_norm_sub_one_le_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) : nebCharKH h ψ ω k ζ (ψ x) = 1 := by
  have hsq : (p : ℝ)⁻¹ ^ (h + 1) ≤ (p : ℝ)⁻¹ :=
    pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
      (Nat.succ_ne_zero h)
  have hx1 : ‖x‖ = 1 := norm_eq_one_of_norm_sub_le (p := p) norm_one (hx.trans hsq)
  obtain ⟨ux, hux⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = x := by
    let z : ℤ_[p] := ⟨x, hx1.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hx1)
    exact ⟨hz.unit, rfl⟩
  have hres := nebCharH_of_norm_sub_one_le_pow h ψ ω k ζ hp2 hψ hh hζ hpK (a := ux)
    (by rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, hux]; exact hx)
  simp only [nebCharH, intHom_apply, hux] at hres
  exact hres

/-! ### The partner nebentypus `ω⁻¹ω₀^{2k}` at level `h` -/

/-- `(1+T)^ℓ` at `T = ζ⁻¹ − 1` and at `T = ζ − 1` are inverse to each other. -/
theorem oneAddPow_inv_sub_one_mul_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (ℓ : ℤ_[p]) :
    oneAddPow (ζ⁻¹ - 1) (intHom ψ ℓ) * oneAddPow (ζ - 1) (intHom ψ ℓ) = 1 := by
  rw [oneAddPow_sub_one_intHom_prime_pow h ψ ζ⁻¹ hp2 hψ hh hζ.inv hpK,
    oneAddPow_sub_one_intHom_prime_pow h ψ ζ hp2 hψ hh hζ hpK, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ (hζ.ne_zero (pow_ne_zero _ hp.out.ne_zero)))]

/-- **`nebCharH` in closed form**: `ψ_neb(a) = ω(ā) · ζ^{ℓ⟨a⟩ mod p^h} · ω₀(ā)^{−k}`. -/
theorem nebCharH_eq (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharH h ψ ω k ζ a
      = intHom ψ (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
        * ζ ^ (PadicInt.toZModPow h (logQuot a)).val
        * (intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) :
            ℤ_[p]))⁻¹ ^ k := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hLle : ‖intHom ψ (logQuot a)‖ ≤ 1 := by
    rw [norm_intHom ψ hψ]; exact PadicInt.norm_le_one _
  have hpL : ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    have hle : ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ ≤ (p : ℝ)⁻¹ := by
      rw [norm_mul, hpK]; exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) hLle
    rw [hpK, sq]
    calc ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖ * ‖((p : ℕ) : K) * intHom ψ (logQuot a)‖
        ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ :=
          mul_le_mul hle hle (norm_nonneg _) (inv_nonneg.2 (Nat.cast_nonneg _))
      _ < (p : ℝ)⁻¹ := mul_lt_of_lt_one_left (inv_pos.2 (by exact_mod_cast hp.out.pos))
          (inv_lt_one_p (p := p))
  have hw0 : weightPoint p 0 ζ = ζ - 1 := by
    rw [weightPoint, Int.cast_zero, mul_zero, PadicExpLog.padicExp_zero, mul_one]
  have hbin := oneAddPow_weightPoint_mul_padicExp_prime_pow ψ hp2 hψ hh hζ hpK 0 (k : ℤ)
    (logQuot a)
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
  have ht0 : intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
      ≠ 0 :=
    ((teichRes _).isUnit.map (intHom ψ)).ne_zero
  have ho0 : intHom ψ (oneUnitPart a) ≠ 0 := by
    intro h0
    have hn : ‖intHom ψ (oneUnitPart a)‖ = 1 := by
      rw [norm_intHom ψ hψ, oneUnitPart, PadicInt.norm_units]
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rw [nebCharH_apply h ψ ω k ζ hp2 hψ hh hζ hpK,
    specialize_univChar (intHom ψ) (norm_intHom ψ hψ)
      (inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k)
      (norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k) ω a, ← hbin, hexp,
    oneAddPow_sub_one_intHom_prime_pow h ψ ζ hp2 hψ hh hζ hpK, ha]
  simp only [mul_pow, inv_pow, mul_inv]
  field_simp

/-- **The partner point carries the inverse nebentypus** at conductor `p^{h+1}`:
at `T_{χ_k}(ζ⁻¹)` with tame character `ω⁻¹ω₀^{2k}`, the nebentypus is `ψ_neb⁻¹`. -/
theorem nebCharH_partnerChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharH h ψ (partnerChar p ω k) k ζ⁻¹ a = (nebCharH h ψ ω k ζ a)⁻¹ := by
  have hω : intHom ψ (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]) ≠ 0 :=
    ((ω _).isUnit.map (intHom ψ)).ne_zero
  have ht : intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
      ≠ 0 :=
    ((teichRes _).isUnit.map (intHom ψ)).ne_zero
  have hz : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ hp.out.ne_zero)
  rw [nebCharH_eq h ψ (partnerChar p ω k) k ζ⁻¹ hp2 hψ hh hζ.inv hpK,
    nebCharH_eq h ψ ω k ζ hp2 hψ hh hζ hpK, partnerChar_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, map_mul, map_pow, map_units_inv]
  simp only [inv_pow, mul_inv, inv_inv]
  field_simp
  ring

/-- The partner nebentypus function on `K`, at the image of a unit. -/
theorem nebCharKH_partnerChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharKH h ψ (partnerChar p ω k) k ζ⁻¹ (intHom ψ (a : ℤ_[p]))
      = (nebCharKH h ψ ω k ζ (intHom ψ (a : ℤ_[p])))⁻¹ :=
  nebCharH_partnerChar h ψ ω k ζ hp2 hψ hh hζ hpK a

/-- The shape constant of the partner level-`h` halo weight at `g ∈ M1Kh h ψ` is
`nebCharKH(g 1 1)⁻¹` (`g 1 1 = ψ d` with `d` a unit, `mem_M1Kh_iff`, `mem_Mh_iff`). -/
theorem autFactor_haloWeightH_partner_eq_inv_nebCharKH (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h))
    (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ⁻¹‖) (h1 : ‖classicalPoint p k ζ⁻¹‖ < 1)
    (hT : ‖TH p h (classicalPoint p k ζ⁻¹)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh h ψ) :
    (haloWeightH h ψ (classicalPoint p k ζ⁻¹) (partnerChar p ω k) hp2 hψ h0 h1
          hT).toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebCharKH h ψ ω k ζ (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1) := by
  rw [autFactor_haloWeightH_classicalPoint_eq_nebCharKH h ψ (partnerChar p ω k) k ζ⁻¹ hp2 hψ
    hζ.inv.pow_eq_one h0 h1 hT g]
  obtain ⟨δ, hδ, hδg⟩ := (mem_M1Kh_iff h ψ).1 g.2
  have hd : ‖δ 1 1‖ = 1 := (mem_Mh_iff.1 hδ).2.2.1
  obtain ⟨d, hd'⟩ : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = δ 1 1 := by
    let z : ℤ_[p] := ⟨δ 1 1, hd.le⟩
    have hz : IsUnit z := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def]; exact hd)
    exact ⟨hz.unit, rfl⟩
  have hg11 : g.1 1 1 = intHom ψ (d : ℤ_[p]) := by
    rw [← hδg, RingHom.mapMatrix_apply, Matrix.map_apply, intHom_apply, hd']
  rw [hg11, nebCharKH_partnerChar h ψ ω k ζ hp2 hψ hh hζ (norm_natCast_p ψ hψ) d]

omit [Fintype ι] [DecidableEq ι] in
/-- The constants of the partner level-`h` classical datum are the inverses of the datum's. -/
theorem classicalDataH_partnerChar_u (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (i : ι) (t : Fin p)
    (a : ZMod (p ^ h)) :
    (classicalDataH ψ (partnerChar p ω k) θG U hU vRep hvΔ uu hp2 hψ hh hζ.inv hpK k).u i t a
      = ((classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k).u i t a)⁻¹ := by
  rw [classicalDataH_u_eq_nebCharH h ψ (partnerChar p ω k) k ζ⁻¹ θG U hU vRep hvΔ uu hp2 hψ hh
      hζ.inv hpK,
    classicalDataH_u_eq_nebCharH h ψ ω k ζ θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK,
    nebCharH_partnerChar h ψ ω k ζ hp2 hψ hh hζ hpK]

end LWX

end
