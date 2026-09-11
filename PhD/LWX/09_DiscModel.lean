/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«08_AmiceBasis»
import PhD.LWX.«08_HaloWeightH»
import PhD.LWX.«07_Seam»

/-!
# The disc model of the induced representation at level `h`, and the `M₁`-action — SKELETON

[LWX, (2.3.1)] at analyticity level `m = h + 1`: `OB_{qp^{-m}}` is the space of functions on `ℤ_p`
which are analytic on every disc `a + pʰℤ_p` (`a` running over `ℤ/pʰ`), with the maximum of the
Gauss norms of the `pʰ` Taylor expansions; its model is `c(ℤ/pʰ × ℕ, K)` (`08_AmiceBasis.lean`).

The level `M₁` of [LWX, (2.3.3)] acts on it by the same formula (2.3.2)
`(f ∣ δ)(z) = [cz+d]·f((az+b)/(cz+d))`, but the formula no longer preserves a single disc: it
**permutes the discs**.  Writing `t_a(w) = a + pʰw` for the parametrisation of the disc `a` and
`a' = möb δ (a) mod pʰ` for the image disc, the matrix identity

  `δ · t_a = t_{a'} · δ'`,   `δ' = t_{a'}⁻¹ · δ · t_a ∈ M_h`

(`discConj`, `discConj_mem_Mh`) says the action carries the Taylor expansion on the disc `a'` to
the Taylor expansion on the disc `a`, through the *single-disc* weight action of `δ'` at the
level `M_h` — which is exactly `08_HaloWeightH.lean`'s `AnalyticWeight` action.  So the disc action
is a `blockOp` of `kappaSlash`s, one per disc, permuted by `discImage` (`discSlash`), and it is a
right action because `discImage`/`discConj` satisfy the cocycle rules
(`discImage_mul`, `discConj_mul`).

Pointwise, `discSlash` is [LWX, (2.3.2)] verbatim: `discEval_discSlash`.

## Main declarations

* `LWX.discImage`, `LWX.discConj`, `LWX.discConj_mem_Mh`, `LWX.mobiusFun_add_pow_mul` — the
  conjugation identity.
* `LWX.discImage_mul`, `LWX.discImage_one`, `LWX.discConj_mul`, `LWX.discConj_one` — the cocycle.
* `LWX.discSlash`, `LWX.discSlash_one`, `LWX.discSlash_mul`, `LWX.discSlashAction`,
  `LWX.discSMulSlashClass`, `LWX.isCompactoid_discSlash`.
* **`LWX.discEval_discSlash`** — the action is [LWX, (2.3.2)] pointwise.
-/

open Filter Topology TateFredholm QMF

open scoped Nat TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

section LocalMatAux

/-- The denominator unit, as an element of `ℤ_p` (a local restatement of the private
`LWX.denUnit_coe`). -/
private theorem coe_denUnit (δ : LocalMat p) (z : ℤ_[p]) :
    ((δ.denUnit z : ℤ_[p]ˣ) : ℤ_[p]) = δ.c * z + (δ.d : ℤ_[p]) :=
  (δ.isUnit_c_mul_add z).unit_spec

/-- The denominator does not vanish over `ℚ_p` (a local restatement of the private
`LWX.coe_den_ne_zero'`). -/
private theorem den_ne_zero (δ : LocalMat p) (z : ℤ_[p]) :
    ((δ.c : ℤ_[p]) : ℚ_[p]) * ((z : ℤ_[p]) : ℚ_[p]) + (((δ.d : ℤ_[p])) : ℚ_[p]) ≠ 0 := by
  intro hc
  refine (δ.isUnit_c_mul_add z).ne_zero (Subtype.coe_injective ?_)
  push_cast
  exact hc

/-- The Möbius value over `ℚ_p`, division form (a local restatement of the private
`LWX.coe_mobiusFun`). -/
private theorem coe_mobiusFun (δ : LocalMat p) (z : ℤ_[p]) :
    ((δ.mobiusFun z : ℤ_[p]) : ℚ_[p])
      = (((δ.a : ℤ_[p]) : ℚ_[p]) * ((z : ℤ_[p]) : ℚ_[p]) + ((δ.b : ℤ_[p]) : ℚ_[p]))
        / (((δ.c : ℤ_[p]) : ℚ_[p]) * ((z : ℤ_[p]) : ℚ_[p]) + (((δ.d : ℤ_[p])) : ℚ_[p])) := by
  have hDM : (δ.c * z + (δ.d : ℤ_[p])) * δ.mobiusFun z = δ.a * z + δ.b := by
    rw [LocalMat.mobiusFun, mul_left_comm,
      Ring.mul_inverse_cancel _ (δ.isUnit_c_mul_add z), mul_one]
  have hcast := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hDM
  push_cast at hcast
  rw [eq_div_iff (den_ne_zero δ z), mul_comm]
  exact hcast

/-- The denominator cocycle (a local restatement of the private `LWX.den_cocycle`). -/
private theorem denUnit_mul (g₁ g₂ : M1 p) (z : ℤ_[p]) :
    ((M1.toLocalMat (g₁ * g₂)).denUnit z : ℤ_[p])
      = ((M1.toLocalMat g₁).denUnit ((M1.toLocalMat g₂).mobiusFun z) : ℤ_[p])
        * ((M1.toLocalMat g₂).denUnit z : ℤ_[p]) := by
  rw [coe_denUnit, coe_denUnit, coe_denUnit]
  refine Subtype.coe_injective ?_
  push_cast [coe_mobiusFun]
  simp only [M1.coe_toLocalMat_a, M1.coe_toLocalMat_b, M1.coe_toLocalMat_c,
    M1.coe_toLocalMat_d, Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hB0 := den_ne_zero (M1.toLocalMat g₂) z
  simp only [M1.coe_toLocalMat_c, M1.coe_toLocalMat_d] at hB0
  field_simp
  ring

/-- Möbius composition (a local restatement of the private `LWX.mobius_cocycle`). -/
private theorem mobiusFun_mul (g₁ g₂ : M1 p) (z : ℤ_[p]) :
    (M1.toLocalMat (g₁ * g₂)).mobiusFun z
      = (M1.toLocalMat g₁).mobiusFun ((M1.toLocalMat g₂).mobiusFun z) := by
  set A := M1.toLocalMat g₁ with hA
  set B := M1.toLocalMat g₂ with hB
  set C := M1.toLocalMat (g₁ * g₂) with hC
  have h1 : C.c * z + (C.d : ℤ_[p])
      = (A.c * B.mobiusFun z + (A.d : ℤ_[p])) * (B.c * z + (B.d : ℤ_[p])) := by
    have h2 := denUnit_mul g₁ g₂ z
    rwa [coe_denUnit, coe_denUnit, coe_denUnit] at h2
  have h3 : C.a * z + (C.b : ℤ_[p])
      = (A.a * B.mobiusFun z + A.b) * (B.c * z + (B.d : ℤ_[p])) := by
    refine Subtype.coe_injective ?_
    push_cast [coe_mobiusFun]
    simp only [hA, hB, hC, M1.coe_toLocalMat_a, M1.coe_toLocalMat_b,
      M1.coe_toLocalMat_c, M1.coe_toLocalMat_d, Submonoid.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    have hB0 := den_ne_zero (M1.toLocalMat g₂) z
    simp only [M1.coe_toLocalMat_c, M1.coe_toLocalMat_d] at hB0 ⊢
    field_simp
    ring
  rw [LocalMat.mobiusFun, LocalMat.mobiusFun, h3, h1]
  obtain ⟨uB, huB⟩ := B.isUnit_c_mul_add z
  obtain ⟨uA, huA⟩ := A.isUnit_c_mul_add (B.mobiusFun z)
  rw [← huA, ← huB, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, mul_inv,
    Units.val_mul]
  have hcancel : ((uB : ℤ_[p])) * (((uB⁻¹ : ℤ_[p]ˣ)) : ℤ_[p]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (A.a * B.mobiusFun z + A.b) * (uB : ℤ_[p])
        * (((uA⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((uB⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
      = (A.a * B.mobiusFun z + A.b) * ((uA⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
        * ((uB : ℤ_[p]) * ((uB⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) := by ring
    _ = (A.a * B.mobiusFun z + A.b) * ((uA⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
        rw [hcancel, mul_one]

/-- `toZModPow` is the residue of the approximation. -/
theorem val_toZModPow (n : ℕ) (z : ℤ_[p]) : (PadicInt.toZModPow n z).val = z.appr n :=
  ZMod.val_natCast_of_lt (PadicInt.appr_lt _ _)

/-- The identity Möbius map. -/
private theorem mobiusFun_one (z : ℤ_[p]) : (M1.toLocalMat (1 : M1 p)).mobiusFun z = z := by
  have ha : ((M1.toLocalMat (1 : M1 p)).a : ℤ_[p]) = 1 := by
    refine Subtype.ext ?_
    rw [M1.coe_toLocalMat_a]
    simp
  have hb : ((M1.toLocalMat (1 : M1 p)).b : ℤ_[p]) = 0 := by
    refine Subtype.ext ?_
    rw [M1.coe_toLocalMat_b]
    simp
  have hc : ((M1.toLocalMat (1 : M1 p)).c : ℤ_[p]) = 0 := by
    refine Subtype.ext ?_
    rw [M1.coe_toLocalMat_c]
    simp
  have hd : (((M1.toLocalMat (1 : M1 p)).d : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    refine Subtype.ext ?_
    rw [M1.coe_toLocalMat_d]
    simp
  rw [LocalMat.mobiusFun, ha, hb, hc, hd, zero_mul, zero_add, Ring.inverse_one, mul_one,
    one_mul, add_zero]

end LocalMatAux

section Conjugation

variable (h : ℕ) (δ : M1 p) (a : ZMod (p ^ h))

/-- **The image disc**: `möb δ` sends the disc `a + pʰℤ_p` into the disc
`(möb δ a) mod pʰ + pʰℤ_p` (`möb δ` is `1`-Lipschitz). -/
def discImage : ZMod (p ^ h) :=
  PadicInt.toZModPow h ((M1.toLocalMat δ).mobiusFun ((a.val : ℕ) : ℤ_[p]))

/-- The matrix `t_{a'}⁻¹·δ·t_a` of the conjugated local matrix, `t_a = (pʰ a; 0 1)`. -/
def discConjMat : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0
        - (((discImage h δ a).val : ℕ) : ℚ_[p]) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0,
      ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * ((a.val : ℕ) : ℚ_[p])
          + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1
        - (((discImage h δ a).val : ℕ) : ℚ_[p])
          * ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])
              + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) / (p : ℚ_[p]) ^ h;
     (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * (p : ℚ_[p]) ^ h,
      (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])
        + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1]

@[simp] theorem discConjMat_apply_zero_zero :
    discConjMat h δ a 0 0 = (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0
      - (((discImage h δ a).val : ℕ) : ℚ_[p]) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 := rfl

@[simp] theorem discConjMat_apply_zero_one :
    discConjMat h δ a 0 1
      = ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * ((a.val : ℕ) : ℚ_[p])
          + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1
        - (((discImage h δ a).val : ℕ) : ℚ_[p])
          * ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])
              + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) / (p : ℚ_[p]) ^ h := rfl

@[simp] theorem discConjMat_apply_one_zero :
    discConjMat h δ a 1 0
      = (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * (p : ℚ_[p]) ^ h := rfl

@[simp] theorem discConjMat_apply_one_one :
    discConjMat h δ a 1 1
      = (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])
        + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 := rfl

/-- **The conjugated matrix lies in `M_h`**: `‖c'‖ = ‖c‖·p^{−h} ≤ p^{−(h+1)}`, `‖d'‖ = 1`
(`‖c·a‖ < 1 = ‖d‖`), `det δ' = det δ ≠ 0`, and the `b`-entry is integral **because** `a'` was
chosen as the residue of `möb δ a`:
`δ₀₀a + δ₀₁ − a'(δ₁₀a + δ₁₁) = (δ₁₀a + δ₁₁)·(möb δ a − a')` has norm `≤ p^{−h}`. -/
theorem discConjMat_mem_Mh : discConjMat h δ a ∈ Mh p h := by
  obtain ⟨hδ1, hδ2, hδ3, hδ4⟩ := δ.2
  have hple : ∀ n : ℕ, ‖((n : ℕ) : ℚ_[p])‖ ≤ 1 := fun n => by
    rw [show ((n : ℕ) : ℚ_[p]) = ((n : ℤ_[p]) : ℚ_[p]) from by push_cast; ring,
      ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  have hpph : ‖((p : ℚ_[p])) ^ h‖ = (p : ℝ)⁻¹ ^ h := by rw [norm_pow, Padic.norm_p]
  have hpne : ((p : ℚ_[p])) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hpinv1 : ((p : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hpinvpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  -- the `a`-side data as `p`-adic integers
  set A := M1.toLocalMat δ with hA
  set zA : ℤ_[p] := ((a.val : ℕ) : ℤ_[p]) with hzA
  set zA' : ℤ_[p] := (((discImage h δ a).val : ℕ) : ℤ_[p]) with hzA'
  have hD : ((A.denUnit zA : ℤ_[p]ˣ) : ℤ_[p]) = A.c * zA + (A.d : ℤ_[p]) :=
    (A.isUnit_c_mul_add zA).unit_spec
  have hDM : (A.c * zA + (A.d : ℤ_[p])) * A.mobiusFun zA = A.a * zA + A.b := by
    rw [LocalMat.mobiusFun, mul_left_comm,
      Ring.mul_inverse_cancel _ (A.isUnit_c_mul_add zA), mul_one]
  -- `möb δ (a) ≡ a' (mod pʰ)`
  have hres : PadicInt.toZModPow h (A.mobiusFun zA - zA') = 0 := by
    rw [map_sub, hzA', map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]
    rfl
  have hmob : ‖A.mobiusFun zA - zA'‖ ≤ (p : ℝ)⁻¹ ^ h := by
    have hspan : (A.mobiusFun zA - zA') ∈ Ideal.span {(p : ℤ_[p]) ^ h} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
      exact hres
    have hn := (PadicInt.norm_le_pow_iff_mem_span_pow _ h).mpr hspan
    rwa [show ((p : ℝ) ^ (-(h : ℤ))) = (p : ℝ)⁻¹ ^ h from by
      rw [zpow_neg, zpow_natCast, inv_pow]] at hn
  -- the numerator of the `b`-entry is `den·(möb − a')`
  have hnum : (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * ((a.val : ℕ) : ℚ_[p])
        + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1
      - (((discImage h δ a).val : ℕ) : ℚ_[p])
        * ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])
            + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)
      = (((A.c * zA + (A.d : ℤ_[p])) * (A.mobiusFun zA - zA') : ℤ_[p]) : ℚ_[p]) := by
    have hexp : (A.c * zA + (A.d : ℤ_[p])) * (A.mobiusFun zA - zA')
        = A.a * zA + A.b - zA' * (A.c * zA + (A.d : ℤ_[p])) := by
      rw [mul_sub, hDM]
      ring
    rw [hexp]
    push_cast [hA]
    simp only [M1.coe_toLocalMat_a, M1.coe_toLocalMat_b, M1.coe_toLocalMat_c,
      M1.coe_toLocalMat_d, hzA, hzA']
    push_cast
    ring
  have hbnorm : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * ((a.val : ℕ) : ℚ_[p])
        + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1
      - (((discImage h δ a).val : ℕ) : ℚ_[p])
        * ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])
            + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)‖ ≤ (p : ℝ)⁻¹ ^ h := by
    rw [hnum, ← PadicInt.norm_def]
    calc ‖(A.c * zA + (A.d : ℤ_[p])) * (A.mobiusFun zA - zA')‖
        ≤ ‖(A.c * zA + (A.d : ℤ_[p]))‖ * ‖A.mobiusFun zA - zA'‖ := norm_mul_le _ _
      _ ≤ 1 * (p : ℝ)⁻¹ ^ h :=
          mul_le_mul (PadicInt.norm_le_one _) hmob (norm_nonneg _) zero_le_one
      _ = (p : ℝ)⁻¹ ^ h := one_mul _
  -- the four entry bounds
  have h00 : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0
      - (((discImage h δ a).val : ℕ) : ℚ_[p])
        * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hδ1 0 0) ?_)
    rw [norm_neg, norm_mul]
    exact mul_le_one₀ (hple _) (norm_nonneg _) (hδ1 1 0)
  have h01 : ‖((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * ((a.val : ℕ) : ℚ_[p])
        + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1
      - (((discImage h δ a).val : ℕ) : ℚ_[p])
        * ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])
            + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) / (p : ℚ_[p]) ^ h‖ ≤ 1 := by
    rw [norm_div, hpph, div_le_one (by positivity)]
    exact hbnorm
  have h10 : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * (p : ℚ_[p]) ^ h‖
      ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [norm_mul, hpph, pow_succ, mul_comm ((p : ℝ)⁻¹ ^ h)]
    exact mul_le_mul_of_nonneg_right hδ2 (by positivity)
  have h11 : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])
      + (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖ = 1 := by
    have hsmall : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 * ((a.val : ℕ) : ℚ_[p])‖ < 1 := by
      rw [norm_mul]
      calc ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖ * ‖((a.val : ℕ) : ℚ_[p])‖
          ≤ (p : ℝ)⁻¹ * 1 := mul_le_mul hδ2 (hple _) (norm_nonneg _) (by positivity)
        _ = (p : ℝ)⁻¹ := mul_one _
        _ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hδ3]; exact hsmall.ne), hδ3,
      max_eq_right hsmall.le]
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      simp only [discConjMat, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.of_apply]
    · exact h00
    · exact h01
    · exact h10.trans (pow_le_one₀ (by positivity) hpinv1)
    · exact h11.le
  · simpa only [discConjMat, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.of_apply] using h10
  · simpa only [discConjMat, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.of_apply] using h11
  · have key : ∀ A B C D α r n : ℚ_[p], n ≠ 0 →
        (A - r * C) * (C * α + D) - (A * α + B - r * (C * α + D)) / n * (C * n)
          = A * D - B * C := by
      intro A B C D α r n hn
      field_simp
      ring
    rw [Matrix.det_fin_two] at hδ4
    rw [discConjMat, Matrix.det_fin_two_of, key _ _ _ _ _ _ _ hpne]
    exact hδ4

/-- The conjugated matrix, as an element of the level `M₁`. -/
def discConj : M1 p := ⟨discConjMat h δ a, Mh_le_M1 h (discConjMat_mem_Mh h δ a)⟩

@[simp] theorem coe_discConj :
    (discConj h δ a : Matrix (Fin 2) (Fin 2) ℚ_[p]) = discConjMat h δ a := rfl

theorem discConj_mem_Mh : (discConj h δ a : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Mh p h :=
  discConjMat_mem_Mh h δ a

/-- The `K`-side conjugated matrix, as an element of the level `M1Kh`. -/
def discConjK {K : Type*} [NontriviallyNormedField K] (ψ : ℚ_[p] →+* K) : M1Kh h ψ :=
  ⟨(RingHom.mapMatrix ψ) (discConj h δ a).1, ⟨_, discConj_mem_Mh h δ a, rfl⟩⟩

@[simp] theorem coe_discConjK {K : Type*} [NontriviallyNormedField K] (ψ : ℚ_[p] →+* K) :
    (discConjK h δ a ψ : Matrix (Fin 2) (Fin 2) K)
      = (RingHom.mapMatrix ψ) (discConj h δ a).1 := rfl

/-- The lower row of the conjugate: the denominator is unchanged, `c'w + d' = c·(a + pʰw) + d`. -/
theorem denUnit_discConj (w : ℤ_[p]) :
    ((M1.toLocalMat (discConj h δ a)).denUnit w : ℤ_[p])
      = ((M1.toLocalMat δ).denUnit (((a.val : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) : ℤ_[p]) := by
  rw [coe_denUnit, coe_denUnit]
  refine Subtype.coe_injective ?_
  push_cast
  simp only [M1.coe_toLocalMat_c, M1.coe_toLocalMat_d, coe_discConj,
    discConjMat_apply_one_zero, discConjMat_apply_one_one]
  ring

/-- **The conjugation identity** `möb δ (a + pʰw) = a' + pʰ·möb δ' (w)`: the disc `a` is carried
to the disc `a'` by the single-disc Möbius map of the conjugate. -/
theorem mobiusFun_add_pow_mul (w : ℤ_[p]) :
    (M1.toLocalMat δ).mobiusFun (((a.val : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ h * w)
      = ((((discImage h δ a).val : ℕ)) : ℤ_[p])
        + (p : ℤ_[p]) ^ h * (M1.toLocalMat (discConj h δ a)).mobiusFun w := by
  have hpne : ((p : ℚ_[p])) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  set A := M1.toLocalMat δ with hA
  set A' := M1.toLocalMat (discConj h δ a) with hA'
  set z : ℤ_[p] := ((a.val : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ h * w with hz
  have hDM : (A.c * z + (A.d : ℤ_[p])) * A.mobiusFun z = A.a * z + A.b := by
    rw [LocalMat.mobiusFun, mul_left_comm,
      Ring.mul_inverse_cancel _ (A.isUnit_c_mul_add z), mul_one]
  have hDM' : (A'.c * w + (A'.d : ℤ_[p])) * A'.mobiusFun w = A'.a * w + A'.b := by
    rw [LocalMat.mobiusFun, mul_left_comm,
      Ring.mul_inverse_cancel _ (A'.isUnit_c_mul_add w), mul_one]
  have hden : A'.c * w + (A'.d : ℤ_[p]) = A.c * z + (A.d : ℤ_[p]) := by
    have hd := denUnit_discConj h δ a w
    rwa [coe_denUnit, coe_denUnit] at hd
  have hRHS : (A.c * z + (A.d : ℤ_[p])) * (((((discImage h δ a).val : ℕ)) : ℤ_[p])
      + (p : ℤ_[p]) ^ h * A'.mobiusFun w)
      = (A.c * z + (A.d : ℤ_[p])) * ((((discImage h δ a).val : ℕ)) : ℤ_[p])
        + (p : ℤ_[p]) ^ h * (A'.a * w + A'.b) := by
    rw [mul_add, ← hDM', ← hden]
    ring
  refine mul_left_cancel₀ (A.isUnit_c_mul_add z).ne_zero ?_
  rw [hDM, hRHS]
  refine Subtype.coe_injective ?_
  push_cast [hz, hA, hA']
  simp only [M1.coe_toLocalMat_a, M1.coe_toLocalMat_b, M1.coe_toLocalMat_c,
    M1.coe_toLocalMat_d, coe_discConj, discConjMat_apply_zero_zero,
    discConjMat_apply_zero_one]
  field_simp
  ring

/-- The image disc of `z` is the disc of `möb δ z` (`toZModPow` of the conjugation identity). -/
theorem toZModPow_mobiusFun (z : ℤ_[p]) :
    PadicInt.toZModPow h ((M1.toLocalMat δ).mobiusFun z)
      = discImage h δ (PadicInt.toZModPow h z) := by
  have hz : ((((PadicInt.toZModPow h z).val : ℕ)) : ℤ_[p])
      + (p : ℤ_[p]) ^ h * discCoord h z = z := by
    rw [val_toZModPow]
    exact appr_add_pow_mul_discCoord h z
  have hppow : (PadicInt.toZModPow h ((p : ℤ_[p]) ^ h)) = 0 := by
    rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  conv_lhs => rw [← hz]
  rw [mobiusFun_add_pow_mul h δ (PadicInt.toZModPow h z) (discCoord h z), map_add,
    map_mul, hppow, zero_mul, add_zero, map_natCast, ZMod.natCast_zmod_val]

variable {h δ a}

@[simp] theorem discImage_one (a : ZMod (p ^ h)) : discImage h (1 : M1 p) a = a := by
  rw [discImage, mobiusFun_one, map_natCast, ZMod.natCast_zmod_val]

@[simp] theorem discConj_one (a : ZMod (p ^ h)) : discConj h (1 : M1 p) a = 1 := by
  have hpne : ((p : ℚ_[p])) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  refine Subtype.ext ?_
  rw [coe_discConj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [discConjMat, discImage_one, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Submonoid.coe_one, Matrix.one_apply,
      Fin.isValue] <;>
    norm_num

/-- **The disc cocycle**: `discImage` is a right action of `M₁` on the discs. -/
theorem discImage_mul (δ₁ δ₂ : M1 p) (a : ZMod (p ^ h)) :
    discImage h (δ₁ * δ₂) a = discImage h δ₁ (discImage h δ₂ a) := by
  have h1 : discImage h (δ₁ * δ₂) a
      = PadicInt.toZModPow h ((M1.toLocalMat δ₁).mobiusFun
          ((M1.toLocalMat δ₂).mobiusFun (((a.val : ℕ) : ℤ_[p])))) := by
    rw [discImage, mobiusFun_mul]
  rw [h1, toZModPow_mobiusFun]
  rfl

/-- **The matrix cocycle** `(δ₁δ₂)' = δ₁'·δ₂'` at the intermediate disc
(`t_{a''}⁻¹δ₁δ₂t_a = (t_{a''}⁻¹δ₁t_{a'})(t_{a'}⁻¹δ₂t_a)`). -/
theorem discConj_mul (δ₁ δ₂ : M1 p) (a : ZMod (p ^ h)) :
    discConj h (δ₁ * δ₂) a = discConj h δ₁ (discImage h δ₂ a) * discConj h δ₂ a := by
  have hpne : ((p : ℚ_[p])) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, coe_discConj, coe_discConj, coe_discConj]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [discImage_mul, discConjMat_apply_zero_zero, discConjMat_apply_zero_one,
      discConjMat_apply_one_zero, discConjMat_apply_one_one, Submonoid.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    field_simp <;> ring

end Conjugation

section Action

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable (h : ℕ) (ψ : ℚ_[p] →+* K) {UK : Subgroup Kˣ} {ρ : ℝ}
  (κ : AnalyticWeight UK (M1Kh h ψ) ρ)

/-- **The disc action of `M₁`** ([LWX, (2.3.2)] on `OB_{qp^{-m}}`): the block operator whose
`(a, b)` block is the single-disc weight action of `δ' = discConj h δ a` when `b` is the image
disc `discImage h δ a`, and `0` otherwise. -/
def discSlash (δ : M1 p) : c(ZMod (p ^ h) × ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K) :=
  blockOp fun a b => if b = discImage h δ a then κ.kappaSlash (discConjK h δ a ψ) else 0

omit [CharZero K] in
theorem matrixCoeff_discSlash (δ : M1 p) (a b : ZMod (p ^ h)) (m n : ℕ) :
    matrixCoeff (discSlash h ψ κ δ) (a, m) (b, n)
      = if b = discImage h δ a then matrixCoeff (κ.kappaSlash (discConjK h δ a ψ)) m n else 0 := by
  rw [discSlash, matrixCoeff_blockOp]
  split_ifs with hb
  · rfl
  · exact matrixCoeff_zero m n

omit [CharZero K] in
/-- The `a`-th block of a block operator, applied to a vector. -/
private theorem blockProj_blockOp (T : ZMod (p ^ h) → ZMod (p ^ h) → (c(ℕ, K) →L[K] c(ℕ, K)))
    (f : c(ZMod (p ^ h) × ℕ, K)) (a : ZMod (p ^ h)) :
    cSpace.blockProj a (blockOp T f) = ∑ b : ZMod (p ^ h), T a b (cSpace.blockProj b f) := by
  have hf : blockOp T f = ∑ a' : ZMod (p ^ h), ∑ b : ZMod (p ^ h),
      cSpace.blockIncl a' (T a' b (cSpace.blockProj b f)) := by
    rw [blockOp]
    simp only [sum_apply, ContinuousLinearMap.comp_apply]
  rw [hf, map_sum, Finset.sum_eq_single a]
  · rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [cSpace.blockProj_blockIncl, if_pos rfl]
  · intro a' _ hne
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => by
      rw [cSpace.blockProj_blockIncl, if_neg fun heq => hne heq.symm]
  · exact fun hcon => absurd (Finset.mem_univ a) hcon

omit [CharZero K] in
theorem blockProj_discSlash (δ : M1 p) (f : c(ZMod (p ^ h) × ℕ, K)) (a : ZMod (p ^ h)) :
    cSpace.blockProj a (discSlash h ψ κ δ f)
      = κ.kappaSlash (discConjK h δ a ψ) (cSpace.blockProj (discImage h δ a) f) := by
  rw [discSlash, blockProj_blockOp, Finset.sum_eq_single (discImage h δ a)]
  · rw [if_pos rfl]
  · intro b _ hne
    rw [if_neg hne, zero_apply]
  · exact fun hcon => absurd (Finset.mem_univ _) hcon

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The conjugate of the identity is the identity. -/
theorem discConjK_one (a : ZMod (p ^ h)) : discConjK h (1 : M1 p) a ψ = 1 := by
  refine Subtype.ext ?_
  rw [coe_discConjK, discConj_one, Submonoid.coe_one, map_one]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The `K`-side matrix cocycle. -/
theorem discConjK_mul (δ₁ δ₂ : M1 p) (a : ZMod (p ^ h)) :
    discConjK h (δ₁ * δ₂) a ψ
      = discConjK h δ₁ (discImage h δ₂ a) ψ * discConjK h δ₂ a ψ := by
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, coe_discConjK, coe_discConjK, coe_discConjK, discConj_mul,
    Submonoid.coe_mul, map_mul]

omit [CharZero K] in
theorem discSlash_one : discSlash h ψ κ 1 = ContinuousLinearMap.id K c(ZMod (p ^ h) × ℕ, K) := by
  refine ContinuousLinearMap.ext fun f => DFunLike.ext _ _ fun x => ?_
  obtain ⟨a, m⟩ := x
  have hb := blockProj_discSlash h ψ κ 1 f a
  rw [discImage_one, discConjK_one, AnalyticWeight.kappaSlash_one] at hb
  exact DFunLike.congr_fun hb m

omit [CharZero K] in
/-- **The right-action law** (`blockOp_comp`, `discImage_mul`, `discConj_mul`,
`AnalyticWeight.kappaSlash_mul`). -/
theorem discSlash_mul (δ₁ δ₂ : M1 p) :
    discSlash h ψ κ (δ₁ * δ₂) = (discSlash h ψ κ δ₂).comp (discSlash h ψ κ δ₁) := by
  rw [discSlash, discSlash, discSlash, blockOp_comp]
  refine congrArg blockOp (funext fun a => funext fun c => ?_)
  rw [Finset.sum_eq_single (discImage h δ₂ a)]
  · rw [if_pos rfl, discImage_mul, discConjK_mul, AnalyticWeight.kappaSlash_mul]
    split_ifs with hc
    · rfl
    · rw [ContinuousLinearMap.comp_zero]
  · intro b _ hne
    rw [if_neg hne, ContinuousLinearMap.zero_comp]
  · exact fun hcon => absurd (Finset.mem_univ _) hcon

set_option warn.classDefReducibility false in
/-- The disc model as a right `M₁`-module — the level-`h` form of [LWX, (2.3.2)]. -/
@[instance_reducible]
def discSlashAction : RightSlashAction (M1 p) c(ZMod (p ^ h) × ℕ, K) where
  slash f δ := discSlash h ψ κ δ f
  zero_slash δ := map_zero (discSlash h ψ κ δ)
  slash_one f := by rw [discSlash_one]; rfl
  slash_mul f δ₁ δ₂ := by rw [discSlash_mul]; rfl
  add_slash f g δ := map_add (discSlash h ψ κ δ) f g

set_option warn.classDefReducibility false in
set_option linter.defProp false in
/-- The disc action commutes with scalars. -/
def discSMulSlashClass :
    letI := discSlashAction h ψ κ
    RightSlashAction.SMulSlashClass K (M1 p) c(ZMod (p ^ h) × ℕ, K) :=
  letI := discSlashAction h ψ κ
  ⟨fun r f δ => map_smul (discSlash h ψ κ δ) r f⟩

/-- A natural number has norm at most one in `ℚ_p`. -/
private theorem norm_natCast_le_one (n : ℕ) : ‖((n : ℕ) : ℚ_[p])‖ ≤ 1 := by
  rw [show ((n : ℕ) : ℚ_[p]) = ((n : ℤ_[p]) : ℚ_[p]) from by push_cast; ring,
    ← PadicInt.norm_def]
  exact PadicInt.norm_le_one _

include h κ in
omit [CharZero K] in
/-- The level bounds force `ψ` to contract the unit ball: `‖ψ y‖ ≤ 1` for `‖y‖ ≤ 1`
(apply `LevelBounds.integral` to the diagonal matrix `!![y, 0; 0, 1] ∈ M_h`). -/
theorem norm_map_le_one {y : ℚ_[p]} (hy : ‖y‖ ≤ 1) : ‖ψ y‖ ≤ 1 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [map_zero, norm_zero]
    exact zero_le_one
  · have hMh : !![y, 0; 0, 1] ∈ Mh p h := by
      refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [hy]
      · show ‖(0 : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)
        rw [norm_zero]
        positivity
      · show ‖(1 : ℚ_[p])‖ = 1
        exact norm_one
      · rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
        exact hy0
    have hmem : (RingHom.mapMatrix ψ) !![y, 0; 0, 1] ∈ M1Kh h ψ := ⟨_, hMh, rfl⟩
    have hb := κ.toWeightSeries.bounds.integral hmem 0 0
    simpa using hb

include h κ in
omit [CharZero K] in
/-- The level bounds force `‖ψ p‖ < 1` (apply `LevelBounds.c_le` to `!![1, 0; p^{h+1}, 1]`). -/
theorem norm_map_p_lt_one : ‖ψ ((p : ℕ) : ℚ_[p])‖ < 1 := by
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_le
  have hpn : ‖((p : ℕ) : ℚ_[p]) ^ (h + 1)‖ = (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [norm_pow, Padic.norm_p]
  have hpn1 : ‖((p : ℕ) : ℚ_[p]) ^ (h + 1)‖ ≤ 1 := by
    rw [hpn]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1R)
  have hMh : !![1, 0; ((p : ℕ) : ℚ_[p]) ^ (h + 1), 1] ∈ Mh p h := by
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · show ‖(1 : ℚ_[p])‖ ≤ 1
        exact le_of_eq norm_one
      · show ‖(0 : ℚ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      · show ‖((p : ℕ) : ℚ_[p]) ^ (h + 1)‖ ≤ 1
        exact hpn1
      · show ‖(1 : ℚ_[p])‖ ≤ 1
        exact le_of_eq norm_one
    · show ‖((p : ℕ) : ℚ_[p]) ^ (h + 1)‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)
      exact le_of_eq hpn
    · show ‖(1 : ℚ_[p])‖ = 1
      exact norm_one
    · rw [Matrix.det_fin_two_of, mul_one, zero_mul, sub_zero]
      exact one_ne_zero
  have hmem : (RingHom.mapMatrix ψ) !![1, 0; ((p : ℕ) : ℚ_[p]) ^ (h + 1), 1] ∈ M1Kh h ψ :=
    ⟨_, hMh, rfl⟩
  have hc := κ.toWeightSeries.bounds.c_le hmem
  have hc' : ‖ψ ((p : ℕ) : ℚ_[p])‖ ^ (h + 1) ≤ ρ := by
    rw [← norm_pow, ← map_pow]
    simpa using hc
  refine lt_of_pow_lt_pow_left₀ (h + 1) zero_le_one ?_
  rw [one_pow]
  exact hc'.trans_lt κ.toWeightSeries.bounds.rho_lt_one

include h κ in
omit [CharZero K] in
/-- `‖ψ y‖ ≤ ‖ψ p‖` for `‖y‖ ≤ p⁻¹` (write `y = p·(y/p)` and apply `norm_map_le_one`). -/
theorem norm_map_le_norm_map_p {y : ℚ_[p]} (hy : ‖y‖ ≤ (p : ℝ)⁻¹) :
    ‖ψ y‖ ≤ ‖ψ ((p : ℕ) : ℚ_[p])‖ := by
  have hpne : ((p : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hyq : ‖y / ((p : ℕ) : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p,
      div_le_one (inv_pos.mpr (by exact_mod_cast hp.out.pos))]
    exact hy
  calc ‖ψ y‖ = ‖ψ ((p : ℕ) : ℚ_[p])‖ * ‖ψ (y / ((p : ℕ) : ℚ_[p]))‖ := by
        rw [← norm_mul, ← map_mul, mul_div_cancel₀ _ hpne]
    _ ≤ ‖ψ ((p : ℕ) : ℚ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_map_le_one h ψ κ hyq) (norm_nonneg _)
    _ = ‖ψ ((p : ℕ) : ℚ_[p])‖ := mul_one _

omit [CharZero K] in
/-- **`U_p` is compactoid on the disc model** ([Buzzard, Lemma 12.2] blockwise): if `‖a‖ ≤ p⁻¹`
then every conjugate `δ'` has `‖a'‖ ≤ ‖a‖ + ‖a'δ₁₀‖ ≤ max(p⁻¹, ρ)`, so every block is compactoid
(`AnalyticWeight.isCompactoid_kappaSlash`) and hence so is the block operator. -/
theorem isCompactoid_discSlash (_hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1) {δ : M1 p}
    (hδ : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0‖ ≤ (p : ℝ)⁻¹) :
    IsCompactoid (discSlash h ψ κ δ) := by
  have hp1 := norm_map_p_lt_one h ψ κ
  have hρ1 : ρ < 1 := lt_of_le_of_lt (le_max_left _ _) hσ
  refine isCompactoid_blockOp (T := fun a b => if b = discImage h δ a then
    κ.kappaSlash (discConjK h δ a ψ) else 0) fun a b => ?_
  split_ifs with hb
  · rw [AnalyticWeight.kappaSlash_def]
    refine κ.toWeightSeries.isCompactoid_kappaSlash _ (σ := max ρ ‖ψ ((p : ℕ) : ℚ_[p])‖)
      (le_max_left _ _) (max_lt hρ1 hp1) (le_max_of_le_right ?_)
    show ‖ψ ((discConj h δ a : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0)‖ ≤ _
    rw [coe_discConj, discConjMat_apply_zero_zero]
    refine norm_map_le_norm_map_p h ψ κ ?_
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hδ ?_)
    rw [norm_neg, norm_mul]
    refine (mul_le_mul_of_nonneg_right (norm_natCast_le_one _) (norm_nonneg _)).trans ?_
    rw [one_mul]
    exact δ.2.2.1
  · exact isCompactoid_zero

end Action

section Evaluation

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

omit [CharZero K] in
/-- **The weight action, evaluated**: the generating series of the slashed sequence is the
automorphy factor times the composite with the Möbius series
(`WeightSeries.kappaSlash_apply`, `evalAt_mul`, `evalAt_pow`). -/
theorem evalAt_mk_kappaSlash {UK : Subgroup Kˣ} {S : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    {ρ : ℝ} (κ : AnalyticWeight UK S ρ) (g : S) (f : c(ℕ, K)) {w : K} (hw : ‖w‖ ≤ 1) :
    evalAt (PowerSeries.mk fun j => κ.kappaSlash g f j) w
      = evalAt (κ.toWeightSeries.autFactor g.1) w
        * evalAt (PowerSeries.mk fun i => f i) (evalAt (mobius g.1) w) := by
  set W := κ.toWeightSeries with hW
  set A := W.autFactor g.1 with hA
  set m := mobius g.1 with hm
  have hAS : PowerSeries.AbsSummable A := W.absSummable_autFactor g.2
  have hmS : PowerSeries.AbsSummable m := W.absSummable_mobius g.2
  have hcoef1 : ∀ i j : ℕ, ‖PowerSeries.coeff j (A * m ^ i)‖ ≤ 1 := fun i j => by
    rw [hA, hm, ← W.yCoeff_genFun (W.bounds.d_ne_zero g.2) i, coeff_yCoeff]
    exact W.norm_coeff_genFun_le_one g.2 j i
  have hbound : ∀ j i : ℕ,
      ‖PowerSeries.coeff j (A * m ^ i) * f i * w ^ j‖ ≤ ‖f i‖ := by
    intro j i
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖PowerSeries.coeff j (A * m ^ i)‖ * ‖f i‖ * ‖w‖ ^ j
        ≤ 1 * ‖f i‖ * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hcoef1 i j) (norm_nonneg _))
            (pow_le_one₀ (norm_nonneg _) hw) (by positivity) (by positivity)
      _ = ‖f i‖ := by rw [one_mul, mul_one]
  have hJ : ∀ i : ℕ, Summable fun j : ℕ =>
      ‖PowerSeries.coeff j (A * m ^ i) * f i * w ^ j‖ := by
    intro i
    have hsum := summable_norm_evalAt
      (PowerSeries.absSummable_mul hAS (PowerSeries.absSummable_pow hmS i)) hw
    refine (hsum.mul_right ‖f i‖).of_nonneg_of_le (fun _ => norm_nonneg _) fun j => ?_
    rw [show PowerSeries.coeff j (A * m ^ i) * f i * w ^ j
        = PowerSeries.coeff j (A * m ^ i) * w ^ j * f i from by ring, norm_mul]
  have htend : Filter.Tendsto (Function.uncurry fun j i : ℕ =>
      PowerSeries.coeff j (A * m ^ i) * f i * w ^ j) Filter.cofinite (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    rw [Filter.eventually_cofinite]
    have hIfin : {i : ℕ | ¬ ‖f i‖ < ε}.Finite := by
      have h0 := (cSpace.tendsto_cofinite f).norm
      rw [norm_zero] at h0
      have h1 := h0.eventually_mem (Iio_mem_nhds hε)
      rw [Filter.eventually_cofinite] at h1
      simpa using h1
    have hJfin : ∀ i : ℕ, {j : ℕ | ¬ ‖PowerSeries.coeff j (A * m ^ i) * f i * w ^ j‖
        < ε}.Finite := by
      intro i
      have h2 := (hJ i).tendsto_cofinite_zero.eventually_mem (Iio_mem_nhds hε)
      rw [Filter.eventually_cofinite] at h2
      simpa using h2
    refine Set.Finite.subset (Set.Finite.biUnion hIfin fun i _ =>
      (hJfin i).prod (Set.finite_singleton i)) ?_
    rintro ⟨j, i⟩ hpair
    simp only [Set.mem_ofPred_eq, Function.uncurry] at hpair
    have hi : ¬ ‖f i‖ < ε := fun hlt => hpair ((hbound j i).trans_lt hlt)
    exact Set.mem_biUnion hi (Set.mem_prod.mpr ⟨hpair, rfl⟩)
  have huncurry : Summable (Function.uncurry fun j i : ℕ =>
      PowerSeries.coeff j (A * m ^ i) * f i * w ^ j) :=
    TateFredholm.summable_of_tendsto_cofinite htend
  have hterm : ∀ j : ℕ,
      PowerSeries.coeff j (PowerSeries.mk fun j => κ.kappaSlash g f j) * w ^ j
        = ∑' i, PowerSeries.coeff j (A * m ^ i) * f i * w ^ j := fun j => by
    rw [PowerSeries.coeff_mk, AnalyticWeight.kappaSlash_def, WeightSeries.kappaSlash_apply,
      tsum_mul_right]
  have hinner : ∀ i : ℕ, (∑' j, PowerSeries.coeff j (A * m ^ i) * f i * w ^ j)
      = evalAt A w * (f i * evalAt m w ^ i) := by
    intro i
    rw [tsum_congr fun j => show PowerSeries.coeff j (A * m ^ i) * f i * w ^ j
        = PowerSeries.coeff j (A * m ^ i) * w ^ j * f i from by ring, tsum_mul_right,
      ← evalAt, evalAt_mul hAS (PowerSeries.absSummable_pow hmS i) hw, evalAt_pow hmS hw]
    ring
  rw [evalAt, tsum_congr hterm,
    ← Summable.tsum_comm (f := fun j i : ℕ => PowerSeries.coeff j (A * m ^ i) * f i * w ^ j)
      huncurry,
    tsum_congr hinner, tsum_mul_left, evalAt]
  exact congrArg _ (tsum_congr fun i => by rw [PowerSeries.coeff_mk])

variable (h : ℕ) (ψ : ℚ_[p] →+* K) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **The disc action is [LWX, (2.3.2)] pointwise**:
`(f ∣ δ)(z) = [cz + d](T₀)·f(möb δ z)` for every `z ∈ ℤ_p`.

Proof: on the disc of `z` the action is the single-disc action of `δ' = discConj h δ (disc z)`
(`blockProj_discSlash`), whose evaluation is `evalAt (autFactor ψδ') (ψ w)·(f_{a'} at möb δ' w)`
(`evalAt_mk_kappaSlash`); the automorphy factor evaluates to `κ_{T₀,h}(c'w + d') = κ_{T₀,h}(cz+d)`
(`evalAt_autFactor_haloWeightH`, `denUnit_discConj`, `haloCharFunH_psi`), and the argument is
`möb δ z` by the conjugation identity `mobiusFun_add_pow_mul`. -/
theorem discEval_discSlash (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) (δ : M1 p)
    (f : c(ZMod (p ^ h) × ℕ, K)) (z : ℤ_[p]) :
    discEval ψ h (discSlash h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) δ f) z
      = HaloInt.specialize (intHom ψ) T₀ (univChar ω ((M1.toLocalMat δ).denUnit z))
        * discEval ψ h f ((M1.toLocalMat δ).mobiusFun z) := by
  have hpne : ((p : ℤ_[p]) ^ h) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hdiscEval : ∀ (F : c(ZMod (p ^ h) × ℕ, K)) (x : ℤ_[p]),
      discEval ψ h F x
        = evalAt (PowerSeries.mk fun k => F (PadicInt.toZModPow h x, k))
            (intHom ψ (discCoord h x)) := fun _ _ => rfl
  obtain ⟨κ, hκ⟩ : ∃ κ' : AnalyticWeight (haloUnitsH h ψ) (M1Kh h ψ) (haloRhoH p h T₀),
      κ' = haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a' : ZMod (p ^ h), a' = PadicInt.toZModPow h z := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u' : ℤ_[p], u' = discCoord h z := ⟨_, rfl⟩
  rw [← hκ]
  have hzsplit : ((a.val : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ h * u = z := by
    rw [ha, hu, val_toZModPow]
    exact appr_add_pow_mul_discCoord h z
  have hwK : ‖intHom ψ u‖ ≤ 1 := by
    rw [norm_intHom ψ hψ]
    exact PadicInt.norm_le_one _
  have hdenK : (discConjK h δ a ψ : Matrix (Fin 2) (Fin 2) K) 1 0 * intHom ψ u
      + (discConjK h δ a ψ : Matrix (Fin 2) (Fin 2) K) 1 1
      = intHom ψ (((M1.toLocalMat δ).denUnit z : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [coe_discConjK, ← intHom_denUnit ψ (discConj h δ a) u]
    congr 1
    rw [denUnit_discConj h δ a u, hzsplit]
  have hfst : evalAt (κ.toWeightSeries.autFactor (discConjK h δ a ψ).1) (intHom ψ u)
      = HaloInt.specialize (intHom ψ) T₀ (univChar ω ((M1.toLocalMat δ).denUnit z)) := by
    rw [hκ, evalAt_autFactor_haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT (discConjK h δ a ψ) hwK,
      hdenK, haloCharFunH_psi h ψ T₀ ω hp2 hψ h0 h1 hT]
  have hidx : PadicInt.toZModPow h ((M1.toLocalMat δ).mobiusFun z) = discImage h δ a := by
    rw [toZModPow_mobiusFun, ha]
  have hcoord : discCoord h ((M1.toLocalMat δ).mobiusFun z)
      = (M1.toLocalMat (discConj h δ a)).mobiusFun u := by
    have hmobsplit : (M1.toLocalMat δ).mobiusFun z
        = ((((discImage h δ a).val : ℕ)) : ℤ_[p])
          + (p : ℤ_[p]) ^ h * (M1.toLocalMat (discConj h δ a)).mobiusFun u := by
      rw [← hzsplit]
      exact mobiusFun_add_pow_mul h δ a u
    have happ : ((((M1.toLocalMat δ).mobiusFun z).appr h : ℕ) : ℤ_[p])
        = ((((discImage h δ a).val : ℕ)) : ℤ_[p]) := by
      rw [← val_toZModPow h ((M1.toLocalMat δ).mobiusFun z), hidx]
    have hsp : ((((discImage h δ a).val : ℕ)) : ℤ_[p])
        + (p : ℤ_[p]) ^ h * discCoord h ((M1.toLocalMat δ).mobiusFun z)
        = ((((discImage h δ a).val : ℕ)) : ℤ_[p])
          + (p : ℤ_[p]) ^ h * (M1.toLocalMat (discConj h δ a)).mobiusFun u := by
      rw [← hmobsplit, ← happ]
      exact appr_add_pow_mul_discCoord h ((M1.toLocalMat δ).mobiusFun z)
    exact mul_left_cancel₀ hpne (add_left_cancel hsp)
  have hsnd : evalAt (PowerSeries.mk fun i => cSpace.blockProj (discImage h δ a) f i)
        (evalAt (mobius (discConjK h δ a ψ).1) (intHom ψ u))
      = discEval ψ h f ((M1.toLocalMat δ).mobiusFun z) := by
    rw [hdiscEval f ((M1.toLocalMat δ).mobiusFun z), hidx, hcoord, coe_discConjK,
      ← intHom_mobiusFun ψ hψ (discConj h δ a) u]
    rfl
  have hmkeq : (PowerSeries.mk fun k => (discSlash h ψ κ δ f) (a, k))
      = PowerSeries.mk (fun k => κ.kappaSlash (discConjK h δ a ψ)
          (cSpace.blockProj (discImage h δ a) f) k) :=
    PowerSeries.ext fun k => by
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      exact DFunLike.congr_fun (blockProj_discSlash h ψ κ δ f a) k
  rw [hdiscEval (discSlash h ψ κ δ f) z, ← ha, ← hu, hmkeq,
    evalAt_mk_kappaSlash κ (discConjK h δ a ψ) _ hwK, hfst, hsnd]

end Evaluation

end LWX

end
