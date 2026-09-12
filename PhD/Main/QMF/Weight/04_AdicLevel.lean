/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.Weight.«03_SlashAction»
import PhD.Main.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Wild levels at a finite place — SKELETON (slopes-hecke board)

The general layer states its levels with *norms* (`QMF.SigmaNorm`, `QMF.LevelBounds`), while
the classical description of `Σ₀(γ)`, `Σ₁(p^k)` is by the *valuation*.  On a `Valued` field
whose norm comes from a rank-one valuation the two are interchangeable, and mathlib already
provides the dictionary: `Valued.toNormedField.norm_le_iff : ‖x‖ ≤ ‖y‖ ↔ v x ≤ v y`, together
with `norm_le_one_iff`, `one_le_norm_iff`, `norm_lt_one_iff`.  This file records the
consequences the weight layer needs, so that no application has to re-prove them by hand (the
Jacobs fork's `norm_le_of_valued_le` / `norm_eq_one_of_valued_eq_one` are retired in favour of
these).

## Main declarations

* `QMF.Sigma0'.levelBounds_valued` — `LevelBounds (Sigma0' K γ hγ) ‖y‖` for any `y` of
  valuation `γ`, at a `Valued` field with a rank-one valuation.
* `QMF.SigmaOne` — the `Σ₁`-type level `{integral, ‖c‖ ≤ ρ², ‖d − 1‖ ≤ ρ}` (the norm form of
  [Jacobs, §2.1 p. 29]'s "`c ≡ 0 mod p²`, `d ≡ 1 mod p`"), with `levelBounds_sigmaOne`.
* `QMF.mem_sigmaOne_iff_valued` — the same level described by the valuation (no `ϖ ≠ 0`
  hypothesis is needed: the norm/valuation dictionary is unconditional).
-/

open scoped WithZero

namespace QMF

section Valued

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]
  [Valuation.RankOne (Valued.v : Valuation K Γ₀)]

open scoped Valued

/-- **The level bounds of `Σ₀'(γ)` at a valued field**: with `ρ = ‖y‖` for any `y` of valuation
`γ`, the norm-form bounds hold — the dictionary is mathlib's `Valued.toNormedField.norm_le_iff`
(the norm is the rank-one image of the valuation, which is strictly monotone). -/
theorem Sigma0'.levelBounds_valued {γ : Γ₀} (hγ : γ < 1) {y : K} (hy : Valued.v y = γ) :
    LevelBounds (Sigma0' K γ hγ) ‖y‖ := by
  have hy1 : ‖y‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr (hy ▸ hγ)
  refine Sigma0'.levelBounds (norm_nonneg _) hy1 (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact Valued.toNormedField.norm_le_one_iff.mpr hx
  · exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr hx.le)
      (Valued.toNormedField.one_le_norm_iff.mpr hx.ge)
  · exact Valued.toNormedField.norm_le_iff.mpr (hy ▸ hx)

end Valued

section SigmaOne

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **The `Σ₁`-type wild level in norm form** ([Jacobs, §2.1 p. 29]: "in all cases of
`(a b; c d)` that we will calculate with, `c ≡ 0 mod 9` and `d ≡ 1 mod 9`"): integral entries,
`‖c‖ ≤ ρ²` and `‖d − 1‖ ≤ ρ`.  The Jacobs fork's `sigma1Norm` is the case `ρ = ‖3‖`. -/
def SigmaOne (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) K) where
  carrier := {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ^ 2 ∧ ‖g 1 1 - 1‖ ≤ ρ}
  one_mem' := by
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Matrix.one_apply_ne hij]
    · simp only [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), norm_zero]
      positivity
    · simp [hρ0]
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    have hsq : ρ ^ 2 ≤ ρ := by nlinarith
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
        · rw [norm_mul]
          exact mul_le_one₀ (hg1 _ _) (norm_nonneg _) (hh1 _ _)
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul]
      · exact (mul_le_mul hg2 (hh1 0 0) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
      · exact (mul_le_mul (hg1 1 1) hh2 (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · have hexp : (g * h) 1 1 - 1
          = g 1 0 * h 0 1 + ((g 1 1 - 1) * (h 1 1 - 1) + ((g 1 1 - 1) + (h 1 1 - 1))) := by
        rw [Matrix.mul_apply, Fin.sum_univ_two]
        ring
      rw [hexp]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        exact (mul_le_mul (hg2.trans hsq) (hh1 0 1) (norm_nonneg _) hρ0).trans_eq (mul_one _)
      · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · rw [norm_mul]
          exact (mul_le_mul hg3 (hh3.trans hρ.le) (norm_nonneg _) hρ0).trans_eq (mul_one _)
        · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hg3 hh3)

variable {K}

theorem levelBounds_sigmaOne {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    LevelBounds (SigmaOne K ρ hρ0 hρ) ρ where
  rho_nonneg := hρ0
  rho_lt_one := hρ
  integral hg := hg.1
  c_le hg := hg.2.1.trans (by nlinarith)
  d_unit := fun {g} hg => by
    have h : ‖g 1 1 - 1‖ < 1 := hg.2.2.trans_lt hρ
    rw [show g 1 1 = 1 + (g 1 1 - 1) by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne'),
      norm_one, max_eq_left h.le]

end SigmaOne

section SigmaOneValued

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]
  [Valuation.RankOne (Valued.v : Valuation K Γ₀)]

open scoped Valued

/-- **The `Σ₁`-level in valuation form**: membership of `SigmaOne K ‖ϖ‖` is the classical
congruence description `v(g i j) ≤ 1`, `v(c) ≤ v(ϖ)²`, `v(d − 1) ≤ v(ϖ)`. -/
theorem mem_sigmaOne_iff_valued {ϖ : K} (hϖ : Valued.v ϖ < 1)
    {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ SigmaOne K ‖ϖ‖ (norm_nonneg _) (Valued.toNormedField.norm_lt_one_iff.mpr hϖ) ↔
      (∀ i j, Valued.v (g i j) ≤ 1) ∧ Valued.v (g 1 0) ≤ Valued.v ϖ ^ 2 ∧
        Valued.v (g 1 1 - 1) ≤ Valued.v ϖ := by
  have hsq : ‖ϖ‖ ^ 2 = ‖ϖ ^ 2‖ := (norm_pow ϖ 2).symm
  have hvsq : Valued.v ϖ ^ 2 = Valued.v (ϖ ^ 2) := (map_pow Valued.v ϖ 2).symm
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i j => Valued.toNormedField.norm_le_one_iff.mp (h1 i j), ?_, ?_⟩
    · rw [hvsq]
      exact Valued.toNormedField.norm_le_iff.mp (hsq ▸ h2)
    · exact Valued.toNormedField.norm_le_iff.mp h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i j => Valued.toNormedField.norm_le_one_iff.mpr (h1 i j), ?_, ?_⟩
    · rw [hsq]
      exact Valued.toNormedField.norm_le_iff.mpr (hvsq ▸ h2)
    · exact Valued.toNormedField.norm_le_iff.mpr h3

end SigmaOneValued

end QMF
