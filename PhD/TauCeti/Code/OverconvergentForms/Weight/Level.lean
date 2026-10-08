/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Level monoids in norm form

For a nonarchimedean normed field `L` and `0 ≤ ρ < 1`, the monoid
`Σ(ρ) = {γ ∈ M₂(L) | ‖γ_{ij}‖ ≤ 1, ‖c‖ ≤ ρ, ‖d‖ = 1, det γ ≠ 0}` — Buzzard's `M_t` at `ρ = ‖ϖ‖^t`,
Jacobs's `Σ_α` at `ρ = ‖p‖^α` — the predicate `LevelBounds S ρ` on a submonoid `S ⊆ M₂(L)`, the
determinant bound `‖det γ‖ ≤ σ → ‖a‖ ≤ σ`, the units of `Σ(ρ)`, the element `η = diag(ϖ, 1)`, the
`Σ₁`-type levels, and the adjugate dictionary between the right-handed monoid `Σ(ρ)` and the
left-handed monoid `Σ₀(ρ)` of Pollack–Stevens.

[Buz07, §9, p. 68]: "define `M_t` to be the elements `(γ_j)` of `M₂(𝒪_p)` with the property
that if `γ_j = ((a_j b_j), (c_j d_j))` then `det(γ_j) ≠ 0`, `π_j^{t_j}` divides `c_j`, and `π_j`
does not divide `d_j`. Then `M_t` is a monoid under multiplication." [Jac03, Definition 1.27,
p. 19]: "Given `α ∈ ℕ`, let `Σ_α = {γ = ((a b), (c d)) ∈ M₂(ℤ_p) : p^α ∣ c, p ∤ d, det(γ) ≠ 0}`."

## Main definitions

* `AutomorphicForm.SigmaNorm L ρ hρ0 hρ`: the norm-form level monoid `Σ(ρ)`.
* `AutomorphicForm.LevelBounds S ρ`: the bounds a level submonoid must satisfy.
* `AutomorphicForm.eta ϖ`: the matrix `diag(ϖ, 1)`.
* `AutomorphicForm.SigmaOne L ρ hρ0 hρ`: the `Σ₁`-type level `‖c‖ ≤ ρ²`, `‖d − 1‖ ≤ ρ`.
* `AutomorphicForm.Sigma0 L ρ hρ0 hρ`: the left-handed monoid `‖a‖ = 1`, `‖c‖ ≤ ρ`.
* `AutomorphicForm.adjugateEquiv`: `Σ(ρ)ᵐᵒᵖ ≃* Σ₀(ρ)` by the adjugate.

## Main results

* `AutomorphicForm.LevelBounds.norm_apply_zero_zero_le_of_norm_det_le`: the determinant bound.
* `AutomorphicForm.isUnit_sigmaNorm_iff`: the units of `Σ(ρ)` are the elements with `‖det‖ = 1`.
* `AutomorphicForm.not_isUnit_eta`: `η` is not a unit.
* `AutomorphicForm.adjugate_mem_sigma0_iff`: the adjugate exchanges `Σ(ρ)` and `Σ₀(ρ)`.

Roadmap: §1.1.1–§1.1.4. Tau Ceti home: `TauCeti/NumberTheory/AutomorphicForm/Weight/Level.lean`.
-/

open Matrix

namespace Matrix

variable {R : Type*} [CommRing R]

/-- In dimension `2` the adjugate preserves the determinant. -/
theorem det_adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) R) : (adjugate A).det = A.det := by
  rw [det_adjugate]
  simp

/-- In dimension `2` the adjugate is an involution. -/
theorem adjugate_adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) R) : adjugate (adjugate A) = A := by
  rw [adjugate_adjugate A (by simp)]
  simp

end Matrix

namespace AutomorphicForm

variable (L : Type*) [NormedField L] [IsUltrametricDist L]

/-- **The norm-form level monoid** `Σ(ρ)`: integral entries, `‖c‖ ≤ ρ`, `‖d‖ = 1`, nonzero
determinant. Source: [Buz07, §9, p. 68]; [Jac03, Definition 1.27]. -/
def SigmaNorm (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) L) where
  carrier := {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0}
  one_mem' := by
    refine ⟨fun i j => ?_, by simpa using hρ0, by simp, by simp⟩
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply_ne, *]
  mul_mem' := by
    rintro g h ⟨hgint, hgc, hgd, hgdet⟩ ⟨hhint, hhc, hhd, hhdet⟩
    have hsum : ∀ i j, (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := fun i j => by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨fun i j => ?_, ?_, ?_, by simp [hgdet, hhdet]⟩
    · rw [hsum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
        exact (norm_mul_le _ _).trans (mul_le_one₀ (hgint _ _) (norm_nonneg _) (hhint _ _))
    · rw [hsum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact (norm_mul_le _ _).trans
          ((mul_le_of_le_one_right (norm_nonneg _) (hhint 0 0)).trans hgc)
      · simpa [hgd] using hhc
    · have hlt : ‖g 1 0 * h 0 1‖ < ‖g 1 1 * h 1 1‖ := by
        simpa [hgd, hhd] using
          ((mul_le_of_le_one_right (norm_nonneg _) (hhint 0 1)).trans hgc).trans_lt hρ
      rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne,
        max_eq_right hlt.le, norm_mul, hgd, hhd, mul_one]

variable {L}

theorem mem_sigmaNorm_iff {ρ : ℝ} {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g ∈ SigmaNorm L ρ hρ0 hρ ↔
      (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0 :=
  Iff.rfl

/-- **The level bounds** of a submonoid `S ⊆ M₂(L)` at radius `ρ`: every member has integral
entries, `‖c‖ ≤ ρ`, `‖d‖ = 1` and nonzero determinant, and `0 ≤ ρ < 1`. Equivalently
`S ≤ SigmaNorm L ρ`. Source: roadmap §1.1.1. -/
structure LevelBounds (S : Submonoid (Matrix (Fin 2) (Fin 2) L)) (ρ : ℝ) : Prop where
  rho_nonneg : 0 ≤ ρ
  rho_lt_one : ρ < 1
  integral : ∀ {g}, g ∈ S → ∀ i j, ‖g i j‖ ≤ 1
  c_le : ∀ {g}, g ∈ S → ‖g 1 0‖ ≤ ρ
  d_unit : ∀ {g}, g ∈ S → ‖g 1 1‖ = 1
  det_ne_zero : ∀ {g}, g ∈ S → g.det ≠ 0

variable {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}

theorem levelBounds_sigmaNorm (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : LevelBounds (SigmaNorm L ρ hρ0 hρ) ρ :=
  ⟨hρ0, hρ, fun hg => hg.1, fun hg => hg.2.1, fun hg => hg.2.2.1, fun hg => hg.2.2.2⟩

omit [IsUltrametricDist L] in
theorem LevelBounds.mono {T : Submonoid (Matrix (Fin 2) (Fin 2) L)} (hb : LevelBounds T ρ)
    (hST : S ≤ T) : LevelBounds S ρ :=
  ⟨hb.rho_nonneg, hb.rho_lt_one, fun hg => hb.integral (hST hg), fun hg => hb.c_le (hST hg),
    fun hg => hb.d_unit (hST hg), fun hg => hb.det_ne_zero (hST hg)⟩

omit [IsUltrametricDist L] in
/-- Level bounds at `ρ` are level bounds at every `ρ ≤ ρ' < 1`. -/
theorem LevelBounds.mono_radius (hb : LevelBounds S ρ) {ρ' : ℝ} (hρρ' : ρ ≤ ρ') (hρ' : ρ' < 1) :
    LevelBounds S ρ' :=
  ⟨hb.rho_nonneg.trans hρρ', hρ', fun hg => hb.integral hg, fun hg => (hb.c_le hg).trans hρρ',
    fun hg => hb.d_unit hg, fun hg => hb.det_ne_zero hg⟩

theorem LevelBounds.le_sigmaNorm (hb : LevelBounds S ρ) :
    S ≤ SigmaNorm L ρ hb.rho_nonneg hb.rho_lt_one :=
  fun _ hg => ⟨hb.integral hg, hb.c_le hg, hb.d_unit hg, hb.det_ne_zero hg⟩

theorem LevelBounds.of_le (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (h : S ≤ SigmaNorm L ρ hρ0 hρ) :
    LevelBounds S ρ :=
  (levelBounds_sigmaNorm hρ0 hρ).mono h

omit [IsUltrametricDist L] in
theorem LevelBounds.d_ne_zero (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) :
    g 1 1 ≠ 0 := fun h0 => by
  simpa [h0] using hb.d_unit hg

theorem LevelBounds.norm_det_le_one (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L}
    (hg : g ∈ S) : ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_one₀ (hb.integral hg _ _) (norm_nonneg _) (hb.integral hg _ _)
  · rw [norm_neg, norm_mul]
    exact mul_le_one₀ (hb.integral hg _ _) (norm_nonneg _) (hb.integral hg _ _)

/-- On a level, `c z + d` is a unit of the valuation ring for every `z` in the closed unit ball:
`‖c z + d‖ = 1`. Source: roadmap §1.2.2 ("`c z + d ∈ 𝒪^×` because `‖c‖ < 1 = ‖d‖`"). -/
theorem LevelBounds.norm_mul_add_eq_one (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L}
    (hg : g ∈ S) {z : L} (hz : ‖z‖ ≤ 1) : ‖g 1 0 * z + g 1 1‖ = 1 := by
  have hd := hb.d_unit hg
  have hlt : ‖g 1 0 * z‖ < ‖g 1 1‖ := by
    rw [hd, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans_lt
      ((hb.c_le hg).trans_lt hb.rho_lt_one)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le, hd]

/-- **The determinant bound**: on a level, `‖det γ‖ ≤ σ` with `ρ ≤ σ` forces `‖a‖ ≤ σ`, since
`a d = det γ + b c` with `‖d‖ = 1` and `‖b c‖ ≤ ρ`. Source: roadmap §1.1.2; [Buz07, proof of
Lemma 12.2]. -/
theorem LevelBounds.norm_apply_zero_zero_le_of_norm_det_le (hb : LevelBounds S ρ) {σ : ℝ}
    (hρσ : ρ ≤ σ) {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (hdet : ‖g.det‖ ≤ σ) :
    ‖g 0 0‖ ≤ σ := by
  have hd : ‖g 1 1‖ = 1 := hb.d_unit hg
  have hkey : g 0 0 * g 1 1 = g.det + g 0 1 * g 1 0 := by
    rw [Matrix.det_fin_two]
    ring
  calc ‖g 0 0‖ = ‖g 0 0 * g 1 1‖ := by rw [norm_mul, hd, mul_one]
    _ = ‖g.det + g 0 1 * g 1 0‖ := by rw [hkey]
    _ ≤ max ‖g.det‖ ‖g 0 1 * g 1 0‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ σ := by
      refine max_le hdet ?_
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hb.integral hg 0 1)).trans
        ((hb.c_le hg).trans hρσ)

/-- The units of `Σ(ρ)` are its elements of determinant norm `1`. Source: roadmap §1.1.2. -/
theorem isUnit_sigmaNorm_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : SigmaNorm L ρ hρ0 hρ} :
    IsUnit g ↔ ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hb := levelBounds_sigmaNorm (L := L) hρ0 hρ
    have hmul : ((u : SigmaNorm L ρ hρ0 hρ) : Matrix (Fin 2) (Fin 2) L).det *
        ((↑u⁻¹ : SigmaNorm L ρ hρ0 hρ) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
      rw [← Matrix.det_mul, ← Submonoid.coe_mul, Units.mul_inv, Submonoid.coe_one, Matrix.det_one]
    have hu := hb.norm_det_le_one (u : SigmaNorm L ρ hρ0 hρ).2
    have hv := hb.norm_det_le_one (↑u⁻¹ : SigmaNorm L ρ hρ0 hρ).2
    have hn := congrArg norm hmul
    rw [norm_mul, norm_one] at hn
    refine le_antisymm hu (not_lt.mp fun hlt => ?_)
    have := mul_le_of_le_one_right (norm_nonneg
      ((u : SigmaNorm L ρ hρ0 hρ) : Matrix (Fin 2) (Fin 2) L).det) hv
    linarith
  · intro hdet
    obtain ⟨g, hg⟩ := g
    change ‖g.det‖ = 1 at hdet
    obtain ⟨hgint, hgc, hgd, hgdet⟩ := id hg
    have hdetinv : ‖(g.det)⁻¹‖ = 1 := by rw [norm_inv, hdet, inv_one]
    have ha : ‖g 0 0‖ = 1 := by
      have hkey : g 0 0 * g 1 1 = g.det + g 0 1 * g 1 0 := by
        rw [Matrix.det_fin_two]
        ring
      have hlt : ‖g 0 1 * g 1 0‖ < ‖g.det‖ := by
        rw [hdet, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hgint 0 1)).trans_lt (hgc.trans_lt hρ)
      have h1 : ‖g 0 0 * g 1 1‖ = 1 := by
        rw [hkey, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le,
          hdet]
      rwa [norm_mul, hgd, mul_one] at h1
    have hentry : ∀ i j, ‖((g.det)⁻¹ • g.adjugate) i j‖ = ‖g.adjugate i j‖ := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul, hdetinv, one_mul]
    have hmem : (g.det)⁻¹ • g.adjugate ∈ SigmaNorm L ρ hρ0 hρ := by
      refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
      · rw [hentry, Matrix.adjugate_fin_two]
        fin_cases i <;> fin_cases j <;> simp [hgint]
      · rw [hentry, Matrix.adjugate_fin_two]
        simpa using hgc
      · rw [hentry, Matrix.adjugate_fin_two]
        simpa using ha
      · rw [Matrix.det_smul, Matrix.det_adjugate_fin_two]
        simp [hgdet]
    refine isUnit_iff_exists.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_, Subtype.ext ?_⟩
    · show g * ((g.det)⁻¹ • g.adjugate) = 1
      rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hgdet, one_smul]
    · show ((g.det)⁻¹ • g.adjugate) * g = 1
      rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ hgdet, one_smul]

variable (L) in
/-- The matrix `η = diag(ϖ, 1)`. Source: roadmap §1.1.2; [Buz07, §12]. -/
def eta (ϖ : L) : Matrix (Fin 2) (Fin 2) L := !![ϖ, 0; 0, 1]

omit [IsUltrametricDist L] in
@[simp] theorem det_eta (ϖ : L) : (eta L ϖ).det = ϖ := by
  simp [eta, Matrix.det_fin_two_of]

theorem eta_mem_sigmaNorm {ϖ : L} (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    eta L ϖ ∈ SigmaNorm L ρ hρ0 hρ := by
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [eta, hϖ1]
  · simp [eta, hρ0]
  · simp [eta]
  · rw [det_eta]
    exact hϖ0

/-- `η` lies in every `Σ(ρ)` but is not a unit there when `‖ϖ‖ < 1`. Source: roadmap §1.1.2. -/
theorem not_isUnit_eta {ϖ : L} (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    ¬ IsUnit (⟨eta L ϖ, eta_mem_sigmaNorm hϖ0 hϖ1.le hρ0 hρ⟩ : SigmaNorm L ρ hρ0 hρ) := by
  rw [isUnit_sigmaNorm_iff]
  change ‖(eta L ϖ).det‖ ≠ 1
  rw [det_eta]
  exact hϖ1.ne

variable (L) in
/-- **The `Σ₁`-type level**: `‖c‖ ≤ ρ²` and `‖d − 1‖ ≤ ρ` inside `Σ(ρ)` — Jacobs's `Σ₁(p)`
(`c ≡ 0 mod p²`, `d ≡ 1 mod p`) at `ρ = ‖p‖`. Source: roadmap §1.1.3. -/
def SigmaOne (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) L) where
  carrier := {g | g ∈ SigmaNorm L ρ hρ0 hρ ∧ ‖g 1 0‖ ≤ ρ ^ 2 ∧ ‖g 1 1 - 1‖ ≤ ρ}
  one_mem' := by
    refine ⟨(SigmaNorm L ρ hρ0 hρ).one_mem, ?_, ?_⟩
    · rw [Matrix.one_apply_ne (by decide), norm_zero]
      positivity
    · rw [Matrix.one_apply_eq, sub_self, norm_zero]
      exact hρ0
  mul_mem' := by
    rintro g h ⟨hg, hgc, hgd⟩ ⟨hh, hhc, hhd⟩
    have hsum : ∀ i j, (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := fun i j => by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨(SigmaNorm L ρ hρ0 hρ).mul_mem hg hh, ?_, ?_⟩
    · rw [hsum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hh.1 0 0)).trans hgc
      · rw [norm_mul, hg.2.2.1, one_mul]
        exact hhc
    · have hkey : (g * h) 1 1 - 1 = g 1 0 * h 0 1 + (g 1 1 * (h 1 1 - 1) + (g 1 1 - 1)) := by
        rw [hsum]
        ring
      rw [hkey]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hh.1 0 1)).trans hg.2.1
      · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hgd)
        rw [norm_mul, hg.2.2.1, one_mul]
        exact hhd

theorem mem_sigmaOne_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g ∈ SigmaOne L ρ hρ0 hρ ↔ g ∈ SigmaNorm L ρ hρ0 hρ ∧ ‖g 1 0‖ ≤ ρ ^ 2 ∧ ‖g 1 1 - 1‖ ≤ ρ :=
  Iff.rfl

theorem sigmaOne_le_sigmaNorm (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    SigmaOne L ρ hρ0 hρ ≤ SigmaNorm L ρ hρ0 hρ := fun _ hg => hg.1

theorem levelBounds_sigmaOne (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : LevelBounds (SigmaOne L ρ hρ0 hρ) ρ :=
  (levelBounds_sigmaNorm hρ0 hρ).mono (sigmaOne_le_sigmaNorm hρ0 hρ)

variable (L) in
/-- **The left-handed monoid** `Σ₀(ρ) = {‖a‖ = 1, ‖c‖ ≤ ρ, integral, det ≠ 0}` of Pollack–Stevens.
Source: roadmap §1.1.4, convention 2. -/
def Sigma0 (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) L) where
  carrier := {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 0 0‖ = 1 ∧ g.det ≠ 0}
  one_mem' := by
    refine ⟨fun i j => ?_, by simpa using hρ0, by simp, by simp⟩
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply_ne, *]
  mul_mem' := by
    rintro g h ⟨hgint, hgc, hga, hgdet⟩ ⟨hhint, hhc, hha, hhdet⟩
    have hsum : ∀ i j, (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := fun i j => by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨fun i j => ?_, ?_, ?_, by simp [hgdet, hhdet]⟩
    · rw [hsum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
        exact (norm_mul_le _ _).trans (mul_le_one₀ (hgint _ _) (norm_nonneg _) (hhint _ _))
    · rw [hsum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact (norm_mul_le _ _).trans
          ((mul_le_of_le_one_right (norm_nonneg _) (hhint 0 0)).trans hgc)
      · exact (norm_mul_le _ _).trans
          ((mul_le_of_le_one_left (norm_nonneg _) (hgint 1 1)).trans hhc)
    · have hlt : ‖g 0 1 * h 1 0‖ < ‖g 0 0 * h 0 0‖ := by
        rw [norm_mul, norm_mul, hga, hha, mul_one]
        exact ((mul_le_of_le_one_left (norm_nonneg _) (hgint 0 1)).trans hhc).trans_lt hρ
      rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le,
        norm_mul, hga, hha, mul_one]

theorem mem_sigma0_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g ∈ Sigma0 L ρ hρ0 hρ ↔
      (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 0 0‖ = 1 ∧ g.det ≠ 0 :=
  Iff.rfl

/-- **The adjugate dictionary**: `adj ((a b), (c d)) = ((d −b), (−c a))` sends `Σ(ρ)` onto `Σ₀(ρ)`.
Source: roadmap §1.1.4. -/
theorem adjugate_mem_sigma0_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g.adjugate ∈ Sigma0 L ρ hρ0 hρ ↔ g ∈ SigmaNorm L ρ hρ0 hρ := by
  rw [mem_sigma0_iff, mem_sigmaNorm_iff, Matrix.det_adjugate_fin_two, Matrix.adjugate_fin_two]
  simp [Fin.forall_fin_two]
  tauto

theorem adjugate_mem_sigmaNorm_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g.adjugate ∈ SigmaNorm L ρ hρ0 hρ ↔ g ∈ Sigma0 L ρ hρ0 hρ := by
  rw [← adjugate_mem_sigma0_iff (g := g.adjugate), Matrix.adjugate_adjugate_fin_two]

variable (L) in
/-- **Right actions of `Σ(ρ)` are left actions of `Σ₀(ρ)` along the adjugate**: the
anti-automorphism `adj` of `M₂(L)` induces a monoid isomorphism `Σ(ρ)ᵐᵒᵖ ≃* Σ₀(ρ)`. Source:
roadmap §1.1.4, convention 2 ("the dictionary to the left-handed form is the adjugate"). -/
noncomputable def adjugateEquiv (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    (SigmaNorm L ρ hρ0 hρ)ᵐᵒᵖ ≃* Sigma0 L ρ hρ0 hρ where
  toFun g := ⟨(g.unop : Matrix (Fin 2) (Fin 2) L).adjugate, adjugate_mem_sigma0_iff.mpr g.unop.2⟩
  invFun g := MulOpposite.op ⟨(g : Matrix (Fin 2) (Fin 2) L).adjugate,
    adjugate_mem_sigmaNorm_iff.mpr g.2⟩
  left_inv g := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact Matrix.adjugate_adjugate_fin_two _
  right_inv g := by
    apply Subtype.ext
    exact Matrix.adjugate_adjugate_fin_two _
  map_mul' g h := by
    apply Subtype.ext
    change ((h.unop * g.unop : SigmaNorm L ρ hρ0 hρ) : Matrix (Fin 2) (Fin 2) L).adjugate = _
    rw [Submonoid.coe_mul, Matrix.adjugate_mul_distrib]
    rfl

@[simp] theorem adjugateEquiv_apply_coe {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} (g : (SigmaNorm L ρ hρ0 hρ)ᵐᵒᵖ) :
    (adjugateEquiv L ρ hρ0 hρ g : Matrix (Fin 2) (Fin 2) L) =
      (g.unop : Matrix (Fin 2) (Fin 2) L).adjugate :=
  rfl

omit [IsUltrametricDist L] in
/-- The adjugate of `η = diag(ϖ, 1)` is the left-handed `diag(1, ϖ)`. Source: roadmap §1.1.4. -/
theorem adjugate_eta (ϖ : L) : (eta L ϖ).adjugate = !![1, 0; 0, ϖ] := by
  rw [eta, Matrix.adjugate_fin_two_of]
  simp

end AutomorphicForm
