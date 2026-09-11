/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.«05_GenFun»
import PhD.TateFredholm.«06_WeightGenFun»
import PhD.TateFredholm.«00_Compose»

/-!
# Abstract weight data for the weight-`κ` action (Jacobs, Definition 1.27)

[Jacobs, *Slopes of Compact Hecke Operators*, Ch. 1 §1.5 Definition 1.27]:

> "Let κ : ℤ×_p → 𝒪×_p be a locally analytic character, i.e. a continuous group
> homomorphism.  Given α ∈ ℕ, let Σ_α = {γ = (a b; c d) ∈ M₂(ℤ_p) : p^α | c, p ∤ d,
> det(γ) ≠ 0}.  The weight κ action of γ ∈ Σ_α on A_p is given by the continuous
> ℂ_p-linear extension of the map sending z^k ↦ κ(cz + d)/(cz + d)² ((az+b)/(cz+d))^k.
> …  Note, that by κ(cz + d) we mean the power series expansion of κ(cz + d) at zero."

This file defines the **abstract weight datum** `QMF.WeightSeries S ρ`: the expansion
`κ(c·x + d)` as a power-series-valued function of the lower row `(c, d)`, together with
the five facts the action laws consume — normalisation at the identity, row decay at
the level `ρ`, summability, and the κ-cocycle.

**Status: engine, not API.**  `WeightSeries` is the implementation record on which the
action theory (`PhD/QMF/Weight/03_SlashAction.lean`) is proved once.  The public notion of
a weight is `QMF.AnalyticWeight U S ρ` (`PhD/QMF/Weight/04_Char.lean`: an honest character
analytic at the wild level), whose `toWeightSeries` feeds this engine and which re-exports
the action API (`AnalyticWeight.kappaSlash`, `_one`, `_mul`, `matrixCoeff_kappaSlash`,
`kappaSlashAction`); the forms space `QMF.Weight.Forms` takes an `AnalyticWeight`.
Downstream code should not need to name `WeightSeries`.  The Jacobs weight (`κ(u) = exp₃(t·log₃ u)`,
`PhD/JacobsSlash/`), the classical algebraic weights (`κ(u) = u^(n+2)`,
`PhD/QMF/Weight/06_Algebraic.lean`) and honest character expansions
(`PhD/QMF/Weight/04_Char.lean`) are all instances.

* `QMF.SigmaNorm K ρ hρ0 hρ` — the norm-form of Def 1.27's `Σ_α`: integral entries,
  `‖c‖ ≤ ρ`, `‖d‖ = 1`, `det ≠ 0`.  The archetype level monoid; instances may act
  through any submonoid `S` satisfying `QMF.LevelBounds S ρ` (e.g. the thesis's `Σ₁(3)`,
  whose `d ≡ 1 (3)` congruence is the analyticity domain of the Jacobs character, or a
  valued-field `Sigma0'` via the norm dictionary).
* `QMF.LevelBounds S ρ` — the norm bounds the analytic estimates extract from `S`.
* `QMF.linX`, `QMF.numX`, `QMF.mobius` — `c·x + d`, `a·x + b`, and the Möbius series
  `w_γ = (a·x + b)/(c·x + d)` (one-variable; general-`K` forms of the Jacobs fork's).
* `QMF.WeightSeries S ρ` — the weight datum.
* `QMF.yExtend` — a one-variable series as a `y`-degree-`0` two-variable series.
* `QMF.WeightSeries.genFun` — `κcol·(linSeries γ)⁻¹·(quadSeries γ)⁻¹`, the generating
  function of [Jacobs, Prop 2.6], taken as the definition of the action
  (`PhD/QMF/Weight/03_SlashAction.lean`).
-/

open TateFredholm PowerSeries
open scoped TateFredholm

namespace QMF

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The norm-form level monoid of [Jacobs, Def 1.27]: `Σ_α` with `p^α | c` read as
`‖c‖ ≤ ρ`, `p ∤ d` as `‖d‖ = 1`, and `M₂(ℤ_p)` as integral entries.  (`0 ≤ ρ` is
needed for `1 ∈`: the `(1,0)`-entry of the identity has norm `0`.) -/
def SigmaNorm (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) K) where
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

omit [CompleteSpace K] in
/-- Membership in `SigmaNorm K ρ hρ0 hρ` unfolds to its four defining conditions: integral
entries, `‖c‖ ≤ ρ`, `‖d‖ = 1`, and nonzero determinant. -/
theorem mem_sigmaNorm_iff {ρ : ℝ} {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ SigmaNorm K ρ hρ0 hρ ↔ (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0 :=
  Iff.rfl

/-- The norm bounds a level submonoid must satisfy for the weight-action estimates:
integral entries, `‖c‖ ≤ ρ` and `d` a unit, for every member.  `SigmaNorm K ρ hρ0 hρ`
itself satisfies them (`levelBounds_sigmaNorm`), as does any submonoid of it. -/
structure LevelBounds (S : Submonoid (Matrix (Fin 2) (Fin 2) K)) (ρ : ℝ) : Prop where
  rho_nonneg : 0 ≤ ρ
  rho_lt_one : ρ < 1
  integral : ∀ {g}, g ∈ S → ∀ i j, ‖g i j‖ ≤ 1
  c_le : ∀ {g}, g ∈ S → ‖g 1 0‖ ≤ ρ
  d_unit : ∀ {g}, g ∈ S → ‖g 1 1‖ = 1

omit [CompleteSpace K] in
/-- The archetype monoid `SigmaNorm` satisfies its own level bounds. -/
theorem levelBounds_sigmaNorm {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    LevelBounds (SigmaNorm K ρ hρ0 hρ) ρ where
  rho_nonneg := hρ0
  rho_lt_one := hρ
  integral hg := hg.1
  c_le hg := hg.2.1
  d_unit hg := hg.2.2.1

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Level bounds restrict to any smaller submonoid. -/
theorem LevelBounds.mono {S T : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}
    (hb : LevelBounds T ρ) (hST : S ≤ T) : LevelBounds S ρ where
  rho_nonneg := hb.rho_nonneg
  rho_lt_one := hb.rho_lt_one
  integral hg := hb.integral (hST hg)
  c_le hg := hb.c_le (hST hg)
  d_unit hg := hb.d_unit (hST hg)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The `(1,1)`-entry of a member of a bounded level is nonzero. -/
theorem LevelBounds.d_ne_zero {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}
    (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S) :
    g 1 1 ≠ 0 := by
  intro hc
  have := hb.d_unit hg
  rw [hc, norm_zero] at this
  exact zero_ne_one this

omit [CompleteSpace K] in
/-- Members of a bounded level have determinant of norm `≤ 1` (integral entries). -/
theorem LevelBounds.norm_det_le_one {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}
    (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S) : ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_one₀ (hb.integral hg _ _) (norm_nonneg _) (hb.integral hg _ _)
  · rw [norm_neg, norm_mul]
    exact mul_le_one₀ (hb.integral hg _ _) (norm_nonneg _) (hb.integral hg _ _)

omit [CompleteSpace K] in
/-- **Small determinant forces a small `a`-entry** on a bounded level: if `‖det g‖ ≤ σ`
with `ρ ≤ σ`, then `‖g₀₀‖ ≤ σ` (`a·d = det g + b·c`, `‖d‖ = 1`, `‖b·c‖ ≤ ρ`) — the
matrix-entry form of [Buzzard, Lemma 12.2 proof]'s "`det((x_δ)_p)/det(η_p)` is a unit". -/
theorem LevelBounds.norm_apply_zero_zero_le_of_norm_det_le
    {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ σ : ℝ} (hb : LevelBounds S ρ)
    (hρσ : ρ ≤ σ) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S) (hdet : ‖g.det‖ ≤ σ) :
    ‖g 0 0‖ ≤ σ := by
  have hd : ‖g 1 1‖ = 1 := hb.d_unit hg
  have hkey : g 0 0 * g 1 1 = g.det + g 0 1 * g 1 0 := by
    rw [Matrix.det_fin_two]; ring
  calc ‖g 0 0‖ = ‖g 0 0 * g 1 1‖ := by rw [norm_mul, hd, mul_one]
    _ = ‖g.det + g 0 1 * g 1 0‖ := by rw [hkey]
    _ ≤ max ‖g.det‖ ‖g 0 1 * g 1 0‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ σ := by
      refine max_le hdet ?_
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hb.integral hg 0 1)).trans
        ((hb.c_le hg).trans hρσ)

/-- The linear factor `c·x + d` of `γ`, as a one-variable series (general-`K` form of
the Jacobs fork's `linX`). -/
noncomputable def linX (γ : Matrix (Fin 2) (Fin 2) K) : PowerSeries K :=
  PowerSeries.C (γ 1 1) + PowerSeries.C (γ 1 0) * PowerSeries.X

/-- The numerator `a·x + b` of the Möbius map of `γ`. -/
noncomputable def numX (γ : Matrix (Fin 2) (Fin 2) K) : PowerSeries K :=
  PowerSeries.C (γ 0 1) + PowerSeries.C (γ 0 0) * PowerSeries.X

/-- The Möbius map of `γ` as a formal series: `w_γ = (a·x + b)/(c·x + d)`. -/
noncomputable def mobius (γ : Matrix (Fin 2) (Fin 2) K) : PowerSeries K :=
  numX γ * (linX γ)⁻¹

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The constant coefficient of `linX γ` is `d = γ 1 1`. -/
@[simp] theorem constantCoeff_linX (γ : Matrix (Fin 2) (Fin 2) K) :
    PowerSeries.constantCoeff (linX γ) = γ 1 1 := by simp [linX]

/-- **The abstract weight datum** ([Jacobs, Def 1.27] with the character abstracted):
the power-series expansion `col c d` of `κ(c·x + d)`, the level bounds of the acting
monoid `S`, and the four analytic facts the action laws consume.  The cocycle field is
the only character-specific analysis; each instance proves it its own way (Jacobs: ODE
+ p-adic binomial theorem; algebraic weights: polynomial algebra; honest characters:
evaluation injectivity). -/
structure WeightSeries (S : Submonoid (Matrix (Fin 2) (Fin 2) K)) (ρ : ℝ) where
  /-- The norm bounds of the acting monoid. -/
  bounds : LevelBounds S ρ
  /-- The expansion of `κ(c·x + d)` as a function of the lower row `(c, d)`. -/
  col : K → K → PowerSeries K
  /-- Normalisation at the identity matrix (`lin 1 = (0, 1)`): `κ(1) = 1`. -/
  col_zero_one : col 0 1 = 1
  /-- Row decay at the level: `‖coeff m (κcol)‖ ≤ ρ^m` on `S` ([Jacobs, p. 29]:
  "exp₃(t log(cx + d)) converges to an element of 𝒪₃[[x]]", quantified). -/
  rowDecay : ∀ {g}, g ∈ S → ∀ m : ℕ, ‖PowerSeries.coeff m (col (g 1 0) (g 1 1))‖ ≤ ρ ^ m
  /-- Absolute summability of the κ-column (the `compAn` admissibility). -/
  absSummable : ∀ {g}, g ∈ S → AbsSummable (col (g 1 0) (g 1 1))
  /-- **The κ-cocycle**: `κ(lin (δγ)) = κ(lin γ)·(κ(lin δ) ∘ w_γ)` — the automorphy
  transformation of the character column under composition. -/
  cocycle : ∀ {γ δ : Matrix (Fin 2) (Fin 2) K}, γ ∈ S → δ ∈ S →
    col ((δ * γ) 1 0) ((δ * γ) 1 1)
      = col (γ 1 0) (γ 1 1) * compAn (col (δ 1 0) (δ 1 1)) (mobius γ)

namespace WeightSeries

variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Two weight data with the same column family are equal — every other field is a
proposition (`LevelBounds` is a Prop-structure). -/
theorem ext {W₁ W₂ : WeightSeries S ρ} (h : W₁.col = W₂.col) : W₁ = W₂ := by
  cases W₁
  cases W₂
  simp only at h
  subst h
  rfl

/-- A one-variable series as a two-variable series of `y`-degree `0`. -/
noncomputable def yExtend (φ : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  fun p => if p 1 = 0 then PowerSeries.coeff (p 0) φ else 0

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The coefficients of `yExtend` (definitional). -/
@[simp] theorem coeff_yExtend (φ : PowerSeries K) (p : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff p (yExtend φ) =
      if p 1 = 0 then PowerSeries.coeff (p 0) φ else 0 :=
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `yExtend φ` is concentrated in `y`-degree `0`. -/
theorem yExtend_yDeg0 (φ : PowerSeries K) :
    ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p (yExtend φ) = 0 :=
  fun _ hp => if_neg hp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `yExtend` sends `1` to `1`. -/
@[simp] theorem yExtend_one : yExtend (1 : PowerSeries K) = 1 := by
  refine MvPowerSeries.ext fun p => ?_
  rw [coeff_yExtend, MvPowerSeries.coeff_one]
  by_cases h1 : p 1 = 0
  · rw [if_pos h1, PowerSeries.coeff_one]
    by_cases h0 : p 0 = 0
    · rw [if_pos h0, if_pos (TateFredholm.fin2_eq_zero h0 h1)]
    · rw [if_neg h0, if_neg fun hc => h0 (by rw [hc]; simp)]
  · rw [if_neg h1, if_neg fun hc => h1 (by rw [hc]; simp)]

/-- **The generating function of the weight-`κ` action** ([Jacobs, Proposition 2.6],
taken as definition): `κ(cx + d) / ((cx + d)(cx + d − axy − by))`. -/
noncomputable def genFun (W : WeightSeries S ρ) (γ : Matrix (Fin 2) (Fin 2) K) :
    MvPowerSeries (Fin 2) K :=
  yExtend (W.col (γ 1 0) (γ 1 1)) * (linSeries γ)⁻¹ * (quadSeries γ)⁻¹

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The `κ`-column extends to a row-decaying two-variable series (its `y`-degree is
`0`, so the row bound is the `rowDecay` field). -/
theorem rowIntAt_yExtend (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : RowIntAt ρ (yExtend (W.col (g 1 0) (g 1 1))) := by
  intro p
  rw [coeff_yExtend]
  split_ifs with h
  · exact W.rowDecay hg (p 0)
  · simp [pow_nonneg W.bounds.rho_nonneg]

omit [CompleteSpace K] in
/-- The linear factor of a level element is row-decaying. -/
theorem rowIntAt_linSeries_of_mem (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : RowIntAt ρ (linSeries g) :=
  rowIntAt_linSeries W.bounds.rho_nonneg (W.bounds.integral hg 1 1)
    (W.bounds.c_le hg)

omit [CompleteSpace K] in
/-- The quadratic factor of a level element is shift-decaying (its `a`- and `b`-entries
sit at `y`-degree `1`, where the shift weight is `1`). -/
theorem shiftIntAt_quadSeries_of_mem (W : WeightSeries S ρ)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S) : ShiftIntAt ρ (quadSeries g) := by
  have hρ0 := W.bounds.rho_nonneg
  rw [quadSeries_eq]
  refine (((shiftIntAt_monomial hρ0 ?_).add (shiftIntAt_monomial hρ0 ?_)).sub
    (shiftIntAt_monomial hρ0 ?_)).sub (shiftIntAt_monomial hρ0 ?_)
  · simpa using W.bounds.d_unit hg |>.le
  · simpa using W.bounds.c_le hg
  · simpa using W.bounds.integral hg 0 0
  · simpa using W.bounds.integral hg 0 1

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The norm of the constant coefficient of either denominator factor is `1`. -/
theorem norm_constantCoeff_linSeries (W : WeightSeries S ρ)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S) :
    ‖MvPowerSeries.constantCoeff (linSeries g)‖ = 1 := by
  rw [constantCoeff_linSeries]; exact W.bounds.d_unit hg

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The constant coefficient of the quadratic factor is a unit on the level. -/
theorem norm_constantCoeff_quadSeries (W : WeightSeries S ρ)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S) :
    ‖MvPowerSeries.constantCoeff (quadSeries g)‖ = 1 := by
  rw [constantCoeff_quadSeries]; exact W.bounds.d_unit hg

omit [CompleteSpace K] in
/-- Coefficient integrality of the generating function on the level
([Jacobs, p. 29–30] for the Jacobs weight; the general form consumes only the
`WeightSeries` fields). -/
theorem coeffInt_genFun (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : CoeffInt (W.genFun g) := by
  have hρ0 := W.bounds.rho_nonneg
  have hρ1 := W.bounds.rho_lt_one.le
  refine CoeffInt.mul (CoeffInt.mul ?_ ?_) ?_
  · exact CoeffInt.of_rowIntAt hρ0 hρ1 (W.rowIntAt_yExtend hg)
  · exact (CoeffInt.of_rowIntAt hρ0 hρ1 (W.rowIntAt_linSeries_of_mem hg)).inv
      (W.norm_constantCoeff_linSeries hg)
  · refine CoeffInt.inv ?_ (W.norm_constantCoeff_quadSeries hg)
    intro p
    exact (W.shiftIntAt_quadSeries_of_mem hg p).trans (pow_le_one₀ hρ0 hρ1)

omit [CompleteSpace K] in
/-- Every coefficient of the generating function is integral, read at `x^j y^i`. -/
theorem norm_coeff_genFun_le_one (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) (j i : ℕ) :
    ‖MvPowerSeries.coeff (idx j i) (W.genFun g)‖ ≤ 1 :=
  W.coeffInt_genFun hg _

omit [CompleteSpace K] in
/-- **Row decay of the generating function for `U_ϖ`-type elements** ([Jacobs, Lemma 2.7
proof]: "`h_{k,l}(x/3, y)` lies in `𝒪₃[[x, y]]`", i.e. every coefficient of `x^j y^i` is
`≤ σ^j`): if `‖g₀₀‖ ≤ σ` with `ρ ≤ σ`, the generating function of `g ∈ S` is row-integral
at level `σ`.  Each factor is: `κ(cx+d)` by `rowDecay`, `(cx+d)⁻¹` by `‖c‖ ≤ ρ ≤ σ`, and
`(cx + d − axy − by)⁻¹` by `‖a‖ ≤ σ` (`rowIntAt_quadSeries`). -/
theorem rowIntAt_genFun (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) {σ : ℝ} (hρσ : ρ ≤ σ) (ha : ‖g 0 0‖ ≤ σ) : RowIntAt σ (W.genFun g) := by
  have hρ0 := W.bounds.rho_nonneg
  have hσ0 : 0 ≤ σ := hρ0.trans hρσ
  have hc : ‖g 1 0‖ ≤ σ := (W.bounds.c_le hg).trans hρσ
  refine RowIntAt.mul hσ0 (RowIntAt.mul hσ0 ?_ ?_) ?_
  · exact (W.rowIntAt_yExtend hg).mono hρ0 hρσ
  · exact (rowIntAt_linSeries hσ0 (W.bounds.integral hg 1 1) hc).inv hσ0
      (W.norm_constantCoeff_linSeries hg)
  · exact (rowIntAt_quadSeries hσ0 (W.bounds.integral hg 1 1) hc ha
      (W.bounds.integral hg 0 1)).inv hσ0 (W.norm_constantCoeff_quadSeries hg)

omit [CompleteSpace K] in
/-- The shifted row bound `‖coeff (x^j y^i)‖ ≤ ρ^(j − i)` (truncated subtraction) —
between full row decay (false at `γ = 1`) and mere integrality, exactly what the level
supports and what column decay needs. -/
theorem shiftIntAt_genFun (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : ShiftIntAt ρ (W.genFun g) := by
  have hρ0 := W.bounds.rho_nonneg
  have hρ1 := W.bounds.rho_lt_one.le
  refine ShiftIntAt.mul hρ0 hρ1 (ShiftIntAt.mul hρ0 hρ1 ?_ ?_) ?_
  · exact ShiftIntAt.of_rowIntAt hρ0 hρ1 (W.rowIntAt_yExtend hg)
  · exact ShiftIntAt.of_rowIntAt hρ0 hρ1
      (((W.rowIntAt_linSeries_of_mem hg)).inv hρ0 (W.norm_constantCoeff_linSeries hg))
  · exact (W.shiftIntAt_quadSeries_of_mem hg).inv hρ0 hρ1
      (W.norm_constantCoeff_quadSeries hg)

omit [CompleteSpace K] in
/-- The shifted bound, read at `x^j y^i`: `‖coeff‖ ≤ ρ^(j−i)`. -/
theorem norm_coeff_genFun_le_shift (W : WeightSeries S ρ)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S) (j i : ℕ) :
    ‖MvPowerSeries.coeff (idx j i) (W.genFun g)‖ ≤ ρ ^ (j - i) := by
  simpa using W.shiftIntAt_genFun hg (idx j i)

omit [CompleteSpace K] in
/-- Column decay: each column of the generating function is a Tate-algebra element
([Jacobs, (2.1.3)]). -/
theorem tendsto_coeff_genFun (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) (i : ℕ) :
    Filter.Tendsto (fun j => MvPowerSeries.coeff (idx j i) (W.genFun g))
      Filter.cofinite (nhds 0) := by
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun j => W.norm_coeff_genFun_le_shift hg j i) ?_
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one W.bounds.rho_nonneg
    W.bounds.rho_lt_one).comp (Filter.tendsto_sub_atTop_nat i)

end WeightSeries

end QMF
