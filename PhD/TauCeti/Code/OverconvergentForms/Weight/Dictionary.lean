/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Level.Local
import PhD.TauCeti.Code.OverconvergentForms.Weight.Level

/-!
# The valuation dictionary between `M_t` and `Σ(ρ)`

For a field `K` with a rank-one valuation, Buzzard's monoid `M_t = {ϖ^t ∣ c, ϖ ∤ d, det ≠ 0}` of
`Level/Local.lean` (valued form, `LocalLevel.monoidM`) is the norm-form monoid `Σ(‖ϖ‖^t)` of
`Weight/Level.lean`, the Iwahori subgroup `Iw(ϖ^t)` lies in it, and the `U₁`-type subgroup
`Iw₁(ϖ^{2t})` has `Σ₁`-type bounds at `‖ϖ‖^t`. This is the only point at which Layer 1 cites
Layer 0.

Roadmap: §1.1.1 ("Prove the valuation dictionary `M_t = SigmaNorm F_𝔭 ‖ϖ‖^t`"), §1.1.3 ("the image
under `θ_𝔭` of a `U₁(𝔭^{2t})`-type group has `Σ₁`-type bounds at `ρ = ‖ϖ‖^t`"). Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Weight/Dictionary.lean`.
-/

open scoped Valued

namespace AutomorphicForm

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  [hv : (Valued.v : Valuation K Γ₀).RankOne]

/-- **The dictionary** `M_t = Σ(‖ϖ‖^t)`: Buzzard's monoid in valued form is the norm-form level
monoid at radius `‖ϖ‖^t`. Source: roadmap §1.1.1; [L0] `LocalLevel.mem_monoidM_iff_norm`. -/
theorem mem_monoidM_iff_mem_sigmaNorm {ϖ : K} (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ LocalLevel.monoidM K (Valued.v ϖ ^ t) (pow_lt_one₀ zero_le hϖ1 (by omega)) ↔
      g ∈ SigmaNorm K (‖ϖ‖ ^ t) (pow_nonneg (norm_nonneg ϖ) t)
        (pow_lt_one₀ (norm_nonneg ϖ) (Valued.toNormedField.norm_lt_one_iff.mpr hϖ1) (by omega)) :=
  LocalLevel.mem_monoidM_iff_norm hϖ1 ht

/-- The Iwahori subgroup `Iw(ϖ^t)` has level bounds `‖ϖ‖^t`. Source: roadmap §1.1.1 ("so that
`Iw(𝔭^t)` and the `U₁`-type groups have level bounds `‖ϖ‖^t`"). -/
theorem coe_mem_sigmaNorm_of_mem_iwahori {ϖ : K} (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {g : GL (Fin 2) K} (hg : g ∈ LocalLevel.iwahori K (Valued.v ϖ ^ t)) :
    (g : Matrix (Fin 2) (Fin 2) K) ∈ SigmaNorm K (‖ϖ‖ ^ t) (pow_nonneg (norm_nonneg ϖ) t)
      (pow_lt_one₀ (norm_nonneg ϖ) (Valued.toNormedField.norm_lt_one_iff.mpr hϖ1) (by omega)) :=
  (mem_monoidM_iff_mem_sigmaNorm hϖ1 ht).mp (LocalLevel.coe_mem_monoidM _ hg)

/-- A `U₁(ϖ^{2t})`-type subgroup has `Σ₁`-type bounds at `‖ϖ‖^t`: `‖c‖ ≤ ‖ϖ‖^{2t} = (‖ϖ‖^t)²` and
`‖d − 1‖ ≤ ‖ϖ‖^{2t} ≤ ‖ϖ‖^t`. Source: roadmap §1.1.3. -/
theorem coe_mem_sigmaOne_of_mem_iwahoriOne {ϖ : K} (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {g : GL (Fin 2) K} (hg : g ∈ LocalLevel.iwahoriOne K (Valued.v ϖ ^ (2 * t))) :
    (g : Matrix (Fin 2) (Fin 2) K) ∈ SigmaOne K (‖ϖ‖ ^ t) (pow_nonneg (norm_nonneg ϖ) t)
      (pow_lt_one₀ (norm_nonneg ϖ) (Valued.toNormedField.norm_lt_one_iff.mpr hϖ1) (by omega)) := by
  have hle : Valued.v ϖ ^ (2 * t) ≤ Valued.v ϖ ^ t :=
    pow_le_pow_right_of_le_one' hϖ1.le (by omega)
  have hiw : g ∈ LocalLevel.iwahori K (Valued.v ϖ ^ t) :=
    LocalLevel.iwahori_mono hle (LocalLevel.iwahoriOne_le_iwahori _ hg)
  refine ⟨coe_mem_sigmaNorm_of_mem_iwahori hϖ1 ht hiw, ?_, ?_⟩
  · have hc : Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ≤ Valued.v ϖ ^ (2 * t) := hg.1.2.2
    rw [← pow_mul, mul_comm t 2, ← norm_pow, Valued.toNormedField.norm_le_iff, map_pow]
    exact hc
  · have hd : Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ Valued.v ϖ ^ (2 * t) := hg.2
    rw [← norm_pow, Valued.toNormedField.norm_le_iff, map_pow]
    exact hd.trans hle

end AutomorphicForm
