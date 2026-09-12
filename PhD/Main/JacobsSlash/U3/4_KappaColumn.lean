/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.JacobsSlash.«3_BinomialTheorem»
import PhD.Main.JacobsSlash.U3.«1_Setting»
import PhD.Main.JacobsSlash.«2_U3Data»
import PhD.Main.QMF.Weight.«03_SlashAction»

/-!
# The Jacobs κ-column and the `Σ₁(3)` bounds

[Jacobs, §2.1 p. 29]: "In all cases of `(a b; c d)` that we will calculate with, `c ≡ 0
mod 9` and `d ≡ 1 mod 9`. … Then `κ(cx + d) = … = (cx + d)^t`.  Lastly, we write
`(cx + d)^t = exp₃(t log(cx + d))`."

This file holds the Jacobs-specific analytic facts consumed by the weight datum
`jacobsExpansionData` (`U3/5_KappaWeight.lean`): the norm bounds on the entries of the
acting monoid `Σ₁(3)` (via the valuation ↔ norm dictionary of `K₃`), and the closed form
of the κ-column `κ(c·x + d)` of the transcribed series `kappaSeries₂`.

The weight *action*, its action laws, the Möbius calculus, the integrality estimates and
the κ-cocycle live in the general layer `PhD/Main/QMF/Weight/` (`WeightSeries`, `kappaSlash`,
`AnalyticWeight`); the fork's former copies of all of these — `kappaSlash t ht`,
`kappaSlashAction`, the ODE proof `kappaCol_cocycle`, the `CoeffInt`/`ShiftInt`/`yCoeff`/
`mobius` calculus — were retired on 2026-08-19 (forms-headline board, T002), the
thesis weight being the honest character `jacobsWeight` whose cocycle is derived by
evaluation injectivity.

(The valuation ↔ norm dictionary these bounds run on is mathlib's
`Valued.toNormedField.norm_le_iff` / `norm_le_one_iff`; the fork's own
`norm_le_of_valued_le` / `norm_eq_one_of_valued_eq_one` were retired on 2026-08-20,
slopes-hecke board C4.)

## Main declarations

* `JacobsSlash.norm_sigma1_entry_le_one`, `norm_sigma1_lower_right_sub_one_le`,
  `norm_sigma1_lower_right`, `norm_sigma1_lower_left_le`, `norm_sigma1_ratio_le` — the
  `Σ₁(3)` bounds: integral entries, `‖d − 1‖ ≤ ‖3‖`, `‖d‖ = 1`, `‖c‖ ≤ ‖3‖²`, `‖c/d‖ ≤ ‖3‖²`.
* `JacobsSlash.coeff_yCoeff_kappaSeries₂`, `JacobsSlash.kappaSeries₂_eq_yExtend` — the
  κ-column `κ(c·x + d)` has `xⁿ`-coefficient `κ(d)·(t choose n)·(c/d)ⁿ`, and `kappaSeries₂` is
  its `y`-extension.
-/

open TateFredholm JacobsSlash
open scoped TateFredholm PowerSeries

/- See `1_Setting.lean`: pin the adic `Algebra ℚ K₃` path. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/-- The entries of `g ∈ Σ₁(3)` are integral. -/
theorem norm_sigma1_entry_le_one (g : Sigma1₃) : ∀ i j : Fin 2, ‖g.1 i j‖ ≤ 1 := by
  obtain ⟨⟨hint, -, -, -⟩, -⟩ := g.2
  exact fun i j => Valued.toNormedField.norm_le_one_iff.mpr (hint i j)

/-- The `(1,1)`-entry of `g ∈ Σ₁(3)` is a `1`-unit mod `3`. -/
theorem norm_sigma1_lower_right_sub_one_le (g : Sigma1₃) :
    ‖g.1 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  obtain ⟨-, ha1⟩ := g.2
  exact Valued.toNormedField.norm_le_iff.mpr
    (le_trans ha1 (le_of_eq valued_three_eq_γ₃.symm))

/-- The `(1,1)`-entry of `g ∈ Σ₁(3)` has norm one. -/
theorem norm_sigma1_lower_right (g : Sigma1₃) : ‖g.1 1 1‖ = 1 :=
  JacobsSlash.norm_eq_one_of_norm_sub_one_lt_one
    ((norm_sigma1_lower_right_sub_one_le g).trans_lt norm_three_lt_one)

/-- The `(1,0)`-entry of `g ∈ Σ₁(3)` is divisible by `9`. -/
theorem norm_sigma1_lower_left_le (g : Sigma1₃) :
    ‖g.1 1 0‖ ≤ ‖(3 : K₃)‖ ^ 2 := by
  obtain ⟨⟨-, hc, -, -⟩, -⟩ := g.2
  have h90 : (9 : K₃) ≠ 0 := by norm_num
  have hn9 : ‖(9 : K₃)‖ = ‖(3 : K₃)‖ ^ 2 := by
    rw [show (9 : K₃) = 3 * 3 by norm_num, norm_mul, sq]
  rw [← hn9]
  exact Valued.toNormedField.norm_le_iff.mpr (le_trans hc (le_of_eq valued_nine_eq.symm))

/-- `‖c/d‖ ≤ ‖3‖²` for the lower row of a `Σ₁(3)` element. -/
theorem norm_sigma1_ratio_le (g : Sigma1₃) :
    ‖g.1 1 0 / g.1 1 1‖ ≤ ‖(3 : K₃)‖ ^ 2 := by
  rw [norm_div, norm_sigma1_lower_right g, div_one]
  exact norm_sigma1_lower_left_le g

/-- The `κ`-column in closed form: `κ(c·x + d)` has `xⁿ`-coefficient
`κ(d)·(t choose n)·(c/d)ⁿ`.  (The `y`-degree-`0` column of `kappaSeries₂`, which is where
all of its mass sits.) -/
theorem coeff_yCoeff_kappaSeries₂ (t c d : K₃) (n : ℕ) :
    PowerSeries.coeff n (QMF.yCoeff (kappaSeries₂ t c d) 0)
      = unitPow t d * (binomialCoeff t n * (c / d) ^ n) := by
  rw [QMF.coeff_yCoeff, coeff_kappaSeries₂, if_pos (by simp), idx_apply_zero]

/-- `kappaSeries₂` is the `y`-extension of its κ-column (it is `y`-degree-`0` concentrated
by definition). -/
theorem kappaSeries₂_eq_yExtend (t c d : K₃) :
    kappaSeries₂ t c d
      = QMF.WeightSeries.yExtend
          (PowerSeries.mk fun n => unitPow t d * (binomialCoeff t n * (c / d) ^ n)) := by
  refine MvPowerSeries.ext fun p => ?_
  rw [QMF.WeightSeries.coeff_yExtend, coeff_kappaSeries₂]
  split_ifs with h1
  · exact (PowerSeries.coeff_mk (p 0) (fun n => unitPow t d * (binomialCoeff t n * (c / d) ^ n))).symm
  · rfl

end JacobsSlash
