/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.U3.«4_KappaColumn»
import PhD.QMF.Weight.«04_Char»
import PhD.QMF.Weight.«04_AdicLevel»

/-!
# The thesis weight `κ_t` as an honest analytic weight

[Jacobs, p. 29]: "In all cases of `(a b; c d)` that we will calculate with, `c ≡ 0
mod 9` and `d ≡ 1 mod 9`. … Write `cx + d = 4^ρ` … Then `κ(cx + d) = κ(4^ρ) = κ(4)^ρ
= 4^{tρ} = (4^ρ)^t = (cx + d)^t`.  Lastly, we write `(cx + d)^t = exp₃(t log(cx + d))`."

This file builds the thesis weight as a `QMF.AnalyticWeight`: the character
`jacobsChar : oneUnits K₃ ‖3‖ →* K₃ˣ`, `u ↦ u^t = exp₃(t·log₃ u)`, together with its
expansion datum `jacobsExpansionData` — the binomial column `κ(d)·∑ₙ (t choose n)(c/d)ⁿ xⁿ`
(the `y`-degree-`0` column of the transcribed `kappaSeries₂`), its row decay on `Σ₁(3)`, and
the evaluation law `hasSum_jacobsCol_unitPow` ([Jacobs, p. 29] via the `p`-adic binomial
theorem).  Everything the general layer needs of the weight (the action, its action laws,
the κ-cocycle, compactness) is then supplied by `PhD/QMF/Weight/` with no Jacobs-specific
re-proof; the only bridge to the fork's transcription is `genFun_jacobsWeight`: the
generating function of the headline weight is the fork's `weightGenFun`.

## Main declarations

* `JacobsSlash.levelBounds_sigma1₃` — `Σ₁(3)` satisfies the norm-form level bounds at
  `ρ = ‖3‖`.
* `JacobsSlash.hasSum_jacobsCol_unitPow` — the honest-character statement: the column
  evaluates to `u ↦ u^t` on the closed unit ball.
* `JacobsSlash.jacobsChar`, `JacobsSlash.jacobsExpansionData`, **`JacobsSlash.jacobsWeight`** —
  the thesis weight `κ_t : AnalyticWeight (oneUnits K₃ ‖3‖ …) Σ₁(3) ‖3‖`.
* `JacobsSlash.genFun_jacobsWeight`, `JacobsSlash.matrixCoeff_kappaSlash_jacobsWeight` —
  [Jacobs, Prop 2.6] at the headline weight: the matrix of `(jacobsWeight t ht).kappaSlash g`
  is the coefficient array of `weightGenFun t g`.
-/

open TateFredholm PowerSeries JacobsSlash
open scoped TateFredholm

/- See `1_Setting.lean`: pin the adic `Algebra ℚ K₃` path. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/-! ### The Jacobs weight over any complete ultrametric field with `‖3‖ < 1`

The thesis character `u ↦ uᵗ` and its binomial expansion are field-generic; the level is the
norm-defined `Σ₁(3)`-type monoid `sigma1Norm` ([Jacobs, §2.1 p. 29]: "in all cases of
`(a b; c d)` that we will calculate with, `c ≡ 0 mod 9` and `d ≡ 1 mod 9`").  The thesis's own
weight is this construction at `K₃` restricted to `Σ₁(3)`; the base-changed weight over an
extension `L ⊇ K₃` is the same construction at `ι t` (`U3/«10_Eigenforms»`). -/

section Generic

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-- The norm-form `Σ₁(3)`-type level: integral entries, `‖c‖ ≤ ‖3‖²`, `‖d − 1‖ ≤ ‖3‖`
([Jacobs, §2.1 p. 29]: "`c ≡ 0 mod 9` and `d ≡ 1 mod 9`" — the mod-`3` condition on `d` is what
the binomial expansion needs). -/
abbrev sigma1Norm (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    (h3 : ‖(3 : K)‖ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) K) :=
  QMF.SigmaOne K ‖(3 : K)‖ (norm_nonneg _) h3

omit [CompleteSpace K] [CharZero K] in
theorem levelBounds_sigma1Norm (h3 : ‖(3 : K)‖ < 1) :
    QMF.LevelBounds (sigma1Norm K h3) ‖(3 : K)‖ :=
  QMF.levelBounds_sigmaOne (norm_nonneg _) h3

/-- **The honest-character statement, field-generic** ([Jacobs, p. 29]): on the closed unit
ball the Jacobs column evaluates to `u ↦ uᵗ = exp₃(t·log₃ u)` (the `p`-adic binomial theorem
`tsum_binomialCoeff_eq_unitPow` needs `t` in the closure of `ℕ`). -/
theorem hasSum_jacobsColOf_unitPow (h3 : ‖(3 : K)‖ < 1) (t : K) (ht : ‖t‖ < 1)
    (hnat : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖t - (n : K)‖ < ε) {c d z : K}
    (hd : ‖d - 1‖ ≤ ‖(3 : K)‖) (hcd : ‖c / d‖ ≤ ‖(3 : K)‖ ^ 2) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => PowerSeries.coeff n
        (PowerSeries.mk fun n => unitPow t d * (binomialCoeff t n * (c / d) ^ n)) * z ^ n)
      (unitPow t (c * z + d)) := by
  have he : ‖c / d * z‖ ≤ ‖(3 : K)‖ ^ 2 := by
    rw [norm_mul]
    exact (mul_le_mul hcd hz (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hone : ‖(1 + c / d * z) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [add_sub_cancel_left]
    exact he.trans (by nlinarith [norm_nonneg (3 : K)])
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg, norm_one] at hd
    exact absurd (hd.trans_lt h3) (lt_irrefl _)
  have hterm : (fun n => PowerSeries.coeff n
        (PowerSeries.mk fun n => unitPow t d * (binomialCoeff t n * (c / d) ^ n)) * z ^ n)
      = fun n => unitPow t d * (binomialCoeff t n * (c / d * z) ^ n) := by
    funext n
    rw [PowerSeries.coeff_mk, mul_pow]
    ring
  rw [hterm]
  have hs : HasSum (fun n => binomialCoeff t n * (c / d * z) ^ n)
      (unitPow t (1 + c / d * z)) := by
    have h := (summable_binomialCoeff_mul_pow h3 ht.le he).hasSum
    rwa [tsum_binomialCoeff_eq_unitPow h3 ht.le he hnat] at h
  have hfin := hs.mul_left (unitPow t d)
  rwa [← unitPow_mul h3 ht.le hd hone,
    show d * (1 + c / d * z) = c * z + d from by field_simp; ring] at hfin

private theorem isUnit_unitPowOf (h3 : ‖(3 : K)‖ < 1) {t : K} (ht : ‖t‖ < 1) {x : K}
    (hx : ‖x - 1‖ ≤ ‖(3 : K)‖) : IsUnit (unitPow t x) := by
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  have h1 := norm_unitPow_sub_one_le h3 ht hx
  rw [h0, zero_sub, norm_neg, norm_one] at h1
  nlinarith [norm_nonneg t, norm_nonneg (3 : K), ht]

/-- The thesis character on the principal `‖3‖`-units, field-generic. -/
noncomputable def jacobsCharOf (h3 : ‖(3 : K)‖ < 1) (t : K) (ht : ‖t‖ < 1) :
    QMF.oneUnits K ‖(3 : K)‖ (norm_nonneg _) h3 →* Kˣ where
  toFun u := (isUnit_unitPowOf h3 ht u.2).unit
  map_one' := by
    refine Units.ext ?_
    rw [IsUnit.unit_spec, Units.val_one, OneMemClass.coe_one, Units.val_one, unitPow_one]
  map_mul' u v := by
    refine Units.ext ?_
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec,
      MulMemClass.coe_mul, Units.val_mul]
    exact unitPow_mul h3 ht.le u.2 v.2

@[simp] theorem jacobsCharOf_apply (h3 : ‖(3 : K)‖ < 1) (t : K) (ht : ‖t‖ < 1)
    (u : QMF.oneUnits K ‖(3 : K)‖ (norm_nonneg _) h3) :
    ((jacobsCharOf h3 t ht u : Kˣ) : K) = unitPow t ((u : Kˣ) : K) :=
  IsUnit.unit_spec _

/-- The Jacobs expansion datum, field-generic, at the level `sigma1Norm`. -/
noncomputable def jacobsExpansionDataOf (h3 : ‖(3 : K)‖ < 1) (t : K) (ht : ‖t‖ < 1)
    (hnat : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖t - (n : K)‖ < ε) :
    QMF.ExpansionData (sigma1Norm K h3) ‖(3 : K)‖ (QMF.oneUnits K ‖(3 : K)‖ (norm_nonneg _) h3)
      (jacobsCharOf h3 t ht) where
  bounds := levelBounds_sigma1Norm h3
  col c d := PowerSeries.mk fun n => unitPow t d * (binomialCoeff t n * (c / d) ^ n)
  rowDecay := fun {g} hg m => by
    rw [PowerSeries.coeff_mk, norm_mul]
    have hratio : ‖g 1 0 / g 1 1‖ ≤ ‖(3 : K)‖ ^ 2 := by
      rw [norm_div, (levelBounds_sigma1Norm h3).d_unit hg, div_one]
      exact hg.2.1
    calc ‖unitPow t (g 1 1)‖ * ‖binomialCoeff t m * (g 1 0 / g 1 1) ^ m‖
        ≤ 1 * ‖(3 : K)‖ ^ m :=
          mul_le_mul (norm_unitPow_le_one h3 ht hg.2.2)
            (norm_binomialCoeff_mul_pow_le h3 ht.le hratio m) (norm_nonneg _) zero_le_one
      _ = ‖(3 : K)‖ ^ m := one_mul _
  mem_level := fun {g} hg z hz hu =>
    QMF.levelUnit_mem_oneUnits
      (hg.2.1.trans (by nlinarith [norm_nonneg (3 : K), h3])) hg.2.2 hz hu
  eval := fun {g} hg z hz hu => by
    have hratio : ‖g 1 0 / g 1 1‖ ≤ ‖(3 : K)‖ ^ 2 := by
      rw [norm_div, (levelBounds_sigma1Norm h3).d_unit hg, div_one]
      exact hg.2.1
    have hts := (hasSum_jacobsColOf_unitPow h3 t ht hnat hg.2.2 hratio hz).tsum_eq
    refine hts.trans ?_
    rw [jacobsCharOf_apply]
    exact congrArg (unitPow t) (IsUnit.unit_spec hu).symm

/-- **The Jacobs weight `κ_t` over any complete ultrametric field with `‖3‖ < 1`** — the
input of `QMF.Weight.Forms` over extensions of `ℚ₃` (base change of the thesis's spaces). -/
noncomputable def jacobsWeightOf (h3 : ‖(3 : K)‖ < 1) (t : K) (ht : ‖t‖ < 1)
    (hnat : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖t - (n : K)‖ < ε) :
    QMF.AnalyticWeight (QMF.oneUnits K ‖(3 : K)‖ (norm_nonneg _) h3) (sigma1Norm K h3) ‖(3 : K)‖ :=
  ⟨_, jacobsExpansionDataOf h3 t ht hnat⟩

end Generic

/-- `Σ₁(3) ≤ sigma1Norm K₃` (the valuation-defined level sits in the norm-defined one). -/
theorem sigma1₃_le_sigma1Norm : Sigma1₃ ≤ sigma1Norm K₃ norm_three_lt_one := fun g hg =>
  ⟨fun i j => norm_sigma1_entry_le_one ⟨g, hg⟩ i j, norm_sigma1_lower_left_le ⟨g, hg⟩,
    norm_sigma1_lower_right_sub_one_le ⟨g, hg⟩⟩

/-- **The Jacobs weight `κ_t`**: the thesis character `u ↦ uᵗ` on the principal
`‖3‖`-units with its expansion datum, analytic at wild level `(Σ₁(3), ‖3‖)` — the input of
`QMF.Weight.Forms` for the thesis's spaces of overconvergent forms.  It is the
field-generic `jacobsWeightOf` restricted to the thesis's valuation-defined level
(`sigma1₃_le_sigma1Norm`), so the same construction over an extension of `K₃` gives the
base-changed spaces (`U3/«10_Eigenforms»`). -/
noncomputable def jacobsWeight (t : K₃) (ht : ‖t‖ < 1) :
    QMF.AnalyticWeight (QMF.oneUnits K₃ ‖(3 : K₃)‖ (norm_nonneg _) norm_three_lt_one)
      Sigma1₃ ‖(3 : K₃)‖ :=
  (jacobsWeightOf norm_three_lt_one t ht (fun _ hε => exists_natCast_close ht.le hε)).restrict
    sigma1₃_le_sigma1Norm

@[simp] theorem jacobsWeight_toChar (t : K₃) (ht : ‖t‖ < 1) :
    (jacobsWeight t ht).toChar = jacobsCharOf norm_three_lt_one t ht :=
  rfl

/-- The `y`-extension of the Jacobs column is `kappaSeries₂` itself (the transcribed
series is `y`-degree-`0` concentrated by definition). -/
theorem yExtend_jacobsCol (t : K₃) (ht : ‖t‖ < 1) (c d : K₃) :
    QMF.WeightSeries.yExtend ((jacobsWeight t ht).toWeightSeries.col c d)
      = kappaSeries₂ t c d :=
  (kappaSeries₂_eq_yExtend t c d).symm

/-- The generating function of the headline Jacobs weight is the fork's transcribed
`weightGenFun` (both are `yExtend(κ-column) · linSeries⁻¹ · quadSeries⁻¹`). -/
theorem genFun_jacobsWeight (t : K₃) (ht : ‖t‖ < 1) (g : Matrix (Fin 2) (Fin 2) K₃) :
    (jacobsWeight t ht).toWeightSeries.genFun g = weightGenFun t g := by
  rw [QMF.WeightSeries.genFun, weightGenFun, yExtend_jacobsCol]

/-- **The fork's matrix formula at the headline weight** ([Jacobs, Prop 2.6]): the matrix of
`(jacobsWeight t ht).kappaSlash g` is the coefficient array of `weightGenFun t g`. -/
theorem matrixCoeff_kappaSlash_jacobsWeight (t : K₃) (ht : ‖t‖ < 1) (g : Sigma1₃) (m r : ℕ) :
    TateFredholm.matrixCoeff ((jacobsWeight t ht).kappaSlash g) m r
      = MvPowerSeries.coeff (TateFredholm.idx m r) (weightGenFun t g.1) := by
  rw [QMF.AnalyticWeight.matrixCoeff_kappaSlash, genFun_jacobsWeight]

end JacobsSlash
