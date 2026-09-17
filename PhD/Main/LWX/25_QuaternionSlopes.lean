/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«23_QuaternionData»
import PhD.Main.LWX.«24_DegreePeriodicity»

/-!
# [LWX, Thms 1.3, 1.5, Cor 1.4] for a definite quaternion algebra over `ℚ`

The headline theorems of `23_ConductorSlopes.lean` and `24_DegreePeriodicity.lean`, read off the
`U_p`-datum `QuaternionInput.upDatum` of `D/ℚ` (`23_QuaternionData.lean`): the unit band at every
vertex, the degree formulas of [LWX, Thm 1.3] and their positivity, [LWX, Cor 1.4], the second
half of [LWX, Thm 1.5] and (1.5.1) for the genuine `U_p` on `S^{D,†,m}`.  The coefficient field
`K` enters only through the hypotheses (a primitive `p`-th root of unity and an algebraically
closed `K` receiving `ℚ_p` isometrically); the conclusions are statements about the integral datum.
-/

open IsDedekindDomain NumberField Filter Topology TateFredholm QMF QMF.Weight
  AbstractHeckeOperatorSlash RightSlashAction
open scoped TateFredholm Pointwise

noncomputable section

namespace LWX

namespace QuaternionInput

variable {p : ℕ} [hp : Fact p.Prime]
variable {D : Type*} [Ring D] [Algebra ℚ D] [RigidificationAt ℚ D (padicPlace p)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (X : QuaternionInput p D ι)
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable (ψ : ℚ_[p] →+* K) {ζ : K}

/-- **The unit band at every vertex of the spectral halo of `D/ℚ`.** -/
theorem hasUnitBand (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) : HasUnitBand X.upDatum ω n :=
  hasUnitBand_of_atkinLehnerFamily (thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt
    (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ injective_vRepQ X.c
    X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape hp2 hψ hζ ω n

/-- **[LWX, Thm 1.3] for `D/ℚ`: `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})`.** -/
theorem degX_succ [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX X.upDatum ω (k + 1)
      = ordDim X.upDatum (partnerChar p ω k) + ordDim X.upDatum (targetChar p ω k) :=
  degX_succ_of_atkinLehnerFamily (thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt
    (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ injective_vRepQ X.c
    X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape X.det_certM1_eq hp2 hψ hζ ω k

/-- **[LWX, Thm 1.3] for `D/ℚ`:**
`deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n})`. -/
theorem degXint_eq [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint X.upDatum ω n
      = p * Fintype.card ι - ordDim X.upDatum (partnerChar p ω n)
        - ordDim X.upDatum (ω * (teichChar p ^ (2 * n))⁻¹) :=
  degXint_of_atkinLehnerFamily (thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt
    (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ injective_vRepQ X.c
    X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape X.det_certM1_eq hp2 hψ hζ ω n

/-- **[LWX, Thm 1.3] for `D/ℚ`: `deg X_{(n,n+1),ω} > 0`.** -/
theorem degXint_pos [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    0 < degXint X.upDatum ω n :=
  degXint_pos_of_atkinLehnerFamily (thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt
    (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ injective_vRepQ X.c
    X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape X.det_certM1_eq hp2 hψ hζ ω n

/-- **[LWX, Cor 1.4] for `D/ℚ`**: `deg X_{n,ω}` is periodic modulo `(p−1)/2` in `n ≥ 1`. -/
theorem degX_succ_add_period [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX X.upDatum ω (k + 1 + (p - 1) / 2) = degX X.upDatum ω (k + 1) :=
  _root_.LWX.degX_succ_add_period (thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt
    (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ injective_vRepQ X.c
    X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape X.det_certM1_eq hp2 hψ hζ ω k

/-- **[LWX, Cor 1.4] for `D/ℚ`**: `deg X_{(n,n+1),ω}` is periodic modulo `(p−1)/2`. -/
theorem degXint_add_period [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint X.upDatum ω (n + (p - 1) / 2) = degXint X.upDatum ω n :=
  _root_.LWX.degXint_add_period (thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt
    (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ injective_vRepQ X.c
    X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape X.det_certM1_eq hp2 hψ hζ ω n

/-- **[LWX, Thm 1.5 (1.5.1)] for the genuine `U_p` of `D/ℚ`**: at every halo point of the
slope-reading region and every analyticity level, every slope of `det(1 − X·U_p)` on `S^{D,†,m}`
is `v(T₀)` times a `T`-free ratio. -/
theorem unitSlope_discHeckeCharPowerSeries_eq_slopeRatio (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries (thetaInt p D) h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT)
            X.level X.level_subset_levelM1 (vRepQ p D) (vRepQ_mem_levelM1 p D) X.idx
            X.uElt)).unitSlope j
      = (((-Real.log ‖T₀‖) * slopeRatio X.upDatum ω j : ℝ) : WithBotTop ℝ) :=
  unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily (thetaInt p D) h ψ X.level
    X.level_subset_levelM1 X.idx X.uElt
    (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ injective_vRepQ X.c
    X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape hp2 hψ hζ ω h0 h1
    hT hκ j

/-- **[LWX, Thm 1.5, second half] for `D/ℚ`, at the polygon level**: the arithmetic progressions
of period `(p−1)/2·p^h t` and common difference `(p−1)/2·p^{h−1}(p−1)`. -/
theorem slopeRatio_add_period [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (h : ℕ) (hh : 0 < h) {ζh : K} (hζh : IsPrimitiveRoot ζh (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (j : ℕ) :
    slopeRatio X.upDatum ω (j + (p - 1) / 2 * (p ^ h * Fintype.card ι))
      = slopeRatio X.upDatum ω j + (((p - 1) / 2 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) :=
  _root_.LWX.slopeRatio_add_period (thetaInt p D) h ψ X.level X.level_subset_levelM1 X.idx X.uElt
    (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ injective_vRepQ X.c
    X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape
    (X.atkinLehnerFamilyH ψ hp2 hψ hζ h hh hζh) X.det_certM1_eq hp2 hψ hh hζ hζh hM ω j

end QuaternionInput

end LWX

end
