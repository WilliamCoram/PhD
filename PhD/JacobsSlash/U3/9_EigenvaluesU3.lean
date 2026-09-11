/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.U3.«8_HeckeSlopes»
import PhD.JacobsSlash.U3.«2_PadicEmbedding»
import PhD.JacobsSlash.«5_EigenSlopes»
import PhD.JacobsSlash.«5_Instance»
import PhD.JacobsSlash.U3.«7_DiamondHecke»

/-!
# The eigenvalues of `U₃` have valuation `j + ½`

**The culmination of the development** — Riesz theory (`PhD.TateFredholm.«09_Riesz»`), the
Newton-polygon zero theory (`PhD.NewtonPolygons`), and the fork's identification of the
genuine Hecke operator (`PhD.JacobsSlash`), composed:

over `ℂ₃`, for every `j : ℕ`, the base-changed matrix of `U₃ = [U₁(9)·η₃·U₁(9)]` has an
eigenvalue `a` of `3`-adic valuation `j + ½` (stated without `rpow` as
`‖a‖² = ‖3‖^(2j+1)`), whose reciprocal is a zero of the base-changed Fredholm
determinant `det(1 − T·U₃)` of the genuine operator, and whose eigenvector lies in the
`ω`-eigenblock of the transcribed diamond operator (`Binvop_comp_Wop_comp_Bop`; the
thesis's "`ω²`-eigenspace of `⟨w⟩`" wording [Jacobs, p. 34] is the same statement under
the primitive-root relabeling `ω ↦ ω²`).

The chain: `charPowerSeriesU3` (the genuine determinant, `«7_Fredholm»`) base-changes
along the isometric `ιC : K₃ →+* ℂ₃` (`«2_PadicEmbedding»`) to the transcribed matrix
(`map_charPowerSeriesU3`, `«8_HeckeSlopes»`); the `4_SlopeReading` slope data of the
middle factor, rescaled to `negLogNorm`, feeds the general bridge
`exists_eigenvector_of_slope_charPowerSeries` (`«5_EigenSlopes»`) — every slope is the
valuation of a reciprocal eigenvalue — and the eigenvector transports along the
diagonalising `B` into the assembled matrix.  The zero of the determinant is certified
by the eigenvector itself (`evalT_charPowerSeries_eq_zero_iff`), so no
Newton-polygon-of-a-product theorem is needed — matching the thesis's own restraint.

`hcn : HClassNumberOne` appears nowhere: the statement is about the certificate block
operator, unconditionally; `hcn` is only needed to read the model as *all* of
`L(U₁(9), A₃)` (`kappaFormsModelEquiv`, `«7_Fredholm»`).
-/

open TateFredholm Quaternion IsDedekindDomain NumberField QMF

namespace JacobsSlash

/-- A fixed primitive cube root of unity in `ℂ₃`. -/
noncomputable def ωC : ℂ_[3] := Classical.choose Instance.exists_omega

theorem ωC_spec : ωC ^ 2 + ωC + 1 = 0 := Classical.choose_spec Instance.exists_omega

/-- **THE CRUX** ([Jacobs, Cor 2.16] as an eigenvalue statement about the genuine `U₃`):
over `ℂ₃`, for every `j : ℕ` the base-changed matrix of `U₃ = [U₁(9)·η₃·U₁(9)]` has an
eigenvalue `a` of `3`-adic valuation `j + ½` (`‖a‖² = ‖3‖^(2j+1)`); its reciprocal is a
zero of the base-changed Fredholm determinant `det(1 − T·U₃)` of the genuine operator,
and its eigenvector lies in the `ω`-eigenblock of the transcribed diamond operator. -/
theorem exists_eigenvalue_U3_halfIntegral (t : K₃) (ht : ‖t‖ < 1) (j : ℕ) :
    ∃ (a : ℂ_[3]) (y : c(Fin 3 × ℕ, ℂ_[3])), a ≠ 0 ∧ y ≠ 0 ∧
      U3MatrixOp (norm_three_lt_one_of_isometry ιC norm_ιC)
          (norm_map_weight_lt_one ιC norm_ιC ht) (map_ν₃_near ιC norm_ιC) y = a • y ∧
      ‖a‖ ^ 2 = ‖(3 : ℂ_[3])‖ ^ (2 * j + 1) ∧
      PowerSeries.evalT a⁻¹ (PowerSeries.map ιC (charPowerSeriesU3 t ht)) = 0 ∧
      Wop (norm_three_lt_one_of_isometry ιC norm_ιC)
          (norm_map_weight_lt_one ιC norm_ιC ht) y = ωC • y := by
  obtain ⟨a, x, ha0, hx0, hax, hnorm⟩ := exists_eigenvector_M22op ωC ωC_spec
    (norm_three_lt_one_of_isometry ιC norm_ιC) (norm_map_weight_lt_one ιC norm_ιC ht)
    (map_sq_ν₃ ιC) (map_ν₃_near ιC norm_ιC) j
  obtain ⟨y, hy0, hyU3, hyW⟩ := exists_eigenvector_U3MatrixOp_of_M22 ωC ωC_spec
    (norm_three_lt_one_of_isometry ιC norm_ιC) (norm_map_weight_lt_one ιC norm_ιC ht)
    (map_ν₃_near ιC norm_ιC) hx0 hax
  refine ⟨a, y, ha0, hy0, hyU3, hnorm, ?_, hyW⟩
  rw [map_charPowerSeriesU3 ιC norm_ιC t ht]
  exact (evalT_charPowerSeries_eq_zero_iff _
    (isCompactoid_U3MatrixOp (norm_three_lt_one_of_isometry ιC norm_ιC)
      (norm_map_weight_lt_one ιC norm_ιC ht) (map_ν₃_near ιC norm_ιC))
    (inv_ne_zero ha0)).mpr ⟨y, hy0, by rw [inv_inv]; exact hyU3⟩

/-! ### The culmination: one composed statement

`«7_DiamondHecke»` identifies the transcribed diamond operator with the genuine Hecke
operator `W = [U₁(9)·μ·U₁(9)]` — twist-free: `heckeW_apply_classRep_eq_delta` says `W`
acts on the `i`-th class representative by `deltaOf i`, and `Wop_eq_blockOp_deltaOf`
(`«4_DiamondW»`) says that `σ_W`-indexed `δ`-matrix *is* `Wop`.  So `Wop` over `K₃` is
the matrix of the genuine `W`, and `map_Wop` base-changes it along `ιC`.  The clause
below therefore reads: **`y` is an `ω`-eigenvector of the base change of the matrix of
the genuine diamond operator** — a single statement, not two parallel facts. -/

/-- **THE CULMINATION** (Riesz + Newton polygons + the fork's two identifications):
for every `j : ℕ` the genuine `U₃ = [U₁(9)·η₃·U₁(9)]` has, over `ℂ₃`, an eigenvalue of
`3`-adic valuation `j + ½` whose reciprocal is a zero of `det(1 − T·U₃)` and whose
eigenvector lies in the `ω`-eigenspace of **the base change of the matrix of the genuine
diamond operator** `W = [U₁(9)·μ·U₁(9)]` — that matrix being `Wop` by
`heckeW_apply_classRep_eq_delta` together with `Wop_eq_blockOp_deltaOf`.

This is [Jacobs, Cor 2.16] together with the [Jacobs, Lemma 2.9/2.10] eigenspace
reading, as one theorem about the genuine Hecke operators (the thesis's "`ω²`-eigenspace
of `⟨w⟩`" wording is this statement under the primitive-root relabeling `ω ↦ ω²`).
Unconditional: `HClassNumberOne` is needed only to know the block model is *all* of
`L(U₁(9), A₃)`. -/
theorem exists_eigenvalue_U3_in_W_eigenspace (t : K₃) (ht : ‖t‖ < 1) (j : ℕ) :
    ∃ (a : ℂ_[3]) (y : c(Fin 3 × ℕ, ℂ_[3])), a ≠ 0 ∧ y ≠ 0 ∧
      U3MatrixOp (norm_three_lt_one_of_isometry ιC norm_ιC)
          (norm_map_weight_lt_one ιC norm_ιC ht) (map_ν₃_near ιC norm_ιC) y = a • y ∧
      ‖a‖ ^ 2 = ‖(3 : ℂ_[3])‖ ^ (2 * j + 1) ∧
      PowerSeries.evalT a⁻¹ (PowerSeries.map ιC (charPowerSeriesU3 t ht)) = 0 ∧
      ∀ W' : c(Fin 3 × ℕ, ℂ_[3]) →L[ℂ_[3]] c(Fin 3 × ℕ, ℂ_[3]),
        (∀ x z, matrixCoeff W' x z = ιC (matrixCoeff (Wop norm_three_lt_one ht) x z)) →
        W' y = ωC • y := by
  obtain ⟨a, y, ha0, hy0, hyU3, hnorm, hzero, hyW⟩ :=
    exists_eigenvalue_U3_halfIntegral t ht j
  refine ⟨a, y, ha0, hy0, hyU3, hnorm, hzero, fun W' hW' => ?_⟩
  have hWeq : W' = Wop (norm_three_lt_one_of_isometry ιC norm_ιC)
      (norm_map_weight_lt_one ιC norm_ιC ht) :=
    TateFredholm.ext_matrixCoeff fun x z => by
      rw [hW' x z, ← map_Wop ιC norm_ιC norm_three_lt_one ht x z]
  rw [hWeq]
  exact hyW

end JacobsSlash
