/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Weight.«07_Fredholm»
import PhD.TateFredholm.«06_Slopes»
import PhD.NewtonPolygons.OfSlopes
import PhD.NewtonPolygons.CoeffVal

/-!
# Slopes of `det(1 − T·[UηU])` at a general analytic weight

[Jacobs, Thm 2.12] and [Buzzard, *Eigenvarieties*, §13] read the slopes of `U_ϖ` off the
Newton polygon of its Fredholm determinant.  The input is row decay of the matrix, which at a
general analytic weight is the same estimate that makes `[UηU]` compact
(`QMF.Weight.isCompactoid_heckeBlockOp`, via `norm_matrixCoeff_kappaSlash_le`): for `η` with
`‖det θ(η)‖ ≤ σ` and `ρ ≤ σ < 1`, every certificate block has `‖matrixCoeff · j i‖ ≤ σ ^ j`.
Hence `‖cₙ‖ ≤ σ ^ (n choose 2)` (`TateFredholm.norm_charCoeff_le_pow`) and the Newton polygon
of `det(1 − T·[UηU])` lies on or above the polygon of unit slopes `0, v σ, 2 v σ, …`.

## Main declarations

* `QMF.Weight.norm_matrixCoeff_heckeBlock_le`, `norm_matrixCoeff_heckeBlockOp_le` — row decay
  of the certificate blocks and of the block operator.
* `QMF.Weight.norm_charCoeff_heckeCharPowerSeries_le` — **the slope bound**
  `‖cₙ‖ ≤ σ ^ (∑_{k < n} ⌊k/|ι|⌋)`.
* `QMF.Weight.blockSlopes` — the slope sequence `k ↦ ⌊k/|ι|⌋ · (−log σ)` those bounds describe.
* `QMF.Weight.isBelow_newtonPolygon_heckeCharPowerSeries` — **the polygon form**: the Newton
  polygon of `det(1 − T·[UηU])` lies on or above the polygon with those unit slopes.

The valuation used for the polygon is the canonical unnormalised one,
`negLogNorm x = −log ‖x‖` (`PhD.NewtonPolygons.CoeffVal`), so a `⌊k/|ι|⌋`-th unit slope of the
bounding polygon is `⌊k/|ι|⌋ · (−log σ)`.  Rescaling to a pseudo-uniformizer (the thesis's `v₃`,
`PseudoUniformizer.val`) divides every slope by `−log ‖ϖ‖`; the fork does that in
`PhD/JacobsSlash/«4_SlopeReading».lean`.
-/

open TateFredholm
open scoped TateFredholm QMF Pointwise

namespace QMF.Weight

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) K)
variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ} {UK : Subgroup Kˣ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (κ : AnalyticWeight UK S ρ) (U : Subgroup G) (hU : (U : Set G) ⊆ levelMonoidOf θ S)
  (χ : S →* Kˣ)
variable {T : Type*} [Fintype T]

omit [Fintype ι] in
/-- **Row decay of a certificate block** ([Jacobs, Lemma 2.7]'s estimate, kept as an
inequality): each summand is a twisted weight action at an element of determinant norm `≤ σ`,
so `‖matrixCoeff · m r‖ ≤ σ ^ m`. -/
theorem norm_matrixCoeff_heckeBlock_le {σ : ℝ} (hρσ : ρ ≤ σ) {η : G}
    (hdet : ‖(θ η).det‖ ≤ σ) (hnorm : ∀ g : S, ‖((χ g : Kˣ) : K)‖ ≤ 1)
    {vRep : T → G} (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (idx : ι → T → ι) (u : ι → T → U) (i j : ι) (m r : ℕ) :
    ‖matrixCoeff (heckeBlock θ κ U hU χ vRep hvΔ idx u i j) m r‖ ≤ σ ^ m := by
  have hσ0 : 0 ≤ σ := κ.toWeightSeries.bounds.rho_nonneg.trans hρσ
  unfold heckeBlock
  rw [matrixCoeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun t _ => ?_
  rw [matrixCoeff_smul, norm_mul]
  -- The certificate element `u(i,t)·vₜ` has determinant norm `≤ σ`, hence `a`-entry norm `≤ σ`.
  have hdet' := norm_det_toMatrix_certificate_le θ U hU κ.toWeightSeries.bounds hdet hv (u i t) t
  have ha : ‖matrixCoeff (κ.kappaSlash (levelMonoidOfToS θ S
      ⟨(u i t : G) * vRep t, mul_mem (hU (u i t).2) (hvΔ t)⟩)) m r‖ ≤ σ ^ m :=
    κ.toWeightSeries.norm_matrixCoeff_kappaSlash_le _ hρσ
      (κ.toWeightSeries.bounds.norm_apply_zero_zero_le_of_norm_det_le hρσ
        (levelMonoidOfToS θ S
          ⟨(u i t : G) * vRep t, mul_mem (hU (u i t).2) (hvΔ t)⟩).2 hdet') m r
  exact (mul_le_mul (hnorm _) ha (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Row decay of the block operator: `‖matrixCoeff · (i,m) (j,r)‖ ≤ σ ^ m`. -/
theorem norm_matrixCoeff_heckeBlockOp_le {σ : ℝ} (hρσ : ρ ≤ σ) {η : G}
    (hdet : ‖(θ η).det‖ ≤ σ) (hnorm : ∀ g : S, ‖((χ g : Kˣ) : K)‖ ≤ 1)
    {vRep : T → G} (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (idx : ι → T → ι) (u : ι → T → U) (p q : ι × ℕ) :
    ‖matrixCoeff (heckeBlockOp θ κ U hU χ vRep hvΔ idx u) p q‖ ≤ σ ^ p.2 := by
  rw [heckeBlockOp, show p = (p.1, p.2) from rfl, show q = (q.1, q.2) from rfl,
    matrixCoeff_blockOp]
  exact norm_matrixCoeff_heckeBlock_le θ κ U hU χ hρσ hdet hnorm hvΔ hv idx u p.1 q.1 p.2 q.2

/-- **The slope bound for `[UηU]` at a general analytic weight**: the coefficients of
`det(1 − T·[UηU])` satisfy `‖cₙ‖ ≤ σ ^ (∑_{k < n} ⌊k/|ι|⌋)` — the Newton polygon lies on or
above the polygon whose unit slopes are `⌊k/|ι|⌋ · v σ` ([Jacobs, Thm 2.12]'s inequality half,
[Buzzard, §13]). -/
theorem norm_charCoeff_heckeCharPowerSeries_le {σ : ℝ} (hρσ : ρ ≤ σ) (hσ0 : 0 ≤ σ) (hσ : σ < 1)
    {η : G} (hdet : ‖(θ η).det‖ ≤ σ) (hnorm : ∀ g : S, ‖((χ g : Kˣ) : K)‖ ≤ 1)
    {vRep : T → G} (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (idx : ι → T → ι) (u : ι → T → U) (n : ℕ) :
    ‖PowerSeries.coeff n (heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u)‖
      ≤ σ ^ (∑ k ∈ Finset.range n, k / Fintype.card ι) := by
  rw [heckeCharPowerSeries, charPowerSeries_coeff]
  exact TateFredholm.norm_charCoeff_le_pow_block hσ0 hσ
    (isCompactoid_heckeBlockOp θ κ U hU χ hρσ hσ hdet hvΔ hv idx u)
    (fun p q => norm_matrixCoeff_heckeBlockOp_le θ κ U hU χ hρσ hdet hnorm hvΔ hv idx u p q) n

/-! ### The polygon form -/

open Finset in
/-- The slope sequence bounded by [Jacobs, Thm 2.12] in the block model with `d` blocks: the
`k`-th unit slope is `⌊k/d⌋ · (−log σ)`, i.e. each value `0, −log σ, 2(−log σ), …` is repeated
`d` times (once per block). -/
noncomputable def blockSlopes (d : ℕ) (σ : ℝ) : ℕ → ℝ :=
  fun k => ((k / d : ℕ) : ℝ) * (-Real.log σ)

theorem monotone_blockSlopes {d : ℕ} {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1) :
    Monotone (blockSlopes d σ) := fun k l hkl => by
  refine mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.div_le_div_right hkl)) ?_
  simpa using Real.log_nonpos hσ0 hσ

theorem sum_blockSlopes (d : ℕ) {σ : ℝ} (k : ℕ) :
    ∑ i ∈ Finset.range k, blockSlopes d σ i
      = ((∑ i ∈ Finset.range k, i / d : ℕ) : ℝ) * (-Real.log σ) := by
  simp only [blockSlopes]
  rw [← Finset.sum_mul, Nat.cast_sum]

/-- **The slope theorem for `[UηU]` at a general analytic weight** ([Jacobs, Thm 2.12]'s
inequality half; [Buzzard, *Eigenvarieties*, §13]; [Serre1962, §5]): the Newton polygon of
`det(1 − T·[UηU])`, taken with respect to `negLogNorm = −log ‖·‖`, lies on or above the polygon
anchored at the origin whose `k`-th unit slope is `⌊k/|ι|⌋ · (−log σ)`.

In words: on the `|ι|`-dimensional block model, the slopes of `U_ϖ` at weight `κ` are at least
`0, 0, …, −log σ, −log σ, …` — each value repeated once per block.  The fork's exact-slope
theorem (unit minors) is the special case where this bound is attained. -/
theorem isBelow_newtonPolygon_heckeCharPowerSeries {σ : ℝ} (hρσ : ρ ≤ σ) (hσ0 : 0 < σ)
    (hσ : σ < 1) {η : G} (hdet : ‖(θ η).det‖ ≤ σ) (hnorm : ∀ g : S, ‖((χ g : Kˣ) : K)‖ ≤ 1)
    {vRep : T → G} (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (idx : ι → T → ι) (u : ι → T → U) :
    (NewtonPolygon₀.ofSlopes (blockSlopes (Fintype.card ι) σ)
        (monotone_blockSlopes hσ0.le hσ.le) 0).IsBelow
      (newtonPolygon₀OfPowerSeries negLogNorm
        (heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u)) := by
  set f := heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u with hfdef
  -- `c₀ = 1`, so the polygon is anchored at the origin, exactly like the explicit witness.
  have hc0 : PowerSeries.coeff 0 f = 1 := by
    rw [hfdef, heckeCharPowerSeries, charPowerSeries_coeff, charCoeff_zero]
  have h1 : ∃ i, coeffVal f i ≠ ⊤ :=
    ⟨0, (coeffVal_zero_of_coeff_zero_eq_one hc0).trans_ne WithTop.coe_ne_top⟩
  -- The slope bound, in the logarithmic form the polygon consumes.
  have hbound : ∀ k, ‖PowerSeries.coeff k f‖
      ≤ σ ^ (∑ i ∈ Finset.range k, i / Fintype.card ι) := fun k =>
    norm_charCoeff_heckeCharPowerSeries_le θ κ U hU χ hρσ hσ0.le hσ hdet hnorm hvΔ hv idx u k
  have hlog : ∀ k, PowerSeries.coeff k f ≠ 0 →
      ∑ i ∈ Finset.range k, blockSlopes (Fintype.card ι) σ i
        ≤ -Real.log ‖PowerSeries.coeff k f‖ := by
    intro k hk
    have h2 := Real.log_le_log (norm_pos_iff.2 hk) (hbound k)
    rw [Real.log_pow] at h2
    rw [sum_blockSlopes]
    linarith
  -- Admissibility: every coefficient has norm `≤ 1`, so every point is at height `≥ 0`.
  have h2 : IsAdmissible (coeffVal f) := by
    refine isAdmissible_of_affine_bound (coeffVal f) (m := 0) (b := 0) fun k a hva => ?_
    have hk : PowerSeries.coeff k f ≠ 0 := fun hcz =>
      WithTop.coe_ne_top (hva.symm.trans (coeffVal_eq_top_iff.mpr hcz))
    have haeq : a = -Real.log ‖PowerSeries.coeff k f‖ :=
      WithTop.coe_inj.mp (hva.symm.trans (coeffVal_of_ne_zero hk))
    have hle1 : ‖PowerSeries.coeff k f‖ ≤ 1 :=
      (hbound k).trans (pow_le_one₀ hσ0.le hσ.le)
    have := Real.log_nonpos (norm_nonneg _) hle1
    simp only [Algebra.algebraMap_self, RingHom.id_apply, haeq]
    linarith
  refine (isNewtonPolygonOf_powerSeries negLogNorm f h1 h2).isGreatest _ ?_ ?_
  · rw [NewtonPolygon₀.ofSlopes_starting_point,
      newtonPolygon₀_starting_point_of_coeff_zero_eq_one hc0]
  · intro k
    rw [show coeffSeq negLogNorm f = coeffVal f from rfl,
      NewtonPolygon₀.height_ofSlopes, zero_add]
    by_cases hk : PowerSeries.coeff k f = 0
    · rw [pointHeight_eq_top_iff.2 (coeffVal_eq_top_iff.2 hk)]
      exact le_top
    · rw [pointHeight_coe (coeffVal_of_ne_zero hk), Algebra.algebraMap_self_apply]
      exact WithBotTop.coe_le_coe.2 (hlog k hk)

end QMF.Weight
