/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.TateFredholm.«04_Matrix»
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Infinite matrices, generating functions, and operators on `c(ℕ, K)`

[Jacobs, *Slopes of Compact Hecke Operators*, §1.1] works with `ℕ × ℕ` matrices over a
ring through their generating functions `H_A(x, y) = ∑ a_{i,j} xⁱ yʲ`, and §1.2 (after
[Serre, IHÉS 12]) with the compact operators they induce on the Banach space `c(ℕ, K)`.
This file provides the dictionary, on top of `PhD.Main.TateFredholm`:

* `Jacobs.idx j i` — the exponent `(j, i)` as a multidegree in `Fin 2 →₀ ℕ` (`x`-degree
  `j` = row, `y`-degree `i` = column, matching the thesis's `∑ a_m^{(r)} x^m y^r` with
  rows `m`).
* `Jacobs.ofCoeffs M` — the operator `c(ℕ, K) →L[K] c(ℕ, K)` with matrix `M` (bounded
  entries, columns vanishing at infinity), i.e. `e_i ↦ ∑_j M j i • e_j`.
* `Jacobs.ofGenFun F` — the operator attached to a two-variable power series.
* `Jacobs.diagRescale α β F` — the coefficientwise rescaling `F(αx, βy)`; the diagonal
  matrices `D(α)` of [Jacobs, Notation 1.2] act on generating functions through it
  ([Jacobs, Proposition 1.3]).
* `Jacobs.diagOp a` — the diagonal operator `diag(a₀, a₁, …)` for `‖a n‖ ≤ 1`.
* compactness from row decay: [Jacobs, Corollary 1.10] in compactoid form.
-/

open TateFredholm
open scoped TateFredholm
open Filter Topology

namespace Jacobs

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The multidegree `x^j y^i` as an element of `Fin 2 →₀ ℕ`: variable `0` is `x` (row
index), variable `1` is `y` (column index). -/
noncomputable def idx (j i : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j + Finsupp.single 1 i

/-- The `x`-degree of `idx j i` is the row index `j`. -/
@[simp] theorem idx_apply_zero (j i : ℕ) : idx j i 0 = j := by
  simp [idx]

/-- The `y`-degree of `idx j i` is the column index `i`. -/
@[simp] theorem idx_apply_one (j i : ℕ) : idx j i 1 = i := by
  simp [idx]

/-- `idx` is injective in both arguments. -/
theorem idx_injective : Function.Injective fun p : ℕ × ℕ => idx p.1 p.2 := by
  intro p q h
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
  simp only [idx_apply_zero, idx_apply_one] at h0 h1
  exact Prod.ext h0 h1

/-- **Extensionality in matrix coefficients**: an operator between coefficient spaces is
determined by its matrix.  (From `norm_eq_iSup_matrixCoeff` applied to the difference: all
its coefficients vanish, so `‖u − v‖ = 0`, and the operator-norm bound finishes.)  Stated
here rather than in `TateFredholm.Matrix` because the last step needs the base to be a
nontrivially normed field. -/
theorem ext_matrixCoeff [IsTate K] {I J : Type*} [DecidableEq I] [DecidableEq J]
    {u v : c(I, K) →L[K] c(J, K)}
    (h : ∀ j i, matrixCoeff u j i = matrixCoeff v j i) : u = v := by
  have hz : ‖u - v‖ = 0 := by
    rw [norm_eq_iSup_matrixCoeff]
    have hterm : ∀ j : J, (⨆ i : I, ‖matrixCoeff (u - v) j i‖) = 0 := fun j => by
      simp [TateFredholm.matrixCoeff_sub, h j]
    rcases isEmpty_or_nonempty J with hJ | hJ
    · simp
    · simp only [hterm]
      exact ciSup_const
  refine ContinuousLinearMap.ext fun f => ?_
  have hle : ‖(u - v) f‖ ≤ 0 := by
    have hop := TateFredholm.le_opNorm (u - v) f
    rwa [hz, zero_mul] at hop
  have h0 : (u - v) f = 0 := norm_le_zero_iff.mp hle
  rw [sub_apply] at h0
  exact sub_eq_zero.mp h0

section OfCoeffs

variable {M : ℕ → ℕ → K} {C : ℝ}

set_option linter.unusedSectionVars false in
/-- A bound for the entries of a matrix indexed by a nonempty type is nonnegative. -/
private theorem bound_nonneg (hbd : ∀ j i, ‖M j i‖ ≤ C) : 0 ≤ C :=
  (norm_nonneg (M 0 0)).trans (hbd 0 0)

/-- The elementary estimate behind the `ε`-management of `tendsto_tsum_row`: if `a` is at
most `δ / (t + 1)` and `b` at most `t`, then `a * b ≤ δ`. -/
private theorem mul_le_of_le_div_add_one {a b t δ : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (ha : a ≤ δ / (t + 1)) (hb' : b ≤ t) : a * b ≤ δ := by
  have ht : (0 : ℝ) ≤ t := hb.trans hb'
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  refine (mul_le_mul ha hb' hb (by positivity)).trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ ht1]
  nlinarith

/-- A row of a matrix with bounded entries multiplies a vanishing family into a vanishing
family: `i ↦ M j i * f i` tends to `0` cofinitely, hence is summable. -/
private theorem tendsto_row_mul (hbd : ∀ j i, ‖M j i‖ ≤ C) (f : c(ℕ, K)) (j : ℕ) :
    Tendsto (fun i => M j i * f i) cofinite (𝓝 0) := by
  refine squeeze_zero_norm (a := fun i => C * ‖f i‖) (fun i => ?_) ?_
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbd j i) (norm_nonneg _))
  · have h0 : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0) := by
      simpa using (cSpace.tendsto_cofinite f).norm
    simpa using h0.const_mul C

/-- The rows of the image are bounded by `C ‖f‖` (ultrametrically, the sum is no larger
than its largest term). -/
private theorem norm_tsum_row_le (hbd : ∀ j i, ‖M j i‖ ≤ C) (f : c(ℕ, K)) (j : ℕ) :
    ‖∑' i, M j i * f i‖ ≤ C * ‖f‖ := by
  have hC : 0 ≤ C * ‖f‖ := mul_nonneg (bound_nonneg hbd) (norm_nonneg f)
  refine (norm_tsum_le_iSup (tendsto_row_mul hbd f j)).trans (Real.iSup_le (fun i => ?_) hC)
  calc ‖M j i * f i‖ ≤ ‖M j i‖ * ‖f i‖ := norm_mul_le _ _
  _ ≤ C * ‖f‖ :=
    mul_le_mul (hbd j i) (cSpace.norm_apply_le f i) (norm_nonneg _) (bound_nonneg hbd)

/-- The image family vanishes at infinity.  Given `ε`, all but finitely many coordinates
`i` have `‖f i‖` small, and there the bounded entries `M j i` keep the terms small
uniformly in `j`; on the remaining finite set the columns of `M` vanish, so the terms are
small for all but finitely many `j`. -/
private theorem tendsto_tsum_row (hbd : ∀ j i, ‖M j i‖ ≤ C)
    (hcol : ∀ i, Tendsto (fun j => M j i) cofinite (𝓝 0)) (f : c(ℕ, K)) :
    Tendsto (fun j => ∑' i, M j i * f i) cofinite (𝓝 0) := by
  have hC : 0 ≤ C := bound_nonneg hbd
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ, 0 < δ ∧ δ < ε := ⟨ε / 2, by linarith, by linarith⟩
  -- The coordinates where `f` is not yet small form a finite set `S`.
  have hev : ∀ᶠ i in cofinite, ‖f i‖ < δ / (C + 1) :=
    NormedAddGroup.tendsto_nhds_zero.1 (cSpace.tendsto_cofinite f) _ (by positivity)
  set S := (Filter.eventually_cofinite.1 hev).toFinset with hS
  have hout : ∀ i ∉ S, ‖f i‖ ≤ δ / (C + 1) := by
    intro i hi
    rw [hS, Set.Finite.mem_toFinset] at hi
    exact (not_not.1 hi).le
  -- On `S` the columns vanish, uniformly over the finitely many members.
  have hin : ∀ᶠ j in cofinite, ∀ i ∈ S, ‖M j i‖ ≤ δ / (‖f‖ + 1) :=
    (Filter.eventually_all_finset S).2 fun i _ =>
      (NormedAddGroup.tendsto_nhds_zero.1 (hcol i) _ (by positivity)).mono fun _ h => h.le
  filter_upwards [hin] with j hj
  refine lt_of_le_of_lt ?_ hδε
  refine (norm_tsum_le_iSup (tendsto_row_mul hbd f j)).trans (Real.iSup_le (fun i => ?_) hδ.le)
  refine (norm_mul_le _ _).trans ?_
  by_cases hi : i ∈ S
  · exact mul_le_of_le_div_add_one hδ.le (norm_nonneg _) (hj i hi) (cSpace.norm_apply_le f i)
  · rw [mul_comm]
    exact mul_le_of_le_div_add_one hδ.le (norm_nonneg _) (hout i hi) (hbd j i)

/-- The image of `f` under the matrix `M`, as an element of the model space. -/
private noncomputable def ofCoeffsFun (hbd : ∀ j i, ‖M j i‖ ≤ C)
    (hcol : ∀ i, Tendsto (fun j => M j i) cofinite (𝓝 0)) (f : c(ℕ, K)) : c(ℕ, K) :=
  ⟨⟨fun j : Ix ℕ => ∑' i, M j i * f i, continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    exact tendsto_tsum_row hbd hcol f⟩

private theorem ofCoeffsFun_apply (hbd : ∀ j i, ‖M j i‖ ≤ C)
    (hcol : ∀ i, Tendsto (fun j => M j i) cofinite (𝓝 0)) (f : c(ℕ, K)) (j : ℕ) :
    ofCoeffsFun hbd hcol f j = ∑' i, M j i * f i := rfl

private theorem norm_ofCoeffsFun_le (hbd : ∀ j i, ‖M j i‖ ≤ C)
    (hcol : ∀ i, Tendsto (fun j => M j i) cofinite (𝓝 0)) (f : c(ℕ, K)) :
    ‖ofCoeffsFun hbd hcol f‖ ≤ C * ‖f‖ := by
  rw [cSpace.norm_eq_iSup]
  refine Real.iSup_le (fun j => ?_) (mul_nonneg (bound_nonneg hbd) (norm_nonneg f))
  rw [ofCoeffsFun_apply]
  exact norm_tsum_row_le hbd f j

/-- The linear map underlying `ofCoeffs`; linearity is `tsum` additivity plus
`tsum_mul_left`, both available since the rows are summable. -/
private noncomputable def ofCoeffsLinear (hbd : ∀ j i, ‖M j i‖ ≤ C)
    (hcol : ∀ i, Tendsto (fun j => M j i) cofinite (𝓝 0)) : c(ℕ, K) →ₗ[K] c(ℕ, K) where
  toFun := ofCoeffsFun hbd hcol
  map_add' f g := by
    refine DFunLike.ext _ _ fun j => ?_
    show (∑' i, M j i * (f + g) i) = (∑' i, M j i * f i) + (∑' i, M j i * g i)
    rw [← ((summable_of_tendsto_cofinite (tendsto_row_mul hbd f j)).hasSum.add
      (summable_of_tendsto_cofinite (tendsto_row_mul hbd g j)).hasSum).tsum_eq]
    exact tsum_congr fun i => mul_add (M j i) (f i) (g i)
  map_smul' r f := by
    refine DFunLike.ext _ _ fun j => ?_
    show (∑' i, M j i * (r • f) i) = r * ∑' i, M j i * f i
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    show M j i * (r * f i) = r * (M j i * f i)
    rw [mul_left_comm]

end OfCoeffs

/-- The operator `c(ℕ, K) →L[K] c(ℕ, K)` attached to a matrix `M : ℕ → ℕ → K` (row
index first) with uniformly bounded entries and columns vanishing at infinity:
`(ofCoeffs M h) f = fun j => ∑' i, M j i * f i`, so that `e_i ↦ ∑_j M j i • e_j`.
[Jacobs, §1.2] after [Serre, Proposition 3] (`TateFredholm.exists_coeffEquiv` is the
norm-preserving version of the same correspondence). -/
noncomputable def ofCoeffs (M : ℕ → ℕ → K)
    (hbd : ∃ C, ∀ j i, ‖M j i‖ ≤ C)
    (hcol : ∀ i, Filter.Tendsto (fun j => M j i) Filter.cofinite (nhds 0)) :
    c(ℕ, K) →L[K] c(ℕ, K) :=
  LinearMap.mkContinuous (ofCoeffsLinear hbd.choose_spec hcol) hbd.choose
    (norm_ofCoeffsFun_le hbd.choose_spec hcol)

/-- `ofCoeffs M` acts by the row sums `∑' i, M j i * f i`. -/
theorem ofCoeffs_apply (M : ℕ → ℕ → K) (hbd : ∃ C, ∀ j i, ‖M j i‖ ≤ C)
    (hcol : ∀ i, Filter.Tendsto (fun j => M j i) Filter.cofinite (nhds 0)) (f : c(ℕ, K))
    (j : ℕ) : ofCoeffs M hbd hcol f j = ∑' i, M j i * f i := rfl

/-- The matrix of `ofCoeffs M` is `M`. -/
theorem matrixCoeff_ofCoeffs (M : ℕ → ℕ → K) (hbd : ∃ C, ∀ j i, ‖M j i‖ ≤ C)
    (hcol : ∀ i, Filter.Tendsto (fun j => M j i) Filter.cofinite (nhds 0)) (j i : ℕ) :
    matrixCoeff (ofCoeffs M hbd hcol) j i = M j i := by
  show (∑' i', M j i' * cSpace.single i (1 : K) i') = M j i
  rw [tsum_eq_single i fun i' hi' => by rw [cSpace.single_apply_of_ne hi', mul_zero],
    cSpace.single_apply_self, mul_one]

set_option linter.unusedSectionVars false in
/-- Row decay `‖M j i‖ ≤ c * ‖q‖ ^ j` (uniform in `i`, with `‖q‖ < 1`) supplies both
hypotheses of `ofCoeffs`. -/
theorem hyps_of_row_decay {M : ℕ → ℕ → K} {q c : K} (hq : ‖q‖ < 1)
    (h : ∀ j i, ‖M j i‖ ≤ ‖c‖ * ‖q‖ ^ j) :
    (∃ C, ∀ j i, ‖M j i‖ ≤ C) ∧
      ∀ i, Filter.Tendsto (fun j => M j i) Filter.cofinite (nhds 0) := by
  have hgeom : Tendsto (fun j : ℕ => ‖c‖ * ‖q‖ ^ j) cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop]
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul ‖c‖
  refine ⟨⟨‖c‖, fun j i => (h j i).trans ?_⟩, fun i => ?_⟩
  · calc ‖c‖ * ‖q‖ ^ j ≤ ‖c‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg q) hq.le) (norm_nonneg c)
    _ = ‖c‖ := mul_one _
  · exact squeeze_zero_norm (fun j => h j i) hgeom

/-- **[Jacobs, Corollary 1.10] / [Serre, corollary to Proposition 4]** in compactoid
form: an operator whose matrix has geometric row decay is compactoid (its row sups
`r_j(u) ≤ ‖c‖ ‖q‖ ^ j` vanish at infinity). -/
theorem isCompactoid_of_row_decay {u : c(ℕ, K) →L[K] c(ℕ, K)} {q c : K} (hq : ‖q‖ < 1)
    (h : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖c‖ * ‖q‖ ^ j) : IsCompactoid u := by
  have hgeom : Tendsto (fun j : ℕ => ‖c‖ * ‖q‖ ^ j) cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop]
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul ‖c‖
  have hle : ∀ j, rowNorm u j ≤ ‖c‖ * ‖q‖ ^ j := fun j =>
    Real.iSup_le (fun i => h j i) (by positivity)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom
    (fun j => rowNorm_nonneg u j) hle

section GenFun

/-- The operator attached to a two-variable power series `F = ∑ a_{j,i} x^j y^i`
(matrix `a_{j,i}` = coefficient of `x^j y^i`, rows `j`).  [Jacobs, §1.1]'s dictionary
between matrices and generating functions, composed with `ofCoeffs`. -/
noncomputable def ofGenFun (F : MvPowerSeries (Fin 2) K)
    (hbd : ∃ C, ∀ j i, ‖MvPowerSeries.coeff (idx j i) F‖ ≤ C)
    (hcol : ∀ i, Filter.Tendsto (fun j => MvPowerSeries.coeff (idx j i) F)
      Filter.cofinite (nhds 0)) :
    c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun j i => MvPowerSeries.coeff (idx j i) F) hbd hcol

/-- The matrix of `ofGenFun F` reads off the coefficients of `F`. -/
theorem matrixCoeff_ofGenFun (F : MvPowerSeries (Fin 2) K)
    (hbd : ∃ C, ∀ j i, ‖MvPowerSeries.coeff (idx j i) F‖ ≤ C)
    (hcol : ∀ i, Filter.Tendsto (fun j => MvPowerSeries.coeff (idx j i) F)
      Filter.cofinite (nhds 0)) (j i : ℕ) :
    matrixCoeff (ofGenFun F hbd hcol) j i = MvPowerSeries.coeff (idx j i) F :=
  matrixCoeff_ofCoeffs _ hbd hcol j i

section DiagRescale

set_option linter.unusedSectionVars false

/-- Coefficientwise diagonal rescaling of a two-variable power series:
`(diagRescale α β F)` has `(j, i)` coefficient `α ^ j * β ^ i * a_{j,i}`, i.e. it is
`F (α x, β y)`.  This is how the diagonal matrices `D(α)` of [Jacobs, Notation 1.2] act
on generating functions. -/
noncomputable def diagRescale (α β : K) (F : MvPowerSeries (Fin 2) K) :
    MvPowerSeries (Fin 2) K :=
  fun p => α ^ p 0 * β ^ p 1 * MvPowerSeries.coeff p F

/-- The coefficients of `diagRescale α β F` (definitional). -/
@[simp] theorem coeff_diagRescale (α β : K) (F : MvPowerSeries (Fin 2) K)
    (p : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff p (diagRescale α β F) = α ^ p 0 * β ^ p 1 *
      MvPowerSeries.coeff p F :=
  rfl

/-- Two rescalings compose into the rescaling by the products. -/
theorem diagRescale_diagRescale (α β α' β' : K) (F : MvPowerSeries (Fin 2) K) :
    diagRescale α β (diagRescale α' β' F) = diagRescale (α * α') (β * β') F := by
  ext p
  simp only [coeff_diagRescale, mul_pow]
  ring

/-- Rescaling by `1, 1` is the identity. -/
theorem diagRescale_one_one (F : MvPowerSeries (Fin 2) K) : diagRescale 1 1 F = F := by
  ext p
  simp [coeff_diagRescale]

/-- `diagRescale` is additive in the series. -/
theorem diagRescale_add (α β : K) (F G : MvPowerSeries (Fin 2) K) :
    diagRescale α β (F + G) = diagRescale α β F + diagRescale α β G := by
  ext p
  simp only [coeff_diagRescale, map_add]
  ring

/-- `diagRescale` fixes the constant series `1`. -/
@[simp] theorem diagRescale_one (α β : K) :
    diagRescale α β (1 : MvPowerSeries (Fin 2) K) = 1 := by
  ext p
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · simp [coeff_diagRescale, MvPowerSeries.coeff_one, hp]

/-- `diagRescale` is multiplicative: rescaling `x, y` commutes with products of series
(the exponents of a convolution product add).  This is what lets the substitution
`F ↦ F(αx, βy)` act on the `weightGenFun` factorisations of [Jacobs, §2.1]. -/
theorem diagRescale_mul (α β : K) (F G : MvPowerSeries (Fin 2) K) :
    diagRescale α β (F * G) = diagRescale α β F * diagRescale α β G := by
  ext p
  simp only [coeff_diagRescale, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun qr hqr => ?_
  have h := Finset.mem_antidiagonal.mp hqr
  have h0 : qr.1 0 + qr.2 0 = p 0 := by rw [← h]; rfl
  have h1 : qr.1 1 + qr.2 1 = p 1 := by rw [← h]; rfl
  rw [← h0, ← h1, pow_add, pow_add]
  ring

end DiagRescale

/-- The diagonal operator `diag(a 0, a 1, …)` on `c(ℕ, K)`, for a norm-bounded
diagonal.  [Jacobs, Notation 1.2] (`D(α)` is `diagOp (α ^ ·)`). -/
noncomputable def diagOp (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) :
    c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun j i => if j = i then a j else 0)
    ⟨1, fun j i => by
      by_cases h : j = i
      · rw [if_pos h]; exact ha j
      · rw [if_neg h, norm_zero]; exact zero_le_one⟩
    fun i => tendsto_nhds_of_eventually_eq <| by
      filter_upwards [Filter.eventually_cofinite_ne i] with j hj using if_neg hj

/-- The matrix of `diagOp a` is the diagonal matrix of the sequence `a`. -/
theorem matrixCoeff_diagOp (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (j i : ℕ) :
    matrixCoeff (diagOp a ha) j i = if j = i then a j else 0 :=
  matrixCoeff_ofCoeffs _ _ _ j i

/-- `diagOp a` acts coordinatewise: `(diag(a) f) j = a j * f j`. -/
theorem diagOp_apply (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (f : c(ℕ, K)) (j : ℕ) :
    diagOp a ha f j = a j * f j := by
  show (∑' i, (if j = i then a j else 0) * f i) = a j * f j
  rw [tsum_eq_single j fun i hi => by rw [if_neg (Ne.symm hi), zero_mul], if_pos rfl]

/-- **[Jacobs, Proposition 1.3]**, operator form: pre- and post-composing with diagonal
operators rescales the generating function, `D(α) ∘ u ∘ D(β) ↔ H_u(αx, βy)`.
(Stated for the matrix; the thesis's `D(α) A D(β)` has `(j,i)` entry `αʲ a_{j,i} βⁱ`.) -/
theorem matrixCoeff_diagOp_comp (a b : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1)
    (u : c(ℕ, K) →L[K] c(ℕ, K)) (j i : ℕ) :
    matrixCoeff ((diagOp a ha).comp (u.comp (diagOp b hb))) j i =
      a j * matrixCoeff u j i * b i := by
  -- The right-hand diagonal turns the basis vector into a multiple of itself.
  have hin : diagOp b hb (cSpace.single i (1 : K)) = b i • cSpace.single i (1 : K) := by
    refine DFunLike.ext _ _ fun j' => ?_
    rw [diagOp_apply]
    show b j' * cSpace.single i (1 : K) j' = b i * cSpace.single i (1 : K) j'
    rcases eq_or_ne j' i with rfl | hj'
    · rfl
    · rw [cSpace.single_apply_of_ne hj', mul_zero, mul_zero]
  show ((diagOp a ha).comp (u.comp (diagOp b hb))) (cSpace.single i 1) j = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hin, map_smul,
    diagOp_apply]
  show a j * (b i * u (cSpace.single i 1) j) = a j * u (cSpace.single i 1) j * b i
  ring

end GenFun

end Jacobs
