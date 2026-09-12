/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.JacobsSlash.U3.«9_EigenvaluesU3»
import PhD.Main.QMF.Weight.«08_BaseChange»

/-!
# The Jacobs crux as a statement about eigenforms

`«9_EigenvaluesU3»` proves [Jacobs, Cor 2.16] as an eigenvalue statement about the base-changed
*matrix* `U3MatrixOp` over `ℂ₃`: for every `j` there is an eigenvalue `a` with `v₃(a) = j + ½`.
Here the thesis's space of forms is base-changed along an isometric embedding
`ι : K₃ ↪ L` — the Jacobs weight is field-generic (`jacobsWeightOf`), the component map is
`mapTheta ι (toMatrix ℚ D v₃)`, and the level data (`U₁(9)`, `η₃`, the certificates) are
unchanged — so that `U₃` acts on `kappaFormsL L ι`, its block operator *is* the base-changed
transcribed matrix (`heckeBlockOpL_eq_U3MatrixOp`), its Fredholm determinant is the base change
of `det(1 − T·U₃)` (`heckeCharPowerSeriesL_eq_map`), and the eigenvalue of the crux is carried
by an honest **eigenform** over `ℂ₃` (`exists_eigenform_U3_halfIntegral`).

## Main declarations

* `JacobsSlash.thetaL`, `JacobsSlash.jacobsWeightL`, `JacobsSlash.kappaFormsL`,
  `JacobsSlash.heckeU3L` — the thesis data over `L`.
* `JacobsSlash.heckeBlockOpL_eq_U3MatrixOp`, `JacobsSlash.heckeCharPowerSeriesL_eq_map`,
  `JacobsSlash.bijective_evalU3L`.
* `JacobsSlash.exists_eigenform_U3_halfIntegral` — **THE CRUX for forms**.
-/

open TateFredholm Quaternion IsDedekindDomain NumberField QMF
open scoped TateFredholm QMF

namespace JacobsSlash

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharZero L]
variable (ι : K₃ →+* L) (hι : ∀ x, ‖ι x‖ = ‖x‖)

/-- The component map over `L`: `g ↦ (g)₃.map ι`. -/
noncomputable abbrev thetaL : Dfx ℚ D →* Matrix (Fin 2) (Fin 2) L :=
  Weight.mapTheta ι (toMatrix ℚ D v₃)

omit [CompleteSpace L] [CharZero L] in
/-- `ι` maps `Σ₁(3)` into the norm-defined level over `L`. -/
theorem map_mem_sigma1Norm {g : Matrix (Fin 2) (Fin 2) K₃} (hg : g ∈ Sigma1₃) :
    g.map ι ∈ sigma1Norm L (norm_three_lt_one_of_isometry ι hι) := by
  obtain ⟨h1, h2, h3⟩ := sigma1₃_le_sigma1Norm hg
  have h3L : ‖(3 : L)‖ = ‖(3 : K₃)‖ := by rw [← map_ofNat ι 3, hι]
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [Matrix.map_apply, hι]
    exact h1 i j
  · rw [Matrix.map_apply, hι, h3L]
    exact h2
  · rw [Matrix.map_apply, show (1 : L) = ι 1 from (map_one ι).symm, ← map_sub, hι, h3L]
    exact h3

omit [CompleteSpace L] [CharZero L] in
/-- `U₁(9)` has wild level `Σ₁(3)` over `L` too. -/
theorem U1_9_subset_levelMonoidL :
    (U1_9 : Set (Dfx ℚ D))
      ⊆ Weight.levelMonoidOf (thetaL ι) (sigma1Norm L (norm_three_lt_one_of_isometry ι hι)) :=
  fun u hu => map_mem_sigma1Norm ι hι (U1_9_subset_levelMonoid1₃ hu)

omit [CompleteSpace L] [CharZero L] in
theorem eta3_mem_levelMonoidL :
    eta3 ∈ Weight.levelMonoidOf (thetaL ι) (sigma1Norm L (norm_three_lt_one_of_isometry ι hι)) :=
  map_mem_sigma1Norm ι hι eta3_mem_levelMonoid1₃

omit [CompleteSpace L] [CharZero L] in
theorem etaRep_mem_levelMonoidL (t : Fin 3) :
    etaRep t
      ∈ Weight.levelMonoidOf (thetaL ι) (sigma1Norm L (norm_three_lt_one_of_isometry ι hι)) :=
  map_mem_sigma1Norm ι hι (etaRep_mem_levelMonoid1₃ t)

omit [IsUltrametricDist L] [CompleteSpace L] [CharZero L] in
include hι in
/-- `ι t` is approximable by naturals (as `t ∈ K₃` is). -/
theorem exists_natCast_close_map {t : K₃} (ht : ‖t‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ‖ι t - (n : L)‖ < ε := by
  obtain ⟨n, hn⟩ := exists_natCast_close ht hε
  exact ⟨n, by rw [← map_natCast ι n, ← map_sub, hι]; exact hn⟩

/-- **The thesis weight over `L`**: `jacobsWeightOf` at `ι t`. -/
noncomputable abbrev jacobsWeightL (t : K₃) (ht : ‖t‖ < 1) :
    QMF.AnalyticWeight
      (QMF.oneUnits L ‖(3 : L)‖ (norm_nonneg _) (norm_three_lt_one_of_isometry ι hι))
      (sigma1Norm L (norm_three_lt_one_of_isometry ι hι)) ‖(3 : L)‖ :=
  jacobsWeightOf (norm_three_lt_one_of_isometry ι hι) (ι t) (norm_map_weight_lt_one ι hι ht)
    (fun _ hε => exists_natCast_close_map ι hι ht.le hε)

/-- **`L(U₁(9), A₃) ⊗ L`**: the thesis's forms with coefficients in `L`. -/
noncomputable abbrev kappaFormsL (t : K₃) (ht : ‖t‖ < 1) :
    Submodule L (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, L)) :=
  Weight.Forms (globalUnits ℚ D) (thetaL ι) (jacobsWeightL ι hι t ht) U1_9
    (U1_9_subset_levelMonoidL ι hι)

/-- `U₃` on the forms over `L`. -/
noncomputable abbrev heckeU3L (t : K₃) (ht : ‖t‖ < 1) :
    kappaFormsL ι hι t ht →ₗ[L] kappaFormsL ι hι t ht :=
  Weight.heckeOperator (thetaL ι) (jacobsWeightL ι hι t ht) U1_9 (U1_9_subset_levelMonoidL ι hι)
    (eta3_mem_levelMonoidL ι hι) finite_image_eta3

/-- The Jacobs columns commute with `ι` (`map_unitPow`, `map_binomialCoeff`). -/
theorem jacobsCol_map (t : K₃) (ht : ‖t‖ < 1) (c d : K₃) :
    (jacobsWeightL ι hι t ht).expansion.col (ι c) (ι d)
      = PowerSeries.map ι ((jacobsWeight t ht).expansion.col c d) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map]
  show PowerSeries.coeff n (PowerSeries.mk fun n => unitPow (ι t) (ι d) *
      (binomialCoeff (ι t) n * (ι c / ι d) ^ n))
    = ι (PowerSeries.coeff n (PowerSeries.mk fun n => unitPow t d *
      (binomialCoeff t n * (c / d) ^ n)))
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_mul, map_mul, map_unitPow ι hι,
    map_binomialCoeff ι, map_pow, map_div₀]

/-- **The block operator of `U₃` over `L` is the base-changed transcribed matrix.** -/
theorem heckeBlockOpL_eq_U3MatrixOp (t : K₃) (ht : ‖t‖ < 1) :
    Weight.heckeBlockOp (thetaL ι) (jacobsWeightL ι hι t ht) U1_9 (U1_9_subset_levelMonoidL ι hι)
        1 etaRep (etaRep_mem_levelMonoidL ι hι) sigmaTable uTable
      = U3MatrixOp (norm_three_lt_one_of_isometry ι hι) (norm_map_weight_lt_one ι hι ht)
          (map_ν₃_near ι hι) := by
  refine ext_matrixCoeff fun p q => ?_
  rw [Weight.matrixCoeff_heckeBlockOp_map ι (toMatrix ℚ D v₃) (jacobsWeight t ht)
      (jacobsWeightL ι hι t ht) U1_9 U1_9_subset_levelMonoid1₃ (U1_9_subset_levelMonoidL ι hι)
      1 1 (fun g hg => map_mem_sigma1Norm ι hι hg)
      (fun g _ => jacobsCol_map ι hι t ht (g 1 0) (g 1 1)) (fun g _ => by simp)
      etaRep etaRep_mem_levelMonoid1₃ (etaRep_mem_levelMonoidL ι hι) sigmaTable uTable p q,
    matrixCoeff_U3MatrixOp_map ι hι ht p q]
  exact congrArg ι (congrArg (fun T => matrixCoeff (blockOp T) p q) (blockEntry_eq_epsOp t ht))

/-- **`det(1 − T·U₃)` over `L` is the base change of `det(1 − T·U₃)`.** -/
theorem heckeCharPowerSeriesL_eq_map (t : K₃) (ht : ‖t‖ < 1) :
    Weight.heckeCharPowerSeries (thetaL ι) (jacobsWeightL ι hι t ht) U1_9
        (U1_9_subset_levelMonoidL ι hι) 1 etaRep (etaRep_mem_levelMonoidL ι hι) sigmaTable uTable
      = PowerSeries.map ι (charPowerSeriesU3 t ht) := by
  rw [Weight.heckeCharPowerSeries, heckeBlockOpL_eq_U3MatrixOp ι hι t ht,
    map_charPowerSeriesU3 ι hι t ht]

/-- Evaluation at the class representatives is bijective over `L` (Theorem 2.1 + Lemma 2.2;
`hClassNumberOne`). -/
theorem bijective_evalU3L (t : K₃) (ht : ‖t‖ < 1) :
    Function.Bijective (Weight.evalAtReps (Γ := globalUnits ℚ D) (thetaL ι) (jacobsWeightL ι hι t ht)
      U1_9 (U1_9_subset_levelMonoidL ι hι) 1 classRep) :=
  Weight.bijective_evalAtReps_of_stabilizer_eq_bot (thetaL ι) (jacobsWeightL ι hι t ht) U1_9
    (U1_9_subset_levelMonoidL ι hι) 1 classRep (classRep_bijective hClassNumberOne)
    stabilizerAt_classRep

/-- **THE CRUX, for forms** ([Jacobs, Cor 2.16]: "The `n`-th slope of `M₂,₂` is `n − ½`"):
for every `j : ℕ` there is an eigenform `φ` of `U₃` on the thesis's space over `ℂ₃` with
eigenvalue `a` of `3`-adic valuation `j + ½`. -/
theorem exists_eigenform_U3_halfIntegral (t : K₃) (ht : ‖t‖ < 1) (j : ℕ) :
    ∃ (a : ℂ_[3]) (φ : kappaFormsL ιC norm_ιC t ht), a ≠ 0 ∧ φ ≠ 0 ∧
      heckeU3L ιC norm_ιC t ht φ = a • φ ∧ ‖a‖ ^ 2 = ‖(3 : ℂ_[3])‖ ^ (2 * j + 1) := by
  obtain ⟨a, y, ha0, hy0, hyU3, hnorm, -, -⟩ := exists_eigenvalue_U3_halfIntegral t ht j
  rw [← heckeBlockOpL_eq_U3MatrixOp ιC norm_ιC t ht] at hyU3
  obtain ⟨φ, rfl⟩ := (bijective_evalU3L ιC norm_ιC t ht).2 y
  have htr := Weight.evalAtReps_heckeOperator (thetaL ιC) (jacobsWeightL ιC norm_ιC t ht) U1_9
    (U1_9_subset_levelMonoidL ιC norm_ιC) 1 (eta3_mem_levelMonoidL ιC norm_ιC) finite_image_eta3
    classRep etaRep (etaRep_mem_levelMonoidL ιC norm_ιC) bijOn_etaRep etaRep_injective sigmaTable
    (fun i t' => unitsIncl ℚ D (dTable i t')) (fun i t' => dTable_mem i t') uTable
    (fun i t' => by rw [uTable_coe]; exact factorisation i t') φ
  refine ⟨a, φ, ha0, fun h0 => hy0 (by rw [h0, map_zero]),
    (bijective_evalU3L ιC norm_ιC t ht).1 ?_, hnorm⟩
  rw [htr, hyU3, map_smul]

end JacobsSlash
