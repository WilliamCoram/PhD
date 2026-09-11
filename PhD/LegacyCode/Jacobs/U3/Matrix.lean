/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.DiamondW
import PhD.Jacobs.U3.Factorisations
import PhD.Jacobs.U3.KappaAction
import PhD.QMF.«03_HeckeMatrix»

/-!
# AG-B: the matrix of `U₃` is the transcribed matrix

The endpoint of the identification tranche.  [Jacobs, p. 28]:

> "Thus, the matrix of U₃ will have the form A = (ε_{i,j}) = (0 ε₀,₁ ε₀,₂; ε₁,₀ 0
> ε₁,₂; ε₂,₀ ε₂,₁ 0) … Our next aim is to calculate the generating functions of the
> non-zero ε_{i,j}."

— the generating functions being (2.1.4)–(2.1.9), transcribed (misprint corrected) as
`Jacobs.h01 … h21` in `PhD.Jacobs.U3Data`.

Two layers.  `heckeU3_apply_classRep` is **unconditional**: the value of the Hecke
operator `[U₁(9)·η₃·U₁(9)]` at each representative `cᵢ` is the `i`-th row of the block
matrix, with blocks the `κ`-actions assembled from the nine certificates — the
computation of [Jacobs, pp. 25–28].  `eval_classRep_injective` needs `HClassNumberOne`
(Theorem 2.1): the `(cᵢ)` are a complete section with trivial stabilisers, so evaluation
at them is injective and the block matrix *determines* the operator.  Together they make
the first layer "the matrix of `U₃`" rather than "a matrix identity at three points".

## Main definitions

* `Jacobs.U3.levelMonoid1`: the wild-level monoid refined to `Σ₁(9)`-components — the
  acting monoid `Δ₁` of the weight-`κ` theory.
* `Jacobs.U3.levelMonoid1ToSigma1`, `Jacobs.U3.kappaLevelAction`,
  `Jacobs.U3.kappaLevelSMulCommClass`: the corestriction `Δ₁ →* Σ₁(9)` and the two
  instances it induces on the Tate algebra.
* `Jacobs.U3.kappaForms`: `L(U₁(9), A₃)` of [Jacobs, Def 1.30] at `p = 3`.
* `Jacobs.U3.heckeU3`: the Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` on `kappaForms`.
* `Jacobs.U3.blockOp`: the `(i,j)` certificate block,
  `∑_{t' : σ(i,t') = j} kappaOp (etaRep t' · u(i,t')⁻¹)₃`.
* `Jacobs.U3.classWeight`: the per-class weight `φᵢ = κ_t(dᵢ)·dᵢ⁻²`, `dᵢ = classDet i`.

## Main results

* `Jacobs.U3.heckeU3_apply_classRep`: **unconditional** — `(U₃ φ)(cᵢ) = ∑ⱼ blockOp i j
  (φ(cⱼ))`.
* `Jacobs.U3.matrixCoeff_blockOp`: the blocks in generating-function form, the
  transcription of [Jacobs, (2.1.4)–(2.1.9)] scaled by the determinant twist.
* `Jacobs.U3.twist_factor`, `Jacobs.U3.blockOp_eq_smul_epsOp`: the twist is the
  coboundary `φᵢ⁻¹·φⱼ`, at scalar and operator level.
* `Jacobs.U3.charPowerSeries_blockOp_eq_U3MatrixOp`: the AG-B ↔ AG-W bridge — the
  certificate matrix and `Jacobs.U3MatrixOp` have the same characteristic power series.
* `Jacobs.U3.eval_classRep_injective`: **completeness** (needs `HClassNumberOne`) —
  evaluation at the three representatives is injective on `kappaForms`.

## Implementation notes

The certificate blocks differ from the thesis's transcribed `ε`-blocks by the scalar
`κ_t(s)·s⁻²`, `s = classDet j / classDet i` (`Factorisations.lean`, "Handedness
normalisation" — the recorded B15 statement amendment).  Decision (2026-08-05): **keep
the operators honest** — `matrixCoeff_blockOp` carries the scalar rather than absorbing
it into `blockOp`'s definition, which would detach `heckeU3_apply_classRep` from the
literal certificates — and discharge the discrepancy spectrally.  The scalar is a
*coboundary*: it factors as `φⱼ/φᵢ` in the per-class weights `φₖ = classWeight t k`
(`twist_factor`), so the assembled block matrix is *conjugate* to the transcribed
`Jacobs.U3MatrixOp` by the blockwise-scalar diagonal `diag (φₖ)`, and
`charPowerSeries_blockOp_eq_U3MatrixOp` identifies their characteristic power series on
the nose.  AG-W's slope analysis of `U3MatrixOp` — Fredholm determinant, eigenvalues,
Newton polygon (`PhD.Jacobs.DiamondW`, `PhD.Jacobs.Slopes`) — therefore applies verbatim
to the genuine Hecke matrix: that the downstream slope arguments may use "the Jacobs
matrices" is a theorem, not a convention.  Independently the scalar is a `1`-unit, so
entrywise norms — all that the machinery of `PhD.Jacobs.SlopeTheorem` ever reads — are
untouched by the twist.
-/

open Quaternion IsDedekindDomain NumberField QMF TateFredholm
open scoped Pointwise

namespace Jacobs.U3

/-- The wild-level monoid refined to `Σ₁(9)`-components: the acting monoid of the
weight-`κ` theory.  (`Σ₀` supports the polynomial weights; `κ` needs the `1`-unit
condition on the `(0,0)`-entry, so the automorphic machinery is instantiated at this
smaller `Δ`.) -/
noncomputable def levelMonoid1 : Submonoid (Dfx ℚ D) :=
  Sigma1.comap (toMatrix ℚ D v₃)

theorem U1_9_subset_levelMonoid1 : (U1_9 : Set (Dfx ℚ D)) ⊆ levelMonoid1 :=
  fun _ hg => Submonoid.mem_comap.mpr (toMatrix_mem_sigma1_of_mem_U1_9 hg)

theorem eta3_mem_levelMonoid1 : eta3 ∈ levelMonoid1 := by
  refine Submonoid.mem_comap.mpr ?_
  rw [eta3, toMatrix_etaAdelic ℚ D v₃ γ₉ γ₉_lt_one pi3 valued_pi3_le_one pi3_ne_zero]
  refine ⟨(Sigma0.eta γ₉ γ₉_lt_one pi3 valued_pi3_le_one pi3_ne_zero).2, ?_⟩
  change Valued.v ((Matrix.of ![![1, 0], ![0, pi3]] : Matrix (Fin 2) (Fin 2) K₃) 0 0 - 1) ≤ γ₉
  simp

/-- The `3`-components of the coset representatives lie in the acting monoid. -/
theorem etaRep_mem_levelMonoid1 (t' : Fin 3) : etaRep t' ∈ levelMonoid1 :=
  Submonoid.mem_comap.mpr (toMatrix_etaRep_mem_sigma1 t')

/-- The corestriction `Δ₁ →* Σ₁(9)` of the `3`-component map (the `Sigma1` analogue of
`QMF.levelMonoidToSigma0`) — the hom through which `Δ₁` acts on the Tate algebra. -/
noncomputable def levelMonoid1ToSigma1 : levelMonoid1 →* Sigma1 :=
  (toMatrix ℚ D v₃).submonoidComap Sigma1

/-- The weight-`κ` action of `Δ₁` on the Tate algebra: `kappaModuleAction` pulled back
along `levelMonoid1ToSigma1`.  A `def` rather than an `instance` because it depends on
the weight parameter `t`. -/
@[instance_reducible]
noncomputable def kappaLevelAction (t : K₃) (ht : ‖t‖ < 1) :
    DistribMulAction levelMonoid1 c(ℕ, K₃) :=
  letI := kappaModuleAction t ht
  DistribMulAction.compHom _ levelMonoid1ToSigma1

/-- `Δ₁` acts on the Tate algebra by `K₃`-linear maps, so `kappaLevelAction` commutes
with the scalars. -/
theorem kappaLevelSMulCommClass (t : K₃) (ht : ‖t‖ < 1) :
    letI := kappaLevelAction t ht
    SMulCommClass levelMonoid1 K₃ c(ℕ, K₃) :=
  letI := kappaModuleAction t ht
  letI := kappaLevelAction t ht
  ⟨fun δ r f => (kappaOp t ht (levelMonoid1ToSigma1 δ)).map_smul r f⟩

/-- The space of weight-`κ` quaternionic modular forms of level `U₁(9)`
(`L(U₁(9), A₃)` of [Jacobs, Def 1.30] at `p = 3`): the level submodule of
`c(ℕ, K₃)`-valued automorphic functions under the `κ`-action of `levelMonoid1`
(`kappaModuleAction`, pulled back along `levelMonoid1ToSigma1`). -/
noncomputable def kappaForms (t : K₃) (ht : ‖t‖ < 1) :
    Submodule K₃ (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) :=
  letI := kappaLevelAction t ht
  haveI := kappaLevelSMulCommClass t ht
  AutomorphicFunction.levelSubmodule K₃ U1_9 U1_9_subset_levelMonoid1

/-- The Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` on weight-`κ` forms
[Jacobs, Def 1.32 + p. 24]: `QMF.heckeOperator` at `η = η₃`, with the finiteness input
supplied by Lemma 2.3. -/
noncomputable def heckeU3 (t : K₃) (ht : ‖t‖ < 1) : kappaForms t ht →ₗ[K₃] kappaForms t ht :=
  letI := kappaLevelAction t ht
  haveI := kappaLevelSMulCommClass t ht
  AutomorphicFunction.heckeOperator K₃ U1_9_subset_levelMonoid1 U1_9_subset_levelMonoid1
    eta3_mem_levelMonoid1 finite_image_eta3

/-- The `(i,j)` block of the certificate matrix: `0` on the diagonal, and off the
diagonal the `κ`-action operator assembled from the certificates as
`∑_{t' : σ(i,t') = j} kappaOp (etaRep t' · u(i,t')⁻¹)₃`.  Its matrix is the transcribed
generating function `h_{i,j}` *scaled by the determinant twist* — see
`matrixCoeff_blockOp` and the module header's decision record. -/
noncomputable def blockOp (t : K₃) (ht : ‖t‖ < 1) (i j : Fin 3) : c(ℕ, K₃) →L[K₃] c(ℕ, K₃) :=
  ∑ t' ∈ {t' | sigmaTable i t' = j},
    kappaOp t ht ⟨toMatrix ℚ D v₃ (etaRep t' * ((uTable i t' : Dfx ℚ D))⁻¹),
      toMatrix_etaRep_mul_inv_uTable_mem_sigma1 i t'⟩

/-- The blocks in generating-function form, **carrying the determinant twist**: the
matrix of `blockOp i j` is the transcription of [Jacobs, (2.1.4)–(2.1.9)]
(`PhD.Jacobs.U3Data`, misprint corrected) scaled by the handedness coboundary
`κ_t(s)·s⁻²`, `s = classDet j / classDet i` — the series-level scalar of
`Factorisations.sum_weightGenFun_eq_h` (recorded B15 statement amendment).  The
diagonal is `0` [Jacobs p. 28] (and there `s = 1` anyway).  For why the scalar is kept
in the statement rather than absorbed into `blockOp`, see the module header. -/
theorem matrixCoeff_blockOp (t : K₃) (ht : ‖t‖ < 1) (i j : Fin 3) (m r : ℕ) :
    matrixCoeff (blockOp t ht i j) m r
      = (Jacobs.unitPow t ((classDet j : K₃) / (classDet i : K₃)) *
            ((classDet j : K₃) / (classDet i : K₃))⁻¹ *
            ((classDet j : K₃) / (classDet i : K₃))⁻¹) *
          MvPowerSeries.coeff (Jacobs.idx m r)
            (![![0, Jacobs.h01 t ν₃, Jacobs.h02 t ν₃],
               ![Jacobs.h10 t ν₃, 0, Jacobs.h12 t ν₃],
               ![Jacobs.h20 t ν₃, Jacobs.h21 t ν₃, 0]] i j) := by
  have hsum : matrixCoeff (blockOp t ht i j) m r
      = ∑ t' ∈ {t' | sigmaTable i t' = j},
          MvPowerSeries.coeff (Jacobs.idx m r) (Jacobs.weightGenFun t
            (adjParams (toMatrix ℚ D v₃ (etaRep t' * ((uTable i t' : Dfx ℚ D))⁻¹)))) := by
    rw [blockOp, matrixCoeff_sum]
    exact Finset.sum_congr rfl fun t' _ => matrixCoeff_kappaOp t ht _ m r
  rcases eq_or_ne j i with rfl | hij
  · have hempty : ({t' | sigmaTable j t' = j} : Finset (Fin 3)) = ∅ := by
      ext t'
      simp [sigmaTable_ne j t']
    rw [hsum, hempty, Finset.sum_empty]
    fin_cases j <;> simp
  · rw [hsum, ← map_sum, sum_weightGenFun_eq_h t ht.le i j hij, MvPowerSeries.coeff_smul]

private theorem classDet_cast_ne_zero (i : Fin 3) : (classDet i : K₃) ≠ 0 := by
  fin_cases i <;> simp [cd0, cd1, cd2]

/-- The per-class normalisation weight `φᵢ = κ_t(dᵢ)·dᵢ⁻²`, `dᵢ = classDet i`: the
coboundary datum of the determinant twist (module header).  Certificate block `(i,j)`
differs from the transcribed one by exactly `φⱼ/φᵢ` (`twist_factor`), which is what
makes the twist a similarity rather than a genuine deformation. -/
noncomputable def classWeight (t : K₃) (i : Fin 3) : K₃ :=
  Jacobs.unitPow t (classDet i : K₃) * ((classDet i : K₃))⁻¹ * ((classDet i : K₃))⁻¹

theorem classWeight_ne_zero (t : K₃) (ht : ‖t‖ ≤ 1) (i : Fin 3) : classWeight t i ≠ 0 :=
  mul_ne_zero (mul_ne_zero
    (Jacobs.unitPow_ne_zero norm_three_lt_one ht (norm_classDet_sub_one_le i))
    (inv_ne_zero (classDet_cast_ne_zero i))) (inv_ne_zero (classDet_cast_ne_zero i))

/-- **The determinant twist is a coboundary**: the scalar carried by certificate block
`(i,j)` (`matrixCoeff_blockOp`, `Factorisations.sum_weightGenFun_eq_h`) factors through
the per-class weights, `κ_t(dⱼ/dᵢ)·(dⱼ/dᵢ)⁻² = φᵢ⁻¹·φⱼ`.  This is the identity that
turns the twist into conjugation by `diag (φₖ)` and hence
(`charPowerSeries_blockOp_eq_U3MatrixOp`) makes it invisible to the characteristic
power series. -/
theorem twist_factor (t : K₃) (ht : ‖t‖ ≤ 1) (i j : Fin 3) :
    Jacobs.unitPow t ((classDet j : K₃) / (classDet i : K₃)) *
        ((classDet j : K₃) / (classDet i : K₃))⁻¹ *
        ((classDet j : K₃) / (classDet i : K₃))⁻¹
      = (classWeight t i)⁻¹ * classWeight t j := by
  have hdi := classDet_cast_ne_zero i
  have hdj := classDet_cast_ne_zero j
  have hij : ‖(classDet j : K₃) / (classDet i : K₃) - 1‖ ≤ ‖(3 : K₃)‖ :=
    norm_div_sub_one_le (norm_classDet_sub_one_le j) (norm_classDet_sub_one_le i)
  have hUi := Jacobs.unitPow_ne_zero norm_three_lt_one ht (norm_classDet_sub_one_le i)
  have hsplit : Jacobs.unitPow t ((classDet j : K₃) / (classDet i : K₃)) *
      Jacobs.unitPow t (classDet i : K₃) = Jacobs.unitPow t (classDet j : K₃) := by
    rw [← Jacobs.unitPow_mul norm_three_lt_one ht hij (norm_classDet_sub_one_le i),
      div_mul_cancel₀ _ hdi]
  simp only [classWeight]
  rw [← hsplit]
  field_simp

/-- The certificate blocks, as operators: block `(i,j)` is the transcribed
`ε`-operator of `PhD.Jacobs.DiamondW` scaled by the coboundary
`(classWeight t i)⁻¹ · classWeight t j` — the operator-level form of the recorded B15
statement amendment. -/
theorem blockOp_eq_smul_epsOp (t : K₃) (ht : ‖t‖ < 1) :
    blockOp t ht = fun i j => ((classWeight t i)⁻¹ * classWeight t j) •
      ![![0, Jacobs.epsOp01 norm_three_lt_one ht ν₃_near,
          Jacobs.epsOp02 norm_three_lt_one ht ν₃_near],
        ![Jacobs.epsOp10 norm_three_lt_one ht ν₃_near, 0,
          Jacobs.epsOp12 norm_three_lt_one ht ν₃_near],
        ![Jacobs.epsOp20 norm_three_lt_one ht ν₃_near,
          Jacobs.epsOp21 norm_three_lt_one ht ν₃_near, 0]] i j := by
  funext i j
  refine TateFredholm.ext_matrixCoeff fun m r => ?_
  rw [matrixCoeff_blockOp t ht i j m r, matrixCoeff_smul, ← twist_factor t ht.le i j]
  congr 1
  fin_cases i <;> fin_cases j <;>
    simp [Jacobs.matrixCoeff_epsOp01, Jacobs.matrixCoeff_epsOp02,
      Jacobs.matrixCoeff_epsOp10, Jacobs.matrixCoeff_epsOp12, Jacobs.matrixCoeff_epsOp20,
      Jacobs.matrixCoeff_epsOp21, matrixCoeff_zero]

/-- **The determinant twist does not move the Fredholm determinant** — the AG-B ↔ AG-W
bridge.  The block operator assembled from the certificate blocks and the transcribed
matrix of `U₃` (`Jacobs.U3MatrixOp`, the object whose slopes AG-W analyses) have the
*same* characteristic power series — the two are conjugate by the blockwise-scalar
diagonal `diag (classWeight t k)`.

This is the theorem that licenses arguing slopes with "the original Jacobs matrices":
Fredholm determinant, eigenvalues with multiplicity, and Newton-polygon slopes of the
certificate matrix coincide on the nose with those of `U3MatrixOp`.  Module header for
the decision record. -/
theorem charPowerSeries_blockOp_eq_U3MatrixOp (t : K₃) (ht : ‖t‖ < 1) :
    charPowerSeries (TateFredholm.blockOp (blockOp t ht))
      = charPowerSeries (Jacobs.U3MatrixOp norm_three_lt_one ht ν₃_near) := by
  rw [blockOp_eq_smul_epsOp t ht]
  exact Jacobs.charPowerSeries_twist_U3MatrixOp norm_three_lt_one ht ν₃_near
    (classWeight t) (fun i => (classWeight t i)⁻¹)
    (fun i => mul_inv_cancel₀ (classWeight_ne_zero t ht.le i))

private theorem sum_kappaOp_eq_sum_blockOp (t : K₃) (ht : ‖t‖ < 1) (i : Fin 3)
    (f : Fin 3 → c(ℕ, K₃)) :
    ∑ t' : Fin 3, kappaOp t ht
        ⟨toMatrix ℚ D v₃ (etaRep t' * ((uTable i t' : Dfx ℚ D))⁻¹),
          toMatrix_etaRep_mul_inv_uTable_mem_sigma1 i t'⟩ (f (sigmaTable i t'))
      = ∑ j : Fin 3, blockOp t ht i j (f j) := by
  refine (Finset.sum_fiberwise Finset.univ (sigmaTable i) _).symm.trans
    (Finset.sum_congr rfl fun j _ => ?_)
  rw [blockOp, sum_apply]
  exact Finset.sum_congr rfl fun t' ht' => by rw [show sigmaTable i t' = j by simpa using ht']

/-- **AG-B headline (unconditional)**: on the weight-`κ` space, the Hecke operator `U₃`
evaluated at the class representatives is given by the certificate block matrix:

  `(U₃ φ)(cᵢ) = ∑ⱼ blockOp i j (φ(cⱼ))`.

[Jacobs, pp. 25–28].  The blocks carry the determinant twist (`matrixCoeff_blockOp`);
by `charPowerSeries_blockOp_eq_U3MatrixOp` this does not affect the spectral theory. -/
theorem heckeU3_apply_classRep (t : K₃) (ht : ‖t‖ < 1) (φ : kappaForms t ht) (i : Fin 3) :
    ((heckeU3 t ht φ : kappaForms t ht) :
        AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
      = ∑ j : Fin 3, blockOp t ht i j
          ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep j)) := by
  letI := kappaLevelAction t ht
  haveI := kappaLevelSMulCommClass t ht
  have key := AutomorphicFunction.heckeOperator_apply_rep (Γ := globalUnits ℚ D) K₃
    U1_9_subset_levelMonoid1 eta3_mem_levelMonoid1 finite_image_eta3 φ
    etaRep etaRep_mem_levelMonoid1 bijOn_etaRep etaRep_injective (classRep i)
    (fun t' => classRep (sigmaTable i t'))
    (fun t' => unitsIncl ℚ D (dTable i t')) (fun t' => dTable_mem i t')
    (fun t' => uTable i t') (factorisation i)
    (fun t' => Submonoid.mem_comap.mpr (toMatrix_etaRep_mul_inv_uTable_mem_sigma1 i t'))
  exact key.trans (sum_kappaOp_eq_sum_blockOp t ht i
    fun j => (φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep j))

/-- **Completeness** (needs Theorem 2.1, hence `HClassNumberOne`): evaluation at the
three representatives is injective on `kappaForms` — the block matrix determines `U₃`.
This is the injectivity half of [Jacobs, (2.1.1)]: `L(U, A₃) ≅ ⊕ᵢ A₃`. -/
theorem eval_classRep_injective (t : K₃) (ht : ‖t‖ < 1)
    (hcn : HClassNumberOne) (φ ψ : kappaForms t ht)
    (h : ∀ i : Fin 3,
      ((φ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
        = ((ψ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)) :
    φ = ψ := by
  letI := kappaLevelAction t ht
  haveI := kappaLevelSMulCommClass t ht
  refine Subtype.ext (AutomorphicFunction.ext fun g => ?_)
  obtain ⟨i, d, hd, w, hw, rfl⟩ := exists_classRep_factorisation hcn g
  rw [mul_assoc, φ.1.left_invt' hd, ψ.1.left_invt' hd,
    AutomorphicFunction.apply_mul_coe K₃ U1_9_subset_levelMonoid1 φ.2 ⟨w, hw⟩,
    AutomorphicFunction.apply_mul_coe K₃ U1_9_subset_levelMonoid1 ψ.2 ⟨w, hw⟩, h i]

/-- Convenience form of `eval_classRep_injective` with the class-number-one hypothesis
discharged by the FLT interface `hClassNumberOne`.

**Depends on the tranche's single external `sorry`** (see `hClassNumberOne`'s contract):
`#print axioms` shows `sorryAx` with exactly that one source until FLT's proof is
ported.  The hypothesis form above is the axiom-clean, board-gradable statement. -/
theorem eval_classRep_injective' (t : K₃) (ht : ‖t‖ < 1) (φ ψ : kappaForms t ht)
    (h : ∀ i : Fin 3,
      ((φ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
        = ((ψ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)) :
    φ = ψ :=
  eval_classRep_injective t ht hClassNumberOne φ ψ h

end Jacobs.U3
