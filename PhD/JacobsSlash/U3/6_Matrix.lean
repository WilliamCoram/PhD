/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.«4_DiamondW»
import PhD.JacobsSlash.CN1.«4_Dictionary»
import PhD.JacobsSlash.U3.«5_Factorisations»
import PhD.JacobsSlash.U3.«5_KappaWeight»
import PhD.QMF.Slash.«04_HeckeMatrix»
import PhD.QMF.Weight.«07_Quaternionic»

/-!
# The matrix of `U₃` is the transcribed matrix — twist-free

The endpoint of the identification, in the thesis's own convention.  [Jacobs, p. 28]:

> "Thus, the matrix of U₃ will have the form A = (ε_{i,j}) = (0 ε₀,₁ ε₀,₂; ε₁,₀ 0
> ε₁,₂; ε₂,₀ ε₂,₁ 0) … Our next aim is to calculate the generating functions of the
> non-zero ε_{i,j}."

— the generating functions being (2.1.4)–(2.1.9), transcribed (misprint corrected) as
`JacobsSlash.h01 … h21` in `PhD.JacobsSlash.«2_U3Data»`.

**The fork's blocks are twist-free**: in the thesis orientation the certificate blocks
equal the transcribed `ε`-operators ON THE NOSE (`blockEntry_eq_epsOp`) — the
left-action library's `classWeight` coboundary vanishes identically
(`«5_Factorisations».sum_weightGenFun_eq_h`), so `matrixCoeff_blockEntry` carries no
scalar and the bridge `charPowerSeries_blockEntry_eq_U3MatrixOp` is definitional after
the block identification.

`heckeU3_apply_classRep` is **unconditional**: the value of `[U₁(9)·η₃·U₁(9)]` at each
representative `cᵢ` is the `i`-th row of the block matrix — the general matrix recipe
`QMF.Weight.heckeOperator_apply_rep` at the thesis-shape certificates of
`«5_Factorisations»`; the blocks themselves are the general certificate blocks
`QMF.Weight.heckeBlock` at those certificates.  `eval_classRep_injective` needs
`HClassNumberOne` (Theorem 2.1).

## Main definitions

* `JacobsSlash.levelMonoid1₃`: the single acting monoid `Δ₁(3) = toMatrix⁻¹(Σ₁(3))`
  (`QMF.Weight.levelMonoidOf`) — shared by `heckeU3` and (in `«7_DiamondHecke»`) `heckeW`.
* `JacobsSlash.kappaForms`: the weight-`κ` forms `L(U₁(9), c(ℕ, K₃))` — the headline
  `QMF.Weight.Forms` at `jacobsWeight t ht`.
* `JacobsSlash.heckeU3`: the Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` — the headline
  `QMF.Weight.heckeOperator` at `η₃`.
* `JacobsSlash.blockEntry`: the `(i,j)` certificate block `∑_{σ(i,t')=j} κ((u(i,t')·vₜ')₃)` —
  `QMF.Weight.heckeBlock` at `etaRep`/`sigmaTable`/`uTable`.

## Main statements

* `JacobsSlash.matrixCoeff_blockEntry`: the blocks ARE the transcribed generating
  functions — twist-free.
* `JacobsSlash.heckeU3_apply_classRep`: `(U₃ φ)(cᵢ) = ∑ⱼ blockEntry i j (φ(cⱼ))`.
* `JacobsSlash.eval_classRep_injective`: completeness of the three evaluations
  (given class number one).
-/

open Quaternion IsDedekindDomain NumberField QMF TateFredholm
open AbstractHeckeOperatorSlash RightSlashAction
open scoped Pointwise

namespace JacobsSlash

/-- **The acting monoid** `Δ₁(3)`: adelic units whose `3`-component matrix lies in
`Σ₁(3)` — the wild-level monoid `θ⁻¹(Σ₁(3))` of the general theory
(`QMF.Weight.levelMonoidOf`), the single acting monoid of the development: `heckeU3` and
(in `«7_DiamondHecke»`) `heckeW` are the *same* `heckeOperator` construction over it, at
`η₃` and at `μ` respectively, so they act on one space.  `Σ₁(9)` survives only as the level
congruence cutting out `U₁(9)`. -/
noncomputable abbrev levelMonoid1₃ : Submonoid (Dfx ℚ D) :=
  Weight.levelMonoidOf (toMatrix ℚ D v₃) Sigma1₃

theorem U1_9_subset_levelMonoid1₃ : (U1_9 : Set (Dfx ℚ D)) ⊆ levelMonoid1₃ :=
  fun _ hg =>
    Submonoid.mem_comap.mpr (sigma1_le_sigma1₃ (toMatrix_mem_sigma1_of_mem_U1_9 hg))

theorem eta3_mem_levelMonoid1₃ : eta3 ∈ levelMonoid1₃ := by
  refine Submonoid.mem_comap.mpr ?_
  rw [toMatrix_eta3]
  refine ⟨⟨fun i j => ?_, ?_, ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j
    · simpa [pi3] using valued_pi3_le_one
    · simp
    · simp
    · simp
  · simp
  · simp
  · simp [Matrix.det_fin_two]
  · simp

/-- The `3`-components of the coset representatives lie in the acting monoid. -/
theorem etaRep_mem_levelMonoid1₃ (t' : Fin 3) : etaRep t' ∈ levelMonoid1₃ :=
  Submonoid.mem_comap.mpr (sigma1_le_sigma1₃ (toMatrix_etaRep_mem_sigma1 t'))

/-- **`L(U₁(9), A₃)`** ([Jacobs, Def 1.30] at `p = 3`): the headline space of
overconvergent forms `QMF.Weight.Forms` at the Jacobs weight `κ_t` and level `U₁(9)`, in the
thesis's own right-slash form — the slash-fixed points of `U₁(9)` on `c(ℕ, K₃)`-valued
automorphic functions on `Dˣ\(D ⊗ 𝔸_f)ˣ`. -/
noncomputable abbrev kappaForms (t : K₃) (ht : ‖t‖ < 1) :
    Submodule K₃ (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) :=
  FormsQ ℚ D v₃ (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃

/-- **The Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]`** on weight-`κ` forms
[Jacobs, Def 1.32 + p. 24]: the headline `QMF.Weight.heckeOperator` at `η = η₃`, with the
finiteness input supplied by Lemma 2.3 (`finite_image_eta3`, right-coset form). -/
noncomputable abbrev heckeU3 (t : K₃) (ht : ‖t‖ < 1) :
    kappaForms t ht →ₗ[K₃] kappaForms t ht :=
  heckeUpiQ ℚ D v₃ (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ pi3 pi3_ne_zero
    eta3_mem_levelMonoid1₃ finite_image_eta3

/-- The `(i,j)` block of the `U₃` matrix: the general certificate block
`QMF.Weight.heckeBlock` at the `«5_Factorisations»` data (right-coset representatives `etaRep`,
index table `sigmaTable`, level-unit table `uTable`) — `∑_{t' : σ(i,t') = j} κ((u(i,t')·vₜ')₃)`,
the thesis's own acting elements. -/
noncomputable abbrev blockEntry (t : K₃) (ht : ‖t‖ < 1) :
    Fin 3 → Fin 3 → (c(ℕ, K₃) →L[K₃] c(ℕ, K₃)) :=
  Weight.heckeBlock (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ 1
    etaRep etaRep_mem_levelMonoid1₃ sigmaTable uTable

/-- The blocks in generating-function form — **twist-free**: the matrix of
`blockEntry i j` is the transcription of [Jacobs, (2.1.4)–(2.1.9)] ON THE NOSE
(`PhD.JacobsSlash.«2_U3Data»`, misprint corrected).  The diagonal is `0`
[Jacobs p. 28]. -/
theorem matrixCoeff_blockEntry (t : K₃) (ht : ‖t‖ < 1) (i j : Fin 3) (m r : ℕ) :
    matrixCoeff (blockEntry t ht i j) m r
      = MvPowerSeries.coeff (idx m r)
          (![![0, JacobsSlash.h01 t ν₃, JacobsSlash.h02 t ν₃],
             ![JacobsSlash.h10 t ν₃, 0, JacobsSlash.h12 t ν₃],
             ![JacobsSlash.h20 t ν₃, JacobsSlash.h21 t ν₃, 0]] i j) := by
  have hsum : matrixCoeff (blockEntry t ht i j) m r
      = ∑ t' ∈ {t' | sigmaTable i t' = j},
          MvPowerSeries.coeff (idx m r) (JacobsSlash.weightGenFun t
            (toMatrix ℚ D v₃ ((uTable i t' : Dfx ℚ D) * etaRep t'))) := by
    simp only [blockEntry, Weight.heckeBlock, MonoidHom.one_apply, Units.val_one, one_smul,
      matrixCoeff_sum]
    exact Finset.sum_congr rfl fun t' _ => matrixCoeff_kappaSlash_jacobsWeight t ht _ m r
  rcases eq_or_ne j i with rfl | hij
  · have hempty : ({t' | sigmaTable j t' = j} : Finset (Fin 3)) = ∅ := by
      ext t'
      simp [sigmaTable_ne j t']
    rw [hsum, hempty, Finset.sum_empty]
    fin_cases j <;> simp
  · rw [hsum, ← map_sum, sum_weightGenFun_eq_h t i j hij]

/-- The certificate blocks, as operators — **exact**: block `(i,j)` *is* the
transcribed `ε`-operator of `PhD.JacobsSlash.«4_DiamondW»`, with no coboundary
scalar. -/
theorem blockEntry_eq_epsOp (t : K₃) (ht : ‖t‖ < 1) :
    blockEntry t ht
      = ![![0, epsOp01 norm_three_lt_one ht ν₃_near,
            epsOp02 norm_three_lt_one ht ν₃_near],
          ![epsOp10 norm_three_lt_one ht ν₃_near, 0,
            epsOp12 norm_three_lt_one ht ν₃_near],
          ![epsOp20 norm_three_lt_one ht ν₃_near,
            epsOp21 norm_three_lt_one ht ν₃_near, 0]] := by
  funext i j
  refine ext_matrixCoeff fun m r => ?_
  rw [matrixCoeff_blockEntry t ht i j m r]
  fin_cases i <;> fin_cases j <;>
    simp [matrixCoeff_epsOp01, matrixCoeff_epsOp02, matrixCoeff_epsOp10,
      matrixCoeff_epsOp12, matrixCoeff_epsOp20, matrixCoeff_epsOp21]

/-- **The block/transcription bridge — definitional in the thesis orientation**: the
block operator assembled from the certificate blocks *is* the transcribed matrix of
`U₃` (`JacobsSlash.U3MatrixOp`), so the characteristic power series coincide with no
conjugation needed. -/
theorem charPowerSeries_blockEntry_eq_U3MatrixOp (t : K₃) (ht : ‖t‖ < 1) :
    charPowerSeries (blockOp (blockEntry t ht))
      = charPowerSeries (U3MatrixOp norm_three_lt_one ht ν₃_near) := by
  rw [blockEntry_eq_epsOp t ht]
  rfl

/-- **The headline (unconditional)**: on the weight-`κ` space, the Hecke operator `U₃`
evaluated at the class representatives is given by the certificate block matrix:

  `(U₃ φ)(cᵢ) = ∑ⱼ blockEntry i j (φ(cⱼ))`

[Jacobs, pp. 25–28] — with the blocks equal to the transcribed data on the nose
(`matrixCoeff_blockEntry`, twist-free). -/
theorem heckeU3_apply_classRep (t : K₃) (ht : ‖t‖ < 1) (φ : kappaForms t ht)
    (i : Fin 3) :
    (heckeU3 t ht φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
        (classRep i)
      = ∑ j : Fin 3, blockEntry t ht i j
          ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
            (classRep j)) :=
  Weight.heckeOperator_apply_rep (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9
    U1_9_subset_levelMonoid1₃ 1 eta3_mem_levelMonoid1₃ finite_image_eta3 classRep etaRep
    etaRep_mem_levelMonoid1₃ bijOn_etaRep etaRep_injective sigmaTable
    (fun i t' => unitsIncl ℚ D (dTable i t')) (fun i t' => dTable_mem i t') uTable
    (fun i t' => by rw [uTable_coe]; exact factorisation i t') φ i

/-- **Completeness** (needs Theorem 2.1, hence `HClassNumberOne`): evaluation at the
three representatives is injective on `kappaForms` — the general
`QMF.Weight.ext_of_forall_rep` at the complete family `classRep` (`classRep_bijective`). -/
theorem eval_classRep_injective (t : K₃) (ht : ‖t‖ < 1)
    (hcn : HClassNumberOne) (φ ψ : kappaForms t ht)
    (h : ∀ i : Fin 3,
      (φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
        = (ψ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
            (classRep i)) :
    φ = ψ :=
  Weight.ext_of_forall_rep (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ 1
    classRep (classRep_bijective hcn).2 h

/-- Convenience form with the class-number-one hypothesis discharged by
`hClassNumberOne`, proven in `PhD/JacobsSlash/CN1/` (sorry-free, standard axioms). -/
theorem eval_classRep_injective' (t : K₃) (ht : ‖t‖ < 1) (φ ψ : kappaForms t ht)
    (h : ∀ i : Fin 3,
      (φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
        = (ψ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
            (classRep i)) :
    φ = ψ :=
  eval_classRep_injective t ht hClassNumberOne φ ψ h

end JacobsSlash
