/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.JacobsSlash.U3.«6_Matrix»
import PhD.Main.QMF.Weight.«07_Fredholm»

/-!
# `det(1 − T·U₃)`: the Fredholm determinant of the genuine Hecke operator

`PhD.Main.JacobsSlash.U3.«6_Matrix»` proved that the Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]`
on the weight-`κ` space evaluates at the class representatives through the certificate
block matrix (`heckeU3_apply_classRep`), and that evaluation at the representatives is
injective under `HClassNumberOne` (`eval_classRep_injective`).  This file upgrades the
two into a model isomorphism and defines the object the slope theory is about:

* `evalU3` — evaluation at the three representatives, landing in the block model
  `c(Fin 3 × ℕ, K₃)` — the general `QMF.Weight.evalAtReps` at `classRep`; `bijective_evalU3`
  ([Buz07, §9]: `L(U,A) ≅ ⊕_λ A^{Γ_λ}`, with the invariants trivialised by Lemma 2.2's
  `stabilizerAt_classRep = ⊥`) is the general neat-level model isomorphism
  `QMF.Weight.bijective_evalAtReps_of_stabilizer_eq_bot` at Theorem 2.1
  (`classRep_bijective`), and `kappaFormsModelEquiv` packages it (both under
  `hcn : HClassNumberOne`).
* `evalU3_heckeU3` — **unconditional** transport: under `evalU3`, the Hecke operator is
  the assembled certificate block operator `blockOp (blockEntry t ht)` — the general
  `QMF.Weight.evalAtReps_heckeOperator` at the `«5_Factorisations»` certificates.
* `charPowerSeriesU3` — the Fredholm determinant `det(1 − T·U₃)`, defined through the
  block model; `isCompactoid_blockOpU3` (the general compactness theorem
  `QMF.Weight.isCompactoid_heckeBlockOp` at `‖det (η₃)₃‖ = ‖3‖`) makes the compact-operator
  theory applicable, and `charPowerSeriesU3_eq_U3MatrixOp` computes it by the transcribed
  matrix `JacobsSlash.U3MatrixOp` — the object whose slopes the slope-theory files analysed.

**Twist-free simplifications over the left-action original**: the blocks are the
`ε`-operators on the nose (`blockEntry_eq_epsOp`), so the determinant bridge is the
definitional `charPowerSeries_blockEntry_eq_U3MatrixOp`.  The whole block layer
(`evalU3`, `blockEntry`, `evalU3_heckeU3`, `isCompactoid_blockOpU3`) is the general
`PhD/Main/QMF/Weight/06_Compact.lean` model instantiated at the Jacobs data — nothing here is
Jacobs-specific except the certificates.

The extension-field factorisation into the `M`-eigenblocks and the slope reading are in
`PhD.Main.JacobsSlash.U3.«8_HeckeSlopes»` (they need `ω ∉ K₃`).
-/

open Quaternion IsDedekindDomain NumberField QMF TateFredholm
open AbstractHeckeOperatorSlash RightSlashAction

namespace JacobsSlash

/-- `K₃` is a Tate ring: `3` is a pseudo-uniformizer.  (Required by the compactoid
closure lemmas; the `[IsTate _]`-hypothesis pattern of `PhD.Main.TateFredholm.«06_BlockOp»`.) -/
instance : IsTate K₃ :=
  ⟨⟨PseudoUniformizer.ofNormLtOne (by norm_num : (3 : K₃) ≠ 0) norm_three_lt_one⟩⟩

variable (t : K₃) (ht : ‖t‖ < 1)

/-- Evaluation of a weight-`κ` form at the three class representatives, assembled into
the block model `c(Fin 3 × ℕ, K₃)`: the general block-model evaluation
`QMF.Weight.evalAtReps` at `classRep` — the `i`-th block of `evalU3 φ` is `φ(cᵢ)`.
[Buz07, §9 p. 69]: "`f ∈ L(U,A)` is determined by `f(τ_λ)`". -/
noncomputable abbrev evalU3 : kappaForms t ht →ₗ[K₃] c(Fin 3 × ℕ, K₃) :=
  Weight.evalAtReps (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ 1
    classRep

/-- **[Buz07, §9 p. 69] at the Jacobs data**: evaluation at the class representatives is
a bijection onto the block model — the general neat-level model isomorphism
`QMF.Weight.bijective_evalAtReps_of_stabilizer_eq_bot` at Theorem 2.1 (`classRep_bijective`)
and Lemma 2.2 (`stabilizerAt_classRep i = ⊥`). -/
theorem bijective_evalU3 (hcn : HClassNumberOne) :
    Function.Bijective (evalU3 t ht) :=
  Weight.bijective_evalAtReps_of_stabilizer_eq_bot (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9
    U1_9_subset_levelMonoid1₃ 1 classRep (classRep_bijective hcn) stabilizerAt_classRep

/-- The model isomorphism `L(U₁(9), A₃) ≅ ⊕ᵢ A₃` [Jacobs, (2.1.1)], packaged: under
`HClassNumberOne`, weight-`κ` forms are exactly the block model `c(Fin 3 × ℕ, K₃)`. -/
noncomputable def kappaFormsModelEquiv (hcn : HClassNumberOne) :
    kappaForms t ht ≃ₗ[K₃] c(Fin 3 × ℕ, K₃) :=
  LinearEquiv.ofBijective (evalU3 t ht) (bijective_evalU3 t ht hcn)

/-- **Unconditional transport**: under evaluation at the representatives, the Hecke
operator `U₃` is the assembled certificate block operator — the general transport
`QMF.Weight.evalAtReps_heckeOperator` at the `«5_Factorisations»` certificates. -/
theorem evalU3_heckeU3 (φ : kappaForms t ht) :
    evalU3 t ht (heckeU3 t ht φ) = blockOp (blockEntry t ht) (evalU3 t ht φ) :=
  Weight.evalAtReps_heckeOperator (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9
    U1_9_subset_levelMonoid1₃ 1 eta3_mem_levelMonoid1₃ finite_image_eta3 classRep etaRep
    etaRep_mem_levelMonoid1₃ bijOn_etaRep etaRep_injective sigmaTable
    (fun i t' => unitsIncl ℚ D (dTable i t')) (fun i t' => dTable_mem i t') uTable
    (fun i t' => by rw [uTable_coe]; exact factorisation i t') φ

/-- `‖det (η₃)₃‖ ≤ ‖3‖`: the determinant certificate of the compactness theorem at the
Jacobs data (`(η₃)₃ = diag(3, 1)`). -/
theorem norm_det_toMatrix_eta3_le : ‖(toMatrix ℚ D v₃ eta3).det‖ ≤ ‖(3 : K₃)‖ := by
  rw [toMatrix_eta3, Matrix.det_fin_two_of]
  simp

/-- The assembled certificate block operator is compactoid: the general compactness
theorem `QMF.Weight.isCompactoid_heckeBlockOp` ([Jacobs, Lemma 2.7] / [Buz07, Lemma 12.2]) at
the Jacobs data, with determinant certificate `‖det (η₃)₃‖ = ‖3‖ ≤ ‖3‖`. -/
theorem isCompactoid_blockOpU3 : IsCompactoid (blockOp (blockEntry t ht)) :=
  Weight.isCompactoid_heckeBlockOp (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9
    U1_9_subset_levelMonoid1₃ 1 le_rfl norm_three_lt_one norm_det_toMatrix_eta3_le
    etaRep_mem_levelMonoid1₃ bijOn_etaRep sigmaTable uTable

/-- **`det(1 − T·U₃)`** — the Fredholm determinant (characteristic power series) of the
Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` on the weight-`κ` space: the general
`QMF.Weight.heckeCharPowerSeries` at the `«5_Factorisations»` certificates, i.e. the
characteristic power series of the block operator `blockOp (blockEntry t ht)` through which
`U₃` acts on the model (`evalU3_heckeU3`).  (The definition itself needs no
`HClassNumberOne`: the block operator is assembled from the unconditional certificates;
`hcn` is needed only to know the model is *all* of `L(U₁(9), A₃)`, via
`kappaFormsModelEquiv`.) -/
noncomputable abbrev charPowerSeriesU3 : PowerSeries K₃ :=
  Weight.heckeCharPowerSeries (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9
    U1_9_subset_levelMonoid1₃ 1 etaRep etaRep_mem_levelMonoid1₃ sigmaTable uTable

/-- **The `K₃`-headline**: `det(1 − T·U₃)` is computed by the transcribed Jacobs matrix
— with no determinant twist, because the fork's blocks equal the `ε`-operators exactly.
With it, every slope theorem about `JacobsSlash.U3MatrixOp` is a theorem about the
genuine `U₃`. -/
theorem charPowerSeriesU3_eq_U3MatrixOp :
    charPowerSeriesU3 t ht
      = charPowerSeries (U3MatrixOp norm_three_lt_one ht ν₃_near) :=
  charPowerSeries_blockEntry_eq_U3MatrixOp t ht

end JacobsSlash
