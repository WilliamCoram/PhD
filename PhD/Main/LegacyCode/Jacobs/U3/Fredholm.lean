/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3.Matrix

/-!
# `det(1 − T·U₃)`: the Fredholm determinant of the genuine Hecke operator

The `K₃`-level endgame of the identification (board `.mathlib-quality/jacobs-endgame/`).
`PhD.Jacobs.U3.Matrix` proved that the Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` on the
weight-`κ` space evaluates at the class representatives through the certificate block
matrix (`heckeU3_apply_classRep`), and that evaluation at the representatives is
injective under `HClassNumberOne` (`eval_classRep_injective`).  This file upgrades the
two into a model isomorphism and defines the object the slope theory is about:

* `evalU3` — evaluation at the three representatives, landing in the block model
  `c(Fin 3 × ℕ, K₃)`; `bijective_evalU3` ([Buz07, §9]: `L(U,A) ≅ ⊕_λ A^{Γ_λ}`, with the
  invariants trivialised by Lemma 2.2's `stabilizerAt_classRep = ⊥`) and the packaged
  `kappaFormsModelEquiv` (both under `hcn : HClassNumberOne`).
* `evalU3_heckeU3` — **unconditional** transport: under `evalU3`, the Hecke operator is
  the assembled certificate block operator `TateFredholm.blockOp (blockOp t ht)`.
* `charPowerSeriesU3` — the Fredholm determinant `det(1 − T·U₃)`, defined through the
  block model; `isCompactoid_blockOpU3` makes the compact-operator theory applicable,
  and `charPowerSeriesU3_eq_U3MatrixOp` (the determinant-twist bridge of
  `PhD.Jacobs.U3.Matrix`) computes it by the transcribed matrix `Jacobs.U3MatrixOp` —
  the object whose slopes the AG-W/Tranche-A theory analysed.

The extension-field factorisation into the `M`-eigenblocks and the slope reading are in
`PhD.Jacobs.U3.HeckeSlopes` (they need `ω ∉ K₃`).
-/

open Quaternion IsDedekindDomain NumberField QMF TateFredholm

namespace Jacobs.U3

/-- `K₃` is a Tate ring: `3` is a pseudo-uniformizer.  (Required by the compactoid
closure lemmas and `summable_minor`; the `[IsTate _]`-hypothesis pattern is the
machine-checked amendment of the AG-W board's B2 log.) -/
instance : IsTate K₃ :=
  ⟨⟨PseudoUniformizer.ofNormLtOne (by norm_num : (3 : K₃) ≠ 0) norm_three_lt_one⟩⟩

variable (t : K₃) (ht : ‖t‖ < 1)

/-- Evaluation of a weight-`κ` form at the three class representatives, assembled into
the block model `c(Fin 3 × ℕ, K₃)`: the `i`-th block of `evalU3 φ` is `φ(cᵢ)`.
[Buz07, §9 p. 69]: "`f ∈ L(U,A)` is determined by `f(τ_λ)`". -/
noncomputable def evalU3 : kappaForms t ht →ₗ[K₃] c(Fin 3 × ℕ, K₃) where
  toFun φ := ∑ i : Fin 3, cSpace.blockIncl i
    (((φ : kappaForms t ht) :
        AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i))
  map_add' φ ψ := by simp [Finset.sum_add_distrib]
  map_smul' r φ := by simp [Finset.smul_sum]

/-- The `i`-th block of `evalU3 φ` is the value `φ(cᵢ)`. -/
theorem blockProj_evalU3 (φ : kappaForms t ht) (i : Fin 3) :
    cSpace.blockProj i (evalU3 t ht φ)
      = ((φ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i) := by
  simp only [evalU3, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    cSpace.blockProj_blockIncl, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **[Buz07, §9 p. 69] at the Jacobs data**: evaluation at the class representatives is
a bijection onto the block model.  Injectivity is `eval_classRep_injective`; surjectivity
is `AutomorphicFunction.bijective_evalAtReps` at the section provided by
`exists_classRep_section`, with the `Γ_λ`-invariant restriction trivialised by Lemma 2.2
(`stabilizerAt_classRep i = ⊥`). -/
theorem bijective_evalU3 (hcn : HClassNumberOne) :
    Function.Bijective (evalU3 t ht) := by
  letI := kappaLevelAction t ht
  haveI := kappaLevelSMulCommClass t ht
  constructor
  · refine fun φ ψ h => eval_classRep_injective t ht hcn φ ψ fun i => ?_
    simpa only [blockProj_evalU3] using congrArg (cSpace.blockProj i) h
  · intro F
    obtain ⟨σsec, hσ, hcr⟩ := exists_classRep_section hcn
    choose idx hidx using hcr
    obtain ⟨φ, hφ⟩ := (AutomorphicFunction.bijective_evalAtReps (A := c(ℕ, K₃)) K₃
      U1_9_subset_levelMonoid1 σsec hσ).2 (fun q => ⟨cSpace.blockProj (idx q) F,
        fun v => by
          have h1 : (v : Dfx ℚ D) = 1 :=
            Subgroup.mem_bot.mp (stabilizerAt_classRep (idx q) ▸ hidx q ▸ v.2)
          rw [show ∀ p : (v : Dfx ℚ D) ∈ levelMonoid1,
              (⟨(v : Dfx ℚ D), p⟩ : levelMonoid1) = 1 from fun _ => Subtype.ext h1,
            one_smul]⟩)
    refine ⟨φ, DFunLike.ext _ _ fun x => ?_⟩
    obtain ⟨i, n⟩ := x
    have h2 : idx (Quotient.mk'' (classRep i)) = i := by
      obtain ⟨d, hd, u, hu, heq⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp
        (hidx (Quotient.mk'' (classRep i)) ▸ hσ (Quotient.mk'' (classRep i))))
      exact (classRep_index_unique hd hu heq).symm
    have h3 : ((φ : kappaForms t ht) :
        AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
          (σsec (Quotient.mk'' (classRep i)))
        = cSpace.blockProj (idx (Quotient.mk'' (classRep i))) F :=
      congrArg Subtype.val (congrFun hφ (Quotient.mk'' (classRep i)))
    rw [hidx (Quotient.mk'' (classRep i)), h2] at h3
    simpa only [cSpace.blockProj_apply] using
      congrArg (fun g => g n) ((blockProj_evalU3 t ht φ i).trans h3)

/-- The model isomorphism `L(U₁(9), A₃) ≅ ⊕ᵢ A₃` [Jacobs, (2.1.1)], packaged: under
`HClassNumberOne`, weight-`κ` forms are exactly the block model `c(Fin 3 × ℕ, K₃)`. -/
noncomputable def kappaFormsModelEquiv (hcn : HClassNumberOne) :
    kappaForms t ht ≃ₗ[K₃] c(Fin 3 × ℕ, K₃) :=
  LinearEquiv.ofBijective (evalU3 t ht) (bijective_evalU3 t ht hcn)

/-- **Unconditional transport**: under evaluation at the representatives, the Hecke
operator `U₃` is the assembled certificate block operator.  This is
`heckeU3_apply_classRep` read through the block model (`blockIncl`/`blockProj`
orthogonality collapses the double sum). -/
theorem evalU3_heckeU3 (φ : kappaForms t ht) :
    evalU3 t ht (heckeU3 t ht φ)
      = TateFredholm.blockOp (blockOp t ht) (evalU3 t ht φ) := by
  simp only [evalU3, LinearMap.coe_mk, AddHom.coe_mk, heckeU3_apply_classRep, map_sum,
    blockOp_blockIncl]
  exact Finset.sum_comm

-- Public-API candidate (BlockOp/TateFredholm): duplicates `TateFredholm.IsCompactoid.smul`
-- (09_Riesz.lean, outside this file's import closure); deduplicate once the BlockOp import
-- chain reaches Riesz.  Compactoidness is closed under scalar multiples: rows scale by `‖s‖`.
private theorem isCompactoid_smul (s : K₃) {u : c(ℕ, K₃) →L[K₃] c(ℕ, K₃)}
    (hu : IsCompactoid u) : IsCompactoid (s • u) := by
  have hb : ∀ j, rowNorm (s • u) j ≤ ‖s‖ * rowNorm u j := by
    intro j
    refine Real.iSup_le (fun i => ?_) (mul_nonneg (norm_nonneg s) (rowNorm_nonneg u j))
    calc ‖matrixCoeff (s • u) j i‖ = ‖s‖ * ‖matrixCoeff u j i‖ := norm_mul _ _
      _ ≤ ‖s‖ * rowNorm u j :=
          mul_le_mul_of_nonneg_left (norm_matrixCoeff_le_rowNorm_of_isTate u j i)
            (norm_nonneg s)
  exact squeeze_zero (fun j => rowNorm_nonneg _ j) hb (by simpa using hu.const_mul ‖s‖)

/-- The assembled certificate block operator is compactoid: its blocks are the
transcribed `ε`-operators scaled by the (norm-one) coboundary weights
(`blockOp_eq_smul_epsOp`), and compactoidness is closed under scalars and block
assembly. -/
theorem isCompactoid_blockOpU3 : IsCompactoid (TateFredholm.blockOp (blockOp t ht)) := by
  rw [blockOp_eq_smul_epsOp t ht]
  refine isCompactoid_blockOp fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      smul_zero]
  · exact isCompactoid_zero_clm norm_three_lt_one
  · exact isCompactoid_smul _ (isCompactoid_epsOp01 norm_three_lt_one ht ν₃_near)
  · exact isCompactoid_smul _ (isCompactoid_epsOp02 norm_three_lt_one ht ν₃_near)
  · exact isCompactoid_smul _ (isCompactoid_epsOp10 norm_three_lt_one ht ν₃_near)
  · exact isCompactoid_zero_clm norm_three_lt_one
  · exact isCompactoid_smul _ (isCompactoid_epsOp12 norm_three_lt_one ht ν₃_near)
  · exact isCompactoid_smul _ (isCompactoid_epsOp20 norm_three_lt_one ht ν₃_near)
  · exact isCompactoid_smul _ (isCompactoid_epsOp21 norm_three_lt_one ht ν₃_near)
  · exact isCompactoid_zero_clm norm_three_lt_one

/-- **`det(1 − T·U₃)`** — the Fredholm determinant (characteristic power series) of the
Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` on the weight-`κ` space, computed through the
block model of `evalU3`/`kappaFormsModelEquiv`: by `evalU3_heckeU3` the operator acts on
the model as `TateFredholm.blockOp (blockOp t ht)`, whose characteristic power series
this is.  (The definition itself needs no `HClassNumberOne`: the block operator is
assembled from the unconditional certificates; `hcn` is needed only to know the model is
*all* of `L(U₁(9), A₃)`, via `kappaFormsModelEquiv`.) -/
noncomputable def charPowerSeriesU3 : PowerSeries K₃ :=
  charPowerSeries (TateFredholm.blockOp (blockOp t ht))

/-- **The `K₃`-headline**: `det(1 − T·U₃)` is computed by the transcribed Jacobs matrix.
This is the determinant-twist bridge `charPowerSeries_blockOp_eq_U3MatrixOp` restated
through `charPowerSeriesU3`; with it, every Tranche-A/AG-W/AG-NP theorem about
`Jacobs.U3MatrixOp` is a theorem about the genuine `U₃`. -/
theorem charPowerSeriesU3_eq_U3MatrixOp :
    charPowerSeriesU3 t ht
      = charPowerSeries (Jacobs.U3MatrixOp norm_three_lt_one ht ν₃_near) :=
  charPowerSeries_blockOp_eq_U3MatrixOp t ht

end Jacobs.U3
