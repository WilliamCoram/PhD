/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Conjugation

/-!
# Block-diagonal maps between block models with different fibres — SKELETON

`blockDiag f` (`Conjugation.lean`) applies one operator `f : c(I, R) →L[R] c(I, R)` in every
diagonal block of `c(σ × I, R)`.  The disc model of `S^{D,†,m}` (`PhD/LWX/DiscModel.lean`) needs
the same construction for a map `f : c(I, R) →L[R] c(I', R)` **changing the fibre**
(`I = ℤ/pʰ × ℕ`, `I' = ℕ`: the monomial-to-Mahler map at level `h`), together with the rectangular
block operators `blockOpMap T`, `T : σ → σ → (c(I, R) →L[R] c(I', R))`, and the composition rules
with `blockOp`/`blockDiag` used to move the seam identity from one block to the block model.

## Main declarations

* `TateFredholm.blockOpMap`, `TateFredholm.blockMap`, `matrixCoeff_blockOpMap`,
  `matrixCoeff_blockMap`.
* `blockMap_comp_blockOp`, `blockOp_comp_blockMap`, `blockMap_comp`, `blockMap_id`,
  `blockMap_eq_blockDiag`.
* `TateFredholm.blockMapEquiv`, `coe_blockMapEquiv`, `coe_blockMapEquiv_symm`.
-/

open scoped TateFredholm

noncomputable section

namespace TateFredholm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {I I' I'' : Type*} [DecidableEq I]
  [DecidableEq I'] [DecidableEq I'']

/-- The rectangular block operator `c(σ × I, R) →L[R] c(σ × I', R)` with blocks `T a b`. -/
def blockOpMap (T : σ → σ → (c(I, R) →L[R] c(I', R))) : c(σ × I, R) →L[R] c(σ × I', R) :=
  ∑ a : σ, ∑ b : σ, (cSpace.blockIncl a).comp ((T a b).comp (cSpace.blockProj b))

/-- The block-diagonal map with the same fibre map `f` in every block. -/
def blockMap (f : c(I, R) →L[R] c(I', R)) : c(σ × I, R) →L[R] c(σ × I', R) :=
  blockOpMap fun a b => if a = b then f else 0

omit [DecidableEq I] [DecidableEq I'] in
theorem blockOpMap_blockIncl (T : σ → σ → (c(I, R) →L[R] c(I', R))) (b : σ) (x : c(I, R)) :
    blockOpMap T (cSpace.blockIncl b x) = ∑ a : σ, cSpace.blockIncl a (T a b x) := by
  have hterm : ∀ a b' : σ,
      ((cSpace.blockIncl a).comp ((T a b').comp (cSpace.blockProj b'))) (cSpace.blockIncl b x)
        = if b' = b then cSpace.blockIncl a ((T a b) x) else 0 := by
    intro a b'
    show cSpace.blockIncl a ((T a b') (cSpace.blockProj b' (cSpace.blockIncl b x))) = _
    rw [cSpace.blockProj_blockIncl]
    by_cases hb : b' = b
    · subst hb
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hb, if_neg hb, map_zero, map_zero]
  rw [blockOpMap, _root_.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [_root_.sum_apply]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [DecidableEq I'] in
@[simp] theorem matrixCoeff_blockOpMap (T : σ → σ → (c(I, R) →L[R] c(I', R))) (a b : σ)
    (j : I') (i : I) :
    matrixCoeff (blockOpMap T) (a, j) (b, i) = matrixCoeff (T a b) j i := by
  show blockOpMap T (cSpace.single (b, i) 1) (a, j) = _
  rw [← cSpace.blockIncl_single b i (1 : R), blockOpMap_blockIncl, cSpace.sum_apply]
  simp only [cSpace.blockIncl_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

omit [DecidableEq I] [DecidableEq I'] in
theorem blockMap_blockIncl (f : c(I, R) →L[R] c(I', R)) (a : σ) (x : c(I, R)) :
    blockMap (σ := σ) f (cSpace.blockIncl a x) = cSpace.blockIncl a (f x) := by
  rw [blockMap, blockOpMap_blockIncl,
    Finset.sum_eq_single a (fun b _ hb => by
      rw [if_neg hb, zero_apply, map_zero])
      fun hcon => absurd (Finset.mem_univ a) hcon, if_pos rfl]

omit [DecidableEq I'] in
@[simp] theorem matrixCoeff_blockMap (f : c(I, R) →L[R] c(I', R)) (a b : σ) (j : I') (i : I) :
    matrixCoeff (blockMap (σ := σ) f) (a, j) (b, i) = if a = b then matrixCoeff f j i else 0 := by
  rw [blockMap, matrixCoeff_blockOpMap]
  split_ifs <;> simp

omit [DecidableEq I] in
/-- When the fibres agree, `blockMap` is `blockDiag`. -/
theorem blockMap_eq_blockDiag (f : c(I, R) →L[R] c(I, R)) :
    blockMap (σ := σ) f = blockDiag f := rfl

theorem blockMap_id : blockMap (σ := σ) (ContinuousLinearMap.id R c(I, R))
    = ContinuousLinearMap.id R c(σ × I, R) := by
  rw [blockMap_eq_blockDiag]
  exact blockDiag_id

/-- Left composition with a block-diagonal map acts blockwise. -/
theorem blockMap_comp_blockOp (f : c(I, R) →L[R] c(I', R))
    (T : σ → σ → (c(I, R) →L[R] c(I, R))) :
    (blockMap f).comp (blockOp T) = blockOpMap fun a b => f.comp (T a b) := by
  refine ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨b, i⟩ := y
  rw [matrixCoeff_blockOpMap]
  show blockMap f (blockOp T (cSpace.single (b, i) 1)) (a, j) = _
  rw [← cSpace.blockIncl_single b i (1 : R), blockOp_blockIncl, map_sum, cSpace.sum_apply,
    Finset.sum_congr rfl fun a' _ => by rw [blockMap_blockIncl]]
  simp only [cSpace.blockIncl_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-- Right composition with a block-diagonal map acts blockwise. -/
theorem blockOp_comp_blockMap (T : σ → σ → (c(I', R) →L[R] c(I', R)))
    (f : c(I, R) →L[R] c(I', R)) :
    (blockOp T).comp (blockMap f) = blockOpMap fun a b => (T a b).comp f := by
  refine ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨b, i⟩ := y
  rw [matrixCoeff_blockOpMap]
  show blockOp T (blockMap f (cSpace.single (b, i) 1)) (a, j) = _
  rw [← cSpace.blockIncl_single b i (1 : R), blockMap_blockIncl, blockOp_blockIncl,
    cSpace.sum_apply]
  simp only [cSpace.blockIncl_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

omit [DecidableEq I'] in
/-- Block-diagonal maps compose blockwise. -/
theorem blockMap_comp (g : c(I', R) →L[R] c(I'', R)) (f : c(I, R) →L[R] c(I', R)) :
    (blockMap (σ := σ) g).comp (blockMap f) = blockMap (g.comp f) := by
  refine ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨b, i⟩ := y
  rw [matrixCoeff_blockMap]
  show blockMap g (blockMap f (cSpace.single (b, i) 1)) (a, j) = _
  rw [← cSpace.blockIncl_single b i (1 : R), blockMap_blockIncl, blockMap_blockIncl,
    cSpace.blockIncl_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl]
    rfl
  · rw [if_neg hab, if_neg hab]

/-- The block-diagonal continuous linear equivalence induced by a fibre equivalence. -/
def blockMapEquiv (e : c(I, R) ≃L[R] c(I', R)) : c(σ × I, R) ≃L[R] c(σ × I', R) :=
  ContinuousLinearEquiv.equivOfInverse (blockMap (e : c(I, R) →L[R] c(I', R)))
    (blockMap (e.symm : c(I', R) →L[R] c(I, R)))
    (fun x => by
      have hx := DFunLike.congr_fun (blockMap_comp (σ := σ)
        (e.symm : c(I', R) →L[R] c(I, R)) (e : c(I, R) →L[R] c(I', R))) x
      rw [ContinuousLinearMap.comp_apply] at hx
      rw [hx, show (e.symm : c(I', R) →L[R] c(I, R)).comp (e : c(I, R) →L[R] c(I', R))
        = ContinuousLinearMap.id R c(I, R) from by ext; simp, blockMap_id]
      rfl)
    (fun x => by
      have hx := DFunLike.congr_fun (blockMap_comp (σ := σ)
        (e : c(I, R) →L[R] c(I', R)) (e.symm : c(I', R) →L[R] c(I, R))) x
      rw [ContinuousLinearMap.comp_apply] at hx
      rw [hx, show (e : c(I, R) →L[R] c(I', R)).comp (e.symm : c(I', R) →L[R] c(I, R))
        = ContinuousLinearMap.id R c(I', R) from by ext; simp, blockMap_id]
      rfl)

@[simp] theorem coe_blockMapEquiv (e : c(I, R) ≃L[R] c(I', R)) :
    (blockMapEquiv (σ := σ) e : c(σ × I, R) →L[R] c(σ × I', R))
      = blockMap (e : c(I, R) →L[R] c(I', R)) := rfl

@[simp] theorem coe_blockMapEquiv_symm (e : c(I, R) ≃L[R] c(I', R)) :
    ((blockMapEquiv (σ := σ) e).symm : c(σ × I', R) →L[R] c(σ × I, R))
      = blockMap (e.symm : c(I', R) →L[R] c(I, R)) := rfl

end TateFredholm

end
