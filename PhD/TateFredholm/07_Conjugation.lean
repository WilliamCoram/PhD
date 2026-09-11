/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.«06_BlockOp»

/-!
# Diagonal intertwining and block-diagonal equivalences

Two general facts about the Fredholm determinant on model spaces, consumed by the
[LWX, Prop 2.17] seam:

* **Diagonal intertwining leaves every principal minor unchanged.**  If `D·M_v = M_u·D`
  entrywise for a diagonal `D = diag(d)` with unit entries — the situation "`P` and `P′`
  are conjugated by an infinite diagonal matrix" of [LWX, Prop 2.17, proof], stated
  *without* inverting `D` (the inverse `diag(1/n!)` is unbounded there) — then
  `det(D_S)·det(M_v^S) = det(M_u^S)·det(D_S)` for every finite `S`, and cancelling the unit
  `det(D_S)` gives `minor v S = minor u S`; hence `charCoeff v = charCoeff u` termwise in the
  defining sums, with **no compactness hypothesis**.  ([LWX, Prop 2.17, proof]: "taking the
  limit of the characteristic polynomial of the first `r × r`-minors … gives
  `det(I∞ − XP′) = det(I∞ − XP)`".)
* The block-diagonal continuous linear equivalence `diagBlockEquiv e` of `c(σ × I, R)`
  induced by an equivalence `e` of `c(I, R)`, with its two composition rules — the vehicle
  for applying `charPowerSeries_conj` blockwise.

## Main declarations

* `TateFredholm.minor_eq_of_diag_intertwine`, `charCoeff_eq_of_diag_intertwine`,
  `charPowerSeries_eq_of_diag_intertwine`.
* `TateFredholm.blockDiag`, `blockDiag_id`, `blockDiag_comp_blockOp`, `blockOp_comp_blockDiag`,
  `blockDiag_comp`, `matrixCoeff_blockDiag` — block-diagonal operators.
* `TateFredholm.diagBlockEquiv`, `coe_diagBlockEquiv`, `coe_diagBlockEquiv_symm`.
-/

open scoped TateFredholm

noncomputable section

namespace TateFredholm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Diag

variable {I : Type*} [DecidableEq I]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
/-- **Diagonal intertwining preserves principal minors**: if `d i · v_{ij} = u_{ij} · d j` with
every `d i` a unit, then `det(v_S) = det(u_S)` for every finite `S` (cancel the unit
`det(diag(d)_S) = ∏_{i ∈ S} d i`). -/
theorem minor_eq_of_diag_intertwine {u v : c(I, R) →L[R] c(I, R)} (d : I → R)
    (hd : ∀ i, IsUnit (d i))
    (h : ∀ i j, d i * matrixCoeff v i j = matrixCoeff u i j * d j) (S : Finset I) :
    minor v S = minor u S := by
  classical
  set Dm : Matrix S S R := Matrix.diagonal fun i : S => d (i : I) with hDm
  have hunit : IsUnit Dm.det := by
    rw [hDm, Matrix.det_diagonal]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      fun i _ => hd i
  have hcomm : Dm * Matrix.of (fun j i : S => matrixCoeff v j i)
      = Matrix.of (fun j i : S => matrixCoeff u j i) * Dm := by
    ext j i
    rw [hDm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, Matrix.of_apply]
    exact h j i
  have hdet := congrArg Matrix.det hcomm
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm _ Dm.det] at hdet
  exact hunit.mul_left_cancel hdet

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
/-- The coefficients of `det(1 − Tu)` are termwise sums of principal minors, so a diagonal
intertwining leaves them unchanged — no compactness needed. -/
theorem charCoeff_eq_of_diag_intertwine {u v : c(I, R) →L[R] c(I, R)} (d : I → R)
    (hd : ∀ i, IsUnit (d i))
    (h : ∀ i j, d i * matrixCoeff v i j = matrixCoeff u i j * d j) (n : ℕ) :
    charCoeff v n = charCoeff u n := by
  unfold charCoeff
  congr 1
  exact tsum_congr fun S => minor_eq_of_diag_intertwine d hd h S

/-- **`det(I∞ − XP′) = det(I∞ − XP)` for diagonally conjugate matrices**
([LWX, Prop 2.17, proof]). -/
theorem charPowerSeries_eq_of_diag_intertwine {u v : c(I, R) →L[R] c(I, R)} (d : I → R)
    (hd : ∀ i, IsUnit (d i))
    (h : ∀ i j, d i * matrixCoeff v i j = matrixCoeff u i j * d j) :
    charPowerSeries v = charPowerSeries u :=
  PowerSeries.ext fun n => by
    rw [charPowerSeries_coeff, charPowerSeries_coeff]
    exact charCoeff_eq_of_diag_intertwine d hd h n

end Diag

section Block

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {I : Type*} [DecidableEq I]

/-- The block-diagonal operator with the same operator `f` in every diagonal block. -/
def blockDiag (f : c(I, R) →L[R] c(I, R)) : c(σ × I, R) →L[R] c(σ × I, R) :=
  blockOp fun a b => if a = b then f else 0

/-- `blockDiag` of the identity is the identity. -/
theorem blockDiag_id : blockDiag (σ := σ) (ContinuousLinearMap.id R c(I, R))
    = ContinuousLinearMap.id R c(σ × I, R) := by
  refine ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨b, i⟩ := y
  rw [blockDiag, matrixCoeff_blockOp]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    by_cases hij : j = i
    · subst hij
      simp [matrixCoeff]
    · simp [matrixCoeff, cSpace.single_apply_of_ne hij,
        cSpace.single_apply_of_ne (show (a, j) ≠ (a, i) from fun h => hij (Prod.ext_iff.mp h).2)]
  · rw [if_neg hab]
    simp [matrixCoeff, cSpace.single_apply_of_ne (show (a, j) ≠ (b, i) from
      fun h => hab (Prod.ext_iff.mp h).1)]
    rfl

/-- Left composition with a block-diagonal operator acts blockwise. -/
theorem blockDiag_comp_blockOp (f : c(I, R) →L[R] c(I, R))
    (T : σ → σ → (c(I, R) →L[R] c(I, R))) :
    (blockDiag f).comp (blockOp T) = blockOp fun a b => f.comp (T a b) := by
  rw [blockDiag, blockOp_comp]
  congr 1
  funext a c
  rw [Finset.sum_eq_single a (fun b _ hb => by
    rw [if_neg fun hab => hb hab.symm, ContinuousLinearMap.zero_comp])
    (fun h => absurd (Finset.mem_univ a) h), if_pos rfl]

/-- Right composition with a block-diagonal operator acts blockwise. -/
theorem blockOp_comp_blockDiag (T : σ → σ → (c(I, R) →L[R] c(I, R)))
    (f : c(I, R) →L[R] c(I, R)) :
    (blockOp T).comp (blockDiag f) = blockOp fun a b => (T a b).comp f := by
  rw [blockDiag, blockOp_comp]
  congr 1
  funext a c
  rw [Finset.sum_eq_single c (fun b _ hb => by
    rw [if_neg hb, ContinuousLinearMap.comp_zero])
    (fun h => absurd (Finset.mem_univ c) h), if_pos rfl]

/-- The matrix of `blockDiag f` is `f`'s matrix on the diagonal blocks and `0` elsewhere. -/
theorem matrixCoeff_blockDiag (f : c(I, R) →L[R] c(I, R)) (a b : σ) (j i : I) :
    matrixCoeff (blockDiag f) (a, j) (b, i) = if a = b then matrixCoeff f j i else 0 := by
  rw [blockDiag, matrixCoeff_blockOp]
  split_ifs <;> simp

/-- Block-diagonal operators compose blockwise. -/
theorem blockDiag_comp (g f : c(I, R) →L[R] c(I, R)) :
    (blockDiag (σ := σ) g).comp (blockDiag f) = blockDiag (g.comp f) := by
  change (blockDiag g).comp (blockOp fun a b => if a = b then f else 0) = _
  rw [blockDiag_comp_blockOp, blockDiag]
  congr 1
  funext a b
  split_ifs <;> simp

/-- The block-diagonal continuous linear equivalence of `c(σ × I, R)` induced by an
equivalence `e` of `c(I, R)`. -/
def diagBlockEquiv (e : c(I, R) ≃L[R] c(I, R)) : c(σ × I, R) ≃L[R] c(σ × I, R) :=
  ContinuousLinearEquiv.equivOfInverse (blockDiag (e : c(I, R) →L[R] c(I, R)))
    (blockDiag (e.symm : c(I, R) →L[R] c(I, R)))
    (fun x => by
      have h := DFunLike.congr_fun (blockDiag_comp (σ := σ)
        (e.symm : c(I, R) →L[R] c(I, R)) (e : c(I, R) →L[R] c(I, R))) x
      rw [ContinuousLinearMap.comp_apply] at h
      rw [h, show (e.symm : c(I, R) →L[R] c(I, R)).comp (e : c(I, R) →L[R] c(I, R))
        = ContinuousLinearMap.id R c(I, R) from by ext; simp, blockDiag_id]
      rfl)
    (fun x => by
      have h := DFunLike.congr_fun (blockDiag_comp (σ := σ)
        (e : c(I, R) →L[R] c(I, R)) (e.symm : c(I, R) →L[R] c(I, R))) x
      rw [ContinuousLinearMap.comp_apply] at h
      rw [h, show (e : c(I, R) →L[R] c(I, R)).comp (e.symm : c(I, R) →L[R] c(I, R))
        = ContinuousLinearMap.id R c(I, R) from by ext; simp, blockDiag_id]
      rfl)

@[simp] theorem coe_diagBlockEquiv (e : c(I, R) ≃L[R] c(I, R)) :
    (diagBlockEquiv (σ := σ) e : c(σ × I, R) →L[R] c(σ × I, R))
      = blockDiag (e : c(I, R) →L[R] c(I, R)) := rfl

@[simp] theorem coe_diagBlockEquiv_symm (e : c(I, R) ≃L[R] c(I, R)) :
    ((diagBlockEquiv (σ := σ) e).symm : c(σ × I, R) →L[R] c(σ × I, R))
      = blockDiag (e.symm : c(I, R) →L[R] c(I, R)) := rfl

end Block

end TateFredholm

end
