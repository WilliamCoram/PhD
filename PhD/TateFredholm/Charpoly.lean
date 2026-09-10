/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Reversed characteristic polynomials: base change and unipotent matrices

Facts about `Matrix.charpolyRev M = det (1 − X·M)` used in the rank and degree computations of
the Riesz–Coleman decomposition (`PhD.TateFredholm.RieszColeman`):

* `Matrix.charpolyRev_map`: `charpolyRev` commutes with ring homomorphisms.
* `Matrix.charpolyRev_mul_comm`, `Matrix.charpolyRev_eq_of_mul_eq`: Sylvester's identity
  `det (1 − X·AB) = det (1 − X·BA)`, and `charpolyRev M = charpolyRev (Q M P)` along a
  factorisation `E = PQ`, `QP = 1` of an idempotent with `ME = EM = M`.
* `Matrix.natDegree_charpolyRev_le`: `deg charpolyRev M ≤ size`.
* `Matrix.exists_mul_eq_of_idempotent`: rank factorisation `E = PQ`, `QP = 1` of an idempotent
  matrix whose range is free (e.g. over a field or a local ring).
* `Matrix.charpolyRev_eq_one_sub_pow_of_mul_eq`, `Matrix.charpolyRev_eq_one_sub_pow_rank`:
  over a field, if `M = E − N` with `E` idempotent, `N` nilpotent and `ME = EM = M`, then
  `charpolyRev M = (1 − X) ^ rank E` (Sylvester along a rank factorisation of `E`, and the
  nilpotent characteristic polynomial `charpoly N = X ^ card` over the reduced ring `K[X]`).
-/

open Polynomial

namespace Matrix

variable {R S : Type*} [CommRing R] [CommRing S] {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-- `charpolyRev` commutes with ring homomorphisms. -/
theorem charpolyRev_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  have h : (1 : Matrix n n S[X]) - (X : S[X]) • (M.map f).map C =
      (1 - (X : R[X]) • M.map C).map (mapRingHom f) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [charpolyRev, charpolyRev, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, coe_mapRingHom]

/-- Sylvester's identity for reversed characteristic polynomials of rectangular products:
`det (1 − X·AB) = det (1 − X·BA)`. -/
theorem charpolyRev_mul_comm (A : Matrix n m R) (B : Matrix m n R) :
    (A * B).charpolyRev = (B * A).charpolyRev := by
  rw [charpolyRev, charpolyRev, Matrix.map_mul, Matrix.map_mul, ← Matrix.smul_mul,
    det_one_sub_mul_comm, Matrix.mul_smul]

/-- Along a factorisation `E = PQ`, `QP = 1` of an idempotent with `ME = EM = M`,
`charpolyRev M = charpolyRev (Q M P)`. -/
theorem charpolyRev_eq_of_mul_eq {E M : Matrix n n R} (hME : M * E = M) (hEM : E * M = M)
    {P : Matrix n m R} {Q : Matrix m n R} (hPQ : P * Q = E) (hQP : Q * P = 1) :
    M.charpolyRev = (Q * M * P).charpolyRev := by
  have hMdec : M = P * (Q * M * P) * Q := by
    have : P * (Q * M * P) * Q = (P * Q) * M * (P * Q) := by simp only [Matrix.mul_assoc]
    rw [this, hPQ, hEM, hME]
  conv_lhs => rw [hMdec]
  rw [charpolyRev_mul_comm (P * (Q * M * P)) Q, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

/-- `det (1 − X·M)` has degree at most the size of `M`. -/
theorem natDegree_charpolyRev_le (M : Matrix n n R) : M.charpolyRev.natDegree ≤ Fintype.card n := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim M.charpolyRev 0, natDegree_zero]
    exact Nat.zero_le _
  · rw [← reverse_charpoly]
    exact (reverse_natDegree_le _).trans (charpoly_natDegree_eq_dim M).le

omit [DecidableEq n] in
/-- An idempotent matrix fixes its range. -/
theorem mulVecLin_eq_self_of_mem_range {E : Matrix n n R} (hE : E * E = E) {v : n → R}
    (hv : v ∈ LinearMap.range E.mulVecLin) : E.mulVecLin v = v := by
  obtain ⟨x, rfl⟩ := hv
  rw [mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, hE]

omit [DecidableEq n] in
/-- The range of an idempotent matrix is a direct summand of `n → R`, hence projective. -/
theorem projective_range_mulVecLin_of_idempotent {E : Matrix n n R} (hE : E * E = E) :
    Module.Projective R (LinearMap.range E.mulVecLin) :=
  Module.Projective.of_split (LinearMap.range E.mulVecLin).subtype E.mulVecLin.rangeRestrict
    (LinearMap.ext fun v ↦ Subtype.ext (mulVecLin_eq_self_of_mem_range hE v.2))

/-- **Rank factorisation of an idempotent** with free range: `E = PQ` with `QP = 1`, the inner
size being the rank of the range of `E` (columns of `P` a basis of the range, `Q` the
coordinates). -/
theorem exists_mul_eq_of_idempotent [Nontrivial R] {E : Matrix n n R} (hE : E * E = E)
    [Module.Free R (LinearMap.range E.mulVecLin)]
    [Module.Finite R (LinearMap.range E.mulVecLin)] :
    ∃ (P : Matrix n (Fin (Module.finrank R (LinearMap.range E.mulVecLin))) R)
      (Q : Matrix (Fin (Module.finrank R (LinearMap.range E.mulVecLin))) n R),
      P * Q = E ∧ Q * P = 1 := by
  set V := LinearMap.range E.mulVecLin with hV
  let b : Module.Basis (Fin (Module.finrank R V)) R V := Module.finBasis R V
  set P' : (Fin (Module.finrank R V) → R) →ₗ[R] (n → R) :=
    V.subtype ∘ₗ b.equivFun.symm.toLinearMap with hP'
  set Q' : (n → R) →ₗ[R] (Fin (Module.finrank R V) → R) :=
    b.equivFun.toLinearMap ∘ₗ E.mulVecLin.rangeRestrict with hQ'
  have hQP' : Q' ∘ₗ P' = LinearMap.id := LinearMap.ext fun x ↦ by
    show b.equivFun (E.mulVecLin.rangeRestrict (V.subtype (b.equivFun.symm x))) = x
    rw [show E.mulVecLin.rangeRestrict (V.subtype (b.equivFun.symm x)) = b.equivFun.symm x from
      Subtype.ext (mulVecLin_eq_self_of_mem_range hE (b.equivFun.symm x).2),
      LinearEquiv.apply_symm_apply]
  have hPQ' : P' ∘ₗ Q' = E.mulVecLin := LinearMap.ext fun x ↦ by
    show V.subtype (b.equivFun.symm (b.equivFun (E.mulVecLin.rangeRestrict x))) = E.mulVecLin x
    rw [LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨LinearMap.toMatrix' P', LinearMap.toMatrix' Q', ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hPQ', ← Matrix.toLin'_apply']
    exact LinearMap.toMatrix'_toLin' E
  · rw [← LinearMap.toMatrix'_comp, hQP', LinearMap.toMatrix'_id]

variable {K : Type*} [Field K]

/-- Over a field, `1 − N` is unipotent for nilpotent `N`: `det (1 − X (1 − N)) = (1 − X) ^ card`. -/
theorem charpolyRev_one_sub_of_isNilpotent (N : Matrix n n K) (hN : IsNilpotent N) :
    (1 - N).charpolyRev = (1 - X) ^ Fintype.card n := by
  have hnil : IsNilpotent (-((X : K[X]) • N.map C)) :=
    ((hN.map (C.mapMatrix : Matrix n n K →+* Matrix n n K[X])).smul (X : K[X])).neg
  have hchar : (-((X : K[X]) • N.map C)).charpoly = X ^ Fintype.card n :=
    sub_eq_zero.mp (isNilpotent_charpoly_sub_pow_of_isNilpotent hnil).eq_zero
  have hmat : (1 : Matrix n n K[X]) - (X : K[X]) • (1 - N).map C =
      scalar n (1 - X) - -((X : K[X]) • N.map C) := by
    refine Matrix.ext fun i j ↦ ?_
    by_cases hij : i = j <;> simp [hij, Matrix.scalar_apply]
    ring
  rw [charpolyRev, hmat, ← eval_charpoly, hchar, eval_pow, eval_X]

/-- Over a field, if `M = E − N` with `E` idempotent, `N` nilpotent, `ME = EM = M` and
`E = PQ`, `QP = 1` is a factorisation through `m → K`, then `charpolyRev M = (1 − X) ^ card m`:
`Q M P = 1 − Q N P` is unipotent and Sylvester's identity (`charpolyRev_eq_of_mul_eq`)
reduces to `charpolyRev_one_sub_of_isNilpotent`. -/
theorem charpolyRev_eq_one_sub_pow_of_mul_eq {E M : Matrix n n K} (hE : E * E = E)
    (hME : M * E = M) (hEM : E * M = M) (hN : IsNilpotent (E - M)) {P : Matrix n m K}
    {Q : Matrix m n K} (hPQ : P * Q = E) (hQP : Q * P = 1) :
    M.charpolyRev = (1 - X) ^ Fintype.card m := by
  rw [charpolyRev_eq_of_mul_eq hME hEM hPQ hQP]
  have hQEP : Q * E * P = 1 := by
    calc Q * E * P = Q * (P * Q) * P := by rw [hPQ]
      _ = (Q * P) * (Q * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one]
  have hM₁eq : Q * M * P = 1 - Q * (E - M) * P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hQEP, sub_sub_cancel]
  have hK : IsNilpotent (Q * (E - M) * P) := by
    obtain ⟨k, hk⟩ := hN
    have hEN : E * (E - M) = E - M := by rw [Matrix.mul_sub, hE, hEM]
    have hpow : ∀ l, (Q * (E - M) * P) ^ (l + 1) = Q * (E - M) ^ (l + 1) * P := by
      intro l
      induction l with
      | zero => simp
      | succ l ih =>
        rw [pow_succ, ih, pow_succ]
        calc Q * (E - M) ^ (l + 1) * P * (Q * (E - M) * P)
            = Q * (E - M) ^ (l + 1) * (P * Q * (E - M)) * P := by simp only [Matrix.mul_assoc]
          _ = Q * ((E - M) ^ (l + 1) * (E - M)) * P := by
            rw [hPQ, hEN]
            simp only [Matrix.mul_assoc]
    exact ⟨k + 1, by rw [hpow, pow_succ, hk, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul]⟩
  rw [hM₁eq, charpolyRev_one_sub_of_isNilpotent _ hK]

/-- Over a field, if `M = E − N` with `E` idempotent, `N` nilpotent and `ME = EM = M`, then
`charpolyRev M = (1 − X) ^ rank E`. -/
theorem charpolyRev_eq_one_sub_pow_rank {E M : Matrix n n K} (hE : E * E = E) (hME : M * E = M)
    (hEM : E * M = M) (hN : IsNilpotent (E - M)) : M.charpolyRev = (1 - X) ^ E.rank := by
  obtain ⟨P, Q, hPQ, hQP⟩ := exists_mul_eq_of_idempotent hE
  rw [charpolyRev_eq_one_sub_pow_of_mul_eq hE hME hEM hN hPQ hQP, Fintype.card_fin]
  rfl

end Matrix
