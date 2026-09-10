/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The resultant of the characteristic polynomial against a polynomial

The finite-dimensional input to Coleman's spectral mapping formula
`det(1 − T·B(φ)) = D(B, det(1 − Tφ))` ([Bel] Proposition II.2.16, [Buz07] p. 21): for a
square matrix `A` over a commutative ring and any polynomial `g`,

  `Res(charpoly A, g) = det (g(A))`.

Over an algebraically closed field both sides are `∏ g(λ)` over the eigenvalues (with
multiplicity); the general case follows by the universal characteristic polynomial
`Matrix.charpoly.univ` (a polynomial-identity reduction to `ℤ[xᵢⱼ, yₖ]`, embedded in an
algebraic closure of its fraction field).  Mathlib PR candidate.

## Main results

* `Matrix.resultant_charpoly`: `Res(charpoly A, g) = det (g(A))` over any commutative ring.
* `Matrix.det_aeval_eq_prod_roots`: `det (g(A)) = ∏ g(λ)` over the roots of `charpoly A`, when
  `charpoly A` splits.

## References

* [Bel] J. Bellaïche, *The eigenbook*, Proposition II.2.16 and Lemma II.2.13.
* [Buz07] K. Buzzard, *Eigenvarieties*, p. 21.
-/

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Both sides are multiplicative in `g`, so it suffices to treat `g = C c` and `g = X - C μ`,
-- where `det (A - μ) = (−1)ⁿ charpoly A (μ)`.  The hypothesis `hg` is removed in
-- `det_aeval_eq_prod_roots` below, after the resultant identity is available.
private theorem det_aeval_eq_prod_roots_of_splits {K : Type*} [CommRing K] [IsDomain K]
    (A : Matrix n n K) (g : K[X]) (hA : A.charpoly.Splits) (hg : g.Splits) :
    (Polynomial.aeval A g).det = (A.charpoly.roots.map g.eval).prod := by
  have hcard : Multiset.card A.charpoly.roots = Fintype.card n := by
    rw [← hA.natDegree_eq_card_roots, charpoly_natDegree_eq_dim]
  let D : K[X] →* K := detMonoidHom.comp (Polynomial.aeval A).toRingHom.toMonoidHom
  let E : K[X] →* K :=
    { toFun := fun g ↦ (A.charpoly.roots.map g.eval).prod
      map_one' := by simp
      map_mul' := fun g h ↦ by simp [eval_mul, Multiset.prod_map_mul] }
  change D g = E g
  rw [hg.eq_prod_roots, map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  congr 1
  · show (Polynomial.aeval A (C g.leadingCoeff)).det =
      (A.charpoly.roots.map (C g.leadingCoeff).eval).prod
    simp [Algebra.algebraMap_eq_smul_one, Multiset.map_const', hcard]
  · congr 1
    refine Multiset.map_congr rfl fun μ _ ↦ ?_
    show (Polynomial.aeval A (X - C μ)).det = (A.charpoly.roots.map (X - C μ).eval).prod
    simp only [map_sub, aeval_X, aeval_C, eval_sub, eval_X, eval_C]
    rw [Algebra.algebraMap_eq_smul_one, ← neg_sub, det_neg, smul_one_eq_diagonal, ← scalar_apply,
      ← eval_charpoly, hA.eval_eq_prod_roots, (charpoly_monic A).leadingCoeff, one_mul]
    simp only [← neg_sub μ]
    rw [show (fun x ↦ -(μ - x)) = Neg.neg ∘ (fun x ↦ μ - x) from rfl, ← Multiset.map_map,
      Multiset.prod_map_neg, Multiset.card_map, hcard]

private theorem resultant_charpoly_of_splits {K : Type*} [CommRing K] [IsDomain K]
    (A : Matrix n n K) (g : K[X]) (m : ℕ) (hg : g.natDegree ≤ m) (hA : A.charpoly.Splits)
    (hgs : g.Splits) :
    Polynomial.resultant A.charpoly g (Fintype.card n) m = (Polynomial.aeval A g).det := by
  have := Polynomial.resultant_eq_prod_eval A.charpoly g m hg hA
  rw [charpoly_natDegree_eq_dim, (charpoly_monic A).leadingCoeff, one_pow, one_mul] at this
  rw [this, det_aeval_eq_prod_roots_of_splits A g hA hgs]

/-- The scalar embedding into matrices commutes with `RingHom.mapMatrix`. -/
theorem algebraMap_comp_eq_mapMatrix_comp {T T' : Type*} [CommRing T] [CommRing T']
    (ψ : T →+* T') :
    (algebraMap T' (Matrix n n T')).comp ψ = ψ.mapMatrix.comp (algebraMap T (Matrix n n T)) := by
  ext t : 1
  simp [Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero ψ)]

/-- **`Res(charpoly A, g) = det (g(A))`** over any commutative ring, with the degree bound `m`
on `g` (the resultant's degree parameter for `charpoly A` is the matrix size). -/
theorem resultant_charpoly {R : Type*} [CommRing R] (A : Matrix n n R) (g : R[X]) (m : ℕ)
    (hg : g.natDegree ≤ m) :
    Polynomial.resultant A.charpoly g (Fintype.card n) m = (Polynomial.aeval A g).det := by
  let U : Matrix n n (MvPolynomial (n × n ⊕ ℕ) ℤ) :=
    Matrix.of fun i j ↦ MvPolynomial.X (Sum.inl (i, j))
  let G : (MvPolynomial (n × n ⊕ ℕ) ℤ)[X] :=
    ∑ k ∈ Finset.range (m + 1), C (MvPolynomial.X (Sum.inr k)) * X ^ k
  have hGdeg : G.natDegree ≤ m := natDegree_sum_le_of_forall_le _ _ fun k hk ↦
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  -- the specialisation `S → R` sending the variables to the entries of `A` and coefficients of `g`
  let φ : MvPolynomial (n × n ⊕ ℕ) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (Sum.elim (fun ij ↦ A ij.1 ij.2) fun k ↦ g.coeff k)
  have hU : U.map φ = A := by
    ext i j
    simp [U, φ]
  have hG : G.map φ = g := by
    conv_rhs => rw [g.as_sum_range' (m + 1) (Nat.lt_succ_of_le hg)]
    simp [G, φ, Polynomial.map_sum, Polynomial.C_mul_X_pow_eq_monomial]
  -- the universal identity, checked in an algebraic closure of the fraction field of `S`
  let K := AlgebraicClosure (FractionRing (MvPolynomial (n × n ⊕ ℕ) ℤ))
  have hinj : Function.Injective (algebraMap (MvPolynomial (n × n ⊕ ℕ) ℤ) K) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (n × n ⊕ ℕ) ℤ)
      (FractionRing (MvPolynomial (n × n ⊕ ℕ) ℤ)) K]
    exact (algebraMap (FractionRing (MvPolynomial (n × n ⊕ ℕ) ℤ)) K).injective.comp
      (IsFractionRing.injective (MvPolynomial (n × n ⊕ ℕ) ℤ) _)
  have hS : Polynomial.resultant U.charpoly G (Fintype.card n) m = (Polynomial.aeval U G).det := by
    apply hinj
    rw [← Polynomial.resultant_map_map, ← charpoly_map, RingHom.map_det,
      map_aeval_eq_aeval_map (algebraMap_comp_eq_mapMatrix_comp
        (algebraMap (MvPolynomial (n × n ⊕ ℕ) ℤ) K)), RingHom.mapMatrix_apply]
    exact resultant_charpoly_of_splits _ _ m (natDegree_map_le.trans hGdeg) (IsAlgClosed.splits _)
      (IsAlgClosed.splits _)
  have := congrArg φ hS
  rwa [← Polynomial.resultant_map_map, ← charpoly_map, RingHom.map_det,
    map_aeval_eq_aeval_map (algebraMap_comp_eq_mapMatrix_comp φ), RingHom.mapMatrix_apply, hU,
    hG] at this

/-- Over a domain in which `charpoly A` splits, `det (g(A)) = ∏ g(λ)` over the roots `λ` of the
characteristic polynomial, for every polynomial `g` (generalising
`Matrix.det_eq_prod_roots_charpoly_of_splits`, the case `g = X`). -/
theorem det_aeval_eq_prod_roots {K : Type*} [CommRing K] [IsDomain K] (A : Matrix n n K)
    (g : K[X]) (hA : A.charpoly.Splits) :
    (Polynomial.aeval A g).det = (A.charpoly.roots.map g.eval).prod := by
  have h := Polynomial.resultant_eq_prod_eval A.charpoly g g.natDegree le_rfl hA
  rw [charpoly_natDegree_eq_dim, (charpoly_monic A).leadingCoeff, one_pow, one_mul,
    resultant_charpoly A g g.natDegree le_rfl] at h
  exact h

end Matrix
