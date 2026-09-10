/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Scalar factorisations and the pairing of characteristic roots

If two square matrices satisfy `A * B = c • 1` then `A` is invertible with `B = c • A⁻¹`, and the
spectra of `A` and `B` are exchanged by `x ↦ c / x`.  This file records that exchange at three
levels of strength: determinants, characteristic polynomials, and root multisets.

This is the linear-algebra half of the Atkin–Lehner reduction (`PhD/LWX/AtkinLehner.lean`): with
`A` the matrix of `U_p`, `B` the matrix of the Atkin–Lehner conjugate `U'_p`, and
`c = p^{k+1}`, the root-multiset statement is [LWX, Prop 3.22]'s slope symmetry.  Nothing here is
`p`-adic or automorphic; the results are stated for an arbitrary commutative ring (determinant and
characteristic-polynomial levels) or algebraically closed field (root level).

## Main declarations

* `Matrix.det_mul_det_of_mul_eq_smul` — `det A * det B = c ^ n`.
* `Matrix.charpolyRev_conj`, `Matrix.charpoly_conj` — conjugation invariance.
* `Matrix.C_det_mul_charpolyRev_eq` — the functional equation
  `C (det A) * charpolyRev B = (-1)^n * (charpoly A).comp (C c * X)`.
* `Matrix.roots_charpolyRev` — the roots of `charpolyRev` are the inverses of those of `charpoly`
  for an invertible matrix (mathlib has no roots-of-`reverse` lemma).
* `Matrix.roots_charpoly_of_mul_eq_smul` — `(charpoly B).roots = (charpoly A).roots.map (c / ·)`.

The slope form (norms of the roots) is the one-line corollary
`LWX.norm_roots_charpoly_atkinLehner` in `PhD/LWX/AtkinLehner.lean`; it is kept there so that this
file stays purely algebraic and free of analysis imports.

## Design note

The root statement is phrased as an identity of **multisets** rather than as [LWX]'s
non-decreasing indexing `α_i = k + 1 − α_{n−1−i}`.  The multiset form is equivalent, avoids
sorting entirely, and serves both consumers directly: summing gives the slope total that
[LWX, Step I] needs, and `Multiset.count` gives the per-slope multiplicities that
[LWX, Step III] needs.
-/

namespace Matrix

open Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R] {A B : Matrix n n R} {c : R}

/-- From `A * B = c • 1`, the determinants multiply to `c ^ n`.  This is the determinant shadow of
[LWX, Prop 3.22] and the only strength [LWX, Step I] consumes. -/
theorem det_mul_det_of_mul_eq_smul (h : A * B = c • (1 : Matrix n n R)) :
    A.det * B.det = c ^ Fintype.card n := by
  rw [← det_mul, h, det_smul, det_one, mul_one]

/-- `charpolyRev` is invariant under conjugation by a one-sided inverse pair. -/
theorem charpolyRev_conj (P Q M : Matrix n n R) (h : Q * P = 1) :
    (P * M * Q).charpolyRev = M.charpolyRev := by
  rw [charpolyRev_mul_comm (P * M) Q, ← mul_assoc, h, one_mul]

/-- `charpoly` is invariant under conjugation by a one-sided inverse pair. -/
theorem charpoly_conj (P Q M : Matrix n n R) (h : Q * P = 1) :
    (P * M * Q).charpoly = M.charpoly := by
  rw [charpoly_mul_comm (P * M) Q, ← mul_assoc, h, one_mul]

/-- **The functional equation.**  From `A * B = c • 1`,
`C (det A) * charpolyRev B = (-1)^n * (charpoly A).comp (C c * X)`.  Substituting `X ↦ c/X`
exchanges the two spectra; this is that exchange stated without division. -/
theorem C_det_mul_charpolyRev_eq (h : A * B = c • (1 : Matrix n n R)) :
    C A.det * B.charpolyRev
      = (-1) ^ Fintype.card n * A.charpoly.comp (C c * X) := by
  have hL : C A.det * B.charpolyRev
      = (A.map C - (C c * X) • (1 : Matrix n n R[X])).det := by
    rw [RingHom.map_det, charpolyRev, ← det_mul, RingHom.mapMatrix_apply]
    congr 1
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ← Matrix.map_mul, h]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one]
      ring_nf
    · simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_ne hij, smul_eq_mul,
        mul_zero, map_zero]
  have hcomp : A.charpoly.comp (C c * X)
      = ((C c * X) • (1 : Matrix n n R[X]) - A.map C).det := by
    show Polynomial.eval₂RingHom (C : R →+* R[X]) (C c * X) A.charpoly = _
    rw [charpoly, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;>
      simp [hij, charmatrix, Matrix.scalar_apply]
  rw [hL, hcomp, ← Matrix.det_neg]
  congr 1
  abel

end CommRing

section Field

variable {K : Type*} [Field K] {A B : Matrix n n K} {c : K}

/-- If `A * B = c • 1` with `c ≠ 0` then `det A ≠ 0`. -/
theorem det_ne_zero_of_mul_eq_smul (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n K)) :
    A.det ≠ 0 := by
  intro hA
  have h' := det_mul_det_of_mul_eq_smul h
  rw [hA, zero_mul] at h'
  exact pow_ne_zero _ hc h'.symm

private theorem reverse_multiset_prod (s : Multiset K[X]) :
    s.prod.reverse = (s.map Polynomial.reverse).prod := by
  refine Multiset.induction_on s ?_ ?_
  · simp [Polynomial.reverse, Polynomial.reflect_one]
  · intro a t ih
    simp [Polynomial.reverse_mul_of_domain, ih]

private theorem reverse_X_sub_C (a : K) : (X - C a).reverse = 1 - C a * X := by
  ext k
  rw [Polynomial.coeff_reverse, natDegree_X_sub_C]
  match k with
  | 0 => rw [Polynomial.revAt_le (Nat.zero_le 1)]; simp
  | 1 => rw [Polynomial.revAt_le le_rfl]; simp [Polynomial.coeff_one]
  | (n + 2) =>
    rw [Polynomial.revAt_eq_self_of_lt (by omega)]
    simp [coeff_X, coeff_one]

variable [IsAlgClosed K]

omit [IsAlgClosed K] in
private theorem reverse_prod_X_sub_C (s : Multiset K) :
    (0 : K) ∉ s →
      (s.map fun a => X - C a).prod.reverse
        = C ((s.map fun a => -a).prod) * (s.map fun a => X - C a⁻¹).prod := by
  refine Multiset.induction_on s ?_ ?_
  · intro _
    simp [Polynomial.reverse, Polynomial.reflect_one]
  · intro a t ih hs
    have ha : a ≠ 0 := fun h => hs (h ▸ Multiset.mem_cons_self a t)
    have ht : (0 : K) ∉ t := fun h => hs (Multiset.mem_cons_of_mem h)
    have hlin : (1 : K[X]) - C a * X = C (-a) * (X - C a⁻¹) := by
      rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ ha, map_neg, map_neg, C_1]
      ring
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.reverse_mul_of_domain,
      reverse_X_sub_C, hlin, ih ht, Multiset.map_cons, Multiset.prod_cons,
      Multiset.map_cons, Multiset.prod_cons, C_mul]
    ring

/-- The characteristic roots of `charpolyRev` are the inverses of those of `charpoly`, when the
matrix is invertible.  Mathlib has no roots-of-`reverse` lemma; this supplies the case we need. -/
theorem roots_charpolyRev (hA : A.det ≠ 0) :
    A.charpolyRev.roots = A.charpoly.roots.map (fun x => x⁻¹) := by
  have hzero : (0 : K) ∉ A.charpoly.roots := by
    intro h0
    exact hA (by rw [Matrix.det_eq_prod_roots_charpoly]; exact Multiset.prod_eq_zero h0)
  have hfac : A.charpoly = (A.charpoly.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic
  have hCne : ((A.charpoly.roots.map fun a => -a).prod) ≠ 0 := by
    intro hcon
    rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at hcon
    obtain ⟨x, hx, hx0⟩ := hcon
    exact hzero (by simpa [neg_eq_zero.mp hx0] using hx)
  rw [← reverse_charpoly]
  conv_lhs => rw [hfac]
  rw [reverse_prod_X_sub_C _ hzero, Polynomial.roots_C_mul _ hCne,
    show (A.charpoly.roots.map fun a => X - C a⁻¹)
        = ((A.charpoly.roots.map fun x => x⁻¹).map fun a => X - C a) by
      rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-- **The root pairing.**  From `A * B = c • 1` with `c ≠ 0`, the characteristic roots of `B` are
the characteristic roots of `A` inverted and scaled by `c`, with multiplicity.  Over the classical
space this is [LWX, Prop 3.22]. -/
theorem roots_charpoly_of_mul_eq_smul (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n K)) :
    B.charpoly.roots = A.charpoly.roots.map (fun x => c / x) := by
  have hA : A.det ≠ 0 := det_ne_zero_of_mul_eq_smul hc h
  have hB : B.det ≠ 0 := by
    intro h0
    have hd := det_mul_det_of_mul_eq_smul h
    rw [h0, mul_zero] at hd
    exact pow_ne_zero _ hc hd.symm
  have hneg : ((-1 : K[X]) ^ Fintype.card n) = C ((-1 : K) ^ Fintype.card n) := by
    rw [map_pow, map_neg, map_one]
  have key : B.charpolyRev.roots = A.charpoly.roots.map (fun x => c⁻¹ * x) := by
    have h4 := congrArg Polynomial.roots (C_det_mul_charpolyRev_eq h)
    rw [Polynomial.roots_C_mul _ hA, hneg,
      Polynomial.roots_C_mul _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
      show (C c * X : K[X]) = C c * X + C 0 by simp,
      Polynomial.roots_comp_C_mul_X_add_C _ _ _ (isUnit_iff_ne_zero.mpr hc)] at h4
    rw [h4]
    refine Multiset.map_congr rfl fun x _ => ?_
    rw [Ring.inverse_eq_inv]
    ring
  rw [roots_charpolyRev hB] at key
  have hmap := congrArg (Multiset.map (fun x : K => x⁻¹)) key
  rw [Multiset.map_map, Multiset.map_map] at hmap
  simpa [Function.comp, mul_inv, div_eq_mul_inv, mul_comm] using hmap

end Field

end Matrix
