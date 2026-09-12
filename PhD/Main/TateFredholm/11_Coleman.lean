/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Instances.Matrix
import PhD.Main.ForMathlib.RingTheory.Polynomial.GaussNorm
import PhD.Main.TateFredholm.«10_Entire»
import PhD.Main.TateFredholm.«00_Resultant»

/-!
# Coleman's `D(B, P)` and the spectral mapping formula

[Bel] §II.2.4 ("A piece of resultant theory", following Coleman [Col97, §A3–A4]): for a
polynomial `B` and a polynomial `P = 1 − a₁T + ⋯ ± aₙTⁿ`, `D(B, P)(T) := ∏ᵢ (1 − T B(tᵢ))`
where the `tᵢ` are the roots of the reciprocal polynomial `P*`, computed universally through
the elementary symmetric functions.  Here `D(B, P)` is realised as a resultant in mathlib's
`Polynomial.resultant`:

  `dPoly B P N = Res_X (reflect N P, 1 − T·B(X))`,

which is Coleman's `Res(P*(X), 1 − TB(X))` ([Buz07] p. 21).  The section `Algebraic` proves
[Bel] Lemma II.2.13 from mathlib's resultant calculus; the section `Normed` extends `D` to
Fredholm series with bounded coefficients ("for `B` fixed, the coefficients of `D(B, P)`
are polynomials in the coefficients `aᵢ` of `P`; they are therefore continuous in `P`",
[Bel] p. 68) via a multilinearity estimate, proves entireness by Buzzard's rescaling trick
([Buz07] p. 21: "`Res(Q, P) = Res(u⁻ⁿQ(uT), P(uT))` … can be used to renormalise"), and
derives [Bel] Lemma II.2.14 / Proposition II.2.15; the section `SpectralMapping` proves
[Bel] Proposition II.2.16, `D(Q, det(1 − Tφ)) = det(1 − TQ(φ))`, first for matrices
(`Matrix.resultant_charpoly`) and then for compactoid operators by truncation.

## Main definitions

* `Coleman.dPoly B P N`: Coleman's `D(B, P)` for polynomials, as a resultant.
* `Coleman.bQ Q u`: Bellaïche's `1 − u⁻¹ Q*` for a polynomial `Q` with leading coefficient `u`.
* `Coleman.dSeries B F`: `D(B, F)` for a power series `F`, the coefficientwise limit of the
  `D(B, trunc F)`.

## Main results

* `Coleman.dPoly_mul`, `Coleman.dSeries_mul`: multiplicativity in the second argument.
* `Coleman.norm_coeff_dSeries_sub_le`, `PowerSeries.IsEntire.dSeries`: Lipschitz continuity and
  entireness of `D(B, ·)` on entire series.
* `Coleman.isUnit_evalT_one_dSeries_bQ_iff`: `D(1 − u⁻¹Q*, S)(1)` is a unit iff `Q` and `S` are
  relatively prime in `R{{T}}` ([Bel] Lemma II.2.14).
* `Coleman.isGoodZero_dSeries_bQ`: `D(1 − u⁻¹Q*, QS)` has a good zero of order `deg Q` at `1`
  ([Bel] Proposition II.2.15).
* `Coleman.charPowerSeries_aeval`: the spectral mapping formula
  `det(1 − T·B(φ)) = D(B, det(1 − Tφ))` for compactoid `φ` ([Bel] Proposition II.2.16).
-/

open Filter Topology Polynomial

noncomputable section

namespace TateFredholm

namespace Coleman

section Algebraic

variable {R : Type*} [CommRing R]

/-- The polynomial `1 − T·B(X)` in `(R[T])[X]`: the outer variable is `T`, the inner
(resultant) variable is `X`. -/
def gPoly (B : R[X]) : (R[X])[X] :=
  1 - Polynomial.C (Polynomial.X : R[X]) * B.map (Polynomial.C : R →+* R[X])

/-- **Coleman's `D(B, P)`** for a polynomial `P` of degree `≤ N`
([Bel] §II.2.4; [Buz07] p. 21 "`D(B,P) = Res(P*(X), 1 − TB(X))`"), as an element of `R[T]`. -/
def dPoly (B P : R[X]) (N : ℕ) : R[X] :=
  Polynomial.resultant ((Polynomial.reflect N P).map (Polynomial.C : R →+* R[X])) (gPoly B)
    N B.natDegree

/-- The normalised reciprocal `Q̃* = u⁻¹ Q*` of a polynomial with leading coefficient `u`
(so that `Q̃*(0) = 1`), and Bellaïche's `B = 1 − Q̃*` ([Bel] proof of Theorem II.2.18:
"`φ' = 1 − Q*(φ)/Q*(0)`"). -/
def bQ (Q : R[X]) (u : Rˣ) : R[X] := 1 - Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse

/-- `1 − u⁻¹Q*` has no constant term when `u` is the leading coefficient of `Q`. -/
theorem bQ_coeff_zero {Q : R[X]} {u : Rˣ} (hu : (u : R) = Q.leadingCoeff) :
    (bQ Q u).coeff 0 = 0 := by
  simp [bQ, coeff_zero_reverse, ← hu, Units.inv_mul]

/-- `deg (1 − u⁻¹Q*) = deg Q` when `Q(0) = 1`. -/
theorem natDegree_bQ {Q : R[X]} {u : Rˣ} (hQ0 : Q.coeff 0 = 1) (hu : (u : R) = Q.leadingCoeff)
    [Nontrivial R] : (bQ Q u).natDegree = Q.natDegree := by
  have hC : (Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse).natDegree = Q.natDegree := by
    rw [natDegree_C_mul_of_isUnit (u⁻¹).isUnit, reverse_natDegree,
      natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hQ0]; exact one_ne_zero)), Nat.sub_zero]
  rcases Nat.eq_zero_or_pos Q.natDegree with h0 | hpos
  · have hQ : Q = 1 := by rw [eq_C_of_natDegree_eq_zero h0, hQ0, C_1]
    subst hQ
    obtain rfl : u = 1 := Units.ext (by simpa using hu)
    simp only [bQ, inv_one, Units.val_one, map_one, one_mul]
    rw [← C_1, reverse_C, C_1, sub_self, natDegree_zero, natDegree_one]
  · rw [bQ, natDegree_sub_eq_right_of_natDegree_lt (by rw [natDegree_one, hC]; exact hpos), hC]

private theorem natDegree_gPoly_le (B : R[X]) : (gPoly B).natDegree ≤ B.natDegree :=
  (natDegree_sub_le _ _).trans
    (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_map_le))

private theorem gPoly_coeff_zero {B : R[X]} (hB0 : B.coeff 0 = 0) : (gPoly B).coeff 0 = 1 := by
  simp [gPoly, coeff_map, hB0]

private theorem natDegree_reflect_eq {P : R[X]} {N : ℕ} (hP : P.natDegree ≤ N)
    (h0 : P.coeff 0 ≠ 0) : (reflect N P).natDegree = N :=
  le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
      rw [coeff_reflect, revAt_eq_self_of_lt hi]
      exact coeff_eq_zero_of_natDegree_lt (hP.trans_lt hi))
    (le_natDegree_of_ne_zero (by rwa [coeff_reflect, revAt_le le_rfl, Nat.sub_self]))

private theorem reflect_succ_of_natDegree_le {P : R[X]} {N : ℕ} (hP : P.natDegree ≤ N) :
    reflect (N + 1) P = X * reflect N P := by
  ext i
  rcases i with _ | i
  · rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, coeff_X_mul_zero]
    exact coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hP)
  · rw [coeff_X_mul, coeff_reflect, coeff_reflect]
    rcases le_or_gt i N with hi | hi
    · rw [revAt_le (Nat.succ_le_succ hi), revAt_le hi, Nat.succ_sub_succ]
    · rw [revAt_eq_self_of_lt (Nat.succ_lt_succ hi), revAt_eq_self_of_lt hi,
        coeff_eq_zero_of_natDegree_lt (hP.trans_lt hi),
        coeff_eq_zero_of_natDegree_lt (hP.trans_lt (hi.trans i.lt_succ_self))]

private theorem natDegree_map_C_reflect {P : R[X]} {N : ℕ} (hP : P.natDegree ≤ N)
    (h0 : P.coeff 0 ≠ 0) : ((reflect N P).map (Polynomial.C : R →+* R[X])).natDegree = N := by
  rw [natDegree_map_eq_of_injective C_injective, natDegree_reflect_eq hP h0]

/-- `D(B, P)(0) = 1` for a Fredholm polynomial `P`. -/
theorem dPoly_coeff_zero (B P : R[X]) (N : ℕ) (hP0 : P.coeff 0 = 1) :
    (dPoly B P N).coeff 0 = 1 := by
  have hC : (evalRingHom (0 : R)).comp Polynomial.C = RingHom.id R := RingHom.ext fun r ↦ by simp
  rw [coeff_zero_eq_eval_zero, ← coe_evalRingHom, dPoly, ← resultant_map_map,
    Polynomial.map_map, hC, Polynomial.map_id]
  have hg : (gPoly B).map (evalRingHom (0 : R)) = 1 := by
    simp [gPoly, Polynomial.map_map, hC]
  rw [hg, resultant_one_right, coeff_reflect, revAt_le le_rfl, Nat.sub_self, hP0, one_pow]

private theorem natDegree_reflect_le_of_le {P : R[X]} {N : ℕ} (hP : P.natDegree ≤ N) :
    (reflect N P).natDegree ≤ N :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    rw [coeff_reflect, revAt_eq_self_of_lt hi]
    exact coeff_eq_zero_of_natDegree_lt (hP.trans_lt hi)

/-- Padding the degree parameter does not change `D(B, P)` when `B(0) = 0`
(`reflect (N+1) P = X · reflect N P` and `Res(X, 1 − TB) = 1`; the padding factors of
`resultant_add_left_deg` are the same on both sides). -/
theorem dPoly_succ (B P : R[X]) {N : ℕ} (hP : P.natDegree ≤ N) (hB0 : B.coeff 0 = 0) :
    dPoly B P (N + 1) = dPoly B P N := by
  nontriviality R
  set f : (R[X])[X] := (reflect N P).map Polynomial.C with hf
  have hfN : f.natDegree ≤ N := natDegree_map_le.trans (natDegree_reflect_le_of_le hP)
  rcases eq_or_ne f 0 with hf0 | hf0
  · rw [dPoly, dPoly, reflect_succ_of_natDegree_le hP, Polynomial.map_mul, Polynomial.map_X, ← hf,
      hf0, mul_zero, resultant_zero_left, resultant_zero_left]
    simp [gPoly_coeff_zero hB0]
  have hpadX := resultant_add_left_deg (X * f) (gPoly B) (f.natDegree + 1) B.natDegree
    (N - f.natDegree) (natDegree_mul_le.trans (by rw [natDegree_X]; omega))
  have hpad := resultant_add_left_deg f (gPoly B) f.natDegree B.natDegree (N - f.natDegree) le_rfl
  have key := resultant_mul_left (X : (R[X])[X]) f (gPoly B) B.natDegree (natDegree_gPoly_le B)
  rw [natDegree_X, add_comm 1 f.natDegree] at key
  rw [dPoly, dPoly, reflect_succ_of_natDegree_le hP, Polynomial.map_mul, Polynomial.map_X, ← hf,
    show N + 1 = f.natDegree + 1 + (N - f.natDegree) by omega, hpadX, key,
    ← pow_one (X : (R[X])[X]), resultant_X_pow_left _ _ _ (natDegree_gPoly_le B),
    gPoly_coeff_zero hB0, one_pow, one_mul, ← hpad, Nat.add_sub_cancel' hfN]

/-- **[Bel] Lemma II.2.13 (i)**, `D(B, PQ) = D(B, P) D(B, Q)` (multiplicativity of the
resultant in its first argument, `reflect_mul`). -/
theorem dPoly_mul (B P Q : R[X]) {N M : ℕ} (hP : P.natDegree ≤ N) (hQ : Q.natDegree ≤ M)
    (hP0 : IsUnit (P.coeff 0)) (hQ0 : IsUnit (Q.coeff 0)) :
    dPoly B (P * Q) (N + M) = dPoly B P N * dPoly B Q M := by
  nontriviality R
  have key := resultant_mul_left ((reflect N P).map Polynomial.C) ((reflect M Q).map Polynomial.C)
    (gPoly B) B.natDegree (natDegree_gPoly_le B)
  rw [natDegree_map_C_reflect hP hP0.ne_zero, natDegree_map_C_reflect hQ hQ0.ne_zero] at key
  rw [dPoly, dPoly, dPoly, reflect_mul P Q hP hQ, Polynomial.map_mul, key]

private theorem gPoly_coeff (B : R[X]) (k : ℕ) :
    (gPoly B).coeff k = (if k = 0 then 1 else 0) - X * Polynomial.C (B.coeff k) := by
  simp [gPoly, coeff_one, coeff_C_mul, coeff_map]

private theorem natDegree_comp_C_mul_X [Nontrivial R] (B : R[X]) (lam : Rˣ) :
    (B.comp (Polynomial.C (lam : R) * X)).natDegree = B.natDegree := by
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ by
    rw [comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt hn, zero_mul]) ?_
  rcases eq_or_ne B 0 with rfl | hB
  · simp
  · refine le_natDegree_of_ne_zero fun h ↦ hB (leadingCoeff_eq_zero.mp ?_)
    rw [comp_C_mul_X_coeff] at h
    exact (lam.isUnit.pow _).mul_left_eq_zero.mp h

/-- **Diagonal conjugation of the Sylvester matrix**: for a unit `λ`,
`D(B, P) = D(B(λX), P(λ⁻¹X))` — the row scaling `λⁱ` and column scaling `λ⁻ʲ` turn the
coefficients `pₖ` into `pₖλ⁻ᵏ` and `bₖ` into `bₖλᵏ` without changing the determinant. -/
theorem dPoly_eq_dPoly_comp (B P : R[X]) (N : ℕ) (lam : Rˣ) :
    dPoly B P N = dPoly (B.comp (Polynomial.C (lam : R) * X))
      (P.comp (Polynomial.C ((lam⁻¹ : Rˣ) : R) * X)) N := by
  nontriviality R
  set μ : R := ((lam⁻¹ : Rˣ) : R) with hμ
  have hlμ : (lam : R) * μ = 1 := lam.mul_inv
  rw [dPoly, dPoly, natDegree_comp_C_mul_X, Polynomial.resultant, Polynomial.resultant]
  set d := B.natDegree
  have hab : (∏ i : Fin (N + d), Polynomial.C (lam : R) ^ (i : ℕ)) *
      ∏ j : Fin (N + d), Polynomial.C μ ^ (j : ℕ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ ↦ by rw [← mul_pow, ← C_mul, hlμ, C_1, one_pow]
  have hconj : Matrix.diagonal (fun i : Fin (N + d) ↦ Polynomial.C (lam : R) ^ (i : ℕ)) *
      sylvester ((reflect N P).map (Polynomial.C : R →+* R[X])) (gPoly B) N d *
        Matrix.diagonal (fun j : Fin (N + d) ↦ Polynomial.C μ ^ (j : ℕ)) =
      sylvester ((reflect N (P.comp (Polynomial.C μ * X))).map (Polynomial.C : R →+* R[X]))
        (gPoly (B.comp (Polynomial.C (lam : R) * X))) N d := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_castAdd, Set.mem_Icc]
      split_ifs with hi
      · obtain ⟨hi1, -⟩ := hi
        have hpow : (lam : R) ^ (i : ℕ) * μ ^ (j₁ : ℕ) = (lam : R) ^ ((i : ℕ) - j₁) := by
          conv_lhs => rw [← Nat.sub_add_cancel hi1]
          rw [pow_add, mul_assoc, ← mul_pow, hlμ, one_pow, mul_one]
        rw [gPoly_coeff, gPoly_coeff, comp_C_mul_X_coeff, mul_comm, ← mul_assoc,
          mul_comm (Polynomial.C μ ^ _), ← C_pow, ← C_pow, ← C_mul, hpow]
        split_ifs with hk
        · rw [hk, pow_zero, C_1, one_mul, mul_one]
        · rw [zero_sub, zero_sub, mul_neg, C_mul, mul_comm (Polynomial.C (B.coeff _))]
          ring
      · simp
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_natAdd, Set.mem_Icc]
      split_ifs with hi
      · obtain ⟨hi1, hi2⟩ := hi
        have hpow : (lam : R) ^ (i : ℕ) * μ ^ (N + j₁) = μ ^ (N - ((i : ℕ) - j₁)) := by
          rw [show N + j₁ = (i : ℕ) + (N - ((i : ℕ) - j₁)) by omega, pow_add, ← mul_assoc,
            ← mul_pow, hlμ, one_pow, one_mul]
        rw [coeff_map, coeff_map, coeff_reflect, coeff_reflect, comp_C_mul_X_coeff,
          revAt_le (by omega : (i : ℕ) - j₁ ≤ N), mul_comm, ← mul_assoc,
          mul_comm (Polynomial.C μ ^ _), ← C_pow, ← C_pow, ← C_mul, hpow, ← C_mul, mul_comm]
      · simp
  rw [← hconj, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    mul_right_comm, hab, one_mul]

/-- **Scaling the roots** ([Buz07] p. 21: "`Res(Q, P) = Res(u⁻ⁿ Q(uT), P(uT))`"):
`D(B, P(λT)) = D(B(λX), P)` for a unit `λ` (`resultant_scaleRoots`). -/
theorem dPoly_comp_C_mul_X (B P : R[X]) (N : ℕ) (lam : Rˣ) :
    dPoly B (P.comp (Polynomial.C (lam : R) * X)) N =
      dPoly (B.comp (Polynomial.C (lam : R) * X)) P N := by
  rw [dPoly_eq_dPoly_comp B _ N lam]
  congr 2
  ext k
  rw [comp_C_mul_X_coeff, comp_C_mul_X_coeff, mul_assoc, ← mul_pow, lam.mul_inv, one_pow, mul_one]

/-- **Scaling `B`**: `D(λB, P)(T) = D(B, P)(λT)` (the ring homomorphism `T ↦ λT` commutes
with the resultant). -/
theorem dPoly_C_mul (B P : R[X]) (N : ℕ) (lam : Rˣ) :
    dPoly (Polynomial.C (lam : R) * B) P N = (dPoly B P N).comp (Polynomial.C (lam : R) * X) := by
  have hψC : (compRingHom (Polynomial.C (lam : R) * X)).comp Polynomial.C = Polynomial.C :=
    RingHom.ext fun r ↦ by simp
  have hF : ((reflect N P).map (Polynomial.C : R →+* R[X])).map
      (compRingHom (Polynomial.C (lam : R) * X)) =
        (reflect N P).map (Polynomial.C : R →+* R[X]) := by
    rw [Polynomial.map_map, hψC]
  have hG : (gPoly B).map (compRingHom (Polynomial.C (lam : R) * X)) =
      gPoly (Polynomial.C (lam : R) * B) := by
    rw [gPoly, gPoly, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C,
      Polynomial.map_map, hψC, coe_compRingHom_apply, X_comp, Polynomial.map_mul, map_C, C_mul]
    ring
  rw [dPoly, dPoly, natDegree_C_mul_of_isUnit lam.isUnit, ← coe_compRingHom_apply]
  -- `rw [← resultant_map_map]` would make the unifier compare `C lam` with a resultant
  refine Eq.trans ?_ (resultant_map_map _ _ _ _ _)
  rw [hF, hG]

private theorem reflect_reflect (N : ℕ) (P : R[X]) : reflect N (reflect N P) = P := by
  ext i
  rw [coeff_reflect, coeff_reflect, revAt_invol]

private theorem natDegree_reverse_eq [Nontrivial R] {Q : R[X]} (hQ0 : Q.coeff 0 = 1) :
    Q.reverse.natDegree = Q.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hQ0]; exact one_ne_zero)),
    Nat.sub_zero]

private theorem gPoly_bQ (Q : R[X]) (u : Rˣ) :
    gPoly (bQ Q u) = Polynomial.C (1 - X) +
      Q.reverse.map (Polynomial.C : R →+* R[X]) *
        Polynomial.C (X * Polynomial.C ((u⁻¹ : Rˣ) : R)) := by
  simp only [gPoly, bQ, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_sub,
    map_one, map_mul]
  ring

/-- **[Bel] Lemma II.2.13 (ii)**: `D(1 − Q̃*, Q)(T) = (1 − T)^{deg Q}`
(`Res(Q*, (1 − T) + T Q̃*) = Res(Q*, 1 − T)`). -/
theorem dPoly_bQ_self (Q : R[X]) (u : Rˣ) (hQ0 : Q.coeff 0 = 1) (hu : (u : R) = Q.leadingCoeff) :
    dPoly (bQ Q u) Q Q.natDegree = (1 - X) ^ Q.natDegree := by
  nontriviality R
  have hdeg : (Q.reverse.map (Polynomial.C : R →+* R[X])).natDegree ≤ Q.natDegree :=
    natDegree_map_le.trans (reverse_natDegree_le Q)
  rw [dPoly, natDegree_bQ hQ0 hu, gPoly_bQ, show reflect Q.natDegree Q = Q.reverse from rfl,
    resultant_add_mul_right _ _ _ _ _ (by rw [natDegree_C, zero_add]) hdeg, resultant_C_right,
    coeff_map,
    coeff_reverse, revAt_le le_rfl, Nat.sub_self, hQ0, C_1, one_pow, one_mul]

/-- Evaluation at `T = 1` turns `D(1 − Q̃*, P)` into a resultant against `Q̃*`:
`D(1 − Q̃*, P)(1) = Res(reflect N P, u⁻¹ Q*)`. -/
theorem eval_one_dPoly_bQ (Q P : R[X]) (u : Rˣ) (N : ℕ) (hQ0 : Q.coeff 0 = 1)
    (hu : (u : R) = Q.leadingCoeff) :
    (dPoly (bQ Q u) P N).eval 1 =
      Polynomial.resultant (Polynomial.reflect N P)
        (Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse) N Q.natDegree := by
  nontriviality R
  have hC : (evalRingHom (1 : R)).comp Polynomial.C = RingHom.id R := RingHom.ext fun r ↦ by simp
  have hg : (gPoly (bQ Q u)).map (evalRingHom (1 : R)) =
      Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse := by
    rw [gPoly, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, coe_evalRingHom,
      eval_X, C_1, one_mul, Polynomial.map_map, hC, Polynomial.map_id, bQ, sub_sub_cancel]
  have hf : ((reflect N P).map (Polynomial.C : R →+* R[X])).map (evalRingHom (1 : R)) =
      reflect N P := by
    rw [Polynomial.map_map, hC, Polynomial.map_id]
  -- `rw` is avoided below: matching `Polynomial.map` patterns against `gPoly (bQ Q u)` makes
  -- the unifier unfold `reflect`/`reverse` and time out.
  have e0 : (dPoly (bQ Q u) P N).eval 1 = (evalRingHom (1 : R)) (Polynomial.resultant
      ((reflect N P).map (Polynomial.C : R →+* R[X])) (gPoly (bQ Q u)) N (bQ Q u).natDegree) := by
    rw [← coe_evalRingHom, dPoly]
  have e1 : (evalRingHom (1 : R)) (Polynomial.resultant
      ((reflect N P).map (Polynomial.C : R →+* R[X])) (gPoly (bQ Q u)) N (bQ Q u).natDegree) =
      Polynomial.resultant (((reflect N P).map (Polynomial.C : R →+* R[X])).map (evalRingHom 1))
        ((gPoly (bQ Q u)).map (evalRingHom 1)) N (bQ Q u).natDegree :=
    (resultant_map_map _ _ _ _ _).symm
  have e2 : Polynomial.resultant (((reflect N P).map (Polynomial.C : R →+* R[X])).map
      (evalRingHom 1)) ((gPoly (bQ Q u)).map (evalRingHom 1)) N (bQ Q u).natDegree =
      Polynomial.resultant (reflect N P) ((gPoly (bQ Q u)).map (evalRingHom 1)) N
        (bQ Q u).natDegree :=
    congrArg (fun F' ↦ Polynomial.resultant F' ((gPoly (bQ Q u)).map (evalRingHom (1 : R))) N
      (bQ Q u).natDegree) hf
  have e3 : Polynomial.resultant (reflect N P) ((gPoly (bQ Q u)).map (evalRingHom 1)) N
      (bQ Q u).natDegree = Polynomial.resultant (reflect N P)
        (Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse) N (bQ Q u).natDegree :=
    congrArg (fun G' ↦ Polynomial.resultant (reflect N P) G' N (bQ Q u).natDegree) hg
  have e4 : Polynomial.resultant (reflect N P) (Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse) N
      (bQ Q u).natDegree = Polynomial.resultant (reflect N P)
        (Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse) N Q.natDegree :=
    congrArg (fun k ↦ Polynomial.resultant (reflect N P)
      (Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse) N k) (natDegree_bQ hQ0 hu)
  exact e0.trans (e1.trans (e2.trans (e3.trans e4)))

/-- **[Bel] Lemma II.2.13 (iii)**: `D(1 − Q̃*, P + CQ)(1) = D(1 − Q̃*, P)(1)`
(`resultant_add_mul_left` after `reflect_mul`). -/
theorem eval_one_dPoly_bQ_add_mul (Q P C' : R[X]) (u : Rˣ) {N : ℕ} (hQ0 : Q.coeff 0 = 1)
    (hu : (u : R) = Q.leadingCoeff) (hC : C'.natDegree + Q.natDegree ≤ N) :
    (dPoly (bQ Q u) (P + C' * Q) N).eval 1 = (dPoly (bQ Q u) P N).eval 1 := by
  rw [eval_one_dPoly_bQ _ _ _ _ hQ0 hu, eval_one_dPoly_bQ _ _ _ _ hQ0 hu]
  have hnN : Q.natDegree ≤ N := le_of_add_le_right hC
  have hmul : reflect N (C' * Q) = reflect (N - Q.natDegree) C' * Q.reverse := by
    have := reflect_mul C' Q (F := N - Q.natDegree) (G := Q.natDegree) (by omega) le_rfl
    rwa [Nat.sub_add_cancel hnN] at this
  have hrev : reflect (N - Q.natDegree) C' * Q.reverse =
      (Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse) *
        (Polynomial.C (u : R) * reflect (N - Q.natDegree) C') := by
    rw [mul_mul_mul_comm, ← C_mul, Units.inv_mul, C_1, one_mul, mul_comm]
  have hk : (Polynomial.C (u : R) * reflect (N - Q.natDegree) C').natDegree + Q.natDegree ≤ N := by
    have := (natDegree_C_mul_le (u : R) (reflect (N - Q.natDegree) C')).trans
      (natDegree_reflect_le_of_le (P := C') (N := N - Q.natDegree) (by omega))
    omega
  -- `rw [hrev]` is avoided: matching it against `C u⁻¹ * Q.reverse` makes the unifier unfold
  -- `reflect` and time out.
  rw [reflect_add, hmul]
  exact (congrArg (fun q ↦ Polynomial.resultant (reflect N P + q)
      (Polynomial.C ((u⁻¹ : Rˣ) : R) * Q.reverse) N Q.natDegree) hrev).trans
    (resultant_add_mul_left _ _ _ _ _ hk
      ((natDegree_C_mul_le _ _).trans (reverse_natDegree_le Q)))

private theorem isCoprime_X_of_isUnit_coeff_zero {f : R[X]} (hf : IsUnit (f.coeff 0)) :
    IsCoprime (X : R[X]) f := by
  obtain ⟨u, hu⟩ := hf
  have h : X * divX f + Polynomial.C (u : R) = f := by rw [hu]; exact X_mul_divX_add f
  have hC : Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.C (u : R) = 1 := by
    rw [← C_mul, Units.inv_mul, C_1]
  exact ⟨-Polynomial.C ((u⁻¹ : Rˣ) : R) * divX f, Polynomial.C ((u⁻¹ : Rˣ) : R), by
    linear_combination -(Polynomial.C ((u⁻¹ : Rˣ) : R)) * h + hC⟩

private theorem isCoprime_of_X_pow_eq_add {f g α β : R[X]} {M : ℕ} (hX : IsCoprime (X : R[X]) g)
    (h : X ^ M = α * f + β * g) : IsCoprime f g := by
  obtain ⟨c, d, hcd⟩ := hX.pow_left (m := M)
  exact ⟨c * α, c * β + d, by linear_combination hcd - c * h⟩

-- Reflection of a Bézout identity `a * f + b * g = 1` at a large degree `M`:
-- `X ^ M = reflect (M − F) a * reflect F f + reflect (M − G) b * reflect G g`.
private theorem X_pow_eq_reflect_add_reflect {a b f g : R[X]} (hab : a * f + b * g = 1) {F G : ℕ}
    (hf : f.natDegree ≤ F) (hg : g.natDegree ≤ G) :
    (X : R[X]) ^ (a.natDegree + b.natDegree + F + G) =
      reflect (a.natDegree + b.natDegree + G) a * reflect F f +
        reflect (a.natDegree + b.natDegree + F) b * reflect G g := by
  have h1 := reflect_mul a f (F := a.natDegree + b.natDegree + G) (G := F) (by omega) hf
  have h2 := reflect_mul b g (F := a.natDegree + b.natDegree + F) (G := G) (by omega) hg
  rw [← h1, ← h2, show a.natDegree + b.natDegree + G + F = a.natDegree + b.natDegree + F + G by
    omega, ← reflect_add, hab, ← C_1, reflect_C, C_1, one_mul]

/-- Reversal preserves coprimality against a polynomial with constant term `1` and unit
leading coefficient: `(reflect N P, Q*) = 1 ↔ (P, Q) = 1` in `R[T]`. -/
theorem isCoprime_reflect_reverse_iff (Q P : R[X]) {N : ℕ} (hQ0 : Q.coeff 0 = 1)
    (hu : IsUnit Q.leadingCoeff) (hP : P.natDegree ≤ N) :
    IsCoprime (Polynomial.reflect N P) Q.reverse ↔ IsCoprime P Q := by
  have hXQ : IsCoprime (X : R[X]) Q :=
    isCoprime_X_of_isUnit_coeff_zero (by rw [hQ0]; exact isUnit_one)
  have hXQr : IsCoprime (X : R[X]) Q.reverse :=
    isCoprime_X_of_isUnit_coeff_zero (by rwa [coeff_zero_reverse])
  constructor
  · rintro ⟨a, b, hab⟩
    have key := X_pow_eq_reflect_add_reflect hab (natDegree_reflect_le_of_le hP)
      (reverse_natDegree_le Q)
    rw [reflect_reflect, show reflect Q.natDegree Q.reverse = Q from reflect_reflect _ Q] at key
    exact isCoprime_of_X_pow_eq_add hXQ key
  · rintro ⟨a, b, hab⟩
    exact isCoprime_of_X_pow_eq_add hXQr (X_pow_eq_reflect_add_reflect hab hP le_rfl)

/-- **The unit criterion** (polynomial form of [Col97, Lemma A3.7], via mathlib's
`isUnit_resultant_iff_isCoprime` for the monic `Q*`): `D(1 − Q̃*, P)(1)` is a unit iff
`P` and `Q` are coprime in `R[T]`. -/
theorem isUnit_eval_one_dPoly_bQ_iff (Q P : R[X]) (u : Rˣ) {N : ℕ} (hQ0 : Q.coeff 0 = 1)
    (hu : (u : R) = Q.leadingCoeff) (hP : P.natDegree ≤ N) :
    IsUnit ((dPoly (bQ Q u) P N).eval 1) ↔ IsCoprime P Q := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨fun _ ↦ ⟨0, 0, Subsingleton.elim _ _⟩, fun _ ↦ isUnit_of_subsingleton _⟩
  have hunit : ∀ {x y : R}, IsUnit x → (IsUnit (x * y) ↔ IsUnit y) :=
    fun hx ↦ ⟨isUnit_of_mul_isUnit_right, hx.mul⟩
  have hmon : Q.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff,
      natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hQ0]; exact one_ne_zero)), hQ0]
  have hd : (reflect N P).natDegree ≤ N := natDegree_reflect_le_of_le hP
  have hpad := resultant_add_right_deg Q.reverse (reflect N P) Q.natDegree (reflect N P).natDegree
    (N - (reflect N P).natDegree) le_rfl
  rw [Nat.add_sub_cancel' hd] at hpad
  rw [eval_one_dPoly_bQ _ _ _ _ hQ0 hu, resultant_C_mul_right, hunit ((u⁻¹).isUnit.pow N),
    resultant_comm, hunit ((isUnit_one.neg).pow _), hpad, ← natDegree_reverse_eq hQ0,
    coeff_natDegree, hmon.leadingCoeff, one_pow, one_mul, isUnit_resultant_iff_isCoprime hmon,
    isCoprime_comm, isCoprime_reflect_reverse_iff Q P hQ0 (hu ▸ u.isUnit) hP]

/-- **Finite spectral mapping** ([Bel] Proposition II.2.16, matrix case; [Buz07] p. 21):
`det(1 − T·B(A)) = D(B, det(1 − TA))` for a square matrix `A` and `B(0) = 0`.  From
`Matrix.resultant_charpoly` and `Matrix.reverse_charpoly`. -/
theorem _root_.Matrix.charpolyRev_aeval {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (B : R[X]) :
    (Polynomial.aeval A B).charpolyRev = dPoly B A.charpolyRev (Fintype.card n) := by
  nontriviality R
  have h1 : reflect (Fintype.card n) A.charpolyRev = A.charpoly := by
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim,
      reflect_reflect]
  rw [dPoly, h1, ← Matrix.charpoly_map, Matrix.resultant_charpoly _ _ _ (natDegree_gPoly_le B),
    Matrix.charpolyRev, gPoly, map_sub, map_one, map_mul, aeval_C,
    ← RingHom.mapMatrix_apply Polynomial.C A,
    ← map_aeval_eq_aeval_map (Matrix.algebraMap_comp_eq_mapMatrix_comp Polynomial.C),
    RingHom.mapMatrix_apply, Algebra.algebraMap_eq_smul_one, smul_one_mul]

end Algebraic

section GaussNormDet

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

-- The hypotheses of the Gauss-norm API, with the instance paths fixed to `R`.
omit [IsUltrametricDist R] [NormOneClass R] in
private theorem nrm_zero : ‖(0 : R)‖ = 0 := norm_zero

omit [IsUltrametricDist R] [NormOneClass R] in
private theorem nrm_neg (a : R) : ‖-a‖ = ‖a‖ := norm_neg a

omit [NormOneClass R] in
private theorem isNonarchimedean_gaussNorm_norm {c : ℝ} (hc : 0 ≤ c) :
    IsNonarchimedean fun p : R[X] ↦ p.gaussNorm norm c :=
  isNonarchimedean_gaussNorm norm nrm_zero norm_nonneg IsUltrametricDist.isNonarchimedean_norm hc

omit [NormOneClass R] in
private theorem gaussNorm_mul_le' {c : ℝ} (hc : 0 ≤ c) (p q : R[X]) :
    (p * q).gaussNorm norm c ≤ p.gaussNorm norm c * q.gaussNorm norm c :=
  gaussNorm_mul_le norm nrm_zero norm_nonneg norm_mul_le IsUltrametricDist.isNonarchimedean_norm
    hc p q

omit [NormOneClass R] in
private theorem gaussNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → R[X]) {c M : ℝ} (hc : 0 ≤ c)
    (hM : 0 ≤ M) (h : ∀ i ∈ s, (f i).gaussNorm norm c ≤ M) :
    (∑ i ∈ s, f i).gaussNorm norm c ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hM
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isNonarchimedean_gaussNorm_norm hc _ _).trans (max_le (h a (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

private theorem gaussNorm_prod_le {ι : Type*} (s : Finset ι) (f : ι → R[X]) {c : ℝ} (hc : 0 ≤ c) :
    (∏ i ∈ s, f i).gaussNorm norm c ≤ ∏ i ∈ s, (f i).gaussNorm norm c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussNorm_one norm c nrm_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (gaussNorm_mul_le' hc _ _).trans
      (mul_le_mul_of_nonneg_left ih (gaussNorm_nonneg norm _ norm_nonneg hc))

omit [IsUltrametricDist R] in
private theorem gaussNorm_intCast_units_le (k : ℤˣ) {c : ℝ} :
    ((k : ℤ) : R[X]).gaussNorm norm c ≤ 1 := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · rw [Units.val_one, Int.cast_one, gaussNorm_one norm c nrm_zero, norm_one]
  · rw [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, gaussNorm_neg norm c _ nrm_neg,
      gaussNorm_one norm c nrm_zero, norm_one]

-- The Gauss norm of a determinant is at most the product of per-column bounds on the Gauss
-- norms of the entries (ultrametric Leibniz expansion).
private theorem gaussNorm_det_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R[X])
    {c : ℝ} (hc : 0 ≤ c) (b : n → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hM : ∀ i j, (M i j).gaussNorm norm c ≤ b j) : M.det.gaussNorm norm c ≤ ∏ j, b j := by
  rw [Matrix.det_apply']
  refine gaussNorm_sum_le _ _ hc (Finset.prod_nonneg fun j _ ↦ hb j) fun σ _ ↦ ?_
  refine (gaussNorm_mul_le' hc _ _).trans ?_
  calc _ ≤ 1 * ∏ j, (M (σ j) j).gaussNorm norm c :=
        mul_le_mul (gaussNorm_intCast_units_le _) (gaussNorm_prod_le _ _ hc)
          (gaussNorm_nonneg norm _ norm_nonneg hc) zero_le_one
    _ ≤ ∏ j, b j := by
        rw [one_mul]
        exact Finset.prod_le_prod (fun j _ ↦ gaussNorm_nonneg norm _ norm_nonneg hc)
          fun j _ ↦ hM _ j

end GaussNormDet

section Normed

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]

omit [CompleteSpace R] in
-- Every `X`-coefficient of `gPoly B = 1 − T·B(X)` has Gauss norm `≤ 1` at the radius `Cb⁻¹`.
private theorem gaussNorm_coeff_gPoly_le {B : R[X]} {Cb : ℝ} (hCb0 : 0 < Cb)
    (hB : ∀ k, ‖B.coeff k‖ ≤ Cb) (k : ℕ) : ((gPoly B).coeff k).gaussNorm norm Cb⁻¹ ≤ 1 := by
  rw [gPoly, coeff_sub, coeff_one, coeff_C_mul, coeff_map, sub_eq_add_neg]
  refine (isNonarchimedean_gaussNorm_norm (inv_nonneg.mpr hCb0.le) _ _).trans (max_le ?_ ?_)
  · dsimp only
    split_ifs
    · rw [gaussNorm_one norm _ nrm_zero, norm_one]
    · rw [gaussNorm_zero]; exact zero_le_one
  · dsimp only
    rw [gaussNorm_neg norm _ _ nrm_neg, mul_comm, C_mul_X_eq_monomial,
      gaussNorm_monomial norm _ nrm_zero, pow_one]
    exact (mul_inv_le_iff₀ hCb0).mpr (by rw [one_mul]; exact hB k)

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem gaussNorm_coeff_map_C_reflect_le {P : R[X]} {C : ℝ} (hP : ∀ k, ‖P.coeff k‖ ≤ C)
    (N k : ℕ) {ρ : ℝ} :
    (((reflect N P).map (Polynomial.C : R →+* R[X])).coeff k).gaussNorm norm ρ ≤ C := by
  rw [coeff_map, gaussNorm_C norm _ nrm_zero, coeff_reflect]
  exact hP _

omit [CompleteSpace R] in
-- The Gauss-norm bound on the Sylvester determinant behind `dPoly`: with `Cb⁻¹` as the radius in
-- `T`, the `N` columns of `gPoly B` are bounded by `1` and the `deg B` columns of `reflect N P`
-- by the coefficient bound `C`.
private theorem gaussNorm_dPoly_le (B P : R[X]) (N : ℕ) {C Cb : ℝ} (hC : 0 ≤ C) (hCb : 0 < Cb)
    (hP : ∀ k, ‖P.coeff k‖ ≤ C) (hB : ∀ k, ‖B.coeff k‖ ≤ Cb) :
    (dPoly B P N).gaussNorm norm Cb⁻¹ ≤ C ^ B.natDegree := by
  have hρ : 0 ≤ Cb⁻¹ := inv_nonneg.mpr hCb.le
  rw [dPoly, Polynomial.resultant]
  refine (gaussNorm_det_le _ hρ (fun j ↦ j.addCases (fun _ ↦ 1) fun _ ↦ C)
    (fun j ↦ by induction j using Fin.addCases <;> simp [hC]) fun i j ↦ ?_).trans_eq ?_
  · induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact gaussNorm_coeff_gPoly_le hCb hB _
      · rw [gaussNorm_zero]; exact zero_le_one
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact gaussNorm_coeff_map_C_reflect_le hP _ _
      · rw [gaussNorm_zero]; exact hC
  · rw [Fin.prod_univ_add]
    simp

omit [CompleteSpace R] in
/-- **Crude Gauss-norm bound**: if all coefficients of `P` are bounded by `C ≥ 1` and those
of `B` by `Cb ≥ 1`, then `‖coeff_j D(B, P)‖ ≤ C^{deg B} Cb^j`.  (Every term of the Sylvester
determinant is a product of `deg B` coefficients of `P` and of `deg B`-many entries `1` or
`−T bₖ`; read off with the Gauss norm at radius `Cb⁻¹`.) -/
theorem norm_coeff_dPoly_le (B P : R[X]) (N : ℕ) {C Cb : ℝ} (hC : 0 ≤ C) (hCb : 0 < Cb)
    (hP : ∀ k, ‖P.coeff k‖ ≤ C) (hB : ∀ k, ‖B.coeff k‖ ≤ Cb) (j : ℕ) :
    ‖(dPoly B P N).coeff j‖ ≤ C ^ B.natDegree * Cb ^ j := by
  have := (le_gaussNorm norm (dPoly B P N) nrm_zero norm_nonneg (inv_nonneg.mpr hCb.le) j).trans
    (gaussNorm_dPoly_le B P N hC hCb hP hB)
  rwa [inv_pow, mul_inv_le_iff₀ (pow_pos hCb j)] at this

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem sylvester_eq_add_sylvester_sub (F F' G : (R[X])[X]) (N d : ℕ) :
    sylvester F' G N d = sylvester F G N d + sylvester (F' - F) 0 N d := by
  ext i j
  induction j using Fin.addCases with
  | left j₁ =>
    simp only [sylvester, Matrix.add_apply, Matrix.of_apply, Fin.addCases_left, coeff_zero]
    split_ifs <;> simp
  | right j₁ =>
    simp only [sylvester, Matrix.add_apply, Matrix.of_apply, Fin.addCases_right, coeff_sub]
    split_ifs <;> simp

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem gaussNorm_coeff_sub_map_C_reflect_le {P P' : R[X]} {δ : ℝ}
    (hδ : ∀ k, ‖P'.coeff k - P.coeff k‖ ≤ δ) (N k : ℕ) {ρ : ℝ} :
    (((reflect N P').map (Polynomial.C : R →+* R[X]) -
      (reflect N P).map (Polynomial.C : R →+* R[X])).coeff k).gaussNorm norm ρ ≤ δ := by
  rw [coeff_sub, coeff_map, coeff_map, ← map_sub, gaussNorm_C norm _ nrm_zero, coeff_reflect,
    coeff_reflect]
  exact hδ _

omit [CompleteSpace R] in
-- The matrix whose columns are those of `sylvester (reflect N P) (gPoly B)` on `s` and those of
-- `sylvester (reflect N P' − reflect N P) 0` off `s`, when a `reflect`-column is off `s`: that
-- column of differences is bounded by `δ`, the other `reflect`-columns by `C`, the `gPoly`
-- columns by `1`.
private theorem gaussNorm_det_piecewise_le (B P P' : R[X]) (N : ℕ) {C Cb δ : ℝ} (hC : 0 ≤ C)
    (hCb : 0 < Cb) (hδ0 : 0 ≤ δ) (hP : ∀ k, ‖P.coeff k‖ ≤ C) (hB : ∀ k, ‖B.coeff k‖ ≤ Cb)
    (hδ : ∀ k, ‖P'.coeff k - P.coeff k‖ ≤ δ) (hδC : ∀ k, ‖P'.coeff k - P.coeff k‖ ≤ C)
    (s : Finset (Fin (N + B.natDegree))) {j₁ : Fin B.natDegree} (hj₁ : Fin.natAdd N j₁ ∉ s) :
    (Matrix.det (Matrix.of fun i j ↦ if j ∈ s then
        sylvester ((reflect N P).map (Polynomial.C : R →+* R[X])) (gPoly B) N B.natDegree i j
      else sylvester ((reflect N P').map (Polynomial.C : R →+* R[X]) -
        (reflect N P).map (Polynomial.C : R →+* R[X])) 0 N B.natDegree i j)).gaussNorm norm Cb⁻¹
      ≤ δ * C ^ (B.natDegree - 1) := by
  refine (gaussNorm_det_le _ (inv_nonneg.mpr hCb.le)
    (fun j ↦ j.addCases (fun _ ↦ 1) fun k ↦ if k = j₁ then δ else C) (fun j ↦ by
      induction j using Fin.addCases with
      | left _ => simp
      | right k => simp only [Fin.addCases_right]; split_ifs <;> assumption)
    fun i j ↦ ?_).trans_eq ?_
  · rw [Matrix.of_apply]
    induction j using Fin.addCases with
    | left k =>
      simp only [Fin.addCases_left]
      split_ifs
      · simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · exact gaussNorm_coeff_gPoly_le hCb hB _
        · rw [gaussNorm_zero]; exact zero_le_one
      · simp only [sylvester, Matrix.of_apply, Fin.addCases_left, coeff_zero]
        split_ifs <;> (rw [gaussNorm_zero]; exact zero_le_one)
    | right k =>
      simp only [Fin.addCases_right]
      split_ifs with hmem hk hk
      · exact absurd hmem (hk ▸ hj₁)
      · simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact gaussNorm_coeff_map_C_reflect_le hP _ _
        · rw [gaussNorm_zero]; exact hC
      · simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact gaussNorm_coeff_sub_map_C_reflect_le hδ _ _
        · rw [gaussNorm_zero]; exact hδ0
      · simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact gaussNorm_coeff_sub_map_C_reflect_le hδC _ _
        · rw [gaussNorm_zero]; exact hC
  · rw [Fin.prod_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Finset.prod_const_one, one_mul]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₁), if_pos rfl,
      Finset.prod_congr rfl fun k hk ↦ if_neg (Finset.ne_of_mem_erase hk), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

omit [CompleteSpace R] in
-- The Gauss-norm form of the multilinearity estimate: expand the Sylvester determinant of `P'`
-- as a sum over the subsets of columns kept from `P` (`MultilinearMap.map_add_univ`), and bound
-- every term other than the `P`-determinant by `δ · C^{deg B − 1}` (a missing `gPoly` column is
-- a zero column).
private theorem gaussNorm_dPoly_sub_le (B P P' : R[X]) (N : ℕ) {C Cb δ : ℝ} (hC : 0 ≤ C)
    (hCb : 0 < Cb) (hδ0 : 0 ≤ δ) (hP : ∀ k, ‖P.coeff k‖ ≤ C) (hP' : ∀ k, ‖P'.coeff k‖ ≤ C)
    (hB : ∀ k, ‖B.coeff k‖ ≤ Cb) (hδ : ∀ k, ‖P'.coeff k - P.coeff k‖ ≤ δ) :
    (dPoly B P' N - dPoly B P N).gaussNorm norm Cb⁻¹ ≤ δ * C ^ (B.natDegree - 1) := by
  classical
  have hRHS : 0 ≤ δ * C ^ (B.natDegree - 1) := mul_nonneg hδ0 (pow_nonneg hC _)
  have hδC : ∀ k, ‖P'.coeff k - P.coeff k‖ ≤ C := fun k ↦ by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (by rw [norm_neg]; exact max_le (hP' k) (hP k))
  set S := sylvester ((reflect N P).map (Polynomial.C : R →+* R[X])) (gPoly B) N B.natDegree
    with hS
  set D := sylvester ((reflect N P').map (Polynomial.C : R →+* R[X]) -
    (reflect N P).map (Polynomial.C : R →+* R[X])) 0 N B.natDegree with hD
  -- the rows of the transposes, as plain functions (so that `Finset.piecewise` type-checks)
  set S' : Fin (N + B.natDegree) → Fin (N + B.natDegree) → R[X] := fun i j ↦ S j i with hS'
  set D' : Fin (N + B.natDegree) → Fin (N + B.natDegree) → R[X] := fun i j ↦ D j i with hD'
  have hexp : (sylvester ((reflect N P').map (Polynomial.C : R →+* R[X])) (gPoly B) N
      B.natDegree).det =
        ∑ s : Finset (Fin (N + B.natDegree)), Matrix.det (Matrix.of (s.piecewise S' D')) := by
    rw [sylvester_eq_add_sylvester_sub, ← Matrix.det_transpose, Matrix.transpose_add]
    exact (Matrix.detRowAlternating (R := R[X])
      (n := Fin (N + B.natDegree))).toMultilinearMap.map_add_univ S' D'
  have huniv : Matrix.of (Finset.univ.piecewise S' D') = S.transpose := by
    ext i j
    simp [hS']
  have hpw : ∀ s : Finset (Fin (N + B.natDegree)), (Matrix.of (s.piecewise S' D')).transpose =
      Matrix.of fun i j ↦ if j ∈ s then S i j else D i j := fun s ↦ by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Finset.piecewise, hS', hD']
    split_ifs <;> rfl
  rw [dPoly, dPoly, Polynomial.resultant, Polynomial.resultant, hexp,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ Finset.univ), huniv, Matrix.det_transpose,
    add_sub_cancel_left]
  refine gaussNorm_sum_le _ _ (inv_nonneg.mpr hCb.le) hRHS fun s hs ↦ ?_
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ ∉ s := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact (Finset.mem_erase.mp hs).1 (Finset.eq_univ_iff_forall.mpr hall)
  rw [← Matrix.det_transpose, hpw]
  induction j₀ using Fin.addCases with
  | left j₁ =>
    rw [Matrix.det_eq_zero_of_column_eq_zero (Fin.castAdd _ j₁) fun i ↦ by
      rw [Matrix.of_apply, if_neg hj₀, hD]
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, coeff_zero]
      split_ifs <;> rfl]
    rw [gaussNorm_zero]
    exact hRHS
  | right j₁ => exact gaussNorm_det_piecewise_le B P P' N hC hCb hδ0 hP hB hδ hδC s hj₀

omit [CompleteSpace R] in
/-- **Multilinearity estimate** ("the coefficients of `D(B, P)` are polynomials in the
coefficients `aᵢ` of `P`, therefore continuous in `P`", [Bel] p. 68): changing the
coefficients of `P` by at most `δ` changes each coefficient of `D(B, P)` by at most
`δ · C^{deg B − 1} · Cb^j`. -/
theorem norm_coeff_dPoly_sub_le (B P P' : R[X]) (N : ℕ) {C Cb δ : ℝ} (hC : 0 ≤ C)
    (hCb : 0 < Cb) (hP : ∀ k, ‖P.coeff k‖ ≤ C) (hP' : ∀ k, ‖P'.coeff k‖ ≤ C)
    (hB : ∀ k, ‖B.coeff k‖ ≤ Cb) (hδ : ∀ k, ‖P.coeff k - P'.coeff k‖ ≤ δ) (j : ℕ) :
    ‖(dPoly B P N).coeff j - (dPoly B P' N).coeff j‖ ≤ δ * C ^ (B.natDegree - 1) * Cb ^ j := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  have hδ' : ∀ k, ‖P.coeff k - P'.coeff k‖ ≤ δ := hδ
  have := (le_gaussNorm norm (dPoly B P N - dPoly B P' N) nrm_zero norm_nonneg
    (inv_nonneg.mpr hCb.le) j).trans (gaussNorm_dPoly_sub_le B P' P N hC hCb hδ0 hP' hP hB hδ')
  rwa [coeff_sub, inv_pow, mul_inv_le_iff₀ (pow_pos hCb j)] at this

omit [CompleteSpace R] in
/-- **The entireness estimate** (Buzzard's renormalisation, [Buz07] p. 21): if
`‖aₖ‖ ≤ C‖ϖ‖^{mk}` for all `k`, then `‖coeff_j D(B, P)‖ ≤ C^{deg B} (‖ϖ‖^m Cb)^j`. -/
theorem norm_coeff_dPoly_le_pow (ϖ : PseudoUniformizer R) (m : ℕ) (B P : R[X])
    (N : ℕ) {C Cb : ℝ} (hC : 1 ≤ C) (hCb : 1 ≤ Cb) (hB : ∀ k, ‖B.coeff k‖ ≤ Cb)
    (hB0 : B.coeff 0 = 0) (hPk : ∀ k, ‖P.coeff k‖ ≤ C * ‖(ϖ : R)‖ ^ (m * k)) (j : ℕ) :
    ‖(dPoly B P N).coeff j‖ ≤ C ^ B.natDegree * (‖(ϖ : R)‖ ^ m * Cb) ^ j := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hϖ0 : 0 < ‖(ϖ : R)‖ := ϖ.norm_pos
  have hϖ1 : ‖(ϖ : R)‖ ≤ 1 := ϖ.norm_lt_one.le
  set lam : Rˣ := ϖ.unit ^ m with hlam
  have hlamR : (lam : R) = (ϖ : R) ^ m := by rw [hlam, Units.val_pow_eq_pow_val]
  rw [dPoly_eq_dPoly_comp B P N lam, ← natDegree_comp_C_mul_X B lam]
  refine norm_coeff_dPoly_le _ _ N (zero_le_one.trans hC)
    (mul_pos (pow_pos hϖ0 m) (zero_lt_one.trans_le hCb)) (fun k ↦ ?_) (fun k ↦ ?_) j
  · rw [comp_C_mul_X_coeff]
    have hmul := ϖ.isMultiplicative.norm_pow_mul (m * k) (P.coeff k * ((lam⁻¹ : Rˣ) : R) ^ k)
    rw [show (ϖ : R) ^ (m * k) * (P.coeff k * ((lam⁻¹ : Rˣ) : R) ^ k) = P.coeff k by
      rw [pow_mul, ← hlamR, mul_left_comm, ← mul_pow, lam.mul_inv, one_pow, mul_one]] at hmul
    have := hPk k
    rw [hmul, mul_comm C] at this
    exact le_of_mul_le_mul_left this (pow_pos hϖ0 _)
  · rw [comp_C_mul_X_coeff, hlamR, ← pow_mul, mul_comm (B.coeff k), ϖ.isMultiplicative.norm_pow_mul]
    rcases k with _ | k
    · rw [hB0, norm_zero, mul_zero]
      positivity
    · exact mul_le_mul (pow_le_pow_of_le_one hϖ0.le hϖ1 (Nat.le_mul_of_pos_right m k.succ_pos))
        (hB _) (norm_nonneg _) (pow_nonneg hϖ0.le m)

/-- **`D(B, F)` for a formal series** with bounded coefficients ([Bel] p. 68: "we define
`D(B, P) = limₙ D(B, Pₙ)` with `Pₙ` the polynomial `∑ᵢ₌₀ⁿ aᵢTⁱ`"): the coefficientwise limit
of `D(B, trunc (N+1) F)`. -/
def dSeries (B : R[X]) (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun j ↦
    limUnder atTop fun N ↦ (dPoly B (PowerSeries.trunc (N + 1) F) N).coeff j

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem exists_coeff_bound (B : R[X]) : ∃ Cb : ℝ, 1 ≤ Cb ∧ ∀ k, ‖B.coeff k‖ ≤ Cb :=
  ⟨1 + ∑ k ∈ Finset.range (B.natDegree + 1), ‖B.coeff k‖,
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), fun k ↦ by
      rcases le_or_gt k B.natDegree with hk | hk
      · exact le_add_of_nonneg_of_le zero_le_one (Finset.single_le_sum (fun _ _ ↦ norm_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
      · rw [coeff_eq_zero_of_natDegree_lt hk, norm_zero]
        positivity⟩

omit [CompleteSpace R] [NormOneClass R] in
private theorem norm_sum_le_of_forall_le {ι : Type*} (s : Finset ι) (f : ι → R) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ s, ‖f i‖ ≤ M) : ‖∑ i ∈ s, f i‖ ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hM
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

omit [CompleteSpace R] [NormOneClass R] in
-- Ultrametric Cauchy criterion: successive differences tending to `0` suffice.
private theorem cauchySeq_of_norm_sub_succ_le {u : ℕ → R} {b : ℕ → ℝ}
    (hb : ∀ k, ‖u (k + 1) - u k‖ ≤ b k) (h0 : Tendsto b atTop (𝓝 0)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h0 (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, show u n - u N = ∑ i ∈ Finset.range (n - N), (u (N + (i + 1)) - u (N + i)) by
    rw [Finset.sum_range_sub (fun i ↦ u (N + i)), Nat.add_sub_cancel' hn, add_zero]]
  refine (norm_sum_le_of_forall_le _ _ (half_pos hε).le fun i _ ↦
    (hb _).trans ?_).trans_lt (half_lt_self hε)
  have := hN (N + i) (Nat.le_add_right _ _)
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem exists_norm_coeff_mul_pow_le {F : PowerSeries R} (hF : PowerSeries.IsEntire F)
    {c : ℝ} (hc : 0 < c) : ∃ C : ℝ, 1 ≤ C ∧ ∀ k, ‖PowerSeries.coeff k F‖ * c ^ k ≤ C := by
  obtain ⟨M, hM⟩ := ((PowerSeries.isRestricted_iff' c F).mp (hF c hc)).bddAbove_range
  exact ⟨max 1 M, le_max_left _ _, fun k ↦ (hM ⟨k, rfl⟩).trans (le_max_right _ _)⟩

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem norm_coeff_trunc_le {F : PowerSeries R} {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hF : ∀ k, ‖PowerSeries.coeff k F‖ ≤ b k) (n k : ℕ) :
    ‖(PowerSeries.trunc n F).coeff k‖ ≤ b k := by
  rw [PowerSeries.coeff_trunc]
  split_ifs
  · exact hF k
  · rw [norm_zero]
    exact hb k

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem isUnit_coeff_zero_trunc {F : PowerSeries R} (hF0 : PowerSeries.coeff 0 F = 1)
    (n : ℕ) : IsUnit ((PowerSeries.trunc (n + 1) F).coeff 0) := by
  rw [PowerSeries.coeff_trunc, if_pos (Nat.succ_pos n), hF0]
  exact isUnit_one

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem dPoly_eq_of_le (B P : R[X]) {N M : ℕ} (hP : P.natDegree ≤ N)
    (hB0 : B.coeff 0 = 0) (hNM : N ≤ M) : dPoly B P M = dPoly B P N :=
  Nat.le_induction rfl (fun _ hNM ih ↦ (dPoly_succ B P (hP.trans hNM) hB0).trans ih) M hNM

/-- The truncations' `D`'s converge coefficientwise (Cauchy by `norm_coeff_dPoly_sub_le`,
since the coefficients of `F` tend to `0`). -/
theorem tendsto_coeff_dPoly_trunc (B : R[X]) {F : PowerSeries R} {C : ℝ} (hC : 1 ≤ C)
    (hFb : ∀ k, ‖PowerSeries.coeff k F‖ ≤ C)
    (hFt : Tendsto (fun k ↦ ‖PowerSeries.coeff k F‖) atTop (𝓝 0)) (hB0 : B.coeff 0 = 0)
    (j : ℕ) :
    Tendsto (fun N ↦ (dPoly B (PowerSeries.trunc (N + 1) F) N).coeff j) atTop
      (𝓝 (PowerSeries.coeff j (dSeries B F))) := by
  obtain ⟨Cb, hCb, hB⟩ := exists_coeff_bound B
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hsucc : ∀ N, ‖(dPoly B (PowerSeries.trunc (N + 1 + 1) F) (N + 1)).coeff j -
      (dPoly B (PowerSeries.trunc (N + 1) F) N).coeff j‖ ≤
        ‖PowerSeries.coeff (N + 1) F‖ * C ^ (B.natDegree - 1) * Cb ^ j := fun N ↦ by
    rw [← dPoly_succ B _ (Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt F N)) hB0]
    refine norm_coeff_dPoly_sub_le B _ _ (N + 1) hC0 (zero_lt_one.trans_le hCb)
      (norm_coeff_trunc_le (fun _ ↦ hC0) hFb _) (norm_coeff_trunc_le (fun _ ↦ hC0) hFb _) hB
      (fun k ↦ ?_) j
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    split_ifs with h1 h2 h2
    · rw [sub_self, norm_zero]; exact norm_nonneg _
    · rw [sub_zero, show k = N + 1 by omega]
    · omega
    · rw [sub_zero, norm_zero]; exact norm_nonneg _
  have hcauchy : CauchySeq fun N ↦ (dPoly B (PowerSeries.trunc (N + 1) F) N).coeff j :=
    cauchySeq_of_norm_sub_succ_le hsucc (by
      simpa [mul_assoc] using
        (hFt.comp (tendsto_add_atTop_nat 1)).mul_const (C ^ (B.natDegree - 1) * Cb ^ j))
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : PowerSeries.coeff j (dSeries B F) = x := by
    rw [dSeries, PowerSeries.coeff_mk]
    exact hx.limUnder_eq
  rw [hlim]
  exact hx

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
/-- On polynomials, `dSeries` is `dPoly` (stability `dPoly_succ`). -/
theorem dSeries_coe (B P : R[X]) {N : ℕ} (hP : P.natDegree ≤ N) (hB0 : B.coeff 0 = 0) :
    dSeries B (P : PowerSeries R) = (dPoly B P N : PowerSeries R) := by
  ext j
  rw [dSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe]
  refine Filter.Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop N] with M hM
  rw [PowerSeries.trunc_coe_eq_self (Nat.lt_succ_of_le (hP.trans hM)),
    dPoly_eq_of_le B P hP hB0 hM]

/-- Lipschitz continuity of `dSeries` in the coefficient sup-norm, on series with
coefficients bounded by `C` and tending to `0`. -/
theorem norm_coeff_dSeries_sub_le (B : R[X]) {F F' : PowerSeries R} {C Cb δ : ℝ} (hC : 1 ≤ C)
    (hCb : 1 ≤ Cb) (hB : ∀ k, ‖B.coeff k‖ ≤ Cb) (hB0 : B.coeff 0 = 0)
    (hFb : ∀ k, ‖PowerSeries.coeff k F‖ ≤ C) (hF'b : ∀ k, ‖PowerSeries.coeff k F'‖ ≤ C)
    (hFt : Tendsto (fun k ↦ ‖PowerSeries.coeff k F‖) atTop (𝓝 0))
    (hF't : Tendsto (fun k ↦ ‖PowerSeries.coeff k F'‖) atTop (𝓝 0))
    (hδ : ∀ k, ‖PowerSeries.coeff k F - PowerSeries.coeff k F'‖ ≤ δ) (j : ℕ) :
    ‖PowerSeries.coeff j (dSeries B F) - PowerSeries.coeff j (dSeries B F')‖ ≤
      δ * C ^ (B.natDegree - 1) * Cb ^ j := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine le_of_tendsto ((tendsto_coeff_dPoly_trunc B hC hFb hFt hB0 j).sub
    (tendsto_coeff_dPoly_trunc B hC hF'b hF't hB0 j)).norm
    (Filter.Eventually.of_forall fun N ↦ ?_)
  refine norm_coeff_dPoly_sub_le B _ _ N hC0 (zero_lt_one.trans_le hCb)
    (norm_coeff_trunc_le (fun _ ↦ hC0) hFb _) (norm_coeff_trunc_le (fun _ ↦ hC0) hF'b _) hB
    (fun k ↦ ?_) j
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  split_ifs
  · exact hδ k
  · rw [sub_zero, norm_zero]
    exact (norm_nonneg _).trans (hδ 0)

omit [IsUltrametricDist R] [CompleteSpace R] in
private theorem exists_pow_bound [IsTate R] {F : PowerSeries R} (hF : PowerSeries.IsEntire F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ϖ : PseudoUniformizer R) (m : ℕ) (Cm : ℝ), 1 ≤ Cm ∧ ‖(ϖ : R)‖ ^ m < ε ∧
      ∀ k, ‖PowerSeries.coeff k F‖ ≤ Cm * ‖(ϖ : R)‖ ^ (m * k) := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨ϖ⟩ := IsTate.nonempty_pseudoUniformizer (A := R)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε ϖ.norm_lt_one
  obtain ⟨Cm, hCm1, hCm⟩ := exists_norm_coeff_mul_pow_le hF (inv_pos.mpr (pow_pos ϖ.norm_pos m))
  refine ⟨ϖ, m, Cm, hCm1, hm, fun k ↦ ?_⟩
  have := hCm k
  rwa [inv_pow, ← pow_mul, mul_inv_le_iff₀ (pow_pos ϖ.norm_pos _)] at this

/-- `D(B, F)` is entire for entire `F` ([Bel] p. 68: "check that the formal series
`D(B, P)` belongs to `R{{T}}`"), by `norm_coeff_dPoly_le_pow` uniformly in the truncations. -/
theorem _root_.PowerSeries.IsEntire.dSeries [IsTate R] (B : R[X]) {F : PowerSeries R}
    (hF : PowerSeries.IsEntire F) (hB0 : B.coeff 0 = 0) :
    PowerSeries.IsEntire (Coleman.dSeries B F) := by
  intro c hc
  rw [PowerSeries.isRestricted_iff']
  obtain ⟨Cb, hCb, hB⟩ := exists_coeff_bound B
  have hCbc : 0 < Cb * c := mul_pos (zero_lt_one.trans_le hCb) hc
  obtain ⟨ϖ, m, Cm, hCm1, hm, hPk⟩ := exists_pow_bound hF (inv_pos.mpr hCbc)
  obtain ⟨C1, hC11, hC1⟩ := exists_norm_coeff_mul_pow_le hF one_pos
  have hbound : ∀ j, ‖PowerSeries.coeff j (Coleman.dSeries B F)‖ ≤
      Cm ^ B.natDegree * (‖(ϖ : R)‖ ^ m * Cb) ^ j := fun j ↦
    le_of_tendsto (tendsto_coeff_dPoly_trunc B hC11 (fun k ↦ by simpa using hC1 k)
      (by simpa using hF.tendsto_norm_coeff_mul_pow 1) hB0 j).norm
      (Filter.Eventually.of_forall fun N ↦ norm_coeff_dPoly_le_pow ϖ m B _ N hCm1 hCb hB hB0
        (norm_coeff_trunc_le (fun k ↦ by positivity) hPk _) j)
  have hr1 : ‖(ϖ : R)‖ ^ m * Cb * c < 1 := by
    rw [mul_assoc]
    exact (mul_lt_mul_of_pos_right hm hCbc).trans_eq (inv_mul_cancel₀ hCbc.ne')
  have hlim : Tendsto (fun j ↦ Cm ^ B.natDegree * (‖(ϖ : R)‖ ^ m * Cb * c) ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr1).const_mul
      (Cm ^ B.natDegree)
  refine squeeze_zero (fun j ↦ by positivity) (fun j ↦ ?_) hlim
  calc ‖PowerSeries.coeff j (Coleman.dSeries B F)‖ * c ^ j
      ≤ Cm ^ B.natDegree * (‖(ϖ : R)‖ ^ m * Cb) ^ j * c ^ j :=
        mul_le_mul_of_nonneg_right (hbound j) (pow_nonneg hc.le j)
    _ = Cm ^ B.natDegree * (‖(ϖ : R)‖ ^ m * Cb * c) ^ j := by ring

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem exists_norm_coeff_le_half_pow {F : PowerSeries R} (hF : PowerSeries.IsEntire F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k, ‖PowerSeries.coeff k F‖ ≤ C * (1 / 2) ^ k := by
  obtain ⟨C, hC1, hC⟩ := exists_norm_coeff_mul_pow_le hF two_pos
  refine ⟨C, hC1, fun k ↦ ?_⟩
  have := hC k
  rwa [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos two_pos k)]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem norm_coeff_le_of_le_half_pow {H : PowerSeries R} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ k, ‖PowerSeries.coeff k H‖ ≤ K * (1 / 2) ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k H‖ ≤ K :=
  (h k).trans (mul_le_of_le_one_right hK (pow_le_one₀ (by norm_num) (by norm_num)))

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem tendsto_norm_coeff_of_le_half_pow {H : PowerSeries R} {K : ℝ}
    (h : ∀ k, ‖PowerSeries.coeff k H‖ ≤ K * (1 / 2) ^ k) :
    Tendsto (fun k ↦ ‖PowerSeries.coeff k H‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ norm_nonneg _) h (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul K)

omit [CompleteSpace R] [NormOneClass R] in
private theorem norm_coeff_mul_le_half_pow {P Q : PowerSeries R} {CP CQ : ℝ} (hCP : 0 ≤ CP)
    (hCQ : 0 ≤ CQ) (hP : ∀ k, ‖PowerSeries.coeff k P‖ ≤ CP * (1 / 2) ^ k)
    (hQ : ∀ k, ‖PowerSeries.coeff k Q‖ ≤ CQ * (1 / 2) ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (P * Q)‖ ≤ CP * CQ * (1 / 2) ^ k := by
  rw [PowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le _ _ (by positivity) fun ij hij ↦ ?_
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  calc ‖PowerSeries.coeff ij.1 P * PowerSeries.coeff ij.2 Q‖
      ≤ CP * (1 / 2) ^ ij.1 * (CQ * (1 / 2) ^ ij.2) := norm_mul_le_of_le (hP _) (hQ _)
    _ = CP * CQ * ((1 / 2) ^ ij.1 * (1 / 2) ^ ij.2) := by ring

omit [CompleteSpace R] [NormOneClass R] in
private theorem norm_coeff_mul_sub_trunc_le {F G : PowerSeries R} {C : ℝ} {N : ℕ}
    (hFG : ∀ k, ‖PowerSeries.coeff k (F * G)‖ ≤ C * (1 / 2) ^ k)
    (hPQ : ∀ k, ‖PowerSeries.coeff k ((PowerSeries.trunc (N + 1) F *
      PowerSeries.trunc (N + 1) G : R[X]) : PowerSeries R)‖ ≤ C * (1 / 2) ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (F * G) - PowerSeries.coeff k ((PowerSeries.trunc (N + 1) F *
      PowerSeries.trunc (N + 1) G : R[X]) : PowerSeries R)‖ ≤ C * (1 / 2) ^ N := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hFG 0)
  rcases le_or_gt k N with hk | hk
  · rw [Polynomial.coe_mul, ← PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc₂ F G
      (Nat.lt_succ_of_le hk) (Nat.lt_succ_of_le hk), sub_self, norm_zero]
    positivity
  · have hpow : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk.le
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((hFG k).trans (mul_le_mul_of_nonneg_left hpow hC)) ?_)
    rw [norm_neg]
    exact (hPQ k).trans (mul_le_mul_of_nonneg_left hpow hC)

/-- **[Bel] Lemma II.2.14 (i)** for entire series: `D(B, FG) = D(B, F) D(B, G)`
(passage to the limit in `dPoly_mul`). -/
theorem dSeries_mul (B : R[X]) {F G : PowerSeries R} (hF : PowerSeries.IsEntire F)
    (hG : PowerSeries.IsEntire G) (hF0 : PowerSeries.coeff 0 F = 1)
    (hG0 : PowerSeries.coeff 0 G = 1) (hB0 : B.coeff 0 = 0) :
    dSeries B (F * G) = dSeries B F * dSeries B G := by
  obtain ⟨Cb, hCb, hB⟩ := exists_coeff_bound B
  obtain ⟨CF, hCF1, hF2⟩ := exists_norm_coeff_le_half_pow hF
  obtain ⟨CG, hCG1, hG2⟩ := exists_norm_coeff_le_half_pow hG
  have hCF0 : 0 ≤ CF := zero_le_one.trans hCF1
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG1
  have hFtr : ∀ N k, ‖PowerSeries.coeff k (PowerSeries.trunc (N + 1) F : PowerSeries R)‖ ≤
      CF * (1 / 2) ^ k := fun N k ↦ by
    rw [Polynomial.coeff_coe]
    exact norm_coeff_trunc_le (fun k ↦ by positivity) hF2 _ k
  have hGtr : ∀ N k, ‖PowerSeries.coeff k (PowerSeries.trunc (N + 1) G : PowerSeries R)‖ ≤
      CG * (1 / 2) ^ k := fun N k ↦ by
    rw [Polynomial.coeff_coe]
    exact norm_coeff_trunc_le (fun k ↦ by positivity) hG2 _ k
  have hFG2 := norm_coeff_mul_le_half_pow hCF0 hCG0 hF2 hG2
  have hPQ2 : ∀ N k, ‖PowerSeries.coeff k ((PowerSeries.trunc (N + 1) F *
      PowerSeries.trunc (N + 1) G : R[X]) : PowerSeries R)‖ ≤ CF * CG * (1 / 2) ^ k := fun N k ↦ by
    rw [Polynomial.coe_mul]
    exact norm_coeff_mul_le_half_pow hCF0 hCG0 (hFtr N) (hGtr N) k
  ext j
  have h1 : Tendsto (fun N ↦ PowerSeries.coeff j (dSeries B ((PowerSeries.trunc (N + 1) F *
      PowerSeries.trunc (N + 1) G : R[X]) : PowerSeries R))) atTop
      (𝓝 (PowerSeries.coeff j (dSeries B (F * G)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun N : ℕ ↦ CF * CG * (1 / 2) ^ N * (CF * CG) ^ (B.natDegree - 1) * Cb ^ j)
        atTop (𝓝 0) := by
      simpa [mul_assoc] using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul
          (CF * CG)).mul_const (((CF * CG) ^ (B.natDegree - 1)) * Cb ^ j)
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) hlim
    rw [norm_sub_rev]
    exact norm_coeff_dSeries_sub_le B (one_le_mul_of_one_le_of_one_le hCF1 hCG1) hCb hB hB0
      (norm_coeff_le_of_le_half_pow (by positivity) hFG2)
      (norm_coeff_le_of_le_half_pow (by positivity) (hPQ2 N))
      (tendsto_norm_coeff_of_le_half_pow hFG2) (tendsto_norm_coeff_of_le_half_pow (hPQ2 N))
      (norm_coeff_mul_sub_trunc_le hFG2 (hPQ2 N)) j
  have h2 : Tendsto (fun N ↦ PowerSeries.coeff j (dSeries B ((PowerSeries.trunc (N + 1) F *
      PowerSeries.trunc (N + 1) G : R[X]) : PowerSeries R))) atTop
      (𝓝 (PowerSeries.coeff j (dSeries B F * dSeries B G))) := by
    have hdegP : ∀ N, (PowerSeries.trunc (N + 1) F).natDegree ≤ N := fun N ↦
      Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt F N)
    have hdegQ : ∀ N, (PowerSeries.trunc (N + 1) G).natDegree ≤ N := fun N ↦
      Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt G N)
    have heq : ∀ N, PowerSeries.coeff j (dSeries B ((PowerSeries.trunc (N + 1) F *
        PowerSeries.trunc (N + 1) G : R[X]) : PowerSeries R)) =
        ∑ ab ∈ Finset.antidiagonal j, (dPoly B (PowerSeries.trunc (N + 1) F) N).coeff ab.1 *
          (dPoly B (PowerSeries.trunc (N + 1) G) N).coeff ab.2 := fun N ↦ by
      rw [dSeries_coe B _ (natDegree_mul_le.trans (add_le_add (hdegP N) (hdegQ N))) hB0,
        Polynomial.coeff_coe, dPoly_mul B _ _ (hdegP N) (hdegQ N) (isUnit_coeff_zero_trunc hF0 N)
          (isUnit_coeff_zero_trunc hG0 N), Polynomial.coeff_mul]
    simp_rw [heq, PowerSeries.coeff_mul]
    refine tendsto_finsetSum _ fun ab _ ↦ Tendsto.mul ?_ ?_
    · exact tendsto_coeff_dPoly_trunc B hCF1 (norm_coeff_le_of_le_half_pow hCF0 hF2)
        (tendsto_norm_coeff_of_le_half_pow hF2) hB0 ab.1
    · exact tendsto_coeff_dPoly_trunc B hCG1 (norm_coeff_le_of_le_half_pow hCG0 hG2)
        (tendsto_norm_coeff_of_le_half_pow hG2) hB0 ab.2
  exact tendsto_nhds_unique h1 h2

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
private theorem eval_one_eq_tsum (p : R[X]) : p.eval 1 = ∑' j, p.coeff j := by
  rw [eval_eq_sum_range, tsum_eq_sum (s := Finset.range (p.natDegree + 1)) fun j hj ↦
    coeff_eq_zero_of_natDegree_lt (by rw [Finset.mem_range, not_lt] at hj; omega)]
  simp

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
/-- `P ↦ D(B, P)_N(1)` is continuous in the coefficients of `P` (it is the determinant of a
matrix whose entries are coefficients of `P` or constants). -/
theorem tendsto_eval_one_dPoly (B : R[X]) (N : ℕ) {P : ℕ → R[X]} {P' : R[X]}
    (hP : ∀ k, Tendsto (fun t ↦ (P t).coeff k) atTop (𝓝 (P'.coeff k))) :
    Tendsto (fun t ↦ (dPoly B (P t) N).eval 1) atTop (𝓝 ((dPoly B P' N).eval 1)) := by
  have key : ∀ Q : R[X], (dPoly B Q N).eval 1 =
      ((sylvester ((reflect N Q).map Polynomial.C) (gPoly B) N B.natDegree).map
        (evalRingHom (1 : R))).det := fun Q ↦ by
    change (evalRingHom (1 : R)) _ = _
    rw [dPoly, resultant, RingHom.map_det, RingHom.mapMatrix_apply]
  simp only [key]
  refine ((Continuous.matrix_det continuous_id).tendsto _).comp
    (tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦ ?_)
  induction j using Fin.addCases with
  | left j₁ =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    exact tendsto_const_nhds
  | right j₁ =>
    by_cases h : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + N)
    · simp only [sylvester, Matrix.of_apply, Fin.addCases_right, if_pos h, coeff_map,
        coeff_reflect, coe_evalRingHom, eval_C]
      exact hP _
    · simp only [sylvester, Matrix.of_apply, Fin.addCases_right, if_neg h, map_zero]
      exact tendsto_const_nhds

/-- The evaluations at `T = 1` of the truncations' `D`'s converge to `D(B, F)(1)` (dominated
convergence, with the uniform entireness bound `norm_coeff_dPoly_le_pow`). -/
theorem tendsto_eval_one_dPoly_trunc [IsTate R] (B : R[X]) {F : PowerSeries R}
    (hF : PowerSeries.IsEntire F) (hB0 : B.coeff 0 = 0) :
    Tendsto (fun N ↦ (dPoly B (PowerSeries.trunc (N + 1) F) N).eval 1) atTop
      (𝓝 (PowerSeries.evalT 1 (dSeries B F))) := by
  obtain ⟨Cb, hCb, hB⟩ := exists_coeff_bound B
  have hCb0 : 0 < Cb := zero_lt_one.trans_le hCb
  obtain ⟨ϖ, m, Cm, hCm1, hm, hPk⟩ := exists_pow_bound hF (inv_pos.mpr hCb0)
  obtain ⟨C1, hC11, hC1⟩ := exists_norm_coeff_mul_pow_le hF one_pos
  have hr1 : ‖(ϖ : R)‖ ^ m * Cb < 1 :=
    (mul_lt_mul_of_pos_right hm hCb0).trans_eq (inv_mul_cancel₀ hCb0.ne')
  simp only [eval_one_eq_tsum, PowerSeries.evalT, one_pow, mul_one]
  exact tendsto_tsum_of_dominated_convergence
    (f := fun N j ↦ (dPoly B (PowerSeries.trunc (N + 1) F) N).coeff j)
    ((summable_geometric_of_lt_one (by positivity) hr1).mul_left (Cm ^ B.natDegree))
    (fun j ↦ tendsto_coeff_dPoly_trunc B hC11 (fun k ↦ by simpa using hC1 k)
      (by simpa using hF.tendsto_norm_coeff_mul_pow 1) hB0 j)
    (Filter.Eventually.of_forall fun N j ↦ norm_coeff_dPoly_le_pow ϖ m B _ N hCm1 hCb hB hB0
      (norm_coeff_trunc_le (fun k ↦ by positivity) hPk _) j)

omit [CompleteSpace R] in
private theorem tendsto_coeff_modByMonic_trunc {Q : R[X]} (hQ : Q.Monic) {S q : PowerSeries R}
    {r : R[X]} (hS : PowerSeries.IsEntire S) (hq : PowerSeries.IsEntire q)
    (hr : r.degree < Q.degree) (hSr : S = (Q : PowerSeries R) * q + r) (k : ℕ) :
    Tendsto (fun N ↦ (PowerSeries.trunc (N + 1) S %ₘ Q).coeff k) atTop (𝓝 (r.coeff k)) := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨c, hc1, hrem⟩ := PowerSeries.exists_forall_norm_coeff_le_of_eq_mul_add hQ
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.1
    ((PowerSeries.isRestricted_iff' c S).mp (hS c (zero_lt_one.trans_le hc1)))).2 _ (half_pos hε))
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨SN, hSN⟩ : ∃ SN : R[X], SN = PowerSeries.trunc (N + 1) S := ⟨_, rfl⟩
  have hdec : S - (SN : PowerSeries R) =
      (Q : PowerSeries R) * (q - ((SN /ₘ Q : R[X]) : PowerSeries R)) +
        ((r - SN %ₘ Q : R[X]) : PowerSeries R) := by
    have h1 : ((SN : R[X]) : PowerSeries R) =
        ((SN %ₘ Q + Q * (SN /ₘ Q) : R[X]) : PowerSeries R) :=
      congrArg _ (Polynomial.modByMonic_add_div _ _).symm
    rw [hSr, h1]
    push_cast
    ring
  have hM : ∀ j, ‖PowerSeries.coeff j (S - (SN : PowerSeries R))‖ * c ^ j ≤ ε / 2 := fun j ↦ by
    rw [map_sub, Polynomial.coeff_coe, hSN, PowerSeries.coeff_trunc]
    split_ifs with hj
    · rw [sub_self, norm_zero, zero_mul]
      exact (half_pos hε).le
    · rw [sub_zero]
      exact (hN₀ j (by omega)).le
  have hk := hrem (hq.sub (Polynomial.isEntire_coe _))
    ((Polynomial.degree_sub_le _ _).trans_lt (max_lt hr (Polynomial.degree_modByMonic_lt _ hQ)))
    hdec hM k
  rw [Polynomial.coeff_sub] at hk
  rw [← hSN, dist_eq_norm, norm_sub_rev]
  exact hk.trans_lt (half_lt_self hε)

/-- **[Bel] Lemma II.2.14 (ii)** at `T = 1` for entire series, reduced-to-remainder form:
`D(1 − Q̃*, S)(1) = D(1 − Q̃*, r)(1)` where `S = Qq + r` is the Euclidean division
(`IsEntire.exists_eq_mul_add`).  The truncations `S_N` of `S` satisfy
`D(1 − Q̃*, S_N)(1) = D(1 − Q̃*, r_N)(1)` for their polynomial remainders `r_N`
(`eval_one_dPoly_bQ_add_mul`); the left side converges by dominated convergence
(`tendsto_eval_one_dPoly_trunc`), the right side because `r_N → r` coefficientwise
(`exists_forall_norm_coeff_le_of_eq_mul_add`) and `D(B, ·)_n(1)` is continuous
(`tendsto_eval_one_dPoly`). -/
theorem evalT_one_dSeries_bQ_eq_of_eq_mul_add [IsTate R] (Q : R[X]) (u : Rˣ)
    (hQ0 : Q.coeff 0 = 1) (hu : (u : R) = Q.leadingCoeff) {S q : PowerSeries R} {r : R[X]}
    (hS : PowerSeries.IsEntire S) (hq : PowerSeries.IsEntire q) (hr : r.degree < Q.degree)
    (hSr : S = (Q : PowerSeries R) * q + r) :
    PowerSeries.evalT 1 (dSeries (bQ Q u) S) = (dPoly (bQ Q u) r Q.natDegree).eval 1 := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨Q', hQ'⟩ : ∃ Q' : R[X], Q' = Polynomial.C ((u⁻¹ : Rˣ) : R) * Q := ⟨_, rfl⟩
  have hQ'm : Q'.Monic := hQ' ▸ Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    (by rw [← hu, Units.inv_mul])
  have hQ'deg : Q'.degree = Q.degree := hQ' ▸ Polynomial.degree_C_mul_of_isUnit (u⁻¹).isUnit Q
  have hSr' : S = (Q' : PowerSeries R) * (PowerSeries.C (u : R) * q) + r := by
    rw [hSr, hQ', Polynomial.coe_mul, Polynomial.coe_C, mul_mul_mul_comm, ← map_mul, Units.inv_mul,
      map_one, one_mul]
  have hB0 : (bQ Q u).coeff 0 = 0 := bQ_coeff_zero hu
  have hAB : (fun N ↦ (dPoly (bQ Q u) (PowerSeries.trunc (N + 1) S) N).eval 1) =ᶠ[atTop]
      fun N ↦ (dPoly (bQ Q u) (PowerSeries.trunc (N + 1) S %ₘ Q') Q.natDegree).eval 1 := by
    filter_upwards [Filter.eventually_ge_atTop Q.natDegree] with N hN
    have hSNeq : PowerSeries.trunc (N + 1) S = PowerSeries.trunc (N + 1) S %ₘ Q' +
        Polynomial.C ((u⁻¹ : Rˣ) : R) * (PowerSeries.trunc (N + 1) S /ₘ Q') * Q := by
      rw [mul_right_comm, ← hQ']
      exact (Polynomial.modByMonic_add_div _ _).symm
    conv_lhs => rw [hSNeq]
    rw [eval_one_dPoly_bQ_add_mul Q _ _ u hQ0 hu ?_, dPoly_eq_of_le _ _ ?_ hB0 hN]
    · exact Polynomial.natDegree_le_natDegree
        (hQ'deg ▸ Polynomial.degree_modByMonic_lt _ hQ'm : _ < Q.degree).le
    · refine (Nat.add_le_add_right (Polynomial.natDegree_C_mul_le ((u⁻¹ : Rˣ) : R) _)
        Q.natDegree).trans ?_
      rw [Polynomial.natDegree_divByMonic _ hQ'm, Polynomial.natDegree_eq_of_degree_eq hQ'deg]
      have := Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt S N)
      omega
  exact tendsto_nhds_unique (tendsto_eval_one_dPoly_trunc (bQ Q u) hS hB0)
    ((tendsto_eval_one_dPoly (bQ Q u) Q.natDegree fun k ↦ tendsto_coeff_modByMonic_trunc hQ'm hS
      ((PowerSeries.isEntire_C _).mul hq) (hQ'deg ▸ hr) hSr' k).congr' hAB.symm)

/-- **The unit criterion for entire series** (the content of [Col97, Lemma A3.7] as used in
[Bel] Proposition II.2.15 and [Buz07] Lemma 3.1): `D(1 − Q̃*, S)(1)` is a unit iff `Q`
and `S` are relatively prime in `R{{T}}`. -/
theorem isUnit_evalT_one_dSeries_bQ_iff [IsTate R] (Q : R[X]) (u : Rˣ) (hQ0 : Q.coeff 0 = 1)
    (hu : (u : R) = Q.leadingCoeff) {S : PowerSeries R} (hS : PowerSeries.IsEntire S) :
    IsUnit (PowerSeries.evalT 1 (dSeries (bQ Q u) S)) ↔
      PowerSeries.IsEntireCoprime (Q : PowerSeries R) S := by
  have hQu : IsUnit Q.leadingCoeff := hu ▸ u.isUnit
  obtain ⟨q, r, hq, hr, hSr⟩ := hS.exists_eq_mul_add hQu
  rw [evalT_one_dSeries_bQ_eq_of_eq_mul_add Q u hQ0 hu hS hq hr hSr,
    isUnit_eval_one_dPoly_bQ_iff Q r u hQ0 hu (Polynomial.natDegree_le_natDegree hr.le),
    PowerSeries.isEntireCoprime_iff_isCoprime_of_eq_mul_add hQu hq hSr, isCoprime_comm]

/-- **[Bel] Proposition II.2.15**: if `P = QS` with `Q` a multiplicative polynomial relatively
prime to the entire `S`, then `D(1 − Q̃*, P)` has a good zero of order `deg Q` at `T = 1`. -/
theorem isGoodZero_dSeries_bQ [IsTate R] (Q : R[X]) (u : Rˣ) (hQ0 : Q.coeff 0 = 1)
    (hu : (u : R) = Q.leadingCoeff) {S : PowerSeries R} (hS : PowerSeries.IsEntire S)
    (hS0 : PowerSeries.coeff 0 S = 1) (hcop : PowerSeries.IsEntireCoprime (Q : PowerSeries R) S) :
    PowerSeries.IsGoodZero (dSeries (bQ Q u) ((Q : PowerSeries R) * S)) 1 Q.natDegree := by
  have hB0 : (bQ Q u).coeff 0 = 0 := bQ_coeff_zero hu
  rw [dSeries_mul _ (Polynomial.isEntire_coe Q) hS (by rw [Polynomial.coeff_coe, hQ0]) hS0 hB0,
    dSeries_coe _ Q le_rfl hB0, dPoly_bQ_self Q u hQ0 hu]
  have h1 : ((((1 : R[X]) - X) ^ Q.natDegree : R[X]) : PowerSeries R) =
      (1 - PowerSeries.C (1 : R) * PowerSeries.X) ^ Q.natDegree := by
    push_cast
    simp
  rw [h1]
  exact PowerSeries.IsGoodZero.of_factor (hS.dSeries _ hB0) (one_mul 1) isUnit_one
    ((isUnit_evalT_one_dSeries_bQ_iff Q u hQ0 hu hS).mpr hcop) Q.natDegree

end Normed

section SpectralMapping

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]
  [IsTate R] {I : Type*} [DecidableEq I]

/-- A polynomial without constant term in a compactoid operator is compactoid
(`IsCompactoid.finset_sum`, `.smul`, `.comp_left`). -/
theorem _root_.TateFredholm.IsCompactoid.aeval {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u)
    (B : R[X]) (hB0 : B.coeff 0 = 0) : IsCompactoid (Polynomial.aeval u B) := by
  rw [Polynomial.aeval_eq_sum_range]
  refine IsCompactoid.finset_sum _ fun k _ ↦ ?_
  cases k with
  | zero =>
    rw [hB0, zero_smul]
    exact isCompactoid_zero
  | succ k =>
    refine IsCompactoid.smul _ ?_
    rw [pow_succ, ContinuousLinearMap.mul_def]
    exact hu.comp_left (u ^ k)

-- The `S × S` block of the matrix of an operator.
private def block (S : Finset I) (w : c(I, R) →L[R] c(I, R)) : Matrix S S R :=
  Matrix.of fun j i ↦ matrixCoeff w j i

omit [IsTate R] in
private theorem block_comp_of_rows (S : Finset I) (a : c(I, R) →L[R] c(I, R))
    {b : c(I, R) →L[R] c(I, R)} (hb : ∀ j ∉ S, ∀ i, matrixCoeff b j i = 0) :
    block S (a.comp b) = block S a * block S b := by
  refine Matrix.ext fun j i ↦ ?_
  show matrixCoeff (a.comp b) j i = _
  rw [matrixCoeff_comp_eq_sum_of_rows a b hb, ← Finset.sum_coe_sort S, Matrix.mul_apply]
  rfl

omit [IsTate R] in
private theorem block_one (S : Finset I) : block S (1 : c(I, R) →L[R] c(I, R)) = 1 := by
  refine Matrix.ext fun j i ↦ ?_
  show matrixCoeff (1 : c(I, R) →L[R] c(I, R)) j i = _
  by_cases h : j = i
  · subst h
    rw [matrixCoeff_one, if_pos rfl, Matrix.one_apply_eq]
  · rw [matrixCoeff_one, if_neg fun h' ↦ h (Subtype.ext h'), Matrix.one_apply_ne h]

omit [IsTate R] in
private theorem block_pow_of_rows (S : Finset I) {w : c(I, R) →L[R] c(I, R)}
    (hw : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) (k : ℕ) : block S (w ^ k) = block S w ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, block_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, ContinuousLinearMap.mul_def, block_comp_of_rows S _ hw, ih]

omit [IsTate R] in
private theorem block_aeval_of_rows (S : Finset I) {w : c(I, R) →L[R] c(I, R)}
    (hw : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) (B : R[X]) :
    block S (Polynomial.aeval w B) = Polynomial.aeval (block S w) B := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  refine Matrix.ext fun j i ↦ ?_
  show matrixCoeff _ (j : I) (i : I) = _
  rw [matrixCoeff_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [matrixCoeff_smul, Matrix.smul_apply, ← block_pow_of_rows S hw, smul_eq_mul]
  rfl

omit [IsTate R] in
private theorem rows_aeval_of_rows (S : Finset I) {w : c(I, R) →L[R] c(I, R)}
    (hw : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) {B : R[X]} (hB0 : B.coeff 0 = 0) :
    ∀ j ∉ S, ∀ i, matrixCoeff (Polynomial.aeval w B) j i = 0 := by
  intro j hj i
  rw [Polynomial.aeval_eq_sum_range, matrixCoeff_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [matrixCoeff_smul]
  cases k with
  | zero => rw [hB0, zero_mul]
  | succ k =>
    rw [pow_succ', ContinuousLinearMap.mul_def]
    exact mul_eq_zero_of_right _ (apply_coord_eq_zero_of_row (hw j hj) _)

omit [IsTate R] in
private theorem charPowerSeries_eq_charpolyRev_of_rows (S : Finset I)
    {w : c(I, R) →L[R] c(I, R)} (hw : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) :
    charPowerSeries w = ((block S w).charpolyRev : PowerSeries R) := by
  ext n
  rw [charPowerSeries_coeff, charCoeff_eq_det_coeff w S hw n, Polynomial.coeff_coe]
  rfl

omit [IsTate R] in
private theorem charPowerSeries_aeval_of_rows (S : Finset I) {w : c(I, R) →L[R] c(I, R)}
    (hw : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) {B : R[X]} (hB0 : B.coeff 0 = 0) :
    charPowerSeries (Polynomial.aeval w B) = dSeries B (charPowerSeries w) := by
  have : Nontrivial R := NormOneClass.nontrivial
  rw [charPowerSeries_eq_charpolyRev_of_rows S (rows_aeval_of_rows S hw hB0),
    block_aeval_of_rows S hw, Matrix.charpolyRev_aeval,
    charPowerSeries_eq_charpolyRev_of_rows S hw, dSeries_coe B (N := Fintype.card S) _ ?_ hB0]
  rw [← Matrix.reverse_charpoly]
  exact (reverse_natDegree_le _).trans (Matrix.charpoly_natDegree_eq_dim _).le

omit [DecidableEq I] in
private theorem norm_pow_sub_pow_le {x y : c(I, R) →L[R] c(I, R)} {D : ℝ} (hD1 : 1 ≤ D)
    (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) (k : ℕ) : ‖x ^ k - y ^ k‖ ≤ k * D ^ k * ‖x - y‖ := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  induction k with
  | zero => simp
  | succ k ih =>
    have hxy : x ^ (k + 1) - y ^ (k + 1) = x ^ k * (x - y) + (x ^ k - y ^ k) * y := by
      rw [pow_succ, pow_succ, mul_sub, sub_mul, sub_add_sub_cancel]
    rw [hxy]
    calc ‖x ^ k * (x - y) + (x ^ k - y ^ k) * y‖
        ≤ ‖x ^ k * (x - y)‖ + ‖(x ^ k - y ^ k) * y‖ := norm_add_le _ _
      _ ≤ ‖x ^ k‖ * ‖x - y‖ + ‖x ^ k - y ^ k‖ * ‖y‖ :=
          add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
      _ ≤ D ^ k * ‖x - y‖ + k * D ^ k * ‖x - y‖ * D :=
          add_le_add
            (mul_le_mul_of_nonneg_right
              ((opNorm_pow_le x k).trans (pow_le_pow_left₀ (opNorm_nonneg x) hx k))
              (opNorm_nonneg _))
            (mul_le_mul ih hy (opNorm_nonneg _)
              (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hD0 k)) (opNorm_nonneg _)))
      _ ≤ D ^ (k + 1) * ‖x - y‖ + k * D ^ (k + 1) * ‖x - y‖ := by
          rw [pow_succ]
          refine add_le_add (mul_le_mul_of_nonneg_right ?_ (opNorm_nonneg _)) (le_of_eq (by ring))
          exact le_mul_of_one_le_right (pow_nonneg hD0 k) hD1
      _ = (k + 1 : ℕ) * D ^ (k + 1) * ‖x - y‖ := by
          push_cast
          ring

omit [DecidableEq I] in
private theorem norm_aeval_sub_aeval_le {x y : c(I, R) →L[R] c(I, R)} {D : ℝ} (hD1 : 1 ≤ D)
    (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) (B : R[X]) :
    ‖Polynomial.aeval x B - Polynomial.aeval y B‖ ≤
      (∑ k ∈ Finset.range (B.natDegree + 1), ‖B.coeff k‖ * (k * D ^ k)) * ‖x - y‖ := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine (opNorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [← smul_sub, mul_assoc]
  exact (opNorm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le hD1 hx hy k) (norm_nonneg _))

omit [DecidableEq I] in
private theorem opNorm_le_of_norm_sub_le {x y : c(I, R) →L[R] c(I, R)} {ε : ℝ}
    (h : ‖x - y‖ ≤ ε) : ‖x‖ ≤ ‖y‖ + ε :=
  calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    _ ≤ ε + ‖y‖ := add_le_add h le_rfl
    _ = ‖y‖ + ε := add_comm _ _

private theorem tendsto_charCoeff_aeval {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u)
    {ι : Type*} {l : Filter ι} {w : ι → c(I, R) →L[R] c(I, R)} (hw : ∀ i, IsCompactoid (w i))
    (hconv : Tendsto (fun i ↦ ‖w i - u‖) l (𝓝 0)) (B : R[X]) (hB0 : B.coeff 0 = 0) (n : ℕ) :
    Tendsto (fun i ↦ charCoeff (Polynomial.aeval (w i) B) n) l
      (𝓝 (charCoeff (Polynomial.aeval u B) n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [charCoeff_zero]
    exact tendsto_const_nhds
  have haev : Tendsto (fun i ↦ ‖Polynomial.aeval (w i) B - Polynomial.aeval u B‖) l (𝓝 0) := by
    refine squeeze_zero' (g := fun i ↦ (∑ k ∈ Finset.range (B.natDegree + 1),
      ‖B.coeff k‖ * (k * (‖u‖ + 1) ^ k)) * ‖w i - u‖)
      (Filter.Eventually.of_forall fun _ ↦ opNorm_nonneg _) ?_ (by simpa using hconv.const_mul _)
    filter_upwards [(tendsto_order.1 hconv).2 1 one_pos] with i hi
    exact norm_aeval_sub_aeval_le (le_add_of_nonneg_left (opNorm_nonneg u))
      (opNorm_le_of_norm_sub_le hi.le) (le_add_of_nonneg_right zero_le_one) B
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun i ↦ (‖Polynomial.aeval u B‖ + 1) ^ (n - 1) *
    ‖Polynomial.aeval (w i) B - Polynomial.aeval u B‖)
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ (by simpa using haev.const_mul _)
  filter_upwards [(tendsto_order.1 haev).2 1 one_pos] with i hi
  exact (norm_charCoeff_sub_le _ _ ((hw i).aeval B hB0) (hu.aeval B hB0) hn).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_of_le_right (opNorm_nonneg _))
      (max_le (opNorm_le_of_norm_sub_le hi.le) (le_add_of_nonneg_right zero_le_one)) _)
      (opNorm_nonneg _))

private theorem tendsto_coeff_dSeries_charPowerSeries {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {ι : Type*} {l : Filter ι} {w : ι → c(I, R) →L[R] c(I, R)}
    (hw : ∀ i, IsCompactoid (w i)) (hconv : Tendsto (fun i ↦ ‖w i - u‖) l (𝓝 0)) (B : R[X])
    (hB0 : B.coeff 0 = 0) (n : ℕ) :
    Tendsto (fun i ↦ PowerSeries.coeff n (dSeries B (charPowerSeries (w i)))) l
      (𝓝 (PowerSeries.coeff n (dSeries B (charPowerSeries u)))) := by
  obtain ⟨Cb, hCb, hB⟩ := exists_coeff_bound B
  have htend : ∀ v : c(I, R) →L[R] c(I, R), IsCompactoid v →
      Tendsto (fun k ↦ ‖charCoeff v k‖) atTop (𝓝 0) := fun v hv ↦ by
    simpa using (PowerSeries.isRestricted_iff' 1 _).mp (charPowerSeries_isEntire v hv 1 one_pos)
  obtain ⟨Cu, hCu1, hCu⟩ := exists_norm_coeff_mul_pow_le
    (fun c hc ↦ charPowerSeries_isEntire u hu c hc : PowerSeries.IsEntire (charPowerSeries u))
    one_pos
  have hub : ∀ k, ‖charCoeff u k‖ ≤ Cu := fun k ↦ by simpa using hCu k
  have hCu0 : 0 ≤ Cu := zero_le_one.trans hCu1
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK0 : 0 < (Cu + 1) ^ (B.natDegree - 1) * Cb ^ n :=
    mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _)
  have hη0 : 0 < min 1 (ε / 2 / ((Cu + 1) ^ (B.natDegree - 1) * Cb ^ n)) :=
    lt_min one_pos (div_pos (half_pos hε) hK0)
  filter_upwards [eventually_norm_charCoeff_sub_le hu hw hconv 1 one_pos hη0] with i hi
  have hδ : ∀ k, ‖charCoeff (w i) k - charCoeff u k‖ ≤
      min 1 (ε / 2 / ((Cu + 1) ^ (B.natDegree - 1) * Cb ^ n)) := fun k ↦ by simpa using hi k
  have hwb : ∀ k, ‖charCoeff (w i) k‖ ≤ Cu + 1 := fun k ↦
    (norm_le_norm_add_norm_sub' _ _).trans (add_le_add (hub k) ((hδ k).trans (min_le_left _ _)))
  rw [dist_eq_norm]
  calc ‖PowerSeries.coeff n (dSeries B (charPowerSeries (w i))) -
        PowerSeries.coeff n (dSeries B (charPowerSeries u))‖
      ≤ min 1 (ε / 2 / ((Cu + 1) ^ (B.natDegree - 1) * Cb ^ n)) *
          (Cu + 1) ^ (B.natDegree - 1) * Cb ^ n :=
        norm_coeff_dSeries_sub_le B (le_add_of_nonneg_left hCu0) hCb hB hB0
          (fun k ↦ by simpa using hwb k)
          (fun k ↦ by simpa using (hub k).trans (le_add_of_nonneg_right zero_le_one))
          (by simpa using htend _ (hw i)) (by simpa using htend u hu)
          (fun k ↦ by simpa using hδ k) n
    _ ≤ ε / 2 / ((Cu + 1) ^ (B.natDegree - 1) * Cb ^ n) *
          ((Cu + 1) ^ (B.natDegree - 1) * Cb ^ n) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) hK0.le
    _ = ε / 2 := div_mul_cancel₀ _ hK0.ne'
    _ < ε := half_lt_self hε

/-- **[Bel] Proposition II.2.16** (spectral mapping): `det(1 − T·B(φ)) = D(B, det(1 − Tφ))`
for a compactoid `φ` and `B(0) = 0`.  The truncations `π_S φ` are row-supported, where both
sides are the finite identity `Matrix.charpolyRev_aeval` on the `S × S` block; both sides are
continuous in `φ` (`norm_charCoeff_sub_le` with the polynomial estimate
`norm_aeval_sub_aeval_le`, and `norm_coeff_dSeries_sub_le` with Serre's uniform estimate
`eventually_norm_charCoeff_sub_le`). -/
theorem charPowerSeries_aeval {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u) (B : R[X])
    (hB0 : B.coeff 0 = 0) :
    charPowerSeries (Polynomial.aeval u B) = dSeries B (charPowerSeries u) := by
  obtain ⟨w, hw⟩ : ∃ w : Finset I → c(I, R) →L[R] c(I, R), ∀ S, w S = (truncation S).comp u :=
    ⟨_, fun _ ↦ rfl⟩
  have hrows : ∀ S : Finset I, ∀ j ∉ S, ∀ i, matrixCoeff (w S) j i = 0 := fun S j hj i ↦ by
    rw [hw]
    show truncation S (u (cSpace.single i 1)) j = 0
    rw [truncation_apply, if_neg hj]
  have hwc : ∀ S, IsCompactoid (w S) := fun S ↦ by
    rw [hw]
    exact hu.comp_left (truncation S)
  have hconv : Tendsto (fun S ↦ ‖w S - u‖) atTop (𝓝 0) := by
    simp only [hw]
    exact tendsto_truncation_comp u hu
  ext n
  rw [charPowerSeries_coeff]
  refine tendsto_nhds_unique (tendsto_charCoeff_aeval hu hwc hconv B hB0 n)
    ((tendsto_coeff_dSeries_charPowerSeries hu hwc hconv B hB0 n).congr fun S ↦ ?_)
  rw [← charPowerSeries_aeval_of_rows S (hrows S) hB0, charPowerSeries_coeff]

end SpectralMapping

end Coleman

end TateFredholm

end
