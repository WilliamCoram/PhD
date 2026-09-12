/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.JacobsSlash.«3_Slopes»
import PhD.Main.JacobsSlash.«3_BaseChange»
import PhD.Main.TateFredholm.«06_BlockOp»

/-!
# The diamond operator `W` and the eigenspace splitting of `U₃` ([Jacobs, §2.1 pp. 31–34])

The AG-W tranche: the full `3 × 3` block matrix of `U₃` (blocks the six `ε_{i,j}` of
`PhD.Main.JacobsSlash.U3Data`, zero diagonal), the diamond operator
`W = [UμU]` (`μ = (1 0; 0 4)` at `3`; a block cyclic permutation with diagonal blocks
`δ₀,₁ = 4κ(−1/2)D(2/5)`, `δ₁,₂ = 4κ(−1/2)D(10/7)`, `δ₂,₀ = (1/16)κ(4)D(7/4)`), the
relation `W³ = 1`, and [Jacobs, Lemma 2.10]: conjugating by the explicit eigenbasis
matrix `B` block-diagonalises `U₃` into `M₁,₁ ⊕ M₂,₂ ⊕ M₃,₃`.  With Serre's partition
lemma (`PhD.Main.JacobsSlash.BlockOp`) this yields the milestone

  `det(1 − T·U₃) = det(1 − T·M₁,₁) · det(1 − T·M₂,₂) · det(1 − T·M₃,₃)`,

whose middle factor's slopes are Tranche A's `1/2, 3/2, 5/2, …` ([Jacobs, Cor 2.16]) and
whose third factor is [Jacobs, §2.2]'s `M₃,₃` (its slope analysis = AG-EXT).

## What is identified, and what is not

The `ε`-blocks — hence `U3MatrixOp` and the milestone above — **are** identified with the
genuine Hecke operator: `JacobsSlash.U3.heckeU3_apply_classRep` computes `U₃ = [U₁(9)·η₃·U₁(9)]`
at the class representatives as the certificate block matrix, and
`JacobsSlash.U3.charPowerSeries_blockOp_eq_U3MatrixOp` shows that matrix has the same
characteristic power series as `U3MatrixOp` (both in `PhD.Main.JacobsSlash.U3.Matrix`; the
formalised inputs Thm 2.1 – Prop 2.6 are listed in `PhD.Main.JacobsSlash.U3Data`'s module header).
So the milestone is a factorisation of the Fredholm determinant of `U₃`.

**Not** identified: the `δ`-blocks and the basis `B` are still *transcribed* from
[Jacobs, pp. 31–33].  Deriving `W`'s matrix from `[UμU]` ([Jacobs, Lemma 2.9] and the
§B.2 factorisations) would need the certificate machinery of `PhD.Main.JacobsSlash.U3.Factorisations`
run again for `μ`; it is not done, and no result here or downstream depends on it —
[Jacobs, Lemma 2.10] (`lemma210`) is proved directly from the Lemma 2.11 identities of
`PhD.Main.JacobsSlash.U3Data`, exactly as the thesis argues it ("since `U₃` and `W` commute, we
can easily verify the following equalities, from which all the cancellation is
evident").  `Wop`/`Wop_cube` are therefore validation of the transcribed data rather than
load-bearing steps.  The consequence is a limit on *wording*, not on content: "the middle
factor of `det(1 − T·U₃)` has slopes `n − 1/2`" is a theorem, while "the `ω²`-eigenspace
of the diamond operator has slopes `n − 1/2`" is not yet formalisable.

## Thesis errata found while transcribing (recorded in decomposition.md, findings 6–7)

* p. 32's list of `δ`'s scrambles its labels (it names `δ₀,₁` twice); the explicit matrix
  display below it is authoritative and is what we transcribe.
* "Clearly `W` has minimal polynomial `F(X) = X² + X + 1`" (p. 32) contradicts the
  nonzero basis exhibited for `K₀ = ker(W − I)` two lines later; the minimal polynomial
  is `X³ − 1`.  (Only `W³ = 1` is ever used, which is what we prove.)
-/

open TateFredholm MvPowerSeries
open scoped TateFredholm

namespace JacobsSlash

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

variable {t ν : K}

section EpsilonRowInt

/-!
### Row integrality of the six remaining `ε`-matrices

Exactly as for `ε₀,₂`, `ε₁,₂` in `PhD.Main.JacobsSlash.U3Data`: each matrix `(a b; c d)` is fed to
`rowInt_weightGenFun`, whose five hypotheses (`‖d‖ = 1`, `‖d − 1‖ ≤ ‖3‖`, `‖c‖ ≤ ‖3‖²`,
`‖a‖ ≤ ‖3‖`, `‖b‖ ≤ 1`) are checked from the valuation table of `ν ≡ 2695 mod 3¹⁰`.
Beyond that table only one new `ν`-fact is needed (the `1`-unit `d = 2(ν + 1)` of `ε₁,₀`,
`ε₂,₁` and the `d = −2ν` of `ε₂,₀`), namely `‖2ν + 1‖ ≤ ‖3‖`.
-/

/-- `2 · 2695 + 1 = 5391 = 3² · 599`, so `2ν + 1` is divisible by `3`. -/
private lemma norm_two_nu_add_one (h3 : ‖(3 : K)‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : ‖2 * ν + 1‖ ≤ ‖(3 : K)‖ := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have hsq : ‖(3 : K)‖ ^ 2 ≤ ‖(3 : K)‖ := by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 2)
  have h5391 : ‖(5391 : K)‖ = ‖(3 : K)‖ ^ 2 :=
    norm_ofNat_eq_pow h3 (n := 5391) (e := 2) (k := 599) (by norm_num) (by norm_num) (by norm_num)
  refine norm_le_of_sub (y := (5391 : K)) ?_ (h5391.le.trans hsq)
  rw [show 2 * ν + 1 - 5391 = 2 * (ν - 2695) by ring, norm_mul, hn2, one_mul]
  exact hνc.trans (by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 10))

/-- First matrix of `ε₀,₁`: `(a b; c d) = (3ν/10, -(ν-2)/10; -(ν-4)/4, -(3ν+2)/4)`. -/
private lemma rowInt_h01M1 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps01M1 ν)) := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hn10 : ‖(10 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 10) (by norm_num) (by norm_num)
  have e00 : eps01M1 ν 0 0 = 3 / 10 * ν := by simp [eps01M1]
  have e01 : eps01M1 ν 0 1 = -1 / 10 * ν + 1 / 5 := by simp [eps01M1]
  have e10 : eps01M1 ν 1 0 = -1 / 4 * ν + 1 := by simp [eps01M1]
  have e11 : eps01M1 ν 1 1 = -3 / 4 * ν - 1 / 2 := by simp [eps01M1]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (-3 / 4 * ν - 1 / 2 : K) = -((3 * ν + 2) / 4) by ring, norm_neg, norm_div,
      norm_three_mul_nu_add_two h3 hνc, hn4, div_one]
  · rw [e11, show (-3 / 4 * ν - 1 / 2 - 1 : K) = -(3 * (ν + 2) / 4) by ring, norm_neg, norm_div,
      hn4, div_one, norm_mul]
    calc ‖(3 : K)‖ * ‖ν + 2‖ ≤ ‖(3 : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left ((norm_nu_add_two h3 hνc).trans h3.le) (norm_nonneg _)
      _ = ‖(3 : K)‖ := mul_one _
  · rw [e10, show (-1 / 4 * ν + 1 : K) = -((ν - 4) / 4) by ring, norm_neg, norm_div, hn4, div_one]
    exact norm_nu_sub_four h3 hνc
  · have ha : ‖eps01M1 ν 0 0‖ = ‖(3 : K)‖ := by
      rw [e00, show (3 / 10 * ν : K) = 3 * ν / 10 by ring, norm_div, hn10, div_one, norm_mul,
        norm_nu h3 hνc, mul_one]
    exact ha.le
  · rw [e01, show (-1 / 10 * ν + 1 / 5 : K) = -((ν - 2) / 10) by ring, norm_neg, norm_div, hn10,
      div_one]
    exact (norm_sub_le_max' _ _).trans (by rw [norm_nu h3 hνc, hn2]; simp)

/-- Second matrix of `ε₀,₁`: `(a b; c d) = (-(ν+2)/10, (ν+2)/10; (ν-4)/4, ν/4)`. -/
private lemma rowInt_h01M2 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps01M2 ν)) := by
  have hsq : ‖(3 : K)‖ ^ 2 ≤ ‖(3 : K)‖ := by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num : 1 ≤ 2)
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hn10 : ‖(10 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 10) (by norm_num) (by norm_num)
  have e00 : eps01M2 ν 0 0 = -1 / 10 * ν - 1 / 5 := by simp [eps01M2]
  have e01 : eps01M2 ν 0 1 = 1 / 10 * ν + 1 / 5 := by simp [eps01M2]
  have e10 : eps01M2 ν 1 0 = 1 / 4 * ν - 1 := by simp [eps01M2]
  have e11 : eps01M2 ν 1 1 = 1 / 4 * ν := by simp [eps01M2]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (1 / 4 * ν : K) = ν / 4 by ring, norm_div, norm_nu h3 hνc, hn4, div_one]
  · rw [e11, show (1 / 4 * ν - 1 : K) = (ν - 4) / 4 by ring, norm_div, hn4, div_one]
    exact (norm_nu_sub_four h3 hνc).trans hsq
  · rw [e10, show (1 / 4 * ν - 1 : K) = (ν - 4) / 4 by ring, norm_div, hn4, div_one]
    exact norm_nu_sub_four h3 hνc
  · rw [e00, show (-1 / 10 * ν - 1 / 5 : K) = -((ν + 2) / 10) by ring, norm_neg, norm_div, hn10,
      div_one]
    exact norm_nu_add_two h3 hνc
  · rw [e01, show (1 / 10 * ν + 1 / 5 : K) = (ν + 2) / 10 by ring, norm_div, hn10, div_one]
    exact (norm_nu_add_two h3 hνc).trans h3.le

/-- `ε₁,₀`: `(a b; c d) = (-5(ν-1), -4; 0, 2(ν+1))`. -/
private lemma rowInt_h10 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps10M ν)) := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hn5 : ‖(5 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 5) (by norm_num) (by norm_num)
  have e00 : eps10M ν 0 0 = -5 * ν + 5 := by simp [eps10M]
  have e01 : eps10M ν 0 1 = -4 := by simp [eps10M]
  have e10 : eps10M ν 1 0 = 0 := by simp [eps10M]
  have e11 : eps10M ν 1 1 = 2 * ν + 2 := by simp [eps10M]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (2 * ν + 2 : K) = 2 * (ν + 1) by ring, norm_mul, hn2, one_mul,
      norm_nu_add_one h3 hνc]
  · rw [e11, show (2 * ν + 2 - 1 : K) = 2 * ν + 1 by ring]
    exact norm_two_nu_add_one h3 hνc
  · rw [e10, norm_zero]
    exact pow_nonneg (norm_nonneg _) 2
  · rw [e00, show (-5 * ν + 5 : K) = -(5 * (ν - 1)) by ring, norm_neg, norm_mul, hn5, one_mul]
    exact norm_nu_sub_one h3 hνc
  · have hb : ‖eps10M ν 0 1‖ = 1 := by
      rw [e01, show (-4 : K) = -(4 : K) by norm_num, norm_neg, hn4]
    exact hb.le

/-- First matrix of `ε₂,₀`: `(a b; c d) = (-21ν/2, 2(ν-2); 7(ν-4)/2, 2(3ν+2))`. -/
private lemma rowInt_h20M1 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps20M1 ν)) := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have e00 : eps20M1 ν 0 0 = -21 / 2 * ν := by simp [eps20M1]
  have e01 : eps20M1 ν 0 1 = 2 * ν - 4 := by simp [eps20M1]
  have e10 : eps20M1 ν 1 0 = 7 / 2 * ν - 14 := by simp [eps20M1]
  have e11 : eps20M1 ν 1 1 = 6 * ν + 4 := by simp [eps20M1]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (6 * ν + 4 : K) = 2 * (3 * ν + 2) by ring, norm_mul, hn2, one_mul,
      norm_three_mul_nu_add_two h3 hνc]
  · rw [e11, show (6 * ν + 4 - 1 : K) = 3 * (2 * ν + 1) by ring, norm_mul]
    calc ‖(3 : K)‖ * ‖2 * ν + 1‖ ≤ ‖(3 : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left ((norm_two_nu_add_one h3 hνc).trans h3.le) (norm_nonneg _)
      _ = ‖(3 : K)‖ := mul_one _
  · rw [e10, show (7 / 2 * ν - 14 : K) = 7 * (ν - 4) / 2 by ring, norm_div, hn2, div_one, norm_mul,
      hn7, one_mul]
    exact norm_nu_sub_four h3 hνc
  · have ha : ‖eps20M1 ν 0 0‖ = ‖(3 : K)‖ := by
      rw [e00, show (-21 / 2 * ν : K) = -(3 * (7 * ν) / 2) by ring, norm_neg, norm_div, hn2,
        div_one, norm_mul, norm_mul, hn7, one_mul, norm_nu h3 hνc, mul_one]
    exact ha.le
  · rw [e01, show (2 * ν - 4 : K) = 2 * (ν - 2) by ring, norm_mul, hn2, one_mul]
    exact (norm_sub_le_max' _ _).trans (by rw [norm_nu h3 hνc, hn2]; simp)

/-- Second matrix of `ε₂,₀`: `(a b; c d) = (7(ν+2)/2, -2(ν+2); -7(ν-4)/2, -2ν)`. -/
private lemma rowInt_h20M2 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps20M2 ν)) := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have e00 : eps20M2 ν 0 0 = 7 / 2 * ν + 7 := by simp [eps20M2]
  have e01 : eps20M2 ν 0 1 = -2 * ν - 4 := by simp [eps20M2]
  have e10 : eps20M2 ν 1 0 = -7 / 2 * ν + 14 := by simp [eps20M2]
  have e11 : eps20M2 ν 1 1 = -2 * ν := by simp [eps20M2]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (-2 * ν : K) = -(2 * ν) by ring, norm_neg, norm_mul, hn2, one_mul,
      norm_nu h3 hνc]
  · rw [e11, show (-2 * ν - 1 : K) = -(2 * ν + 1) by ring, norm_neg]
    exact norm_two_nu_add_one h3 hνc
  · rw [e10, show (-7 / 2 * ν + 14 : K) = -(7 * (ν - 4) / 2) by ring, norm_neg, norm_div, hn2,
      div_one, norm_mul, hn7, one_mul]
    exact norm_nu_sub_four h3 hνc
  · rw [e00, show (7 / 2 * ν + 7 : K) = 7 * (ν + 2) / 2 by ring, norm_div, hn2, div_one, norm_mul,
      hn7, one_mul]
    exact norm_nu_add_two h3 hνc
  · rw [e01, show (-2 * ν - 4 : K) = -(2 * (ν + 2)) by ring, norm_neg, norm_mul, hn2, one_mul]
    exact (norm_nu_add_two h3 hνc).trans h3.le

/-- `ε₂,₁`: `(a b; c d) = (-7(ν-1)/5, -8/5; 0, 2(ν+1))`. -/
private lemma rowInt_h21 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : RowInt (weightGenFun t (eps21M ν)) := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  have hn5 : ‖(5 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 5) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have hn8 : ‖(8 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 8) (by norm_num) (by norm_num)
  have e00 : eps21M ν 0 0 = -7 / 5 * ν + 7 / 5 := by simp [eps21M]
  have e01 : eps21M ν 0 1 = -8 / 5 := by simp [eps21M]
  have e10 : eps21M ν 1 0 = 0 := by simp [eps21M]
  have e11 : eps21M ν 1 1 = 2 * ν + 2 := by simp [eps21M]
  refine rowInt_weightGenFun h3 ht _ ?_ ?_ ?_ ?_ ?_
  · rw [e11, show (2 * ν + 2 : K) = 2 * (ν + 1) by ring, norm_mul, hn2, one_mul,
      norm_nu_add_one h3 hνc]
  · rw [e11, show (2 * ν + 2 - 1 : K) = 2 * ν + 1 by ring]
    exact norm_two_nu_add_one h3 hνc
  · rw [e10, norm_zero]
    exact pow_nonneg (norm_nonneg _) 2
  · rw [e00, show (-7 / 5 * ν + 7 / 5 : K) = -(7 * (ν - 1) / 5) by ring, norm_neg, norm_div, hn5,
      div_one, norm_mul, hn7, one_mul]
    exact norm_nu_sub_one h3 hνc
  · have hb : ‖eps21M ν 0 1‖ = 1 := by
      rw [e01, show (-8 / 5 : K) = -(8 / 5 : K) by norm_num, norm_neg, norm_div, hn8, hn5, div_one]
    exact hb.le

end EpsilonRowInt

section EpsilonIntegrality

variable (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10)
include h3 ht hνc

/-- [Jacobs, Lemma 2.7] for `ε₀,₁`, quantitative form (as for `h₀,₂`/`h₁,₂` in
`PhD.Main.JacobsSlash.U3Data`). -/
theorem norm_coeff_h01_le (m r : ℕ) :
    ‖coeff (idx m r) (h01 t ν)‖ ≤ ‖(3 : K)‖ ^ m := by
  have h := rowInt_add (rowInt_h01M1 h3 ht hνc) (rowInt_h01M2 h3 ht hνc) (idx m r)
  rw [idx_apply_zero] at h
  exact h

/-- [Jacobs, Lemma 2.7] for `ε₁,₀`. -/
theorem norm_coeff_h10_le (m r : ℕ) :
    ‖coeff (idx m r) (h10 t ν)‖ ≤ ‖(3 : K)‖ ^ m := by
  have h := rowInt_h10 h3 ht hνc (idx m r)
  rw [idx_apply_zero] at h
  exact h

/-- [Jacobs, Lemma 2.7] for `ε₂,₀`. -/
theorem norm_coeff_h20_le (m r : ℕ) :
    ‖coeff (idx m r) (h20 t ν)‖ ≤ ‖(3 : K)‖ ^ m := by
  have h := rowInt_add (rowInt_h20M1 h3 ht hνc) (rowInt_h20M2 h3 ht hνc) (idx m r)
  rw [idx_apply_zero] at h
  exact h

/-- [Jacobs, Lemma 2.7] for `ε₂,₁`. -/
theorem norm_coeff_h21_le (m r : ℕ) :
    ‖coeff (idx m r) (h21 t ν)‖ ≤ ‖(3 : K)‖ ^ m := by
  have h := rowInt_h21 h3 ht hνc (idx m r)
  rw [idx_apply_zero] at h
  exact h

end EpsilonIntegrality

section EpsilonOps

variable (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10)

omit [CharZero K] in
/-- Row decay `‖x^m y^r`-coefficient`‖ ≤ ‖3‖ ^ m` supplies both hypotheses of `ofGenFun`
(the case `q = 3`, `c = 1` of `hyps_of_row_decay`). -/
private lemma hyps_of_norm_coeff {F : MvPowerSeries (Fin 2) K} (h3' : ‖(3 : K)‖ < 1)
    (hF : ∀ m r : ℕ, ‖coeff (idx m r) F‖ ≤ ‖(3 : K)‖ ^ m) :
    (∃ C, ∀ j i, ‖MvPowerSeries.coeff (idx j i) F‖ ≤ C) ∧
      ∀ i, Filter.Tendsto (fun j => MvPowerSeries.coeff (idx j i) F)
        Filter.cofinite (nhds 0) :=
  hyps_of_row_decay (q := (3 : K)) (c := (1 : K)) h3'
    (fun j i => by rw [norm_one, one_mul]; exact hF j i)

omit [CharZero K] in
/-- The same row decay makes the operator compactoid ([Jacobs, Corollary 1.10]). -/
private lemma isCompactoid_ofGenFun {F : MvPowerSeries (Fin 2) K} (h3' : ‖(3 : K)‖ < 1)
    (hF : ∀ m r : ℕ, ‖coeff (idx m r) F‖ ≤ ‖(3 : K)‖ ^ m)
    (hbd : ∃ C, ∀ j i, ‖MvPowerSeries.coeff (idx j i) F‖ ≤ C)
    (hcol : ∀ i, Filter.Tendsto (fun j => MvPowerSeries.coeff (idx j i) F)
      Filter.cofinite (nhds 0)) :
    IsCompactoid (ofGenFun F hbd hcol) := by
  refine isCompactoid_of_row_decay (q := (3 : K)) (c := (1 : K)) h3' fun j i => ?_
  rw [matrixCoeff_ofGenFun, norm_one, one_mul]
  exact hF j i

/-- The operator `ε₀,₁` [Jacobs, p. 28], defined by its generating function `h₀,₁`. -/
noncomputable def epsOp01 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (h01 t ν) (hyps_of_norm_coeff _h3 (norm_coeff_h01_le _h3 _ht _hνc)).1
    (hyps_of_norm_coeff _h3 (norm_coeff_h01_le _h3 _ht _hνc)).2

/-- The operator `ε₀,₂`. -/
noncomputable def epsOp02 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (h02 t ν) (hyps_of_norm_coeff _h3 (norm_coeff_h02_le _h3 _ht _hνc)).1
    (hyps_of_norm_coeff _h3 (norm_coeff_h02_le _h3 _ht _hνc)).2

/-- The operator `ε₁,₀`. -/
noncomputable def epsOp10 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (h10 t ν) (hyps_of_norm_coeff _h3 (norm_coeff_h10_le _h3 _ht _hνc)).1
    (hyps_of_norm_coeff _h3 (norm_coeff_h10_le _h3 _ht _hνc)).2

/-- The operator `ε₁,₂`. -/
noncomputable def epsOp12 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (h12 t ν) (hyps_of_norm_coeff _h3 (norm_coeff_h12_le _h3 _ht _hνc)).1
    (hyps_of_norm_coeff _h3 (norm_coeff_h12_le _h3 _ht _hνc)).2

/-- The operator `ε₂,₀`. -/
noncomputable def epsOp20 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (h20 t ν) (hyps_of_norm_coeff _h3 (norm_coeff_h20_le _h3 _ht _hνc)).1
    (hyps_of_norm_coeff _h3 (norm_coeff_h20_le _h3 _ht _hνc)).2

/-- The operator `ε₂,₁`. -/
noncomputable def epsOp21 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (h21 t ν) (hyps_of_norm_coeff _h3 (norm_coeff_h21_le _h3 _ht _hνc)).1
    (hyps_of_norm_coeff _h3 (norm_coeff_h21_le _h3 _ht _hνc)).2

/-!
Compactoidness of the six `ε`-operators, one lemma each ([Jacobs, Corollary 1.10] applied
to the row decay of Lemma 2.7).  These are stated separately — rather than inlined into
the assembly below — so that the block-matrix goals of `isCompactoid_U3MatrixOp` are closed
by `exact`s with fully explicit arguments: placeholder `_`s in the `ofGenFun` arguments
make unification unfold through `blockOp`.
-/

/-- The operator `ε₀,₁` is compactoid ([Jacobs, Lemma 2.7]). -/
lemma isCompactoid_epsOp01 : IsCompactoid (epsOp01 h3 ht hνc) :=
  isCompactoid_ofGenFun h3 (norm_coeff_h01_le h3 ht hνc)
    (hyps_of_norm_coeff h3 (norm_coeff_h01_le h3 ht hνc)).1
    (hyps_of_norm_coeff h3 (norm_coeff_h01_le h3 ht hνc)).2

/-- The operator `ε₀,₂` is compactoid ([Jacobs, Lemma 2.7]). -/
lemma isCompactoid_epsOp02 : IsCompactoid (epsOp02 h3 ht hνc) :=
  isCompactoid_ofGenFun h3 (norm_coeff_h02_le h3 ht hνc)
    (hyps_of_norm_coeff h3 (norm_coeff_h02_le h3 ht hνc)).1
    (hyps_of_norm_coeff h3 (norm_coeff_h02_le h3 ht hνc)).2

/-- The operator `ε₁,₀` is compactoid ([Jacobs, Lemma 2.7]). -/
lemma isCompactoid_epsOp10 : IsCompactoid (epsOp10 h3 ht hνc) :=
  isCompactoid_ofGenFun h3 (norm_coeff_h10_le h3 ht hνc)
    (hyps_of_norm_coeff h3 (norm_coeff_h10_le h3 ht hνc)).1
    (hyps_of_norm_coeff h3 (norm_coeff_h10_le h3 ht hνc)).2

/-- The operator `ε₁,₂` is compactoid ([Jacobs, Lemma 2.7]). -/
lemma isCompactoid_epsOp12 : IsCompactoid (epsOp12 h3 ht hνc) :=
  isCompactoid_ofGenFun h3 (norm_coeff_h12_le h3 ht hνc)
    (hyps_of_norm_coeff h3 (norm_coeff_h12_le h3 ht hνc)).1
    (hyps_of_norm_coeff h3 (norm_coeff_h12_le h3 ht hνc)).2

/-- The operator `ε₂,₀` is compactoid ([Jacobs, Lemma 2.7]). -/
lemma isCompactoid_epsOp20 : IsCompactoid (epsOp20 h3 ht hνc) :=
  isCompactoid_ofGenFun h3 (norm_coeff_h20_le h3 ht hνc)
    (hyps_of_norm_coeff h3 (norm_coeff_h20_le h3 ht hνc)).1
    (hyps_of_norm_coeff h3 (norm_coeff_h20_le h3 ht hνc)).2

/-- The operator `ε₂,₁` is compactoid ([Jacobs, Lemma 2.7]). -/
lemma isCompactoid_epsOp21 : IsCompactoid (epsOp21 h3 ht hνc) :=
  isCompactoid_ofGenFun h3 (norm_coeff_h21_le h3 ht hνc)
    (hyps_of_norm_coeff h3 (norm_coeff_h21_le h3 ht hνc)).1
    (hyps_of_norm_coeff h3 (norm_coeff_h21_le h3 ht hνc)).2

/-- **The matrix of `U₃`** [Jacobs, p. 28]: the `3 × 3` block operator with blocks the
`ε_{i,j}` and zero diagonal ("which shows that the trace of `U₃` is zero").  This *is*
the matrix of the Hecke operator `[U₁(9)·η₃·U₁(9)]`, up to the spectrally-inert
determinant twist: `JacobsSlash.U3.heckeU3_apply_classRep` and
`JacobsSlash.U3.charPowerSeries_blockOp_eq_U3MatrixOp` (`PhD.Main.JacobsSlash.U3.Matrix`; module
header). -/
noncomputable def U3MatrixOp : c(Fin 3 × ℕ, K) →L[K] c(Fin 3 × ℕ, K) :=
  blockOp
    ![![0, epsOp01 h3 ht hνc, epsOp02 h3 ht hνc],
      ![epsOp10 h3 ht hνc, 0, epsOp12 h3 ht hνc],
      ![epsOp20 h3 ht hνc, epsOp21 h3 ht hνc, 0]]

/-- The matrix of `U₃` is compactoid: blockwise from the compactoidness of the six
`ε`-operators and of the zero diagonal ([Jacobs, Corollary 1.10] + `isCompactoid_blockOp`). -/
theorem isCompactoid_U3MatrixOp : IsCompactoid (U3MatrixOp h3 ht hνc) := by
  refine isCompactoid_blockOp fun a b => ?_
  fin_cases a
  · fin_cases b
    · exact isCompactoid_zero
    · exact isCompactoid_epsOp01 h3 ht hνc
    · exact isCompactoid_epsOp02 h3 ht hνc
  · fin_cases b
    · exact isCompactoid_epsOp10 h3 ht hνc
    · exact isCompactoid_zero
    · exact isCompactoid_epsOp12 h3 ht hνc
  · fin_cases b
    · exact isCompactoid_epsOp20 h3 ht hνc
    · exact isCompactoid_epsOp21 h3 ht hνc
    · exact isCompactoid_zero

/-- **Determinant-twist invariance of the `U₃` slope theory** (the AG-B seam; see
`PhD/Jacobs/U3/Factorisations.lean`, "Handedness normalisation").  The block matrix
assembled from the left-handed certificates differs from `U3MatrixOp` blockwise by the
scalars `ψ i · φ j` with `φ i · ψ i = 1` — concretely `φ i = κ_t(dᵢ)·dᵢ⁻²` with
`dᵢ = det θ₃(cᵢ)` — a coboundary, i.e. conjugation by the blockwise diagonal
`diag (φ i)`.  By `TateFredholm.charPowerSeries_blockOp_twist` the Fredholm determinant,
hence every slope statement of this file and `PhD.Main.JacobsSlash.Slopes`, is identical for the
two matrices.  Stated for an arbitrary pointwise-inverse pair `(φ, ψ)`;
`PhD/Jacobs/U3/Matrix.lean` instantiates it at the class-determinant weights. -/
theorem charPowerSeries_twist_U3MatrixOp (φ ψ : Fin 3 → K) (hφψ : ∀ i, φ i * ψ i = 1) :
    charPowerSeries (blockOp fun i j => (ψ i * φ j) •
        ![![0, epsOp01 h3 ht hνc, epsOp02 h3 ht hνc],
          ![epsOp10 h3 ht hνc, 0, epsOp12 h3 ht hνc],
          ![epsOp20 h3 ht hνc, epsOp21 h3 ht hνc, 0]] i j)
      = charPowerSeries (U3MatrixOp h3 ht hνc) :=
  charPowerSeries_blockOp_twist φ ψ hφψ (isCompactoid_U3MatrixOp h3 ht hνc)

/-!
The matrices of the six `ε`-operators, read off their generating functions.  These are what
[Jacobs, Lemma 2.10] is computed with (`lemma210` works entirely at the level of matrix
coefficients).  Public, because they are also the AG-B seam: `PhD/Jacobs/U3/Matrix.lean`
identifies the certificate-assembled blocks with these operators entrywise.
-/

lemma matrixCoeff_epsOp01 (j i : ℕ) :
    matrixCoeff (epsOp01 h3 ht hνc) j i = coeff (idx j i) (h01 t ν) := by
  simp only [epsOp01, matrixCoeff_ofGenFun]

lemma matrixCoeff_epsOp02 (j i : ℕ) :
    matrixCoeff (epsOp02 h3 ht hνc) j i = coeff (idx j i) (h02 t ν) := by
  simp only [epsOp02, matrixCoeff_ofGenFun]

lemma matrixCoeff_epsOp10 (j i : ℕ) :
    matrixCoeff (epsOp10 h3 ht hνc) j i = coeff (idx j i) (h10 t ν) := by
  simp only [epsOp10, matrixCoeff_ofGenFun]

lemma matrixCoeff_epsOp12 (j i : ℕ) :
    matrixCoeff (epsOp12 h3 ht hνc) j i = coeff (idx j i) (h12 t ν) := by
  simp only [epsOp12, matrixCoeff_ofGenFun]

lemma matrixCoeff_epsOp20 (j i : ℕ) :
    matrixCoeff (epsOp20 h3 ht hνc) j i = coeff (idx j i) (h20 t ν) := by
  simp only [epsOp20, matrixCoeff_ofGenFun]

lemma matrixCoeff_epsOp21 (j i : ℕ) :
    matrixCoeff (epsOp21 h3 ht hνc) j i = coeff (idx j i) (h21 t ν) := by
  simp only [epsOp21, matrixCoeff_ofGenFun]

end EpsilonOps

section Toolkit

/-!
### Shared toolkit for the `δ`/`B` computations

The diagonal blocks of `W` and of `B`, `B⁻¹` are all of the form `scalar • D(α)` with `α` a
quotient of numerals prime to `3`; the three block identities `W³ = 1`, `B⁻¹B = 1`, `BB⁻¹ = 1`
are all of the form "block matrix with identity diagonal and zero off-diagonal".  The four
groups of helpers below (unit fractions, `diagOp` calculus, `blockOp`-is-`s • id`, and the
`κ`-collapse) are what those computations run on; they are reused by [Jacobs, Lemma 2.10].
-/

/-- `‖(N/M)^k‖ ≤ 1` for numerals `N`, `M` prime to `3`: both are units. -/
private lemma norm_pow_div_le_one (h3 : ‖(3 : K)‖ < 1) {N M : K} {n m : ℕ}
    (hn : Nat.Coprime n 3) (hm : Nat.Coprime m 3) (hN : N = (n : ℕ)) (hM : M = (m : ℕ))
    (k : ℕ) : ‖(N / M) ^ k‖ ≤ 1 := by
  rw [norm_pow, norm_div, norm_ofNat_eq_one h3 hn hN, norm_ofNat_eq_one h3 hm hM, div_one,
    one_pow]

/-- The diagonal of `D(2/5)` is bounded by `1`. -/
private lemma norm_pow_two_fifths (h3 : ‖(3 : K)‖ < 1) (k : ℕ) : ‖((2 : K) / 5) ^ k‖ ≤ 1 :=
  norm_pow_div_le_one h3 (n := 2) (m := 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) k

/-- The diagonal of `D(10/7)` is bounded by `1`. -/
private lemma norm_pow_ten_sevenths (h3 : ‖(3 : K)‖ < 1) (k : ℕ) : ‖((10 : K) / 7) ^ k‖ ≤ 1 :=
  norm_pow_div_le_one h3 (n := 10) (m := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) k

/-- The diagonal of `D(7/4)` is bounded by `1`. -/
private lemma norm_pow_seven_quarters (h3 : ‖(3 : K)‖ < 1) (k : ℕ) : ‖((7 : K) / 4) ^ k‖ ≤ 1 :=
  norm_pow_div_le_one h3 (n := 7) (m := 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) k

/-- The diagonal of `D(4/7)` is bounded by `1`. -/
private lemma norm_pow_four_sevenths (h3 : ‖(3 : K)‖ < 1) (k : ℕ) : ‖((4 : K) / 7) ^ k‖ ≤ 1 :=
  norm_pow_div_le_one h3 (n := 4) (m := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) k

/-- The diagonal of `D(7/10)` is bounded by `1`. -/
private lemma norm_pow_seven_tenths (h3 : ‖(3 : K)‖ < 1) (k : ℕ) : ‖((7 : K) / 10) ^ k‖ ≤ 1 :=
  norm_pow_div_le_one h3 (n := 7) (m := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) k

omit [CharZero K] in
/-- Diagonal operators compose entrywise: `D(a) ∘ D(b) = D(ab)`. -/
private lemma diagOp_comp (a b : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) :
    (diagOp a ha).comp (diagOp b hb) =
      diagOp (fun n => a n * b n) (fun n => by
        rw [norm_mul]
        exact mul_le_one₀ (ha n) (norm_nonneg _) (hb n)) := by
  refine ContinuousLinearMap.ext fun f => DFunLike.ext _ _ fun j => ?_
  rw [ContinuousLinearMap.comp_apply, diagOp_apply, diagOp_apply, diagOp_apply, mul_assoc]

omit [CharZero K] in
/-- A diagonal operator with all-`1` diagonal is the identity. -/
private lemma diagOp_eq_id (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (h1 : ∀ n, a n = 1) :
    diagOp a ha = ContinuousLinearMap.id K (c(ℕ, K)) := by
  refine ContinuousLinearMap.ext fun f => DFunLike.ext _ _ fun j => ?_
  rw [diagOp_apply, h1, one_mul, ContinuousLinearMap.id_apply]

omit [CharZero K] in
/-- A block operator whose diagonal blocks are `s • 1` and whose off-diagonal blocks vanish
is `s • 1`.  (The `s = 1` case assembles `W³ = 1`; `s = 3` the two `B`-inversions.) -/
private lemma blockOp_eq_smul_id {σ : Type*} [Fintype σ] [DecidableEq σ] (s : K)
    (T : σ → σ → (c(ℕ, K) →L[K] c(ℕ, K)))
    (hdiag : ∀ a, T a a = s • ContinuousLinearMap.id K (c(ℕ, K)))
    (hoff : ∀ a b, a ≠ b → T a b = 0) :
    blockOp T = s • ContinuousLinearMap.id K (c(σ × ℕ, K)) := by
  refine TateFredholm.ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨c, i⟩ := y
  have hrhs : matrixCoeff (s • ContinuousLinearMap.id K (c(σ × ℕ, K))) (a, j) (c, i)
      = s * cSpace.single ((c, i) : σ × ℕ) (1 : K) (a, j) := rfl
  rw [matrixCoeff_blockOp, hrhs]
  by_cases hac : a = c
  · subst hac
    have hd : matrixCoeff (T a a) j i = s * cSpace.single i (1 : K) j := by
      rw [hdiag]
      rfl
    rw [hd]
    by_cases hji : j = i
    · subst hji
      rw [cSpace.single_apply_self, cSpace.single_apply_self]
    · rw [cSpace.single_apply_of_ne hji,
        cSpace.single_apply_of_ne (fun h => hji (congrArg Prod.snd h))]
  · have h0 : matrixCoeff (T a c) j i = 0 := by
      rw [hoff a c hac]
      rfl
    rw [h0, cSpace.single_apply_of_ne (fun h => hac (congrArg Prod.fst h)), mul_zero]

omit [CharZero K] in
/-- A block operator with identity diagonal and vanishing off-diagonal is the identity. -/
private lemma blockOp_eq_id {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T : σ → σ → (c(ℕ, K) →L[K] c(ℕ, K)))
    (hdiag : ∀ a, T a a = ContinuousLinearMap.id K (c(ℕ, K)))
    (hoff : ∀ a b, a ≠ b → T a b = 0) :
    blockOp T = ContinuousLinearMap.id K (c(σ × ℕ, K)) := by
  have h := blockOp_eq_smul_id (1 : K) T (fun a => by rw [hdiag a, one_smul]) hoff
  rwa [one_smul] at h

omit [CharZero K] in
/-- Two diagonal operators whose diagonals are reciprocal compose to the identity. -/
private lemma diagOp_comp_eq_id (a b : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1)
    (hab : ∀ n, a n * b n = 1) :
    (diagOp a ha).comp (diagOp b hb) = ContinuousLinearMap.id K (c(ℕ, K)) := by
  rw [diagOp_comp]
  exact diagOp_eq_id _ _ hab

omit [CharZero K] in
/-- A triple of scalar multiples of diagonal operators composes to the identity as soon as
both the scalars and the diagonals telescope to `1` (the `W³ = 1` pattern). -/
private lemma smul_diagOp_triple (s₁ s₂ s₃ : K) (a b c : ℕ → K)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hs : s₁ * (s₂ * s₃) = 1) (habc : ∀ n, a n * (b n * c n) = 1) :
    (s₁ • diagOp a ha).comp ((s₂ • diagOp b hb).comp (s₃ • diagOp c hc)) =
      ContinuousLinearMap.id K (c(ℕ, K)) := by
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
    diagOp_comp]
  rw [diagOp_eq_id _ _ habc]
  refine Eq.trans ?_ (one_smul K (ContinuousLinearMap.id K (c(ℕ, K))))
  congr 1
  linear_combination hs

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Collecting three multiples of the same operator. -/
private lemma smul_add_smul_add_smul {M : Type*} [AddCommMonoid M] [Module K M]
    (c₁ c₂ c₃ s : K) (X : M) (h : c₁ + c₂ + c₃ = s) :
    c₁ • X + c₂ • X + c₃ • X = s • X := by
  rw [← h, add_smul, add_smul]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Collecting two multiples of an operator and the operator itself. -/
private lemma smul_add_smul_add_one {M : Type*} [AddCommMonoid M] [Module K M]
    (c₁ c₂ s : K) (X : M) (h : c₁ + c₂ + 1 = s) : c₁ • X + c₂ • X + X = s • X := by
  rw [← h, add_smul, add_smul, one_smul]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Three copies of an operator. -/
private lemma add_add_self_eq_three_smul {M : Type*} [AddCommMonoid M] [Module K M] (X : M) :
    X + X + X = (3 : K) • X := by
  rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]

omit [CharZero K] in
/-- `s⁻¹ • blockOp T = 1` for a block matrix with diagonal `s • 1` and zero off-diagonal
(the shape of both `B`-inversions, `B⁻¹` carrying the factor `1/3`). -/
private lemma smul_inv_blockOp_eq_id {σ : Type*} [Fintype σ] [DecidableEq σ] (s : K)
    (hs : s ≠ 0) (T : σ → σ → (c(ℕ, K) →L[K] c(ℕ, K)))
    (hdiag : ∀ a, T a a = s • ContinuousLinearMap.id K (c(ℕ, K)))
    (hoff : ∀ a b, a ≠ b → T a b = 0) :
    s⁻¹ • blockOp T = ContinuousLinearMap.id K (c(σ × ℕ, K)) := by
  rw [blockOp_eq_smul_id s T hdiag hoff, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-!
#### Matrix coefficients of the composites of [Jacobs, Lemma 2.10]

`TateFredholm.matrixCoeff_diagOp_comp` covers the two-sided composites `D(α) ∘ u ∘ D(β)`.  The
entries of `B⁻¹AB` also contain *one-sided* ones (the third row of `B` and the third column
of `3B⁻¹` are the identity), sums of them, and the overall scalar `1/3` carried by `B⁻¹`.
-/

omit [CharZero K] in
/-- One-sided form of [Jacobs, Proposition 1.3]: `D(a) ∘ u` scales the rows. -/
private lemma matrixCoeff_diagOp_comp_left (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1)
    (u : c(ℕ, K) →L[K] c(ℕ, K)) (j i : ℕ) :
    matrixCoeff ((diagOp a ha).comp u) j i = a j * matrixCoeff u j i := by
  show ((diagOp a ha).comp u) (cSpace.single i 1) j = _
  rw [ContinuousLinearMap.comp_apply, diagOp_apply]
  rfl

omit [CharZero K] in
/-- One-sided form of [Jacobs, Proposition 1.3]: `u ∘ D(b)` scales the columns. -/
private lemma matrixCoeff_comp_diagOp_right (b : ℕ → K) (hb : ∀ n, ‖b n‖ ≤ 1)
    (u : c(ℕ, K) →L[K] c(ℕ, K)) (j i : ℕ) :
    matrixCoeff (u.comp (diagOp b hb)) j i = matrixCoeff u j i * b i := by
  have hin : diagOp b hb (cSpace.single i (1 : K)) = b i • cSpace.single i (1 : K) := by
    refine DFunLike.ext _ _ fun j' => ?_
    rw [diagOp_apply]
    show b j' * cSpace.single i (1 : K) j' = b i * cSpace.single i (1 : K) j'
    rcases eq_or_ne j' i with rfl | hj'
    · rfl
    · rw [cSpace.single_apply_of_ne hj', mul_zero, mul_zero]
  show (u.comp (diagOp b hb)) (cSpace.single i 1) j = _
  rw [ContinuousLinearMap.comp_apply, hin, map_smul]
  show b i * u (cSpace.single i 1) j = u (cSpace.single i 1) j * b i
  ring

end Toolkit

section W

variable (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)

/-- `δ₀,₁ = 4κ(−1/2)·D(2/5)` [Jacobs, p. 32 — label per the explicit matrix display;
see the module header's erratum note]. -/
noncomputable def delta01 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ((4 : K) * unitPow t (-1 / 2)) • diagOp (fun n => ((2 : K) / 5) ^ n) (norm_pow_two_fifths _h3)

/-- `δ₁,₂ = 4κ(−1/2)·D(10/7)`. -/
noncomputable def delta12 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ((4 : K) * unitPow t (-1 / 2)) • diagOp (fun n => ((10 : K) / 7) ^ n) (norm_pow_ten_sevenths _h3)

/-- `δ₂,₀ = (1/16)κ(4)·D(7/4)`. -/
noncomputable def delta20 (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ((16 : K)⁻¹ * unitPow t 4) • diagOp (fun n => ((7 : K) / 4) ^ n) (norm_pow_seven_quarters _h3)

/-- **The diamond operator `W`** [Jacobs, (2.1.10) and p. 32]: the block-cyclic operator
with blocks the `δ`'s, *transcribed*.  Unlike the `ε`-blocks, this is **not** identified
with the Hecke operator `[UμU]` — that needs [Jacobs, Lemma 2.9]/§B.2 and is not
formalised (module header).  Nothing depends on it: `lemma210` is proved from the
Lemma 2.11 identities, and `Wop_cube` below serves as validation of the transcription. -/
noncomputable def Wop : c(Fin 3 × ℕ, K) →L[K] c(Fin 3 × ℕ, K) :=
  blockOp
    ![![0, delta01 h3 ht, 0],
      ![0, 0, delta12 h3 ht],
      ![delta20 h3 ht, 0, 0]]

/-- **The block-layout permutation of `Wop`**: the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`.  The `W`
certificates of `PhD.Main.JacobsSlash.U3.«7_DiamondHecke»` index off *this* table, so
"the certificate permutation equals `Wop`'s block layout" is definitional rather than a
remark. -/
def sigmaW : Fin 3 → Fin 3 := ![1, 2, 0]

theorem sigmaW_ne (i : Fin 3) : sigmaW i ≠ i := by decide +revert

/-- The transcribed `δ`-operators indexed by the source class:
`δ₀,₁`, `δ₁,₂`, `δ₂,₀` at `i = 0, 1, 2`. -/
noncomputable def deltaOf (i : Fin 3) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ![delta01 h3 ht, delta12 h3 ht, delta20 h3 ht] i

/-- **`Wop`'s transcribed block layout IS the `σ_W`-indexed `δ`-matrix** — the nonzero
block of row `i` sits at column `σ_W i` and equals `deltaOf i`. -/
theorem Wop_eq_blockOp_deltaOf :
    Wop h3 ht = blockOp (fun i j => if j = sigmaW i then deltaOf h3 ht i else 0) := by
  refine congrArg blockOp ?_
  funext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaW, deltaOf]

/-! ### Base change of the `δ`-layer

The `δ`-side counterpart of the `ε`-side `map_h01 … map_h21` (`«3_BaseChange»`).  It
cannot live there — the `δ`s are defined in this file — so it lives beside them, which is
also where `map_Wop` wants it.  These are what let a statement over an extension field
say "…the base change of the K-matrix of the genuine diamond operator". -/

section BaseChangeW

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharZero L]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [IsUltrametricDist L]
  [CompleteSpace L] [CharZero L] in
/-- `‖3‖ < 1` transports along an isometric embedding (generic-`K` form of
`«8_HeckeSlopes»`'s `K₃`-only version). -/
theorem norm_three_lt_one_of_isometry' (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (h3 : ‖(3 : K)‖ < 1) : ‖(3 : L)‖ < 1 := by
  rw [← map_ofNat f 3, hf]
  exact h3

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [IsUltrametricDist L]
  [CompleteSpace L] [CharZero L] in
/-- The weight disc transports along an isometric embedding. -/
theorem norm_map_lt_one' (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (ht : ‖t‖ < 1) :
    ‖f t‖ < 1 := (hf t).trans_lt ht

omit [CharZero K] in
private theorem matrixCoeff_delta_scaled (a D : K) (hD : ∀ n : ℕ, ‖D ^ n‖ ≤ 1) (m r : ℕ) :
    matrixCoeff (a • diagOp (fun n => D ^ n) hD) m r = if m = r then a * D ^ m else 0 := by
  rw [matrixCoeff_smul, matrixCoeff_diagOp]
  split <;> simp

/-- `δ₀,₁` base-changes to `δ₀,₁` at the image parameters, coefficientwise. -/
theorem map_delta01 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (h3 : ‖(3 : K)‖ < 1)
    (ht : ‖t‖ < 1) (m r : ℕ) :
    matrixCoeff (delta01 (norm_three_lt_one_of_isometry' f hf h3)
        (norm_map_lt_one' f hf ht)) m r
      = f (matrixCoeff (delta01 h3 ht) m r) := by
  rw [delta01, delta01, matrixCoeff_delta_scaled, matrixCoeff_delta_scaled]
  split
  · simp only [map_mul, map_pow, map_div₀, map_ofNat, map_neg, map_one,
      map_unitPow f hf]
  · rw [map_zero]

/-- `δ₁,₂` base-changes to `δ₁,₂` at the image parameters, coefficientwise. -/
theorem map_delta12 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (h3 : ‖(3 : K)‖ < 1)
    (ht : ‖t‖ < 1) (m r : ℕ) :
    matrixCoeff (delta12 (norm_three_lt_one_of_isometry' f hf h3)
        (norm_map_lt_one' f hf ht)) m r
      = f (matrixCoeff (delta12 h3 ht) m r) := by
  rw [delta12, delta12, matrixCoeff_delta_scaled, matrixCoeff_delta_scaled]
  split
  · simp only [map_mul, map_pow, map_div₀, map_ofNat, map_neg, map_one,
      map_unitPow f hf]
  · rw [map_zero]

/-- `δ₂,₀` base-changes to `δ₂,₀` at the image parameters, coefficientwise. -/
theorem map_delta20 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (h3 : ‖(3 : K)‖ < 1)
    (ht : ‖t‖ < 1) (m r : ℕ) :
    matrixCoeff (delta20 (norm_three_lt_one_of_isometry' f hf h3)
        (norm_map_lt_one' f hf ht)) m r
      = f (matrixCoeff (delta20 h3 ht) m r) := by
  rw [delta20, delta20, matrixCoeff_delta_scaled, matrixCoeff_delta_scaled]
  split
  · simp only [map_mul, map_pow, map_div₀, _root_.map_inv₀, map_ofNat,
      map_unitPow f hf]
  · rw [map_zero]

/-- **The diamond matrix base-changes entrywise**: `Wop` over `L` at the image
parameters is the `f`-image of `Wop` over `K`.  With `Wop_eq_blockOp_deltaOf` and
`PhD.Main.JacobsSlash.U3.«7_DiamondHecke»`'s `heckeW_apply_classRep_eq_delta`, this is what
makes "the base change of the matrix of the genuine `W`" a statement one can write. -/
theorem map_Wop (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (h3 : ‖(3 : K)‖ < 1)
    (ht : ‖t‖ < 1) (x z : Fin 3 × ℕ) :
    matrixCoeff (Wop (norm_three_lt_one_of_isometry' f hf h3)
        (norm_map_lt_one' f hf ht)) x z
      = f (matrixCoeff (Wop h3 ht) x z) := by
  obtain ⟨a, j⟩ := x
  obtain ⟨b, i⟩ := z
  simp only [Wop, matrixCoeff_blockOp]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact (map_zero f).symm
  · exact map_delta01 f hf h3 ht j i
  · exact (map_zero f).symm
  · exact (map_zero f).symm
  · exact (map_zero f).symm
  · exact map_delta12 f hf h3 ht j i
  · exact map_delta20 f hf h3 ht j i
  · exact (map_zero f).symm
  · exact (map_zero f).symm

end BaseChangeW

/-- The `κ`-scalar of `W³`: `κ(−1/2)·κ(−1/2)·κ(4) = κ(1/4)·κ(4) = κ(1) = 1`.  Both
applications of `unitPow_mul` are legitimate: `‖−1/2 − 1‖ = ‖−3/2‖ = ‖3‖` and
`‖1/4 − 1‖ = ‖−3/4‖ = ‖3‖`, `‖4 − 1‖ = ‖3‖`. -/
private lemma unitPow_delta_cube (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1) :
    unitPow t (-1 / 2) * unitPow t (-1 / 2) * unitPow t 4 = 1 := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 2) (by norm_num) (by norm_num)
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 4) (by norm_num) (by norm_num)
  have hhalf : ‖(-1 / 2 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (-1 / 2 : K) - 1 = -((3 : K) / 2) by ring, norm_neg, norm_div, hn2, div_one]
  have hquarter : ‖(1 / 4 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (1 / 4 : K) - 1 = -((3 : K) / 4) by ring, norm_neg, norm_div, hn4, div_one]
  have hfour : ‖(4 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (4 : K) - 1 = 3 by norm_num]
  rw [← unitPow_mul h3' ht'.le hhalf hhalf, show (-1 / 2 : K) * (-1 / 2) = 1 / 4 by norm_num,
    ← unitPow_mul h3' ht'.le hquarter hfour, show (1 / 4 : K) * 4 = 1 by norm_num, unitPow_one]

/-- `δ₀,₁ ∘ δ₁,₂ ∘ δ₂,₀ = 1`. -/
private lemma delta_cycle_012 (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1) :
    (delta01 h3' ht').comp ((delta12 h3' ht').comp (delta20 h3' ht')) =
      ContinuousLinearMap.id K (c(ℕ, K)) := by
  simp only [delta01, delta12, delta20]
  refine smul_diagOp_triple _ _ _ _ _ _ _ _ _ ?_ fun n => ?_
  · linear_combination unitPow_delta_cube h3' ht'
  · rw [← mul_pow, ← mul_pow,
      show (2 : K) / 5 * ((10 : K) / 7 * ((7 : K) / 4)) = 1 by norm_num, one_pow]

/-- `δ₁,₂ ∘ δ₂,₀ ∘ δ₀,₁ = 1`. -/
private lemma delta_cycle_120 (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1) :
    (delta12 h3' ht').comp ((delta20 h3' ht').comp (delta01 h3' ht')) =
      ContinuousLinearMap.id K (c(ℕ, K)) := by
  simp only [delta01, delta12, delta20]
  refine smul_diagOp_triple _ _ _ _ _ _ _ _ _ ?_ fun n => ?_
  · linear_combination unitPow_delta_cube h3' ht'
  · rw [← mul_pow, ← mul_pow,
      show (10 : K) / 7 * ((7 : K) / 4 * ((2 : K) / 5)) = 1 by norm_num, one_pow]

/-- `δ₂,₀ ∘ δ₀,₁ ∘ δ₁,₂ = 1`. -/
private lemma delta_cycle_201 (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1) :
    (delta20 h3' ht').comp ((delta01 h3' ht').comp (delta12 h3' ht')) =
      ContinuousLinearMap.id K (c(ℕ, K)) := by
  simp only [delta01, delta12, delta20]
  refine smul_diagOp_triple _ _ _ _ _ _ _ _ _ ?_ fun n => ?_
  · linear_combination unitPow_delta_cube h3' ht'
  · rw [← mul_pow, ← mul_pow,
      show (7 : K) / 4 * ((2 : K) / 5 * ((10 : K) / 7)) = 1 by norm_num, one_pow]

/-- **`W³ = 1`** [Jacobs, Remark 2.8.2].  (The scalar check is
`κ(−1/2)²κ(4) = κ(1) = 1` and `D(2/5)D(10/7)D(7/4) = D(1)`; note the thesis's
"minimal polynomial `X² + X + 1`" is an erratum — see the module header.) -/
theorem Wop_cube :
    (Wop h3 ht).comp ((Wop h3 ht).comp (Wop h3 ht)) =
      ContinuousLinearMap.id K (c(Fin 3 × ℕ, K)) := by
  simp only [Wop, blockOp_comp]
  refine blockOp_eq_id _ ?_ ?_
  · intro a
    fin_cases a <;>
      simp only [Fin.reduceFinMk, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        ContinuousLinearMap.zero_comp, add_zero, zero_add]
    · exact delta_cycle_012 h3 ht
    · exact delta_cycle_120 h3 ht
    · exact delta_cycle_201 h3 ht
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all only [Fin.reduceFinMk, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, add_zero, zero_add,
        ne_eq, not_true_eq_false]

end W

section Diagonalisation

variable (ω : K)
variable (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10)

/-- The generating function of the eigenblock `M₁,₁` [Jacobs, (2.1.14)]:
`(1/16)κ(4)h₀,₂(7x/4, y) + (1/4)κ(−2)h₁,₂(7x/10, y)`. -/
noncomputable def M11genFun : MvPowerSeries (Fin 2) K :=
  ((16 : K)⁻¹ * unitPow t 4) • diagRescale ((7 : K) / 4) 1 (h02 t ν) +
    ((4 : K)⁻¹ * unitPow t (-2)) • diagRescale ((7 : K) / 10) 1 (h12 t ν)

/-- The generating function of the eigenblock `M₃,₃` [Jacobs, (2.1.14) and §2.2 p. 40]:
`(1/16)ωκ(4)h₀,₂(7x/4, y) + (1/4)ω²κ(−2)h₁,₂(7x/10, y)`. -/
noncomputable def M33genFun : MvPowerSeries (Fin 2) K :=
  ((16 : K)⁻¹ * ω * unitPow t 4) • diagRescale ((7 : K) / 4) 1 (h02 t ν) +
    ((4 : K)⁻¹ * ω ^ 2 * unitPow t (-2)) • diagRescale ((7 : K) / 10) 1 (h12 t ν)

/-- Row decay of `H₁,₁`: `‖x^m y^r`-coefficient`‖ ≤ ‖3‖ ^ m`; the proof of
`norm_coeff_M22genFun_le` (`PhD.Main.JacobsSlash.U3Data`) with the scalars `ω²`, `ω` replaced by
`1`, `1` (so no `ω`-hypothesis is needed here). -/
private lemma norm_coeff_M11genFun_le (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1)
    (hνc' : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (m r : ℕ) :
    ‖coeff (idx m r) (M11genFun (t := t) (ν := ν))‖ ≤ ‖(3 : K)‖ ^ m := by
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 4) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 7) (by norm_num) (by norm_num)
  have hn10 : ‖(10 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 10) (by norm_num) (by norm_num)
  have hn16 : ‖(16 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 16) (by norm_num) (by norm_num)
  have hu4 : ‖unitPow t (4 : K)‖ ≤ 1 :=
    norm_unitPow_le_one h3' ht' (le_of_eq (by rw [show (4 : K) - 1 = 3 by norm_num]))
  have hu2 : ‖unitPow t (-2 : K)‖ ≤ 1 :=
    norm_unitPow_le_one h3' ht' (le_of_eq (by rw [show (-2 : K) - 1 = -3 by norm_num, norm_neg]))
  have hc1 : ‖(16 : K)⁻¹ * unitPow t 4‖ ≤ 1 := by
    rw [norm_mul, norm_inv, hn16, inv_one, one_mul]
    exact hu4
  have hc2 : ‖(4 : K)⁻¹ * unitPow t (-2)‖ ≤ 1 := by
    rw [norm_mul, norm_inv, hn4, inv_one, one_mul]
    exact hu2
  have hα1 : ‖(7 : K) / 4‖ = 1 := by rw [norm_div, hn7, hn4, div_one]
  have hα2 : ‖(7 : K) / 10‖ = 1 := by rw [norm_div, hn7, hn10, div_one]
  simp only [M11genFun, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact norm_coeff_smul_diagRescale_le hc1 hα1 (norm_coeff_h02_le h3' ht' hνc' m r)
  · exact norm_coeff_smul_diagRescale_le hc2 hα2 (norm_coeff_h12_le h3' ht' hνc' m r)

/-- Row decay of `H₃,₃`: as for `H₁,₁`, but the scalars now carry `ω`, `ω²`, so the
primitive-cube-root hypothesis is needed (through `‖ω‖ = 1`). -/
private lemma norm_coeff_M33genFun_le (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1)
    (hνc' : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (hω' : ω ^ 2 + ω + 1 = 0) (m r : ℕ) :
    ‖coeff (idx m r) (M33genFun ω (t := t) (ν := ν))‖ ≤ ‖(3 : K)‖ ^ m := by
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 4) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 7) (by norm_num) (by norm_num)
  have hn10 : ‖(10 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 10) (by norm_num) (by norm_num)
  have hn16 : ‖(16 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 16) (by norm_num) (by norm_num)
  have hnω : ‖ω‖ = 1 := norm_omega hω'
  have hu4 : ‖unitPow t (4 : K)‖ ≤ 1 :=
    norm_unitPow_le_one h3' ht' (le_of_eq (by rw [show (4 : K) - 1 = 3 by norm_num]))
  have hu2 : ‖unitPow t (-2 : K)‖ ≤ 1 :=
    norm_unitPow_le_one h3' ht' (le_of_eq (by rw [show (-2 : K) - 1 = -3 by norm_num, norm_neg]))
  have hc1 : ‖(16 : K)⁻¹ * ω * unitPow t 4‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_inv, hn16, inv_one, one_mul, hnω, one_mul]
    exact hu4
  have hc2 : ‖(4 : K)⁻¹ * ω ^ 2 * unitPow t (-2)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_inv, hn4, inv_one, one_mul, norm_pow, hnω, one_pow, one_mul]
    exact hu2
  have hα1 : ‖(7 : K) / 4‖ = 1 := by rw [norm_div, hn7, hn4, div_one]
  have hα2 : ‖(7 : K) / 10‖ = 1 := by rw [norm_div, hn7, hn10, div_one]
  simp only [M33genFun, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact norm_coeff_smul_diagRescale_le hc1 hα1 (norm_coeff_h02_le h3' ht' hνc' m r)
  · exact norm_coeff_smul_diagRescale_le hc2 hα2 (norm_coeff_h12_le h3' ht' hνc' m r)

/-- The operator `M₁,₁`. -/
noncomputable def M11op (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (M11genFun (t := t) (ν := ν))
    (hyps_of_norm_coeff _h3 (norm_coeff_M11genFun_le _h3 _ht _hνc)).1
    (hyps_of_norm_coeff _h3 (norm_coeff_M11genFun_le _h3 _ht _hνc)).2

/-- The operator `M₃,₃` (its slope analysis is AG-EXT, [Jacobs, §2.2]).

The hypothesis `_hω : ω² + ω + 1 = 0` is what makes the defining generating function
`H₃,₃` row-integral (`‖ω‖ = ‖ω²‖ = 1`), exactly as for `M22op` in `PhD.Main.JacobsSlash.U3Data`. -/
noncomputable def M33op (_hω : ω ^ 2 + ω + 1 = 0) (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (M33genFun ω (t := t) (ν := ν))
    (hyps_of_norm_coeff _h3 (norm_coeff_M33genFun_le ω _h3 _ht _hνc _hω)).1
    (hyps_of_norm_coeff _h3 (norm_coeff_M33genFun_le ω _h3 _ht _hνc _hω)).2

variable (hω : ω ^ 2 + ω + 1 = 0)

/-- The change-of-basis operator `B` [Jacobs, p. 33]: columns are the eigenbases
`b^{(0)}, b^{(1)}, b^{(2)}` of the `W`-eigenspaces. -/
noncomputable def Bop (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1) (_hω : ω ^ 2 + ω + 1 = 0) :
    c(Fin 3 × ℕ, K) →L[K] c(Fin 3 × ℕ, K) :=
  blockOp
    ![![((16 : K) * unitPow t (1 / 4)) •
          diagOp (fun n => ((4 : K) / 7) ^ n) (norm_pow_four_sevenths _h3),
        ((16 : K) * ω * unitPow t (1 / 4)) •
          diagOp (fun n => ((4 : K) / 7) ^ n) (norm_pow_four_sevenths _h3),
        ((16 : K) * ω ^ 2 * unitPow t (1 / 4)) •
          diagOp (fun n => ((4 : K) / 7) ^ n) (norm_pow_four_sevenths _h3)],
      ![((4 : K) * unitPow t (-1 / 2)) •
          diagOp (fun n => ((10 : K) / 7) ^ n) (norm_pow_ten_sevenths _h3),
        ((4 : K) * ω ^ 2 * unitPow t (-1 / 2)) •
          diagOp (fun n => ((10 : K) / 7) ^ n) (norm_pow_ten_sevenths _h3),
        ((4 : K) * ω * unitPow t (-1 / 2)) •
          diagOp (fun n => ((10 : K) / 7) ^ n) (norm_pow_ten_sevenths _h3)],
      ![ContinuousLinearMap.id K (c(ℕ, K)), ContinuousLinearMap.id K (c(ℕ, K)),
        ContinuousLinearMap.id K (c(ℕ, K))]]

/-- The inverse basis operator, `B⁻¹ = (1/3)·(3B⁻¹)` with `3B⁻¹` as displayed
[Jacobs, p. 33]. -/
noncomputable def Binvop (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1) (_hω : ω ^ 2 + ω + 1 = 0) :
    c(Fin 3 × ℕ, K) →L[K] c(Fin 3 × ℕ, K) :=
  (3 : K)⁻¹ • blockOp
    ![![((16 : K)⁻¹ * unitPow t 4) •
          diagOp (fun n => ((7 : K) / 4) ^ n) (norm_pow_seven_quarters _h3),
        ((4 : K)⁻¹ * unitPow t (-2)) •
          diagOp (fun n => ((7 : K) / 10) ^ n) (norm_pow_seven_tenths _h3),
        ContinuousLinearMap.id K (c(ℕ, K))],
      ![((16 : K)⁻¹ * ω ^ 2 * unitPow t 4) •
          diagOp (fun n => ((7 : K) / 4) ^ n) (norm_pow_seven_quarters _h3),
        ((4 : K)⁻¹ * ω * unitPow t (-2)) •
          diagOp (fun n => ((7 : K) / 10) ^ n) (norm_pow_seven_tenths _h3),
        ContinuousLinearMap.id K (c(ℕ, K))],
      ![((16 : K)⁻¹ * ω * unitPow t 4) •
          diagOp (fun n => ((7 : K) / 4) ^ n) (norm_pow_seven_quarters _h3),
        ((4 : K)⁻¹ * ω ^ 2 * unitPow t (-2)) •
          diagOp (fun n => ((7 : K) / 10) ^ n) (norm_pow_seven_tenths _h3),
        ContinuousLinearMap.id K (c(ℕ, K))]]

/-!
### The two inverse relations

Both compositions are `blockOp_comp` bookkeeping.  After pushing the scalars out of the
compositions every entry is a sum of three multiples of *one* operator, so it collapses to
`(scalar sum) • (that operator)`; the sums are `3` on the diagonal (through the reciprocal
pairs `κ(4)κ(1/4) = κ(−2)κ(−1/2) = 1` and `ω³ = 1`) and `0` off it (through
`1 + ω + ω² = 0`), which is exactly the factor `1/3` carried by `B⁻¹`.
-/

/-- `κ(4)·κ(1/4) = κ(1) = 1` (`‖4 − 1‖ = ‖3‖`, `‖1/4 − 1‖ = ‖−3/4‖ = ‖3‖`). -/
private lemma unitPow_four_mul_quarter (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1) :
    unitPow t 4 * unitPow t (1 / 4) = 1 := by
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 4) (by norm_num) (by norm_num)
  have hfour : ‖(4 : K) - 1‖ ≤ ‖(3 : K)‖ := by rw [show (4 : K) - 1 = 3 by norm_num]
  have hquarter : ‖(1 / 4 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (1 / 4 : K) - 1 = -((3 : K) / 4) by ring, norm_neg, norm_div, hn4, div_one]
  rw [← unitPow_mul h3' ht'.le hfour hquarter, show (4 : K) * (1 / 4) = 1 by norm_num,
    unitPow_one]

/-- `κ(−2)·κ(−1/2) = κ(1) = 1` (`‖−2 − 1‖ = ‖3‖`, `‖−1/2 − 1‖ = ‖−3/2‖ = ‖3‖`). -/
private lemma unitPow_neg_two_mul_neg_half (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1) :
    unitPow t (-2) * unitPow t (-1 / 2) = 1 := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 2) (by norm_num) (by norm_num)
  have htwo : ‖(-2 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (-2 : K) - 1 = -3 by norm_num, norm_neg]
  have hhalf : ‖(-1 / 2 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (-1 / 2 : K) - 1 = -((3 : K) / 2) by ring, norm_neg, norm_div, hn2, div_one]
  rw [← unitPow_mul h3' ht'.le htwo hhalf, show (-2 : K) * (-1 / 2) = 1 by norm_num,
    unitPow_one]

/-- `D(7/4) ∘ D(4/7) = 1`. -/
private lemma diagOp_74_comp_47 (h3' : ‖(3 : K)‖ < 1) :
    (diagOp (fun n => ((7 : K) / 4) ^ n) (norm_pow_seven_quarters h3')).comp
        (diagOp (fun n => ((4 : K) / 7) ^ n) (norm_pow_four_sevenths h3')) =
      ContinuousLinearMap.id K (c(ℕ, K)) :=
  diagOp_comp_eq_id _ _ _ _ fun n => by
    rw [← mul_pow, show (7 : K) / 4 * ((4 : K) / 7) = 1 by norm_num, one_pow]

/-- `D(4/7) ∘ D(7/4) = 1`. -/
private lemma diagOp_47_comp_74 (h3' : ‖(3 : K)‖ < 1) :
    (diagOp (fun n => ((4 : K) / 7) ^ n) (norm_pow_four_sevenths h3')).comp
        (diagOp (fun n => ((7 : K) / 4) ^ n) (norm_pow_seven_quarters h3')) =
      ContinuousLinearMap.id K (c(ℕ, K)) :=
  diagOp_comp_eq_id _ _ _ _ fun n => by
    rw [← mul_pow, show (4 : K) / 7 * ((7 : K) / 4) = 1 by norm_num, one_pow]

/-- `D(7/10) ∘ D(10/7) = 1`. -/
private lemma diagOp_710_comp_107 (h3' : ‖(3 : K)‖ < 1) :
    (diagOp (fun n => ((7 : K) / 10) ^ n) (norm_pow_seven_tenths h3')).comp
        (diagOp (fun n => ((10 : K) / 7) ^ n) (norm_pow_ten_sevenths h3')) =
      ContinuousLinearMap.id K (c(ℕ, K)) :=
  diagOp_comp_eq_id _ _ _ _ fun n => by
    rw [← mul_pow, show (7 : K) / 10 * ((10 : K) / 7) = 1 by norm_num, one_pow]

/-- `D(10/7) ∘ D(7/10) = 1`. -/
private lemma diagOp_107_comp_710 (h3' : ‖(3 : K)‖ < 1) :
    (diagOp (fun n => ((10 : K) / 7) ^ n) (norm_pow_ten_sevenths h3')).comp
        (diagOp (fun n => ((7 : K) / 10) ^ n) (norm_pow_seven_tenths h3')) =
      ContinuousLinearMap.id K (c(ℕ, K)) :=
  diagOp_comp_eq_id _ _ _ _ fun n => by
    rw [← mul_pow, show (10 : K) / 7 * ((7 : K) / 10) = 1 by norm_num, one_pow]

/-- `B` is invertible with the displayed inverse: `B⁻¹ ∘ B = 1` [Jacobs, p. 33
("moreover, B is invertible")]. -/
theorem Binvop_comp_Bop :
    (Binvop ω h3 ht hω).comp (Bop ω h3 ht hω) =
      ContinuousLinearMap.id K (c(Fin 3 × ℕ, K)) := by
  have hA : unitPow t 4 * unitPow t (1 / 4) = 1 := unitPow_four_mul_quarter h3 ht
  have hB : unitPow t (-2) * unitPow t (-1 / 2) = 1 := unitPow_neg_two_mul_neg_half h3 ht
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  simp only [Binvop, Bop, ContinuousLinearMap.smul_comp, blockOp_comp]
  refine smul_inv_blockOp_eq_id (3 : K) (by norm_num) _ ?_ ?_
  · intro a
    fin_cases a <;>
      simp only [Fin.reduceFinMk, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
        ContinuousLinearMap.id_comp, diagOp_74_comp_47 h3, diagOp_710_comp_107 h3]
    · exact smul_add_smul_add_one _ _ _ _ (by linear_combination hA + hB)
    · exact smul_add_smul_add_one _ _ _ _
        (by linear_combination ω ^ 3 * hA + ω ^ 3 * hB + 2 * hω3)
    · exact smul_add_smul_add_one _ _ _ _
        (by linear_combination ω ^ 3 * hA + ω ^ 3 * hB + 2 * hω3)
  · intro a c hac
    fin_cases a <;> fin_cases c <;>
      simp only [Fin.reduceFinMk, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
        ContinuousLinearMap.id_comp, diagOp_74_comp_47 h3, diagOp_710_comp_107 h3]
    · exact absurd rfl hac
    · exact Eq.trans (smul_add_smul_add_one _ _ 0 _
        (by linear_combination ω * hA + ω ^ 2 * hB + hω)) (zero_smul K _)
    · exact Eq.trans (smul_add_smul_add_one _ _ 0 _
        (by linear_combination ω ^ 2 * hA + ω * hB + hω)) (zero_smul K _)
    · exact Eq.trans (smul_add_smul_add_one _ _ 0 _
        (by linear_combination ω ^ 2 * hA + ω * hB + hω)) (zero_smul K _)
    · exact absurd rfl hac
    · exact Eq.trans (smul_add_smul_add_one _ _ 0 _
        (by linear_combination ω ^ 4 * hA + ω ^ 2 * hB + ω * hω3 + hω)) (zero_smul K _)
    · exact Eq.trans (smul_add_smul_add_one _ _ 0 _
        (by linear_combination ω * hA + ω ^ 2 * hB + hω)) (zero_smul K _)
    · exact Eq.trans (smul_add_smul_add_one _ _ 0 _
        (by linear_combination ω ^ 2 * hA + ω ^ 4 * hB + ω * hω3 + hω)) (zero_smul K _)
    · exact absurd rfl hac

/-- The other inverse relation, `B ∘ B⁻¹ = 1` [Jacobs, p. 33]: the same computation with
the two `ω`-power patterns transposed.  (Needed for the trace-property step of
`charPowerSeries_U3MatrixOp`, where `B` must be a genuine two-sided inverse.) -/
theorem Bop_comp_Binvop :
    (Bop ω h3 ht hω).comp (Binvop ω h3 ht hω) =
      ContinuousLinearMap.id K (c(Fin 3 × ℕ, K)) := by
  have hA : unitPow t 4 * unitPow t (1 / 4) = 1 := unitPow_four_mul_quarter h3 ht
  have hB : unitPow t (-2) * unitPow t (-1 / 2) = 1 := unitPow_neg_two_mul_neg_half h3 ht
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  simp only [Binvop, Bop, ContinuousLinearMap.comp_smul, blockOp_comp]
  refine smul_inv_blockOp_eq_id (3 : K) (by norm_num) _ ?_ ?_
  · intro a
    fin_cases a <;>
      simp only [Fin.reduceFinMk, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
        ContinuousLinearMap.comp_id, diagOp_47_comp_74 h3, diagOp_107_comp_710 h3]
    · exact smul_add_smul_add_smul _ _ _ _ _
        (by linear_combination (1 + 2 * ω ^ 3) * hA + 2 * hω3)
    · exact smul_add_smul_add_smul _ _ _ _ _
        (by linear_combination (1 + 2 * ω ^ 3) * hB + 2 * hω3)
    · exact add_add_self_eq_three_smul _
  · intro a c hac
    fin_cases a <;> fin_cases c <;>
      simp only [Fin.reduceFinMk, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
        diagOp_47_comp_74 h3, diagOp_107_comp_710 h3]
    · exact absurd rfl hac
    · exact Eq.trans (smul_add_smul_add_smul _ _ _ 0 _
        (by linear_combination (4 * ω * unitPow t (1 / 4) * unitPow t (-2)) * hω3 +
          (4 * unitPow t (1 / 4) * unitPow t (-2)) * hω)) (zero_smul K _)
    · exact Eq.trans (smul_add_smul_add_smul _ _ _ 0 _
        (by linear_combination (16 * unitPow t (1 / 4)) * hω)) (zero_smul K _)
    · exact Eq.trans (smul_add_smul_add_smul _ _ _ 0 _
        (by linear_combination (4⁻¹ * ω * unitPow t (-1 / 2) * unitPow t 4) * hω3 +
          (4⁻¹ * unitPow t (-1 / 2) * unitPow t 4) * hω)) (zero_smul K _)
    · exact absurd rfl hac
    · exact Eq.trans (smul_add_smul_add_smul _ _ _ 0 _
        (by linear_combination (4 * unitPow t (-1 / 2)) * hω)) (zero_smul K _)
    · exact Eq.trans (smul_add_smul_add_smul _ _ _ 0 _
        (by linear_combination ((16 : K)⁻¹ * unitPow t 4) * hω)) (zero_smul K _)
    · exact Eq.trans (smul_add_smul_add_smul _ _ _ 0 _
        (by linear_combination ((4 : K)⁻¹ * unitPow t (-2)) * hω)) (zero_smul K _)
    · exact absurd rfl hac

/-!
### The coefficient form of [Jacobs, Lemma 2.11]

Every entry of `B⁻¹AB` is a sum of composites `D(α) ∘ ε_{b,b'} ∘ D(β)`, whose matrix
coefficients are `α ^ j · (coefficient of h_{b,b'}) · β ^ i` — i.e. the coefficients of the
`diagRescale`d series occurring in [Jacobs, Lemma 2.11].  Reading the four proved identities
at the coefficient `x^j y^i` therefore turns them into exactly the six pairings needed, and
`entry_master` below performs the pairing once and for all, with the `ω`-bookkeeping of the
nine entries isolated into its two scalar hypotheses.
-/

private lemma matrixCoeff_M11op (j i : ℕ) :
    matrixCoeff (M11op h3 ht hνc) j i = coeff (idx j i) (M11genFun (t := t) (ν := ν)) := by
  simp only [M11op, matrixCoeff_ofGenFun]

private lemma matrixCoeff_M33op (j i : ℕ) :
    matrixCoeff (M33op ω hω h3 ht hνc) j i =
      coeff (idx j i) (M33genFun ω (t := t) (ν := ν)) := by
  simp only [M33op, matrixCoeff_ofGenFun]

private lemma isCompactoid_M11op : IsCompactoid (M11op h3 ht hνc) :=
  isCompactoid_ofGenFun h3 (norm_coeff_M11genFun_le h3 ht hνc)
    (hyps_of_norm_coeff h3 (norm_coeff_M11genFun_le h3 ht hνc)).1
    (hyps_of_norm_coeff h3 (norm_coeff_M11genFun_le h3 ht hνc)).2

private lemma isCompactoid_M33op : IsCompactoid (M33op ω hω h3 ht hνc) :=
  isCompactoid_ofGenFun h3 (norm_coeff_M33genFun_le ω h3 ht hνc hω)
    (hyps_of_norm_coeff h3 (norm_coeff_M33genFun_le ω h3 ht hνc hω)).1
    (hyps_of_norm_coeff h3 (norm_coeff_M33genFun_le ω h3 ht hνc hω)).2

/-- [Jacobs, Lemma 2.11], first chain, at the coefficient of `x^j y^i`. -/
private lemma coeff_lemma211_first (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1)
    (hνc' : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (j i : ℕ) :
    (16 : K)⁻¹ * unitPow t 4 * (((7 : K) / 4) ^ j * coeff (idx j i) (h02 t ν)) =
      (4 : K) * unitPow t (-1 / 2) * (((10 : K) / 7) ^ i * coeff (idx j i) (h21 t ν)) := by
  have h := congrArg (fun F : MvPowerSeries (Fin 2) K => coeff (idx j i) F)
    (lemma211_first h3' ht' hνc')
  simp only [MvPowerSeries.coeff_smul, coeff_diagRescale, idx_apply_zero, idx_apply_one,
    one_pow, mul_one, one_mul] at h
  linear_combination h

/-- [Jacobs, Lemma 2.11], first chain second equality, at the coefficient of `x^j y^i`. -/
private lemma coeff_lemma211_first' (j i : ℕ) :
    (4 : K) * unitPow t (-1 / 2) * (((10 : K) / 7) ^ i * coeff (idx j i) (h21 t ν)) =
      (4 : K) * unitPow t (-1 / 2) *
        (((7 : K) / 10) ^ j * ((4 : K) / 7) ^ i * coeff (idx j i) (h10 t ν)) := by
  have h := congrArg (fun F : MvPowerSeries (Fin 2) K => coeff (idx j i) F)
    (lemma211_first' (t := t) (ν := ν))
  simp only [MvPowerSeries.coeff_smul, coeff_diagRescale, idx_apply_zero, idx_apply_one,
    one_pow, one_mul] at h
  linear_combination h

/-- [Jacobs, Lemma 2.11], second chain, at the coefficient of `x^j y^i`. -/
private lemma coeff_lemma211_second (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1)
    (hνc' : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (j i : ℕ) :
    (16 : K) * unitPow t (1 / 4) * (((4 : K) / 7) ^ i * coeff (idx j i) (h20 t ν)) =
      (4 : K)⁻¹ * unitPow t (-2) * (((7 : K) / 10) ^ j * coeff (idx j i) (h12 t ν)) := by
  have h := congrArg (fun F : MvPowerSeries (Fin 2) K => coeff (idx j i) F)
    (lemma211_second h3' ht' hνc')
  simp only [MvPowerSeries.coeff_smul, coeff_diagRescale, idx_apply_zero, idx_apply_one,
    one_pow, mul_one, one_mul] at h
  linear_combination h

/-- [Jacobs, Lemma 2.11], second chain second equality, at the coefficient of `x^j y^i`. -/
private lemma coeff_lemma211_second' (j i : ℕ) :
    (4 : K)⁻¹ * unitPow t (-2) * (((7 : K) / 10) ^ j * coeff (idx j i) (h12 t ν)) =
      (4 : K)⁻¹ * unitPow t (-2) *
        (((7 : K) / 4) ^ j * ((10 : K) / 7) ^ i * coeff (idx j i) (h01 t ν)) := by
  have h := congrArg (fun F : MvPowerSeries (Fin 2) K => coeff (idx j i) F)
    (lemma211_second' (t := t) (ν := ν))
  simp only [MvPowerSeries.coeff_smul, coeff_diagRescale, idx_apply_zero, idx_apply_one,
    one_pow, mul_one] at h
  linear_combination h

/-- `κ(−2)·κ(1/4) = κ(−1/2)` (`‖−2 − 1‖ = ‖3‖`, `‖1/4 − 1‖ = ‖−3/4‖ = ‖3‖`): the scalar
identity behind the `ε₁,₀`-term of [Jacobs, Lemma 2.10]. -/
private lemma unitPow_neg_two_mul_quarter (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1) :
    unitPow t (-2) * unitPow t (1 / 4) = unitPow t (-1 / 2) := by
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 4) (by norm_num) (by norm_num)
  have htwo : ‖(-2 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (-2 : K) - 1 = -3 by norm_num, norm_neg]
  have hquarter : ‖(1 / 4 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (1 / 4 : K) - 1 = -((3 : K) / 4) by ring, norm_neg, norm_div, hn4, div_one]
  rw [← unitPow_mul h3' ht'.le htwo hquarter, show (-2 : K) * (1 / 4) = -1 / 2 by norm_num]

/-- `κ(4)·κ(−1/2) = κ(−2)` (`‖4 − 1‖ = ‖3‖`, `‖−1/2 − 1‖ = ‖−3/2‖ = ‖3‖`): the scalar
identity behind the `ε₀,₁`-term of [Jacobs, Lemma 2.10]. -/
private lemma unitPow_four_mul_neg_half (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1) :
    unitPow t 4 * unitPow t (-1 / 2) = unitPow t (-2) := by
  have hn2 : ‖(2 : K)‖ = 1 := norm_ofNat_eq_one h3' (n := 2) (by norm_num) (by norm_num)
  have hfour : ‖(4 : K) - 1‖ ≤ ‖(3 : K)‖ := by rw [show (4 : K) - 1 = 3 by norm_num]
  have hhalf : ‖(-1 / 2 : K) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [show (-1 / 2 : K) - 1 = -((3 : K) / 2) by ring, norm_neg, norm_div, hn2, div_one]
  rw [← unitPow_mul h3' ht'.le hfour hhalf, show (4 : K) * (-1 / 2) = -2 by norm_num]

/-- **The entry engine of [Jacobs, Lemma 2.10]**.  The `(a, c)` entry of `B⁻¹AB` is
`3⁻¹ ∑_{b,b'} (B⁻¹)_{a,b} ∘ ε_{b,b'} ∘ B_{b',c}`; the zero diagonal of `A` leaves the six
terms below, whose `B`/`B⁻¹`-scalars are `χ = (1, ω², ω)`, `ψ = (1, ω, ω²)` (the two
non-trivial columns of `3B⁻¹`, at row `a`) and `φ = (1, ω, ω²)`, `θ = (1, ω², ω)` (the two
non-trivial rows of `B`, at column `c`).  Lemma 2.11 collapses three of them onto
`H₁,₁`'s first summand `(1/16)κ(4)h₀,₂(7x/4, y)` and three onto its second
`(1/4)κ(−2)h₁,₂(7x/10, y)`, leaving the two scalar sums `χ + θ + ψφ` and `ψ + φ + χθ` —
`3` times `ω^{2a}` resp. `ω^a` on the diagonal, and `0` off it. -/
private lemma entry_master (h3' : ‖(3 : K)‖ < 1) (ht' : ‖t‖ < 1)
    (hνc' : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (χ ψ φ θ r₁ r₂ : K)
    (hr₁ : χ + θ + ψ * φ = 3 * r₁) (hr₂ : ψ + φ + χ * θ = 3 * r₂) (j i : ℕ) :
    (3 : K)⁻¹ * (χ * ((16 : K)⁻¹ * unitPow t 4) *
          (((7 : K) / 4) ^ j * coeff (idx j i) (h02 t ν))
        + χ * ((16 : K)⁻¹ * unitPow t 4) * (θ * ((4 : K) * unitPow t (-1 / 2))) *
          (((7 : K) / 4) ^ j * coeff (idx j i) (h01 t ν) * ((10 : K) / 7) ^ i)
        + ψ * ((4 : K)⁻¹ * unitPow t (-2)) * (φ * ((16 : K) * unitPow t (1 / 4))) *
          (((7 : K) / 10) ^ j * coeff (idx j i) (h10 t ν) * ((4 : K) / 7) ^ i)
        + ψ * ((4 : K)⁻¹ * unitPow t (-2)) *
          (((7 : K) / 10) ^ j * coeff (idx j i) (h12 t ν))
        + φ * ((16 : K) * unitPow t (1 / 4)) *
          (coeff (idx j i) (h20 t ν) * ((4 : K) / 7) ^ i)
        + θ * ((4 : K) * unitPow t (-1 / 2)) *
          (coeff (idx j i) (h21 t ν) * ((10 : K) / 7) ^ i))
      = r₁ * ((16 : K)⁻¹ * unitPow t 4 * (((7 : K) / 4) ^ j * coeff (idx j i) (h02 t ν)))
        + r₂ * ((4 : K)⁻¹ * unitPow t (-2) *
            (((7 : K) / 10) ^ j * coeff (idx j i) (h12 t ν))) := by
  have hF1 := coeff_lemma211_first h3' ht' hνc' j i
  have hF1' := coeff_lemma211_first' (t := t) (ν := ν) j i
  have hF2 := coeff_lemma211_second h3' ht' hνc' j i
  have hF2' := coeff_lemma211_second' (t := t) (ν := ν) j i
  have hK1 := unitPow_neg_two_mul_quarter (t := t) h3' ht'
  have hK2 := unitPow_four_mul_neg_half (t := t) h3' ht'
  -- the three `H₁,₁`-first-summand terms
  have hT1a : (4 : K) * unitPow t (-1 / 2) *
      (coeff (idx j i) (h21 t ν) * ((10 : K) / 7) ^ i) =
      (16 : K)⁻¹ * unitPow t 4 * (((7 : K) / 4) ^ j * coeff (idx j i) (h02 t ν)) := by
    linear_combination -hF1
  have hT1b : (4 : K)⁻¹ * unitPow t (-2) * ((16 : K) * unitPow t (1 / 4)) *
      (((7 : K) / 10) ^ j * coeff (idx j i) (h10 t ν) * ((4 : K) / 7) ^ i) =
      (16 : K)⁻¹ * unitPow t 4 * (((7 : K) / 4) ^ j * coeff (idx j i) (h02 t ν)) := by
    linear_combination (4 * (((7 : K) / 10) ^ j * coeff (idx j i) (h10 t ν) *
      ((4 : K) / 7) ^ i)) * hK1 - hF1 - hF1'
  -- the three `H₁,₁`-second-summand terms
  have hT2a : (16 : K) * unitPow t (1 / 4) *
      (coeff (idx j i) (h20 t ν) * ((4 : K) / 7) ^ i) =
      (4 : K)⁻¹ * unitPow t (-2) * (((7 : K) / 10) ^ j * coeff (idx j i) (h12 t ν)) := by
    linear_combination hF2
  have hT2b : (16 : K)⁻¹ * unitPow t 4 * ((4 : K) * unitPow t (-1 / 2)) *
      (((7 : K) / 4) ^ j * coeff (idx j i) (h01 t ν) * ((10 : K) / 7) ^ i) =
      (4 : K)⁻¹ * unitPow t (-2) * (((7 : K) / 10) ^ j * coeff (idx j i) (h12 t ν)) := by
    linear_combination ((4 : K)⁻¹ * (((7 : K) / 4) ^ j * coeff (idx j i) (h01 t ν) *
      ((10 : K) / 7) ^ i)) * hK2 - hF2'
  linear_combination (3⁻¹ * θ) * hT1a + (3⁻¹ * ψ * φ) * hT1b + (3⁻¹ * φ) * hT2a
    + (3⁻¹ * χ * θ) * hT2b
    + (3⁻¹ * ((16 : K)⁻¹ * unitPow t 4 * (((7 : K) / 4) ^ j * coeff (idx j i) (h02 t ν)))) * hr₁
    + (3⁻¹ * ((4 : K)⁻¹ * unitPow t (-2) *
        (((7 : K) / 10) ^ j * coeff (idx j i) (h12 t ν)))) * hr₂

/-- **[Jacobs, Lemma 2.10]**: conjugation by `B` block-diagonalises the matrix of `U₃`
into the three eigenblocks.  The cancellation is powered by [Jacobs, Lemma 2.11]
(proved in `PhD.Main.JacobsSlash.U3Data`). -/
theorem lemma210 :
    (Binvop ω h3 ht hω).comp ((U3MatrixOp h3 ht hνc).comp (Bop ω h3 ht hω)) =
      blockOp
        ![![M11op h3 ht hνc, 0, 0],
          ![0, M22op ω hω h3 ht hνc, 0],
          ![0, 0, M33op ω hω h3 ht hνc]] := by
  simp only [Binvop, Bop, U3MatrixOp, ContinuousLinearMap.smul_comp, blockOp_comp]
  refine TateFredholm.ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨c, i⟩ := y
  fin_cases a <;> fin_cases c <;>
    simp only [Fin.reduceFinMk, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
      add_zero, zero_add, matrixCoeff_blockOp, matrixCoeff_smul, matrixCoeff_add,
      matrixCoeff_zero, matrixCoeff_diagOp_comp_left, matrixCoeff_comp_diagOp_right,
      matrixCoeff_epsOp01, matrixCoeff_epsOp02, matrixCoeff_epsOp10, matrixCoeff_epsOp12,
      matrixCoeff_epsOp20, matrixCoeff_epsOp21, matrixCoeff_M11op, matrixCoeff_M22op,
      matrixCoeff_M33op, M11genFun, M22genFun, M33genFun, map_add, MvPowerSeries.coeff_smul,
      coeff_diagRescale, idx_apply_zero, idx_apply_one, one_pow, mul_one]
  · linear_combination entry_master h3 ht hνc 1 1 1 1 1 1 (by norm_num) (by norm_num) j i
  · linear_combination entry_master h3 ht hνc 1 1 ω (ω ^ 2) 0 0
      (by linear_combination hω) (by linear_combination hω) j i
  · linear_combination entry_master h3 ht hνc 1 1 (ω ^ 2) ω 0 0
      (by linear_combination hω) (by linear_combination hω) j i
  · linear_combination entry_master h3 ht hνc (ω ^ 2) ω 1 1 0 0
      (by linear_combination hω) (by linear_combination hω) j i
  · linear_combination entry_master h3 ht hνc (ω ^ 2) ω ω (ω ^ 2) (ω ^ 2) ω
      (by ring) (by linear_combination (ω * (ω - 1)) * hω) j i
  · linear_combination entry_master h3 ht hνc (ω ^ 2) ω (ω ^ 2) ω 0 0
      (by linear_combination ω * hω) (by linear_combination ω * hω) j i
  · linear_combination entry_master h3 ht hνc ω (ω ^ 2) 1 1 0 0
      (by linear_combination hω) (by linear_combination hω) j i
  · linear_combination entry_master h3 ht hνc ω (ω ^ 2) ω (ω ^ 2) 0 0
      (by linear_combination ω * hω) (by linear_combination ω * hω) j i
  · linear_combination entry_master h3 ht hνc ω (ω ^ 2) (ω ^ 2) ω ω (ω ^ 2)
      (by linear_combination (ω * (ω - 1)) * hω) (by ring) j i

/-- **`B` diagonalises the diamond operator** [Jacobs, Lemma 2.9 reading]:
`B⁻¹·W·B = diag(1, ω·1, ω²·1)`, i.e. column `r` of the transcribed `B` is an
`ω^r`-eigenvector of the transcribed `W`.  (Statement-fix recorded on the W02 ticket: the
expected orientation `diag(1, ω²·1, ω·1)` flips — the `κ`-collapse
`κ(−1/2)·κ(−1/2) = κ(1/4)` makes `W·(column 1) = ω·(column 1)`, as entry `(1, 1)` of the
computation shows.  The two orientations differ by the relabelling `ω ↔ ω²` of the
primitive cube root, so consumers must read block `1` as the `ω`-eigenblock of this `B`.) -/
theorem Binvop_comp_Wop_comp_Bop :
    (Binvop ω h3 ht hω).comp ((Wop h3 ht).comp (Bop ω h3 ht hω)) =
      blockOp
        ![![1, 0, 0],
          ![0, ω • (1 : c(ℕ, K) →L[K] c(ℕ, K)), 0],
          ![0, 0, ω ^ 2 • (1 : c(ℕ, K) →L[K] c(ℕ, K))]] := by
  have hA : unitPow t 4 * unitPow t (1 / 4) = 1 := unitPow_four_mul_quarter h3 ht
  have hB : unitPow t (-2) * unitPow t (-1 / 2) = 1 := unitPow_neg_two_mul_neg_half h3 ht
  have hC : unitPow t (-1 / 2) * unitPow t (-1 / 2) * unitPow t 4 = 1 :=
    unitPow_delta_cube h3 ht
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hcore : (diagOp (fun n => ((7 : K) / 4) ^ n) (norm_pow_seven_quarters h3)).comp
      ((diagOp (fun n => ((2 : K) / 5) ^ n) (norm_pow_two_fifths h3)).comp
        (diagOp (fun n => ((10 : K) / 7) ^ n) (norm_pow_ten_sevenths h3))) =
      ContinuousLinearMap.id K (c(ℕ, K)) := by
    rw [diagOp_comp, diagOp_comp]
    refine diagOp_eq_id _ _ fun n => ?_
    rw [← mul_pow, ← mul_pow,
      show (7 : K) / 4 * ((2 : K) / 5 * ((10 : K) / 7)) = 1 by norm_num, one_pow]
  simp only [Binvop, Bop, Wop, delta01, delta12, delta20, ContinuousLinearMap.smul_comp,
    blockOp_comp]
  refine TateFredholm.ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨c, i⟩ := y
  fin_cases a <;> fin_cases c <;>
    simp only [Fin.reduceFinMk, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
      add_zero, zero_add, hcore, diagOp_710_comp_107 h3, diagOp_74_comp_47 h3,
      ContinuousLinearMap.one_def, matrixCoeff_blockOp, matrixCoeff_smul, matrixCoeff_add,
      matrixCoeff_zero]
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (hC + hB + hA)
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (ω ^ 2 * hC + hB + ω * hA + hω)
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (ω * hC + hB + ω ^ 2 * hA + hω)
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (ω ^ 2 * hC + ω * hB + hA + hω)
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (ω ^ 4 * hC + ω * hB + ω * hA + ω * hω3)
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (ω ^ 3 * hC + ω * hB + ω ^ 2 * hA + hω3 + hω)
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (ω * hC + ω ^ 2 * hB + hA + hω)
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (ω ^ 3 * hC + ω ^ 2 * hB + ω * hA + hω3 + hω)
  · linear_combination ((3 : K)⁻¹ * matrixCoeff (ContinuousLinearMap.id K (c(ℕ, K))) j i) *
      (ω ^ 2 * hC + ω ^ 2 * hB + ω ^ 2 * hA)

/-- **AG-W milestone**: the Fredholm determinant of the matrix of `U₃` factors over the
three eigenblocks,

  `det(1 − T·U₃) = det(1 − T·M₁,₁) · det(1 − T·M₂,₂) · det(1 − T·M₃,₃)`

([Jacobs, Lemma 1.15 applied to the splitting of pp. 32–34]).  The middle factor's
Newton-polygon slopes are `1/2, 3/2, 5/2, …` by Tranche A + AG-NP; the third factor is
[Jacobs, §2.2]'s `M₃,₃` (AG-EXT). -/
theorem charPowerSeries_U3MatrixOp :
    charPowerSeries (U3MatrixOp h3 ht hνc) =
      charPowerSeries (M11op h3 ht hνc) *
        (charPowerSeries (M22op ω hω h3 ht hνc) * charPowerSeries (M33op ω hω h3 ht hνc)) := by
  -- (i) the trace property: `det(1 − T·B⁻¹AB) = det(1 − T·A)` ([Jacobs, Lemma 1.14]).
  have hcpt : IsCompactoid ((Binvop ω h3 ht hω).comp (U3MatrixOp h3 ht hνc)) :=
    (isCompactoid_U3MatrixOp h3 ht hνc).comp_left (Binvop ω h3 ht hω)
  have hcomm := charPowerSeries_comm ((Binvop ω h3 ht hω).comp (U3MatrixOp h3 ht hνc))
    (Bop ω h3 ht hω) hcpt
  rw [ContinuousLinearMap.comp_assoc, lemma210 ω h3 ht hνc hω,
    ← ContinuousLinearMap.comp_assoc, Bop_comp_Binvop ω h3 ht hω,
    ContinuousLinearMap.id_comp] at hcomm
  -- (ii) the block-diagonal operator is compactoid and has vanishing off-diagonal blocks.
  have hcptM : IsCompactoid (blockOp
      ![![M11op h3 ht hνc, 0, 0],
        ![0, M22op ω hω h3 ht hνc, 0],
        ![0, 0, M33op ω hω h3 ht hνc]]) := by
    refine isCompactoid_blockOp fun a b => ?_
    fin_cases a
    · fin_cases b
      · exact isCompactoid_M11op h3 ht hνc
      · exact isCompactoid_zero
      · exact isCompactoid_zero
    · fin_cases b
      · exact isCompactoid_zero
      · exact isCompactoid_M22op ω hω h3 ht hνc
      · exact isCompactoid_zero
    · fin_cases b
      · exact isCompactoid_zero
      · exact isCompactoid_zero
      · exact isCompactoid_M33op ω h3 ht hνc hω
  have hdiag : ∀ (a b : Fin 3) (j i : ℕ), a ≠ b →
      matrixCoeff (blockOp
        ![![M11op h3 ht hνc, 0, 0],
          ![0, M22op ω hω h3 ht hνc, 0],
          ![0, 0, M33op ω hω h3 ht hνc]]) (a, j) (b, i) = 0 := by
    intro a b j i hab
    rw [matrixCoeff_blockOp]
    fin_cases a <;> fin_cases b <;>
      simp_all only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, matrixCoeff_zero, ne_eq,
        not_true_eq_false]
  -- (iii) Serre's partition lemma, iterated over the three blocks.
  rw [← hcomm, charPowerSeries_blockDiag hcptM hdiag]
  simp only [blockCorner_blockOp, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

end Diagonalisation

end JacobsSlash
