/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Fredholm

/-!
# Slope bounds for the Fredholm determinant

Row decay of the matrix bounds the coefficients of `det(1 − Tu)` from below in valuation:
if `‖matrixCoeff u j i‖ ≤ σ ^ j` then every `n × n` principal minor is a product of entries
taken from `n` distinct rows, so `‖minor u S‖ ≤ σ ^ (∑_{j ∈ S} j)` and the smallest possible
row sum for `|S| = n` is `0 + 1 + ⋯ + (n−1) = n(n−1)/2`.  Hence

  `‖cₙ(u)‖ ≤ σ ^ (n choose 2)`,

which says the Newton polygon of `det(1 − Tu)` lies on or above the polygon with unit slopes
`0, v(σ), 2v(σ), …` ([Serre1962, §5]; [Jacobs, Thm 2.12] is the case where the rescaled minors
are units, where the bound is an equality).

This file is the σ-general, weight-free half of `PhD/JacobsSlash/«1_SlopeTheorem».lean`
(whose statements are pinned at `σ = ‖3‖`).

## Main declarations

* `TateFredholm.norm_det_le_pow_of_row_bound` — ultrametric Hadamard bound with row weights.
* `TateFredholm.norm_minor_le_pow_sum` — `‖minor u S‖ ≤ σ ^ (∑_{j ∈ S} w j)` for a row weight `w`.
* `TateFredholm.norm_charCoeff_le_pow` — **the slope bound** `‖cₙ(u)‖ ≤ σ ^ f n`, for any lower
  bound `f` on the weight sum over `n`-element index sets.
* `TateFredholm.choose_two_le_sum`, `TateFredholm.sum_div_le_sum_block` — the two combinatorial
  inputs (identity weight on `ℕ`; block weight on `ι × ℕ`), with the corresponding corollaries
  `norm_charCoeff_le_pow_choose_two` and `norm_charCoeff_le_pow_block`.
* `TateFredholm.choose_two_lt_sum_of_ne_range` — the strict form of `choose_two_le_sum` for
  `S ≠ {0, …, n-1}`, which is what upgrades the bound to an *equality* when the principal block's
  minor is a unit ([Jacobs, Thm 2.12]; see `PhD/JacobsSlash/«1_SlopeTheorem».lean`).
-/

open Filter Topology

noncomputable section

namespace TateFredholm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- Ultrametric Hadamard bound with row weights: `‖det A‖ ≤ σ ^ (∑ j, w j)` when
`‖A j i‖ ≤ σ ^ w j`.  Each Leibniz monomial picks one entry from every row, so its norm is at
most `∏ j, σ ^ w j = σ ^ ∑ j, w j`, and the ultrametric inequality bounds the sum by the max. -/
theorem norm_det_le_pow_of_row_bound {σ : ℝ} (hσ0 : 0 ≤ σ) {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (w : n → ℕ) (hA : ∀ j i, ‖A j i‖ ≤ σ ^ w j) :
    ‖A.det‖ ≤ σ ^ (∑ j, w j) := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun τ _ => ?_
  have hsm : ‖Equiv.Perm.sign τ • ∏ i, A (τ i) i‖ = ‖∏ i, A (τ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h]
    · rw [one_smul]
    · rw [Units.neg_smul, one_smul, norm_neg]
  rw [hsm]
  calc ‖∏ i, A (τ i) i‖ ≤ ∏ i, ‖A (τ i) i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i, σ ^ w (τ i) := Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hA (τ i) i
    _ = ∏ j, σ ^ w j := Equiv.prod_comp τ fun j => σ ^ w j
    _ = σ ^ (∑ j, w j) := Finset.prod_pow_eq_pow_sum _ _ _

variable {I : Type*} [DecidableEq I]

omit [CompleteSpace K] in
/-- The principal minor at `S` is bounded by `σ ^ (∑_{j ∈ S} w j)` when the rows of `u` decay
like `σ ^ w j`. -/
theorem norm_minor_le_pow_sum {σ : ℝ} (hσ0 : 0 ≤ σ)
    {u : c(I, K) →L[K] c(I, K)} (w : I → ℕ)
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ σ ^ w j) (S : Finset I) :
    ‖minor u S‖ ≤ σ ^ (∑ j ∈ S, w j) := by
  rw [minor, ← Finset.sum_coe_sort S w]
  exact norm_det_le_pow_of_row_bound hσ0 _ (fun j : S => w j) fun j i => hdiv _ _

/-- **The slope bound** ([Serre1962, §5]; the inequality half of [Jacobs, Thm 2.12]): row decay
`‖u_{j i}‖ ≤ σ ^ w j`, together with a lower bound `f n` for the row-weight sum over every
`n`-element index set, forces `‖cₙ(u)‖ ≤ σ ^ f n` — i.e. the Newton polygon of `det(1 − Tu)`
lies on or above the polygon through the points `(n, f n · v σ)`. -/
theorem norm_charCoeff_le_pow {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {u : c(I, K) →L[K] c(I, K)} (hu : IsCompactoid u) (w : I → ℕ)
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ σ ^ w j) {f : ℕ → ℕ}
    (hf : ∀ S : Finset I, ∀ n : ℕ, S.card = n → f n ≤ ∑ j ∈ S, w j) (n : ℕ) :
    ‖charCoeff u n‖ ≤ σ ^ f n := by
  rw [charCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine (norm_tsum_le_iSup (summable_minor u hu n).tendsto_cofinite_zero).trans ?_
  refine Real.iSup_le (fun S => ?_) (pow_nonneg hσ0 _)
  exact (norm_minor_le_pow_sum hσ0 w hdiv _).trans
    (pow_le_pow_of_le_one hσ0 hσ1.le (hf _ n S.2))

/-- `{0, …, n-1}` minimises the element sum among `n`-element finsets of `ℕ`, and is the unique
minimiser.  Both halves are proved together, since the induction step for the uniqueness needs
the inequality for the smaller set (and conversely). -/
private theorem sum_range_le_sum_and_eq (n : ℕ) : ∀ S : Finset ℕ, S.card = n →
    ∑ i ∈ Finset.range n, i ≤ ∑ i ∈ S, i ∧
      (∑ i ∈ S, i ≤ ∑ i ∈ Finset.range n, i → S = Finset.range n) := by
  induction n with
  | zero =>
      intro S hS
      rw [Finset.card_eq_zero] at hS
      subst hS
      simp
  | succ k IH =>
      intro S hS
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨M, hMmem, hMmax⟩ : ∃ M ∈ S, ∀ x ∈ S, x ≤ M :=
        ⟨S.max' hne, S.max'_mem hne, fun x hx => S.le_max' x hx⟩
      -- The largest element is at least `k`, since `S ⊆ {0, …, M}` has `k + 1` elements.
      have hMk : k + 1 ≤ M + 1 := by
        have hsub : S ⊆ Finset.range (M + 1) := fun x hx =>
          Finset.mem_range.2 (Nat.lt_succ_of_le (hMmax x hx))
        simpa [hS] using Finset.card_le_card hsub
      have hcardE : (S.erase M).card = k := by
        rw [Finset.card_erase_of_mem hMmem, hS]
        omega
      obtain ⟨hle, heq⟩ := IH _ hcardE
      have hsumS : M + ∑ i ∈ S.erase M, i = ∑ i ∈ S, i :=
        Finset.add_sum_erase S (fun i => i) hMmem
      rw [Finset.sum_range_succ]
      refine ⟨by omega, fun hle2 => ?_⟩
      have hMeq : M = k := by omega
      have hEr : S.erase M = Finset.range k := heq (by omega)
      calc S = insert M (S.erase M) := (Finset.insert_erase hMmem).symm
        _ = insert k (Finset.range k) := by rw [hEr, hMeq]
        _ = Finset.range (k + 1) := Finset.range_add_one.symm

/-- The least row-weight sum for the identity weight on `ℕ`: `0 + 1 + ⋯ + (n−1) = n(n−1)/2`. -/
theorem choose_two_le_sum {S : Finset ℕ} {n : ℕ} (hS : S.card = n) :
    n.choose 2 ≤ ∑ i ∈ S, i := by
  have h := (sum_range_le_sum_and_eq n S hS).1
  rw [Finset.sum_range_id] at h
  rwa [Nat.choose_two_right]

/-- Sums of distinct naturals: an `n`-element finset other than `{0, …, n-1}` has element sum
`> n(n-1)/2` — strictly, hence `≥ n(n-1)/2 + 1`.  ([Jacobs, proof of Thm 2.12]: "the smallest
possible value for the sum of `m` non-negative distinct integers".) -/
theorem choose_two_lt_sum_of_ne_range {S : Finset ℕ} {n : ℕ} (hS : S.card = n)
    (hne : S ≠ Finset.range n) : n.choose 2 + 1 ≤ ∑ i ∈ S, i := by
  obtain ⟨hle, himp⟩ := sum_range_le_sum_and_eq n S hS
  have hlt : ∑ i ∈ Finset.range n, i < ∑ i ∈ S, i :=
    lt_of_le_of_ne hle fun hEq => hne (himp hEq.ge)
  have hch : ∑ i ∈ Finset.range n, i = n.choose 2 := by
    rw [Finset.sum_range_id, Nat.choose_two_right]
  omega

/-- The least row-weight sum for the block weight `(i, m) ↦ m` on `ι × ℕ` with `|ι| = d`:
each value `m` occurs `d` times, so an `n`-element set has weight sum at least
`∑_{k < n} (k / d)`. -/
theorem sum_div_le_sum_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Finset (ι × ℕ)} {n : ℕ} (hS : S.card = n) :
    ∑ k ∈ Finset.range n, k / Fintype.card ι ≤ ∑ p ∈ S, p.2 := by
  induction n generalizing S with
  | zero => simp
  | succ k IH =>
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨M, hMmem, hMmax⟩ := S.exists_max_image Prod.snd hne
      -- `S` sits inside `ι × {0, …, M.2}`, which has `|ι| · (M.2 + 1)` elements.
      have hcard : k + 1 ≤ Fintype.card ι * (M.2 + 1) := by
        have hsub : S ⊆ (Finset.univ : Finset ι) ×ˢ Finset.range (M.2 + 1) := fun p hp =>
          Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_range.2
            (Nat.lt_succ_of_le (hMmax p hp))⟩
        simpa [hS, Finset.card_range] using Finset.card_le_card hsub
      -- Hence the largest second coordinate is at least `⌊k / |ι|⌋`.
      have hdvd : k / Fintype.card ι ≤ M.2 := by
        have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨M.1⟩
        have hk : k < (M.2 + 1) * Fintype.card ι := by
          rw [Nat.mul_comm]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hcard
        exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hpos).2 hk)
      have hcardE : (S.erase M).card = k := by
        rw [Finset.card_erase_of_mem hMmem, hS]
        omega
      have hIH := IH hcardE
      have hsumS : M.2 + ∑ p ∈ S.erase M, p.2 = ∑ p ∈ S, p.2 :=
        Finset.add_sum_erase S (fun p => p.2) hMmem
      rw [Finset.sum_range_succ]
      omega

/-- The slope bound on `c(ℕ, K)` with the identity weight — the shape of [Jacobs, Thm 2.12]. -/
theorem norm_charCoeff_le_pow_choose_two {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {u : c(ℕ, K) →L[K] c(ℕ, K)} (hu : IsCompactoid u)
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ σ ^ j) (n : ℕ) :
    ‖charCoeff u n‖ ≤ σ ^ n.choose 2 :=
  norm_charCoeff_le_pow hσ0 hσ1 hu id hdiv (fun _ _ h => choose_two_le_sum h) n

/-- The slope bound on the block model `c(ι × ℕ, K)`. -/
theorem norm_charCoeff_le_pow_block {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {u : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)} (hu : IsCompactoid u)
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ σ ^ j.2) (n : ℕ) :
    ‖charCoeff u n‖ ≤ σ ^ (∑ k ∈ Finset.range n, k / Fintype.card ι) :=
  norm_charCoeff_le_pow hσ0 hσ1 hu Prod.snd hdiv (fun _ _ h => sum_div_le_sum_block h) n

end TateFredholm
