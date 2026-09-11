/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Fredholm
import PhD.TateFredholm.GenFun

/-!
# Slope bounds for the Fredholm determinant

Row decay of the matrix bounds the coefficients of `det(1 − Tu)` from below in valuation:
if `‖matrixCoeff u j i‖ ≤ σ ^ j` then every `n × n` principal minor is a product of entries
taken from `n` distinct rows, so `‖minor u S‖ ≤ σ ^ (∑_{j ∈ S} j)` and the smallest possible
row sum for `|S| = n` is `0 + 1 + ⋯ + (n−1) = n(n−1)/2`.  Hence

  `‖cₙ(u)‖ ≤ σ ^ (n choose 2)`,

which says the Newton polygon of `det(1 − Tu)` lies on or above the polygon with unit slopes
`0, v(σ), 2v(σ), …` ([Serre1962, §5]).  When the rescaled minors are units the bound is an
equality — [Jacobs, Thm 2.12] proper — and that exact case is proved here too, at an arbitrary
`ϖ` with `‖ϖ‖ < 1`.

Everything here was generalised out of `PhD/JacobsSlash/«1_SlopeTheorem».lean`, whose statements
were pinned at `ϖ = 3` (slopes-hecke board A1/A2, 2026-08-20, and the exact case on 2026-09-01);
that file now keeps only the fork's normalisation `ϖ₃`.

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
  minor is a unit.
* `TateFredholm.norm_charCoeff_of_unit_minors` — **the exact case** ([Jacobs, Thm 2.12] at an
  arbitrary `ϖ`): unit top-left minors of the rescaled matrix `N j i = ϖ⁻ʲ uⱼᵢ` force
  `‖cₘ(u)‖ = ‖ϖ‖ ^ (m.choose 2)`.
* `TateFredholm.val_charCoeff_of_unit_minors` — the same through the additive valuation
  `PseudoUniformizer.val`, normalised by `v_ϖ(ϖ) = 1`: `v_ϖ(cₘ) = m(m−1)/2`.
* `TateFredholm.norm_tsum_eq_of_dominant` — the ultrametric isolated-dominant-term principle
  the equality rests on.
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

/-! ### The exact case: unit minors

[Jacobs, Theorem 2.12]: when the rescaled matrix `N j i = ϖ⁻ʲ · matrixCoeff u j i` has every
top-left minor of norm `1`, the slope bound at the identity weight is an equality.  Three
inputs: the ultrametric dominant-term principle for `tsum`s; the exact contribution of the
principal block `{0, …, m−1}` (row rescaling of determinants); and its strict minimality among
`m`-element index sets (`choose_two_lt_sum_of_ne_range` above). -/

omit [CompleteSpace K] in
/-- A summable family with one term of norm `b` and all others of norm `≤ c < b` has
`‖tsum‖ = b` (ultrametric isolated-dominant-term principle). -/
theorem norm_tsum_eq_of_dominant {ι : Type*} {f : ι → K} (hf : Summable f) (i₀ : ι)
    {c : ℝ} (hc : c < ‖f i₀‖) (h : ∀ i ≠ i₀, ‖f i‖ ≤ c) : ‖∑' i, f i‖ = ‖f i₀‖ := by
  classical
  rw [hf.tsum_eq_add_tsum_ite i₀]
  by_cases hall : ∀ i, i = i₀
  · -- Degenerate case: no other index, so the tail vanishes identically.  (This case must be
    -- separated because `c` may be negative, in which case `h` is vacuous.)
    rw [tsum_congr fun i => if_pos (hall i), tsum_zero, add_zero]
  · obtain ⟨i₁, hi₁⟩ := not_forall.1 hall
    have hc0 : 0 ≤ c := (norm_nonneg (f i₁)).trans (h i₁ hi₁)
    have htail : ‖∑' i, if i = i₀ then (0 : K) else f i‖ ≤ c := by
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hc0 fun i => ?_
      by_cases hi : i = i₀
      · simpa [hi] using hc0
      · simpa [hi] using h i hi
    have hlt : ‖∑' i, if i = i₀ then (0 : K) else f i‖ < ‖f i₀‖ := htail.trans_lt hc
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Row rescaling of determinants: if `A j i = a ^ j * B j i` then
`det A = a ^ (∑ j, j) * det B` — the factorisation `det M_S = ϖ^{∑ rows} · det N_S` behind the
principal-block computation. -/
theorem det_row_smul_pow (a : K) {n : ℕ} (B : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun j i : Fin n => a ^ (j : ℕ) * B j i).det =
      a ^ (∑ j : Fin n, (j : ℕ)) * B.det := by
  rw [Matrix.det_mul_column (fun j : Fin n => a ^ (j : ℕ)) B, Finset.prod_pow_eq_pow_sum]

/-- The tautological identification `Fin m ≃ ↥(Finset.range m)` (both directions are `rfl`,
and `↑(finEquivRange m j) = ↑j` definitionally).  `minor` is indexed by the subtype `↥S` while
the unit-minor hypothesis is indexed by `Fin m`; this is the transport used for the principal
block `S_m = {0, …, m-1}`. -/
private def finEquivRange (m : ℕ) : Fin m ≃ ↥(Finset.range m) where
  toFun j := ⟨(j : ℕ), Finset.mem_range.2 j.2⟩
  invFun x := ⟨(x : ℕ), Finset.mem_range.1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Unit minors force the rescaling element to be nonzero.  No hypothesis on `ϖ` is needed:
were `ϖ = 0` then `ϖ⁻¹ = 0`, so the second row of the rescaled `2 × 2` matrix would vanish and
its determinant would have norm `0`, not `1`. -/
theorem ne_zero_of_unit_minors {ϖ : K} {u : c(ℕ, K) →L[K] c(ℕ, K)}
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => ϖ⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1) :
    ϖ ≠ 0 := by
  intro h0
  have hrow : ∀ i : Fin 2,
      (Matrix.of fun j i : Fin 2 => ϖ⁻¹ ^ (j : ℕ) * matrixCoeff u j i) 1 i = 0 := by
    intro i
    show ϖ⁻¹ ^ (((1 : Fin 2) : ℕ)) * matrixCoeff u 1 i = 0
    rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, h0, inv_zero, pow_one, zero_mul]
  have h := hmin 2
  rw [Matrix.det_eq_zero_of_row_eq_zero 1 hrow, norm_zero] at h
  exact zero_ne_one h

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The principal block contributes exactly `‖ϖ‖ ^ (m(m-1)/2)`: factoring `ϖ ^ j` out of the
`j`-th row of `M_{S_m}` leaves the matrix `N_m` of the unit-minor hypothesis, whence
`‖det M_{S_m}‖ = ‖ϖ‖ ^ (∑_{j < m} j) · 1`. -/
theorem norm_minor_range {ϖ : K} (hne : ϖ ≠ 0) {u : c(ℕ, K) →L[K] c(ℕ, K)}
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => ϖ⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1)
    (m : ℕ) : ‖minor u (Finset.range m)‖ = ‖ϖ‖ ^ m.choose 2 := by
  have hsum : ∑ j : Fin m, (j : ℕ) = m.choose 2 := by
    have hfin : ∑ j : Fin m, (j : ℕ) = ∑ i ∈ Finset.range m, i :=
      Fin.sum_univ_eq_sum_range (fun i => i) m
    rw [hfin, Finset.sum_range_id, Nat.choose_two_right]
  have hdet : minor u (Finset.range m)
      = (Matrix.of fun j i : Fin m => matrixCoeff u (j : ℕ) (i : ℕ)).det :=
    (Matrix.det_submatrix_equiv_self (finEquivRange m) _).symm
  have hfac : (Matrix.of fun j i : Fin m => matrixCoeff u (j : ℕ) (i : ℕ))
      = Matrix.of fun j i : Fin m => ϖ ^ (j : ℕ) *
          (Matrix.of fun j i : Fin m => ϖ⁻¹ ^ (j : ℕ) * matrixCoeff u j i) j i := by
    ext j i
    show matrixCoeff u (j : ℕ) (i : ℕ)
      = ϖ ^ (j : ℕ) * (ϖ⁻¹ ^ (j : ℕ) * matrixCoeff u (j : ℕ) (i : ℕ))
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]
  rw [hdet, hfac, det_row_smul_pow, norm_mul, norm_pow, hmin m, mul_one, hsum]

/-- **[Jacobs, Theorem 2.12]** (norm form, at an arbitrary `ϖ` with `‖ϖ‖ < 1`).  Let `u` be an
operator on `c(ℕ, K)` whose matrix satisfies the divisibility `‖matrixCoeff u j i‖ ≤ ‖ϖ‖ ^ j`
and whose rescaled matrix `N j i = ϖ⁻ʲ · matrixCoeff u j i` has every top-left minor of norm
`1`.  Then `‖c_m(u)‖ = ‖ϖ‖ ^ (m.choose 2)` for every `m` — the slope bound
`norm_charCoeff_le_pow_choose_two` is an equality: the points `(m, m(m−1)/2)` of the Newton
polygon of `det (1 - Tu)` lie on the parabola `½ x (x-1)`. -/
theorem norm_charCoeff_of_unit_minors {ϖ : K} (hϖ : ‖ϖ‖ < 1) (u : c(ℕ, K) →L[K] c(ℕ, K))
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖ϖ‖ ^ j)
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => ϖ⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1)
    (m : ℕ) : ‖charCoeff u m‖ = ‖ϖ‖ ^ m.choose 2 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : {S : Finset ℕ // S.card = m}, (i₀ : Finset ℕ) = Finset.range m :=
    ⟨⟨Finset.range m, Finset.card_range m⟩, rfl⟩
  have hne : ϖ ≠ 0 := ne_zero_of_unit_minors hmin
  have h0 : (0 : ℝ) < ‖ϖ‖ := norm_pos_iff.2 hne
  have hcpt : IsCompactoid u :=
    isCompactoid_of_row_decay' (C := 1) (norm_nonneg ϖ) hϖ fun j i => by
      rw [one_mul]; exact hdiv j i
  -- The principal block `S_m = {0, …, m-1}` contributes exactly `‖ϖ‖ ^ m(m-1)/2`.
  have hdom : ‖minor u (i₀ : Finset ℕ)‖ = ‖ϖ‖ ^ m.choose 2 := by
    rw [hi₀]
    exact norm_minor_range hne hmin m
  -- Every other block is strictly smaller: its row sum exceeds `m(m-1)/2`.
  have hoff : ∀ S ≠ i₀, ‖minor u (S : Finset ℕ)‖ ≤ ‖ϖ‖ ^ (m.choose 2 + 1) := by
    intro S hS
    refine (norm_minor_le_pow_sum (norm_nonneg _) (fun j => j) hdiv _).trans
      (pow_le_pow_of_le_one (norm_nonneg _) hϖ.le ?_)
    exact choose_two_lt_sum_of_ne_range S.2 fun h => hS (Subtype.ext (h.trans hi₀.symm))
  have hc : ‖ϖ‖ ^ (m.choose 2 + 1) < ‖minor u (i₀ : Finset ℕ)‖ := by
    rw [hdom]
    exact pow_lt_pow_right_of_lt_one₀ h0 hϖ (Nat.lt_succ_self _)
  have htsum : ‖∑' S : {S : Finset ℕ // S.card = m}, minor u (S : Finset ℕ)‖
      = ‖minor u (i₀ : Finset ℕ)‖ :=
    norm_tsum_eq_of_dominant (summable_minor u hcpt m) i₀ hc hoff
  rw [charCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, htsum, hdom]

/-- The slope reading of `norm_charCoeff_of_unit_minors` through the additive valuation
`v_ϖ = PseudoUniformizer.val`, normalised by `v_ϖ(ϖ) = 1`:  `v_ϖ(c_m) = m(m-1)/2` — the exact
valuation-sequence input the Newton-polygon machinery consumes (`PhD.NewtonPolygons`). -/
theorem val_charCoeff_of_unit_minors (ϖ : PseudoUniformizer K) (u : c(ℕ, K) →L[K] c(ℕ, K))
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖(ϖ : K)‖ ^ j)
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => (ϖ : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1)
    (m : ℕ) : ϖ.val (charCoeff u m) = (m.choose 2 : ℝ) := by
  have hlt : ‖(ϖ : K)‖ < 1 := by
    rw [PseudoUniformizer.coe_eq]
    exact ϖ.norm_lt_one
  have hnorm := norm_charCoeff_of_unit_minors hlt u hdiv hmin m
  have h0 : (0 : ℝ) < ‖(ϖ : K)‖ := ϖ.norm_pos
  have hlog : Real.log ‖(ϖ : K)‖ ≠ 0 := ϖ.log_norm_neg.ne
  have hne : charCoeff u m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (pow_pos h0 (m.choose 2)).ne' hnorm.symm
  rw [PseudoUniformizer.val_of_ne_zero ϖ hne, hnorm, Real.log_pow, mul_div_assoc,
    div_self hlog, mul_one]

end TateFredholm
