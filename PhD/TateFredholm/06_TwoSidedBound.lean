/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.«05_Fredholm»

/-!
# Two-sided weight bounds for the Fredholm determinant — SKELETON (lwx-halo board)

[LWX, proof of Theorem 3.16] bounds `det(1 − Tu)` for a matrix whose `(a, b)` entry is
divisible by `𝔪^{max(w a − w' b, 0)}` — a *two-sided* (row-minus-column) weight — by
conjugating with the diagonal `diag(T^{w})`.  Principal minors are invariant under
diagonal conjugation, so the same computation runs at the minor level over the
*integral* ring, with no `T⁻¹`: each Leibniz monomial of `minor u S` picks one entry
from every row and every column of `S`, and for a permutation `π` of `S`
`∑_{a ∈ S} w' (π a) = ∑_{a ∈ S} w' a`, so
`‖minor u S‖ ≤ σ ^ (∑_{a ∈ S} w a − ∑_{a ∈ S} w' a)` (truncated subtraction).

Unlike the row-weight file `PhD.TateFredholm.«06_Slopes»` (stated over a field), everything
here runs over an arbitrary complete ultrametric `NormedCommRing` with `‖1‖ = 1` and
carries **no** `IsTate` hypothesis: the definitions consumed (`matrixCoeff`, `minor`,
`charCoeff`) are norm-free, and summability comes from `summable_of_tendsto_cofinite`.

Main declarations:
* `TateFredholm.sum_sub_le_sum_sub_comp` — the permutation inequality
  `∑ w − ∑ w' ≤ ∑_a (w a − w' (π a))` (truncated).
* `TateFredholm.norm_minor_le_pow_sub` — the two-sided Hadamard bound.
* `TateFredholm.summable_minor_of_two_sided` — summability of the `n`-minors from
  cofinite growth of `w − w'`.
* `TateFredholm.norm_charCoeff_le_pow_two_sided` — **the two-sided slope bound**.
* `TateFredholm.sum_comp_div_le_sum_monotone` — the monotone-weight initial-segment
  minimum on `ι × ℕ` (generalises `choose_two_le_sum` and `sum_div_le_sum_block`).
-/

open Filter Topology Finset

noncomputable section

namespace TateFredholm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]
variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
/-- Truncated-subtraction sums against a permutation: for `π : S ≃ S`,
`(∑_{a ∈ S} w a) - (∑_{a ∈ S} w' a) ≤ ∑_{a ∈ S} (w a - w' (π a))` in `ℕ`.
[LWX, proof of Thm 3.16]: the diagonal conjugation `diag(Tʷ)` redistributes the
column weights along the permutation without changing their sum. -/
theorem sum_sub_le_sum_sub_comp (w w' : I → ℕ) (S : Finset I) (π : Equiv.Perm {a // a ∈ S}) :
    (∑ a ∈ S, w a) - (∑ a ∈ S, w' a) ≤
      ∑ a ∈ S.attach, (w a.1 - w' (π a).1) := by
  have hπ : ∑ a ∈ S.attach, w' (π a).1 = ∑ a ∈ S, w' a := by
    rw [← Finset.sum_attach S w']
    exact Finset.sum_equiv π (by simp) fun a _ => rfl
  rw [← Finset.sum_attach S w, ← hπ, tsub_le_iff_right]
  calc ∑ a ∈ S.attach, w a.1
      ≤ ∑ a ∈ S.attach, (w a.1 - w' (π a).1 + w' (π a).1) :=
        Finset.sum_le_sum fun a _ => le_tsub_add
    _ = _ := Finset.sum_add_distrib

omit [CompleteSpace R] in
/-- Ultrametric Hadamard bound with a two-sided weight
([LWX, Thm 3.16 proof, the estimate on `P'`]): if
`‖matrixCoeff u a b‖ ≤ σ ^ (w a - w' b)` for all `a b`, then
`‖minor u S‖ ≤ σ ^ ((∑ a ∈ S, w a) - (∑ a ∈ S, w' a))` (all subtractions truncated). -/
theorem norm_minor_le_pow_sub {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    {u : c(I, R) →L[R] c(I, R)} (w w' : I → ℕ)
    (hdiv : ∀ a b, ‖matrixCoeff u a b‖ ≤ σ ^ (w a - w' b)) (S : Finset I) :
    ‖minor u S‖ ≤ σ ^ ((∑ a ∈ S, w a) - (∑ a ∈ S, w' a)) := by
  rw [minor, Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun τ _ => ?_
  have hsm : ‖Equiv.Perm.sign τ • ∏ i, Matrix.of (fun j i : S => matrixCoeff u j i) (τ i) i‖
      = ‖∏ i, Matrix.of (fun j i : S => matrixCoeff u j i) (τ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h]
    · rw [one_smul]
    · rw [Units.neg_smul, one_smul, norm_neg]
  rw [hsm]
  calc ‖∏ i, Matrix.of (fun j i : S => matrixCoeff u j i) (τ i) i‖
      ≤ ∏ i, ‖Matrix.of (fun j i : S => matrixCoeff u j i) (τ i) i‖ := norm_prod_le _ _
    _ ≤ ∏ i : {a // a ∈ S}, σ ^ (w (τ i).1 - w' i.1) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hdiv (τ i).1 i.1
    _ = σ ^ (∑ i : {a // a ∈ S}, (w (τ i).1 - w' i.1)) :=
        Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ σ ^ ((∑ a ∈ S, w a) - (∑ a ∈ S, w' a)) := by
        refine pow_le_pow_of_le_one hσ0 hσ1 ?_
        have hcomp : ∑ i : {a // a ∈ S}, (w (τ i).1 - w' i.1)
            = ∑ a ∈ S.attach, (w a.1 - w' (τ.symm a).1) := by
          rw [← Finset.univ_eq_attach]
          exact Finset.sum_equiv τ (by simp) fun a _ => by
            rw [Equiv.symm_apply_apply]
        rw [hcomp]
        exact sum_sub_le_sum_sub_comp w w' S τ.symm

/-- The `n`-element minors are summable when the net weight `w − w'` grows cofinitely:
finitely many indices carry net weight below any bar, so finitely many `n`-element
`S` have small weight sum, and the Hadamard bound sends the rest to `0`.
No `IsTate` hypothesis: summability is `summable_of_tendsto_cofinite` over the
complete ultrametric `R`. -/
theorem summable_minor_of_two_sided {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {u : c(I, R) →L[R] c(I, R)} (w w' : I → ℕ)
    (hdiv : ∀ a b, ‖matrixCoeff u a b‖ ≤ σ ^ (w a - w' b))
    (hw : Tendsto (fun a => w a - w' a) cofinite atTop) (n : ℕ) :
    Summable fun S : {S : Finset I // S.card = n} => minor u (S : Finset I) := by
  refine summable_of_tendsto_cofinite ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  -- Tier 1: the finite exceptional set `E₁` where the net weight is `0`, and its
  -- total column excess `C`.
  have hE1 : {a : I | w a - w' a < 1}.Finite := by
    have h := Filter.eventually_cofinite.mp (Filter.tendsto_atTop.mp hw 1)
    simpa [not_le] using h
  set C : ℕ := ∑ a ∈ hE1.toFinset, (w' a - w a) with hCdef
  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one hε hσ1
  -- Tier 2: the exceptional set at the raised bar.
  have hEN : {a : I | w a - w' a < N0 + C + 1}.Finite := by
    have h := Filter.eventually_cofinite.mp (Filter.tendsto_atTop.mp hw (N0 + C + 1))
    simpa [not_le] using h
  -- Bad subsets are contained in the finite `E_N`, hence finitely many.
  have hfin : {T : {S : Finset I // S.card = n} |
      (T : Finset I) ⊆ hEN.toFinset}.Finite := by
    have h1 : {S : Finset I | S ⊆ hEN.toFinset}.Finite := by
      have := hEN.toFinset.powerset.finite_toSet
      refine this.subset fun S hS => ?_
      simpa [Finset.mem_powerset] using hS
    exact h1.preimage Subtype.val_injective.injOn
  refine hfin.subset fun T hT => ?_
  simp only [Set.mem_ofPred_eq, not_lt, dist_zero_right] at hT
  -- `hT : ε ≤ ‖minor u T‖`; show `T ⊆ E_N` by contradiction.
  by_contra hsub
  obtain ⟨a₀, ha₀T, ha₀E⟩ := Finset.not_subset.mp hsub
  have ha₀ : N0 + C + 1 ≤ w a₀ - w' a₀ := by
    have h := ha₀E
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt] at h
    omega
  have ha₀E1 : a₀ ∉ hE1.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt]
    omega
  -- ℤ-level net weight bound: `Σ_T (w − w') ≥ (N0 + C + 1) − C`.
  have hinter : (-(C : ℤ)) ≤ ∑ a ∈ (T : Finset I).filter (fun a => a ∈ hE1.toFinset), ((w a : ℤ) - w' a) := by
    have hterm : ∀ a ∈ (T : Finset I).filter (fun a => a ∈ hE1.toFinset),
        (-((w' a - w a : ℕ) : ℤ)) ≤ (w a : ℤ) - w' a := fun a _ => by omega
    calc (-(C : ℤ)) = -((∑ a ∈ hE1.toFinset, (w' a - w a) : ℕ) : ℤ) := by rw [hCdef]
      _ ≤ -((∑ a ∈ (T : Finset I).filter (fun a => a ∈ hE1.toFinset), (w' a - w a) : ℕ) : ℤ) := by
          have hle : ∑ a ∈ (T : Finset I).filter (fun a => a ∈ hE1.toFinset), (w' a - w a)
              ≤ ∑ a ∈ hE1.toFinset, (w' a - w a) :=
            Finset.sum_le_sum_of_subset fun a ha => (Finset.mem_filter.mp ha).2
          omega
      _ = ∑ a ∈ (T : Finset I).filter (fun a => a ∈ hE1.toFinset), (-((w' a - w a : ℕ) : ℤ)) := by
          push_cast
          rw [← Finset.sum_neg_distrib]
      _ ≤ ∑ a ∈ (T : Finset I).filter (fun a => a ∈ hE1.toFinset), ((w a : ℤ) - w' a) :=
          Finset.sum_le_sum hterm
  have hdiff : ((N0 + C + 1 : ℕ) : ℤ) ≤ ∑ a ∈ (T : Finset I).filter (fun a => a ∉ hE1.toFinset),
      ((w a : ℤ) - w' a) := by
    have ha₀mem : a₀ ∈ (T : Finset I).filter (fun a => a ∉ hE1.toFinset) :=
      Finset.mem_filter.mpr ⟨ha₀T, ha₀E1⟩
    have hnonneg : ∀ a ∈ (T : Finset I).filter (fun a => a ∉ hE1.toFinset), (0 : ℤ) ≤ (w a : ℤ) - w' a := by
      intro a ha
      have := (Finset.mem_filter.mp ha).2
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt] at this
      omega
    have h1 : ((N0 + C + 1 : ℕ) : ℤ) ≤ (w a₀ : ℤ) - w' a₀ := by
      have := ha₀
      omega
    exact h1.trans (Finset.single_le_sum hnonneg ha₀mem)
  have hnet : N0 ≤ (∑ a ∈ (T : Finset I), w a) - (∑ a ∈ (T : Finset I), w' a) := by
    have hsplit : ∑ a ∈ (T : Finset I).filter (fun a => a ∈ hE1.toFinset), ((w a : ℤ) - w' a)
        + ∑ a ∈ (T : Finset I).filter (fun a => a ∉ hE1.toFinset), ((w a : ℤ) - w' a)
        = ∑ a ∈ (T : Finset I), ((w a : ℤ) - w' a) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hcast : ∑ a ∈ (T : Finset I), ((w a : ℤ) - w' a)
        = ((∑ a ∈ (T : Finset I), w a : ℕ) : ℤ)
          - ((∑ a ∈ (T : Finset I), w' a : ℕ) : ℤ) := by
      push_cast
      rw [Finset.sum_sub_distrib]
    omega
  -- Contradiction: the minor is too small.
  have hminor : ‖minor u (T : Finset I)‖ < ε :=
    lt_of_le_of_lt ((norm_minor_le_pow_sub hσ0 hσ1.le w w' hdiv _).trans
      (pow_le_pow_of_le_one hσ0 hσ1.le hnet)) hN0
  exact absurd hT (not_le.mpr hminor)

/-- **The two-sided slope bound** ([LWX, Theorem 3.16], minor-level form): entry bounds
`‖u_{ab}‖ ≤ σ ^ (w a - w' b)`, together with a lower bound `f n` for the net weight sum
`(∑_S w) - (∑_S w')` over every `n`-element `S`, force `‖cₙ(u)‖ ≤ σ ^ f n`. -/
theorem norm_charCoeff_le_pow_two_sided {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {u : c(I, R) →L[R] c(I, R)} (w w' : I → ℕ)
    (hdiv : ∀ a b, ‖matrixCoeff u a b‖ ≤ σ ^ (w a - w' b))
    (hw : Tendsto (fun a => w a - w' a) cofinite atTop) {f : ℕ → ℕ}
    (hf : ∀ S : Finset I, ∀ n : ℕ, S.card = n →
      f n ≤ (∑ a ∈ S, w a) - (∑ a ∈ S, w' a)) (n : ℕ) :
    ‖charCoeff u n‖ ≤ σ ^ f n := by
  rw [charCoeff]
  have hnorm : ‖((-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n},
      minor u (S : Finset I))‖
      = ‖∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)‖ := by
    rcases neg_one_pow_eq_or R n with h | h <;> rw [h]
    · rw [one_mul]
    · rw [neg_one_mul, norm_neg]
  rw [hnorm]
  refine (norm_tsum_le_iSup
    (summable_minor_of_two_sided hσ0 hσ1 w w' hdiv hw n).tendsto_cofinite_zero).trans ?_
  refine Real.iSup_le (fun S => ?_) (pow_nonneg hσ0 _)
  exact (norm_minor_le_pow_sub hσ0 hσ1.le w w' hdiv _).trans
    (pow_le_pow_of_le_one hσ0 hσ1.le (hf _ n S.2))

/-- The monotone-weight initial-segment minimum on `ι × ℕ` with `|ι| = t`: for
monotone `v : ℕ → ℕ`, an `n`-element subset has second-coordinate weight sum at least
`∑_{k < n} v (k / t)` — each value of the second coordinate has only `t` slots.
Generalises `TateFredholm.choose_two_le_sum` (`ι = Unit`, `v = id`) and
`TateFredholm.sum_div_le_sum_block` (`v = id`); proof mirrors the latter's induction. -/
theorem sum_comp_div_le_sum_monotone {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ℕ → ℕ} (hv : Monotone v) {S : Finset (ι × ℕ)} {n : ℕ} (hS : S.card = n) :
    ∑ k ∈ Finset.range n, v (k / Fintype.card ι) ≤ ∑ a ∈ S, v a.2 := by
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
      have hsumS : v M.2 + ∑ p ∈ S.erase M, v p.2 = ∑ p ∈ S, v p.2 :=
        Finset.add_sum_erase S (fun p => v p.2) hMmem
      rw [Finset.sum_range_succ]
      have hvle : v (k / Fintype.card ι) ≤ v M.2 := hv hdvd
      omega

end TateFredholm
