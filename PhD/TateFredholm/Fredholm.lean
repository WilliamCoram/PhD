import PhD.TateFredholm.Matrix
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# The Fredholm determinant
([Bel] §II.1.5 architecture under [JN]'s hypotheses; blueprint 6.16–6.17.  See
`Tate.lean` for the development's overview and dictionary.)

Definitions are norm-free given the topology; the theorems carry `[IsTate R]` (through
the compactness criterion) and **no Noetherian hypothesis** — each statement below
strictly generalises its [JN]-file counterpart. -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Fredholm

variable {R}
variable {I : Type*} [DecidableEq I]

/-- The principal `S × S` minor of the matrix of `u`. -/
def minor (u : c(I, R) →L[R] c(I, R)) (S : Finset I) : R :=
  Matrix.det (Matrix.of fun j i : S => matrixCoeff u j i)

/-- Ultrametric Hadamard bound: a determinant is bounded by the product of row bounds.
Each monomial of the Leibniz expansion is bounded by `∏ j, f j`, and the ultrametric
inequality bounds the sum by the max of its terms. -/
private theorem norm_det_le_of_row_bounds
    {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (f : n → ℝ)
    (hf : ∀ j i, ‖M j i‖ ≤ f j) (hf0 : ∀ j, 0 ≤ f j) :
    ‖M.det‖ ≤ ∏ j, f j := by
  classical
  rw [Matrix.det_apply]
  have hne : (Finset.univ : Finset (Equiv.Perm n)).Nonempty := Finset.univ_nonempty
  refine le_trans (hne.norm_sum_le_sup'_norm _) (Finset.sup'_le _ _ fun σ _ => ?_)
  have hsm : ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ = ‖∏ i, M (σ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
    · rw [one_smul]
    · rw [Units.neg_smul, one_smul, norm_neg]
  rw [hsm]
  calc ‖∏ i, M (σ i) i‖ ≤ ∏ i, ‖M (σ i) i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i, f (σ i) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hf (σ i) i)
    _ = ∏ j, f j := Equiv.prod_comp σ f

/-- Each matrix coefficient is bounded by the operator norm (the `hbound_term` of
`norm_eq_iSup_matrixCoeff`, extracted for reuse). -/
private theorem norm_matrixCoeff_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) (j i : I) :
    ‖matrixCoeff u j i‖ ≤ ‖u‖ := by
  calc ‖matrixCoeff u j i‖ = ‖u (cSpace.single i 1) j‖ := rfl
    _ ≤ ‖u (cSpace.single i 1)‖ := cSpace.norm_apply_le _ _
    _ ≤ ‖u‖ * ‖cSpace.single i (1 : R)‖ := le_opNorm _ _
    _ = ‖u‖ := by rw [cSpace.norm_single_one, mul_one]


/-- Each matrix coefficient is bounded by its row sup `r_j = ⨆ i, ‖a_{ji}‖`. -/
private theorem norm_matrixCoeff_le_rowNorm [IsTate R] (u : c(I, R) →L[R] c(I, R)) (j i : I) :
    ‖matrixCoeff u j i‖ ≤ rowNorm u j :=
  le_ciSup ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact norm_matrixCoeff_le u j i⟩ i

/-- The row sup is bounded by the operator norm. -/
private theorem rowNorm_le_opNorm [IsTate R] (u : c(I, R) →L[R] c(I, R)) (j : I) :
    rowNorm u j ≤ ‖u‖ :=
  Real.iSup_le (fun i => norm_matrixCoeff_le u j i) (opNorm_nonneg u)

/-- `‖(-1)ⁿ‖ = 1` in a norm-one normed ring. -/
private theorem norm_neg_one_pow (m : ℕ) : ‖(-1 : R) ^ m‖ = 1 := by
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow, norm_one]
  · rw [ho.neg_one_pow, norm_neg, norm_one]

/-- The ultrametric Hadamard bound for a principal minor: `‖det(minor)‖ ≤ ∏_{j ∈ S} r_j`. -/
private theorem norm_minor_le_prod [IsTate R] (u : c(I, R) →L[R] c(I, R)) (S : Finset I) :
    ‖minor u S‖ ≤ ∏ j ∈ S, rowNorm u j := by
  have h := norm_det_le_of_row_bounds (Matrix.of fun j i : S => matrixCoeff u (j : I) (i : I))
    (fun j : S => rowNorm u (j : I))
    (fun j i => norm_matrixCoeff_le_rowNorm u _ _) (fun _ => rowNorm_nonneg u _)
  rwa [Finset.prod_coe_sort (s := S) (f := rowNorm u)] at h

/-- The degree-`n` minors vanish cofinitely (ultrametric Hadamard bound + row decay): for `δ`
small, a minor of norm `≥ ε` forces its index set inside the finite "large-row" set, and there
are only finitely many `n`-subsets of a finite set.  This is the engine of `summable_minor`
and of the two `norm_tsum_le_iSup` estimates below. -/
private theorem tendsto_minor_cofinite [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (n : ℕ) :
    Tendsto (fun S : {S : Finset I // S.card = n} => minor u (S : Finset I)) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set D : ℝ := max ‖u‖ 1 with hD
  have hD1 : (1 : ℝ) ≤ D := le_max_right _ _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  set δ : ℝ := ε / D ^ (n - 1) with hδdef
  have hδ0 : 0 < δ := div_pos hε (pow_pos hD0 _)
  have hbad : {j : I | δ ≤ rowNorm u j}.Finite := by
    have hev : ∀ᶠ j in cofinite, rowNorm u j < δ := by
      filter_upwards [Metric.tendsto_nhds.1 hu δ hδ0] with j hj
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at hj
    simpa only [not_lt] using Filter.eventually_cofinite.1 hev
  have hfin : (Subtype.val ⁻¹' ↑(hbad.toFinset.powersetCard n) :
      Set {S : Finset I // S.card = n}).Finite :=
    Set.Finite.preimage Subtype.coe_injective.injOn
      (hbad.toFinset.powersetCard n).finite_toSet
  refine hfin.subset fun S hS => ?_
  rw [Set.mem_setOf_eq, not_lt, dist_eq_norm, sub_zero] at hS
  rw [Set.mem_preimage, Finset.mem_coe, Finset.mem_powersetCard]
  refine ⟨?_, S.2⟩
  by_contra hsub
  rw [Finset.not_subset] at hsub
  obtain ⟨j₀, hj₀S, hj₀B⟩ := hsub
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hj₀B
  have hbound : ‖minor u (S : Finset I)‖ < ε := by
    calc ‖minor u (S : Finset I)‖ ≤ ∏ j ∈ (S : Finset I), rowNorm u j := norm_minor_le_prod u _
      _ = rowNorm u j₀ * ∏ j ∈ (S : Finset I).erase j₀, rowNorm u j :=
          (Finset.mul_prod_erase _ _ hj₀S).symm
      _ ≤ rowNorm u j₀ * D ^ (n - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (rowNorm_nonneg u j₀)
          calc ∏ j ∈ (S : Finset I).erase j₀, rowNorm u j
              ≤ ∏ _j ∈ (S : Finset I).erase j₀, D :=
                Finset.prod_le_prod (fun j _ => rowNorm_nonneg u j)
                  (fun j _ => (rowNorm_le_opNorm u j).trans (le_max_left _ _))
            _ = D ^ (n - 1) := by
                rw [Finset.prod_const, Finset.card_erase_of_mem hj₀S, S.2]
      _ < δ * D ^ (n - 1) := mul_lt_mul_of_pos_right hj₀B (pow_pos hD0 _)
      _ = ε := by rw [hδdef, div_mul_cancel₀ ε (pow_ne_zero _ hD0.ne')]
  exact absurd hS (not_le.2 hbound)

/-- Summability of the degree-`n` minors (ultrametric Hadamard bound + row decay). -/
theorem summable_minor [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (n : ℕ) :
    Summable fun S : {S : Finset I // S.card = n} => minor u (S : Finset I) :=
  summable_of_tendsto_cofinite (tendsto_minor_cofinite u hu n)

/-- The `n`-th coefficient `cₙ = (−1)ⁿ ∑_{|S| = n} det(minor)` of `det(1 − Tu)`. -/
def charCoeff (u : c(I, R) →L[R] c(I, R)) (n : ℕ) : R :=
  (-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)

/-- The *Fredholm determinant* (characteristic power series) `det(1 − Tu) ∈ R⟦T⟧`. -/
def charPowerSeries (u : c(I, R) →L[R] c(I, R)) : PowerSeries R :=
  PowerSeries.mk (charCoeff u)

@[simp] theorem charPowerSeries_coeff (u : c(I, R) →L[R] c(I, R)) (n : ℕ) :
    PowerSeries.coeff n (charPowerSeries u) = charCoeff u n :=
  PowerSeries.coeff_mk n _

/-- `c₀ = 1`: the determinant is a Fredholm series. -/
@[simp] theorem charCoeff_zero (u : c(I, R) →L[R] c(I, R)) : charCoeff u 0 = 1 := by
  have hunique : ∀ S : {S : Finset I // S.card = 0}, S = ⟨∅, Finset.card_empty⟩ := by
    rintro ⟨S, hS⟩
    exact Subtype.ext (Finset.card_eq_zero.1 hS)
  have htsum : (∑' S : {S : Finset I // S.card = 0}, minor u (S : Finset I))
      = minor u (∅ : Finset I) :=
    tsum_eq_single (⟨∅, Finset.card_empty⟩ : {S : Finset I // S.card = 0})
      fun b hb => absurd (hunique b) hb
  have hdet : minor u (∅ : Finset I) = 1 := by
    have : IsEmpty ((∅ : Finset I) : Type _) := Finset.isEmpty_coe_sort.2 rfl
    exact Matrix.det_isEmpty
  rw [charCoeff, htsum, hdet, pow_zero, one_mul]

/-- The Fredholm determinant is entire ([Bel] Lemma II.1.14): it is a restricted power series
(`PowerSeries.IsRestricted`) at *every* radius `C > 0`, i.e. it lies in `R{{T}}`.  All but `b`
rows have sup `< δ`, so an `n`-minor is bounded by `Dᵇ δ^(n−b)`, beating any geometric growth. -/
theorem charPowerSeries_isEntire [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (C : ℝ) (hC : 0 < C) :
    PowerSeries.IsRestricted C (charPowerSeries u) := by
  rw [PowerSeries.isRestricted_iff']
  simp only [charPowerSeries_coeff]
  set δ : ℝ := min (1 / (2 * C)) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδC : δ * C ≤ 1 / 2 := by
    calc δ * C ≤ 1 / (2 * C) * C := mul_le_mul_of_nonneg_right (min_le_left _ _) hC.le
    _ = 1 / 2 := by field_simp
  set D : ℝ := max ‖u‖ 1 with hDdef
  have hD1 : (1 : ℝ) ≤ D := le_max_right _ _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hbad : {j : I | δ ≤ rowNorm u j}.Finite := by
    have hev : ∀ᶠ j in cofinite, rowNorm u j < δ := by
      filter_upwards [Metric.tendsto_nhds.1 hu δ hδ0] with j hj
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at hj
    simpa only [not_lt] using Filter.eventually_cofinite.1 hev
  set b : ℕ := hbad.toFinset.card with hbdef
  have hminor : ∀ n, ∀ S : {S : Finset I // S.card = n},
      ‖minor u (S : Finset I)‖ ≤ D ^ b * δ ^ (n - b) := by
    intro n S
    refine (norm_minor_le_prod u _).trans ?_
    have hunion : ∏ j ∈ (S : Finset I), rowNorm u j
        = (∏ j ∈ (S : Finset I).filter (fun j => δ ≤ rowNorm u j), rowNorm u j)
          * ∏ j ∈ (S : Finset I).filter (fun j => ¬ δ ≤ rowNorm u j), rowNorm u j :=
      (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hcb : ((S : Finset I).filter (fun j => δ ≤ rowNorm u j)).card ≤ b := by
      refine Finset.card_le_card fun j hj => ?_
      rw [Finset.mem_filter] at hj
      exact hbad.mem_toFinset.2 hj.2
    have hcs : n - b ≤ ((S : Finset I).filter (fun j => ¬ δ ≤ rowNorm u j)).card := by
      have hsplit : ((S : Finset I).filter (fun j => δ ≤ rowNorm u j)).card
          + ((S : Finset I).filter (fun j => ¬ δ ≤ rowNorm u j)).card = n := by
        rw [Finset.card_filter_add_card_filter_not, S.2]
      omega
    rw [hunion]
    refine mul_le_mul ?_ ?_
      (Finset.prod_nonneg fun j _ => rowNorm_nonneg u j) (pow_nonneg hD0.le b)
    · calc ∏ j ∈ (S : Finset I).filter (fun j => δ ≤ rowNorm u j), rowNorm u j
          ≤ ∏ _j ∈ (S : Finset I).filter (fun j => δ ≤ rowNorm u j), D :=
            Finset.prod_le_prod (fun j _ => rowNorm_nonneg u j)
              (fun j _ => (rowNorm_le_opNorm u j).trans (le_max_left _ _))
      _ = D ^ ((S : Finset I).filter (fun j => δ ≤ rowNorm u j)).card :=
            Finset.prod_const D
      _ ≤ D ^ b := pow_le_pow_right₀ hD1 hcb
    · calc ∏ j ∈ (S : Finset I).filter (fun j => ¬ δ ≤ rowNorm u j), rowNorm u j
          ≤ ∏ _j ∈ (S : Finset I).filter (fun j => ¬ δ ≤ rowNorm u j), δ := by
            refine Finset.prod_le_prod (fun j _ => rowNorm_nonneg u j) fun j hj => ?_
            rw [Finset.mem_filter, not_le] at hj
            exact hj.2.le
      _ = δ ^ ((S : Finset I).filter (fun j => ¬ δ ≤ rowNorm u j)).card :=
            Finset.prod_const δ
      _ ≤ δ ^ (n - b) := pow_le_pow_of_le_one hδ0.le hδ1 hcs
  have hcoeff : ∀ n, ‖charCoeff u n‖ ≤ D ^ b * δ ^ (n - b) := by
    intro n
    rw [charCoeff]
    have hbound_nonneg : (0 : ℝ) ≤ D ^ b * δ ^ (n - b) :=
      mul_nonneg (pow_nonneg hD0.le _) (pow_nonneg hδ0.le _)
    calc ‖(-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)‖
        ≤ ‖(-1 : R) ^ n‖ * ‖∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)‖ :=
          norm_mul_le _ _
    _ = ‖∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)‖ := by
          rw [norm_neg_one_pow, one_mul]
    _ ≤ ⨆ S : {S : Finset I // S.card = n}, ‖minor u (S : Finset I)‖ :=
          norm_tsum_le_iSup (tendsto_minor_cofinite u hu n)
    _ ≤ D ^ b * δ ^ (n - b) := Real.iSup_le (fun S => hminor n S) hbound_nonneg
  have hgeom : Tendsto (fun n : ℕ => (D / δ) ^ b * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using h2.const_mul ((D / δ) ^ b)
  refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
    mul_nonneg (norm_nonneg _) (pow_nonneg hC.le n)) ?_ hgeom
  rw [Filter.eventually_atTop]
  refine ⟨b, fun n hn => ?_⟩
  have h1 : ‖charCoeff u n‖ * C ^ n ≤ D ^ b * δ ^ (n - b) * C ^ n :=
    mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg hC.le n)
  refine h1.trans ?_
  have hδn : δ ^ (n - b) = δ ^ n / δ ^ b := pow_sub₀ δ hδ0.ne' hn
  have hrew : D ^ b * (δ ^ n / δ ^ b) * C ^ n = (D / δ) ^ b * (δ * C) ^ n := by
    rw [div_pow, mul_pow]
    ring
  rw [hδn, hrew]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (div_nonneg hD0.le hδ0.le) b)
  exact pow_le_pow_left₀ (mul_nonneg hδ0.le hC.le) hδC n

/-- Row-telescoping bound for a difference of determinants: swap the rows of `B` for
those of `A` one at a time; each swap costs one `det` with a single `(A − B)`-row,
bounded by the Hadamard estimate. -/
private theorem norm_det_sub_det_le [IsTate R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι R) (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hA : ∀ p q, ‖A p q‖ ≤ M) (hB : ∀ p q, ‖B p q‖ ≤ M)
    (hAB : ∀ p q, ‖A p q - B p q‖ ≤ ε) (hcard : 1 ≤ Fintype.card ι) :
    ‖A.det - B.det‖ ≤ M ^ (Fintype.card ι - 1) * ε := by
  classical
  set m : ℕ := Fintype.card ι with hm
  obtain ⟨e⟩ : Nonempty (Fin m ≃ ι) := ⟨(Fintype.equivFin ι).symm⟩
  -- the hybrid matrices: rows enumerated before `t` come from `A`, the rest from `B`
  set H : ℕ → Matrix ι ι R :=
    fun t => Matrix.of fun p q => if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q
    with hH
  have hH0 : H 0 = B := by
    ext p q
    show (if ((e.symm p : Fin m) : ℕ) < 0 then A p q else B p q) = B p q
    exact if_neg (Nat.not_lt_zero _)
  have hHm : H m = A := by
    ext p q
    show (if ((e.symm p : Fin m) : ℕ) < m then A p q else B p q) = A p q
    exact if_pos (e.symm p).2
  have htele : A.det - B.det
      = ∑ t ∈ Finset.range m, ((H (t + 1)).det - (H t).det) := by
    rw [Finset.sum_range_sub (fun t => (H t).det), hH0, hHm]
  rw [htele]
  have hne : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.2 hcard⟩
  refine (hne.norm_sum_le_sup'_norm _).trans ((Finset.sup'_le _ _) fun t ht => ?_)
  rw [Finset.mem_range] at ht
  -- the two hybrids differ in row `e t` only
  have hupdate : H (t + 1) = (H t).updateRow (e ⟨t, ht⟩) fun q => A (e ⟨t, ht⟩) q := by
    ext p q
    rw [Matrix.updateRow_apply]
    by_cases hp : p = e ⟨t, ht⟩
    · subst hp
      rw [if_pos rfl]
      show (if ((e.symm (e ⟨t, ht⟩) : Fin m) : ℕ) < t + 1 then A _ q else B _ q) = A _ q
      rw [Equiv.symm_apply_apply]
      exact if_pos (Nat.lt_succ_self t)
    · rw [if_neg hp]
      show (if ((e.symm p : Fin m) : ℕ) < t + 1 then A p q else B p q)
        = (if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q)
      have hne' : ((e.symm p : Fin m) : ℕ) ≠ t := fun h => by
        refine hp ?_
        have heq : e.symm p = ⟨t, ht⟩ := Fin.ext h
        rw [← heq, Equiv.apply_symm_apply]
      by_cases hc : ((e.symm p : Fin m) : ℕ) < t
      · rw [if_pos (Nat.lt_succ_of_lt hc), if_pos hc]
      · have hnot : ¬ ((e.symm p : Fin m) : ℕ) < t + 1 := fun h =>
          hc (lt_of_le_of_ne (Nat.lt_succ_iff.1 h) hne')
        rw [if_neg hnot, if_neg hc]
  -- row `e t` of `H t` is the `B`-row, so the difference is a single-row determinant
  have hBrow : H t = (H t).updateRow (e ⟨t, ht⟩) fun q => B (e ⟨t, ht⟩) q := by
    ext p q
    rw [Matrix.updateRow_apply]
    by_cases hp : p = e ⟨t, ht⟩
    · subst hp
      rw [if_pos rfl]
      show (if ((e.symm (e ⟨t, ht⟩) : Fin m) : ℕ) < t then A _ q else B _ q) = B _ q
      rw [Equiv.symm_apply_apply]
      exact if_neg (lt_irrefl t)
    · rw [if_neg hp]
  have hdiff : (H (t + 1)).det - (H t).det
      = ((H t).updateRow (e ⟨t, ht⟩) fun q =>
          A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q).det := by
    have hadd := Matrix.det_updateRow_add (H t) (e ⟨t, ht⟩)
      (fun q => A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q) (fun q => B (e ⟨t, ht⟩) q)
    have hfun : (fun q => A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q)
        + (fun q => B (e ⟨t, ht⟩) q) = fun q => A (e ⟨t, ht⟩) q := by
      funext q
      show A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q + B (e ⟨t, ht⟩) q = A (e ⟨t, ht⟩) q
      rw [sub_add_cancel]
    rw [hfun] at hadd
    rw [hupdate]
    nth_rewrite 2 [hBrow]
    rw [hadd]
    ring
  rw [hdiff]
  have hHtb : ∀ p q, ‖H t p q‖ ≤ M := fun p q => by
    show ‖if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q‖ ≤ M
    split
    · exact hA p q
    · exact hB p q
  refine (norm_det_le_of_row_bounds _
    (fun p => if p = e ⟨t, ht⟩ then ε else M) (fun p q => ?_) (fun p => ?_)).trans ?_
  · rw [Matrix.updateRow_apply]
    by_cases hp : p = e ⟨t, ht⟩
    · rw [if_pos hp]
      show ‖A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q‖ ≤ if p = e ⟨t, ht⟩ then ε else M
      rw [if_pos hp]
      exact hAB _ _
    · rw [if_neg hp]
      show ‖H t p q‖ ≤ if p = e ⟨t, ht⟩ then ε else M
      rw [if_neg hp]
      exact hHtb p q
  · show (0 : ℝ) ≤ if p = e ⟨t, ht⟩ then ε else M
    split
    · exact hε
    · exact hM
  · have hprod : (∏ p : ι, if p = e ⟨t, ht⟩ then ε else M) = ε * M ^ (m - 1) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (e ⟨t, ht⟩)), if_pos rfl]
      congr 1
      rw [Finset.prod_congr rfl (fun p hp => if_neg (Finset.mem_erase.1 hp).1),
        Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [hprod, mul_comm]

/-- **Quantitative continuity** ([Bel] Lemma II.1.15):
`‖cₙ(u) − cₙ(v)‖ ≤ max(‖u‖,‖v‖)^{n−1}‖u − v‖` — the estimate powering every limit
argument in this section. -/
theorem norm_charCoeff_sub_le [IsTate R] (u v : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (hv : IsCompactoid v)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖charCoeff u n - charCoeff v n‖ ≤ max ‖u‖ ‖v‖ ^ (n - 1) * ‖u - v‖ := by
  have hMx0 : (0 : ℝ) ≤ max ‖u‖ ‖v‖ := le_trans (opNorm_nonneg u) (le_max_left _ _)
  have hnonneg : (0 : ℝ) ≤ max ‖u‖ ‖v‖ ^ (n - 1) * ‖u - v‖ :=
    mul_nonneg (pow_nonneg hMx0 _) (opNorm_nonneg _)
  have hdiffS : ∀ S : {S : Finset I // S.card = n},
      ‖minor u (S : Finset I) - minor v (S : Finset I)‖
        ≤ max ‖u‖ ‖v‖ ^ (n - 1) * ‖u - v‖ := by
    intro S
    have hres := norm_det_sub_det_le
      (Matrix.of fun j i : (S : Finset I) => matrixCoeff u (j : I) (i : I))
      (Matrix.of fun j i : (S : Finset I) => matrixCoeff v (j : I) (i : I))
      (max ‖u‖ ‖v‖) ‖u - v‖ hMx0 (opNorm_nonneg _)
      (fun p q => (norm_matrixCoeff_le u _ _).trans (le_max_left _ _))
      (fun p q => (norm_matrixCoeff_le v _ _).trans (le_max_right _ _))
      (fun p q => by
        show ‖matrixCoeff u (p : I) (q : I) - matrixCoeff v (p : I) (q : I)‖ ≤ ‖u - v‖
        rw [← matrixCoeff_sub]
        exact norm_matrixCoeff_le (u - v) _ _)
      (by rw [Fintype.card_coe, S.2]; exact hn)
    rwa [Fintype.card_coe, S.2] at hres
  have hsub_tendsto : Tendsto (fun S : {S : Finset I // S.card = n} =>
      minor u (S : Finset I) - minor v (S : Finset I)) cofinite (𝓝 0) := by
    simpa using (tendsto_minor_cofinite u hu n).sub (tendsto_minor_cofinite v hv n)
  have htsum : charCoeff u n - charCoeff v n
      = (-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n},
          (minor u (S : Finset I) - minor v (S : Finset I)) := by
    rw [charCoeff, charCoeff, ← mul_sub]
    congr 1
    exact (((summable_minor u hu n).hasSum.sub
      (summable_minor v hv n).hasSum).tsum_eq).symm
  rw [htsum]
  calc ‖(-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n},
        (minor u (S : Finset I) - minor v (S : Finset I))‖
      ≤ ‖(-1 : R) ^ n‖ * ‖∑' S : {S : Finset I // S.card = n},
        (minor u (S : Finset I) - minor v (S : Finset I))‖ := norm_mul_le _ _
  _ = ‖∑' S : {S : Finset I // S.card = n},
        (minor u (S : Finset I) - minor v (S : Finset I))‖ := by
      rw [norm_neg_one_pow, one_mul]
  _ ≤ ⨆ S : {S : Finset I // S.card = n},
        ‖minor u (S : Finset I) - minor v (S : Finset I)‖ :=
      norm_tsum_le_iSup hsub_tendsto
  _ ≤ max ‖u‖ ‖v‖ ^ (n - 1) * ‖u - v‖ := Real.iSup_le hdiffS hnonneg

/-- Principal-minor expansion of `det(1 − t·A)` over any commutative ring: it is the sum
over subsets `s` of the scaled principal minors `(−t)^{|s|}·det(A_s)` — the algebraic heart
of the identity `cₙ = coeffₙ det(1 − TA)`. Proved by row-multilinearity of the determinant
(`map_add_univ`) followed by block-triangular evaluation of each piecewise matrix. -/
private theorem det_one_sub_smul_eq_sum {K : Type*} [CommRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : K) (A : Matrix ι ι K) :
    (1 - t • A).det =
      ∑ s : Finset ι, (-t) ^ s.card * (A.toSquareBlockProp (· ∈ s)).det := by
  have key : (1 - t • A).det
      = ∑ s : Finset ι, Matrix.detRowAlternating
          (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K)) := by
    rw [show (1 - t • A : Matrix ι ι K) = (-(t • A)) + 1 from by abel]
    exact (Matrix.detRowAlternating (R := K) (n := ι)).map_add_univ _ _
  rw [key]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show Matrix.detRowAlternating (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K))
        = Matrix.det (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K)) from rfl]
  have hzero : ∀ i, ¬ (i ∈ s) → ∀ j, (j ∈ s) →
      (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K)) i j = 0 := by
    intro i hi j hj
    rw [Finset.piecewise_eq_of_notMem s (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K) hi]
    exact Matrix.one_apply_ne (by rintro rfl; exact hi hj)
  rw [Matrix.twoBlockTriangular_det _ (· ∈ s) hzero]
  have hid : (Matrix.toSquareBlockProp
      (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K)) (fun i => ¬ (i ∈ s))).det = 1 := by
    have hmat : Matrix.toSquareBlockProp
        (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K)) (fun i => ¬ (i ∈ s)) = 1 := by
      ext a b
      rw [Matrix.toSquareBlockProp_def (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K))
            (fun i => ¬ (i ∈ s)),
          Matrix.of_apply, Finset.piecewise_eq_of_notMem s (-(t • A) : Matrix ι ι K)
            (1 : Matrix ι ι K) a.2]
      simp [Matrix.one_apply, Subtype.ext_iff]
    rw [hmat, Matrix.det_one]
  have hblk : Matrix.toSquareBlockProp
      (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K)) (· ∈ s)
      = (-t) • (A.toSquareBlockProp (· ∈ s)) := by
    ext a b
    rw [Matrix.toSquareBlockProp_def
          (s.piecewise (-(t • A) : Matrix ι ι K) (1 : Matrix ι ι K)) (· ∈ s),
        Matrix.of_apply, Finset.piecewise_eq_of_mem s (-(t • A) : Matrix ι ι K)
          (1 : Matrix ι ι K) a.2]
    simp [Matrix.toSquareBlockProp_def, Matrix.smul_apply, Matrix.neg_apply]
  rw [hid, mul_one, hblk]
  convert Matrix.det_smul (A.toSquareBlockProp (· ∈ s)) (-t) using 3
  exact (Fintype.card_coe s).symm

/-- The principal `T`-minor of a matrix (`T ⊆ S`) is the `S×S` principal block on the image
of `T` in the subtype `↥S`.  Reindexing bookkeeping (`det_submatrix_equiv_self`) that lets the
`↥S`-indexed determinant expansion talk back to the `↥T`-indexed minors of the tsum. -/
private theorem det_toSquareBlockProp_subtype {I : Type*} [DecidableEq I] {R : Type*} [CommRing R]
    (M : Matrix I I R) (S T : Finset I) (hTS : T ⊆ S) :
    ((M.submatrix (fun x : S => (x : I)) (fun x : S => (x : I))).toSquareBlockProp
        (· ∈ T.subtype (· ∈ S))).det
      = (M.submatrix (fun a : T => (a : I)) (fun a : T => (a : I))).det := by
  let e : {x : {x // x ∈ S} // x ∈ T.subtype (· ∈ S)} ≃ {y // y ∈ T} :=
    { toFun := fun b => ⟨b.1.1, Finset.mem_subtype.1 b.2⟩
      invFun := fun a => ⟨⟨a.1, hTS a.2⟩, Finset.mem_subtype.2 a.2⟩
      left_inv := fun b => by ext; rfl
      right_inv := fun a => by ext; rfl }
  rw [Matrix.toSquareBlockProp_def]
  rw [show (Matrix.of fun i j : {x : {x // x ∈ S} // x ∈ T.subtype (· ∈ S)} =>
        (M.submatrix (fun x : {x // x ∈ S} => (x : I)) (fun x : {x // x ∈ S} => (x : I))) i j)
        = (M.submatrix (fun a : {y // y ∈ T} => (a : I))
            (fun a : {y // y ∈ T} => (a : I))).submatrix e e from ?_]
  · exact Matrix.det_submatrix_equiv_self e _
  · ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    rfl

/-- Compatibility with the algebraic determinant for row-supported operators
([Bel] (II.1.2); no compactness needed). -/
theorem charCoeff_eq_det_coeff (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (n : ℕ) :
    charCoeff u n =
      (Matrix.det (1 - (Polynomial.X : Polynomial R) •
        Matrix.of fun j i : S => Polynomial.C (matrixCoeff u j i))).coeff n := by
  classical
  set MI : Matrix I I R := Matrix.of fun j i : I => matrixCoeff u j i with hMI
  set MS : Matrix S S R :=
    MI.submatrix (fun x : S => (x : I)) (fun x : S => (x : I)) with hMS
  set d : Finset {x // x ∈ S} → R := fun s => (MS.toSquareBlockProp (· ∈ s)).det with hd
  -- The RHS matrix is `MS.map C`.
  have hBmap : (Matrix.of fun j i : S => Polynomial.C (matrixCoeff u j i))
      = MS.map (Polynomial.C : R →+* Polynomial R) := by
    ext a b
    rw [hMS, hMI]
    simp [Matrix.map_apply, Matrix.submatrix_apply, Matrix.of_apply]
  -- Pull `C` out of each principal block determinant.
  have hmapdet : ∀ s : Finset {x // x ∈ S},
      ((MS.map (Polynomial.C : R →+* Polynomial R)).toSquareBlockProp (· ∈ s)).det
        = Polynomial.C (d s) := by
    intro s
    rw [show (MS.map (Polynomial.C : R →+* Polynomial R)).toSquareBlockProp (· ∈ s)
          = (MS.toSquareBlockProp (· ∈ s)).map (Polynomial.C : R →+* Polynomial R) from rfl]
    exact (RingHom.map_det (Polynomial.C : R →+* Polynomial R)
      (MS.toSquareBlockProp (· ∈ s))).symm
  -- Coefficient of each summand of the determinant expansion.
  have hterm : ∀ (k : ℕ) (c : R),
      ((-Polynomial.X : Polynomial R) ^ k * Polynomial.C c).coeff n
        = if n = k then (-1) ^ n * c else 0 := by
    intro k c
    rw [Polynomial.coeff_mul_C, neg_pow,
      show ((-1 : Polynomial R) ^ k) = Polynomial.C ((-1 : R) ^ k) by
        rw [Polynomial.C_pow]; norm_num,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs with h
    · subst h; ring
    · ring
  -- Row-supported minors vanish off `S`.
  have hminor0 : ∀ T : Finset I, ¬ (T ⊆ S) → minor u T = 0 := by
    intro T hT
    obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.1 hT
    rw [show minor u T = Matrix.det (Matrix.of fun j i : T => matrixCoeff u ↑j ↑i) from rfl]
    exact Matrix.det_eq_zero_of_row_eq_zero (⟨j, hjT⟩ : {x // x ∈ T}) (fun i => hS j hjS _)
  -- Each `T ⊆ S` minor is the corresponding `S`-block determinant.
  have hfg : ∀ T : Finset I, T ⊆ S → minor u T = d (T.subtype (· ∈ S)) := by
    intro T hTS
    rw [show minor u T = Matrix.det (Matrix.of fun j i : T => matrixCoeff u ↑j ↑i) from rfl, hd]
    show Matrix.det (Matrix.of fun j i : T => matrixCoeff u ↑j ↑i)
        = (MS.toSquareBlockProp (· ∈ T.subtype (· ∈ S))).det
    rw [hMS, det_toSquareBlockProp_subtype MI S T hTS, hMI]
    rfl
  -- The tsum collapses onto the finite family of subsets of `S`.
  have hLHS : (∑' T : {T : Finset I // T.card = n}, minor u (T : Finset I))
      = ∑ s ∈ Finset.univ.filter (fun s : Finset {x // x ∈ S} => n = s.card), d s := by
    rw [tsum_eq_sum (s := (S.powersetCard n).subtype (fun T => T.card = n)) ?_]
    · rw [Finset.sum_subtype_eq_sum_filter,
        Finset.filter_true_of_mem (fun T hT => (Finset.mem_powersetCard.1 hT).2)]
      refine Finset.sum_nbij' (fun T => T.subtype (· ∈ S))
        (fun s => s.map (Function.Embedding.subtype _)) ?_ ?_ ?_ ?_ ?_
      · intro T hT
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [Finset.card_subtype,
          Finset.filter_true_of_mem (fun x hx => (Finset.mem_powersetCard.1 hT).1 hx)]
        exact ((Finset.mem_powersetCard.1 hT).2).symm
      · intro s hs
        rw [Finset.mem_powersetCard]
        refine ⟨fun x hx => ?_, ?_⟩
        · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
          exact a.2
        · rw [Finset.card_map]; exact ((Finset.mem_filter.1 hs).2).symm
      · intro T hT
        show (T.subtype (· ∈ S)).map (Function.Embedding.subtype _) = T
        rw [Finset.subtype_map,
          Finset.filter_true_of_mem (fun x hx => (Finset.mem_powersetCard.1 hT).1 hx)]
      · intro s _
        show (s.map (Function.Embedding.subtype _)).subtype (· ∈ S) = s
        ext x
        simp [Finset.mem_subtype, Finset.mem_map]
      · intro T hT
        exact hfg T (Finset.mem_powersetCard.1 hT).1
    · intro b hb
      exact hminor0 _ fun hbS =>
        hb (Finset.mem_subtype.2 (Finset.mem_powersetCard.2 ⟨hbS, b.2⟩))
  -- Each summand's coefficient, via `hmapdet` and `hterm`.
  have hsummand : ∀ s : Finset {x // x ∈ S},
      ((-Polynomial.X : Polynomial R) ^ s.card *
        ((MS.map (Polynomial.C : R →+* Polynomial R)).toSquareBlockProp (· ∈ s)).det).coeff n
        = if n = s.card then (-1) ^ n * d s else 0 := fun s => by
    rw [hmapdet s, hterm s.card (d s)]
  rw [show charCoeff u n
        = (-1 : R) ^ n * ∑' T : {T : Finset I // T.card = n}, minor u (T : Finset I) from rfl,
    hLHS, hBmap, det_one_sub_smul_eq_sum, Polynomial.finsetSum_coeff,
    Finset.sum_congr rfl (fun s _ => hsummand s), ← Finset.sum_filter, ← Finset.mul_sum]

section TraceProperty

variable {J : Type*} [DecidableEq J]

/-- Row-supported operators are compactoid: their row sups vanish cofinitely. -/
private theorem isCompactoid_of_rows [IsTate R] {w : c(I, R) →L[R] c(J, R)}
    {S : Finset J} (h : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) : IsCompactoid w := by
  have hzero : ∀ j ∉ S, rowNorm w j = 0 := fun j hj => le_antisymm
    (Real.iSup_le (fun i => by rw [h j hj i, norm_zero]) le_rfl) (rowNorm_nonneg w j)
  have hev : ∀ᶠ j in cofinite, rowNorm w j = 0 :=
    S.eventually_cofinite_notMem.mono fun j hj => hzero j hj
  exact Tendsto.congr' (hev.mono fun j hj => hj.symm) tendsto_const_nhds

/-- Truncations of a fixed vector converge to it: `‖π_S f − f‖ ≤ ε` for `S` large. -/
private theorem eventually_norm_truncation_sub_le {f : c(I, R)} {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : Finset I in atTop, ‖truncation S f - f‖ ≤ ε := by
  have hev : ∀ᶠ i in cofinite, ‖f i‖ < ε := by
    filter_upwards [Metric.tendsto_nhds.1 (cSpace.tendsto_cofinite f) ε hε] with i hi
    rwa [dist_zero_right] at hi
  have hfin : {i : I | ¬ ‖f i‖ < ε}.Finite := Filter.eventually_cofinite.1 hev
  rw [Filter.eventually_atTop]
  refine ⟨hfin.toFinset, fun S hS => ?_⟩
  have hcoord : ∀ i, ‖(truncation S f - f) i‖ ≤ ε := by
    intro i
    show ‖truncation S f i - f i‖ ≤ ε
    rw [truncation_apply]
    by_cases hi : i ∈ S
    · rw [if_pos hi, sub_self, norm_zero]
      exact hε.le
    · rw [if_neg hi, zero_sub, norm_neg]
      have : i ∉ hfin.toFinset := fun hmem => hi (hS hmem)
      have hlt : ‖f i‖ < ε := by
        by_contra habs
        exact this (hfin.mem_toFinset.2 habs)
      exact hlt.le
  rw [cSpace.norm_eq_iSup]
  exact Real.iSup_le hcoord hε.le

omit [DecidableEq J] in
/-- A vanishing row of `a` means that `a` evaluates to `0` in that coordinate. -/
theorem apply_coord_eq_zero_of_row {a : c(I, R) →L[R] c(J, R)} {j : J}
    (ha : ∀ i, matrixCoeff a j i = 0) (x : c(I, R)) : (a x) j = 0 := by
  have hcoord : HasSum (fun i => x i * matrixCoeff a j i) ((a x) j) := by
    simpa only [ContinuousLinearMap.comp_apply, cSpace.evalCLM_apply, map_smul,
      smul_eq_mul, matrixCoeff] using (cSpace.hasSum_single x).mapL ((cSpace.evalCLM j).comp a)
  rw [← hcoord.tsum_eq, tsum_congr (fun i => by rw [ha i, mul_zero]), tsum_zero]

private theorem sum_apply_coord {α : Type*} (T : Finset α) (g : α → c(I, R)) (i₀ : I) :
    (∑ x ∈ T, g x) i₀ = ∑ x ∈ T, g x i₀ := by
  induction T using Finset.cons_induction_on with
  | empty => rfl
  | cons x T hx ih =>
      rw [Finset.sum_cons, Finset.sum_cons, ← ih]
      rfl

/-- A vector supported on a finite set is the finite combination of the basis vectors. -/
private theorem eq_sum_single_of_support {g : c(I, R)} {S' : Finset I}
    (hg : ∀ i ∉ S', g i = 0) :
    g = ∑ i ∈ S', g i • cSpace.single i (1 : R) := by
  refine DFunLike.ext _ _ fun i₀ => ?_
  rw [sum_apply_coord]
  by_cases hi : i₀ ∈ S'
  · rw [Finset.sum_eq_single i₀
      (fun i _ hne => by
        show g i • (cSpace.single i (1 : R)) i₀ = 0
        rw [cSpace.single_apply_of_ne (Ne.symm hne), smul_zero])
      (fun habs => absurd hi habs)]
    show g i₀ = g i₀ • (cSpace.single i₀ (1 : R)) i₀
    rw [cSpace.single_apply_self, smul_eq_mul, mul_one]
  · rw [hg i₀ hi]
    refine (Finset.sum_eq_zero fun i hiS => ?_).symm
    show g i • (cSpace.single i (1 : R)) i₀ = 0
    rw [cSpace.single_apply_of_ne fun h => hi (by rw [h]; exact hiS), smul_zero]

/-- Matrix coefficients of a finite sum of operators. -/
theorem matrixCoeff_sum {α : Type*} (T : Finset α) (g : α → c(I, R) →L[R] c(J, R)) (j : J)
    (i : I) : matrixCoeff (∑ x ∈ T, g x) j i = ∑ x ∈ T, matrixCoeff (g x) j i := by
  show ((∑ x ∈ T, g x) (cSpace.single i 1)) j = _
  rw [sum_apply, sum_apply_coord]
  rfl

/-- The matrix of a composition whose right factor is row-supported on the finite set `S` is
the finite matrix product over `S` (the finite kernel of `matrixCoeff_comp`). -/
theorem matrixCoeff_comp_eq_sum_of_rows {L : Type*} [DecidableEq L] (a : c(J, R) →L[R] c(L, R))
    (b : c(I, R) →L[R] c(J, R)) {S : Finset J} (hb : ∀ j ∉ S, ∀ i, matrixCoeff b j i = 0)
    (l : L) (i : I) :
    matrixCoeff (a.comp b) l i = ∑ j ∈ S, matrixCoeff a l j * matrixCoeff b j i := by
  have hsupp : ∀ j ∉ S, (b (cSpace.single i 1)) j = 0 := fun j hj ↦ hb j hj i
  show (a (b (cSpace.single i 1))) l = _
  rw [show b (cSpace.single i 1) = ∑ j ∈ S, (b (cSpace.single i 1)) j • cSpace.single j (1 : R)
    from eq_sum_single_of_support hsupp, map_sum, sum_apply_coord]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul]
  show (b (cSpace.single i 1)) j • (a (cSpace.single j 1)) l = _
  rw [smul_eq_mul, mul_comm]
  rfl

/-- The trace property for a pair of row-supported operators — the finite kernel:
both determinants reduce to `det(1 − X·AB) = det(1 − X·BA)` for finite blocks. -/
private theorem charPowerSeries_comm_of_rows [IsTate R] {J : Type*} [DecidableEq J]
    (a : c(I, R) →L[R] c(J, R)) (b : c(J, R) →L[R] c(I, R))
    {S : Finset J} (ha : ∀ j ∉ S, ∀ i, matrixCoeff a j i = 0)
    {S' : Finset I} (hb : ∀ i ∉ S', ∀ j, matrixCoeff b i j = 0) :
    charPowerSeries (a.comp b) = charPowerSeries (b.comp a) := by
  classical
  -- finite blocks
  set A : Matrix S S' R := Matrix.of fun j i => matrixCoeff a (j : J) (i : I) with hA
  set B : Matrix S' S R := Matrix.of fun i j => matrixCoeff b (i : I) (j : J) with hB
  -- the composites are row-supported
  have hab_rows : ∀ j ∉ S, ∀ j', matrixCoeff (a.comp b) j j' = 0 := fun j hj j' =>
    apply_coord_eq_zero_of_row (ha j hj) _
  have hba_rows : ∀ i ∉ S', ∀ i', matrixCoeff (b.comp a) i i' = 0 := fun i hi i' =>
    apply_coord_eq_zero_of_row (hb i hi) _
  -- the S×S block of `a∘b` is the product `A*B`
  have hAB : ∀ (j j' : S), matrixCoeff (a.comp b) (j : J) (j' : J) = (A * B) j j' := by
    intro j j'
    have hsupp : ∀ i ∉ S', (b (cSpace.single (j' : J) 1)) i = 0 := fun i hi => hb i hi _
    show (a (b (cSpace.single (j' : J) 1))) (j : J) = _
    rw [show b (cSpace.single (j' : J) 1)
        = ∑ i ∈ S', (b (cSpace.single (j' : J) 1)) i • cSpace.single i (1 : R) from
      eq_sum_single_of_support hsupp]
    rw [map_sum, sum_apply_coord]
    rw [Matrix.mul_apply, ← Finset.sum_coe_sort S']
    refine Finset.sum_congr rfl fun i _ => ?_
    show (a ((b (cSpace.single (j' : J) 1)) (i : I) • cSpace.single (i : I) 1)) (j : J) = _
    rw [map_smul]
    show (b (cSpace.single (j' : J) 1)) (i : I) • (a (cSpace.single (i : I) 1)) (j : J)
      = A j i * B i j'
    rw [smul_eq_mul, mul_comm]
    rfl
  -- the S'×S' block of `b∘a` is the product `B*A`
  have hBA : ∀ (i i' : S'), matrixCoeff (b.comp a) (i : I) (i' : I) = (B * A) i i' := by
    intro i i'
    have hsupp : ∀ j ∉ S, (a (cSpace.single (i' : I) 1)) j = 0 := fun j hj => ha j hj _
    show (b (a (cSpace.single (i' : I) 1))) (i : I) = _
    rw [show a (cSpace.single (i' : I) 1)
        = ∑ j ∈ S, (a (cSpace.single (i' : I) 1)) j • cSpace.single j (1 : R) from
      eq_sum_single_of_support hsupp]
    rw [map_sum, sum_apply_coord]
    rw [Matrix.mul_apply, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (b ((a (cSpace.single (i' : I) 1)) (j : J) • cSpace.single (j : J) 1)) (i : I) = _
    rw [map_smul]
    show (a (cSpace.single (i' : I) 1)) (j : J) • (b (cSpace.single (j : J) 1)) (i : I)
      = B i j * A j i'
    rw [smul_eq_mul, mul_comm]
    rfl
  -- assemble via the finite determinant identity
  refine PowerSeries.ext fun n => ?_
  rw [charPowerSeries_coeff, charPowerSeries_coeff,
    charCoeff_eq_det_coeff (a.comp b) S hab_rows n,
    charCoeff_eq_det_coeff (b.comp a) S' hba_rows n]
  congr 1
  have hABmap : (Matrix.of fun j i : S => Polynomial.C (matrixCoeff (a.comp b) (j : J) (i : J)))
      = (A.map Polynomial.C) * (B.map Polynomial.C) := by
    refine Matrix.ext fun j i => ?_
    show Polynomial.C (matrixCoeff (a.comp b) (j : J) (i : J)) = _
    rw [hAB j i, ← Matrix.map_mul]
    rfl
  have hBAmap : (Matrix.of fun i j : S' => Polynomial.C (matrixCoeff (b.comp a) (i : I) (j : I)))
      = (B.map Polynomial.C) * (A.map Polynomial.C) := by
    refine Matrix.ext fun i j => ?_
    show Polynomial.C (matrixCoeff (b.comp a) (i : I) (j : I)) = _
    rw [hBA i j, ← Matrix.map_mul]
    rfl
  rw [hABmap, hBAmap, ← Matrix.smul_mul, Matrix.det_one_sub_mul_comm, Matrix.mul_smul]

/-- **The trace property** ([Bel] Proposition II.1.17), the primitive invariance
statement: `det(1 − T·(u∘v)) = det(1 − T·(v∘u))` for `u` compact, `v` continuous.

*Proof sketch.*  Bellaïche's, verbatim over a Tate ring: truncate `u` and `v`
(`tendsto_truncation_comp`), pass to the limit by `norm_charCoeff_sub_le`, and conclude
by `charCoeff_eq_det_coeff` + `det(1 − AB) = det(1 − BA)` for finite matrices. -/
private theorem charCoeff_eq_sum_of_rows [IsTate R] {w : c(I, R) →L[R] c(I, R)}
    {S : Finset I} (hw : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) (n : ℕ) :
    charCoeff w n = (-1 : R) ^ n
      * ∑ T ∈ (S.powersetCard n).subtype (fun T => T.card = n),
          minor w (T : Finset I) := by
  rw [charCoeff]
  congr 1
  refine tsum_eq_sum fun T hT => ?_
  have hTS : ¬ (T : Finset I) ⊆ S := fun hsub =>
    hT (Finset.mem_subtype.2 (Finset.mem_powersetCard.2 ⟨hsub, T.2⟩))
  obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.1 hTS
  exact Matrix.det_eq_zero_of_row_eq_zero (⟨j, hjT⟩ : {x // x ∈ (T : Finset I)})
    fun i => hw j hjS _

theorem charPowerSeries_comm [IsTate R] {J : Type*} [DecidableEq J]
    (u : c(I, R) →L[R] c(J, R)) (v : c(J, R) →L[R] c(I, R))
    (hu : IsCompactoid u) :
    charPowerSeries (u.comp v) = charPowerSeries (v.comp u) := by
  classical
  refine PowerSeries.ext fun n => ?_
  rw [charPowerSeries_coeff, charPowerSeries_coeff]
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [charCoeff_zero, charCoeff_zero]
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [dist_eq_norm]
  -- global constants
  set KB : ℝ := max (‖u‖ * ‖v‖) 1 with hKB
  have hKB1 : (1 : ℝ) ≤ KB := le_max_right _ _
  have hKB0 : (0 : ℝ) < KB := lt_of_lt_of_le one_pos hKB1
  set P : ℝ := KB ^ (n - 1) with hP
  have hP0 : (0 : ℝ) < P := pow_pos hKB0 _
  have hεq : (0 : ℝ) < ε / 4 := by positivity
  have hv1 : (0 : ℝ) < ‖v‖ + 1 :=
    lt_of_lt_of_le one_pos (by simpa using opNorm_nonneg v)
  have hu1 : (0 : ℝ) < ‖u‖ + 1 :=
    lt_of_lt_of_le one_pos (by simpa using opNorm_nonneg u)
  -- choose S from the compactoid decay of u
  set δ₁ : ℝ := ε / 4 / (P * (‖v‖ + 1)) with hδ₁
  have hδ₁0 : 0 < δ₁ := div_pos hεq (mul_pos hP0 hv1)
  have hSev : ∀ᶠ S : Finset J in atTop, ‖(truncation S).comp u - u‖ ≤ δ₁ := by
    filter_upwards [Metric.tendsto_nhds.1 (tendsto_truncation_comp u hu) δ₁ hδ₁0] with S hS
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (opNorm_nonneg _)] at hS
    exact hS.le
  obtain ⟨S, hS₁⟩ := hSev.exists
  set a : c(I, R) →L[R] c(J, R) := (truncation S).comp u with ha_def
  have ha_rows : ∀ j ∉ S, ∀ i, matrixCoeff a j i = 0 := fun j hj i => by
    show (truncation S (u (cSpace.single i 1))) j = 0
    rw [truncation_apply, if_neg hj]
  have ha_cpt : IsCompactoid a := isCompactoid_of_rows ha_rows
  have ha_norm : ‖a‖ ≤ ‖u‖ := by
    refine (opNorm_comp_le _ _).trans ?_
    have htr : ‖(truncation (R := R) S : c(J, R) →L[R] c(J, R))‖ ≤ 1 :=
      opNorm_le_of_forall _ zero_le_one fun f => by
        rw [one_mul]; exact norm_truncation_apply_le S f
    calc ‖(truncation (R := R) S : c(J, R) →L[R] c(J, R))‖ * ‖u‖
        ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right htr (opNorm_nonneg u)
    _ = ‖u‖ := one_mul _
  -- choose S' handling both the b∘a-limit and the finitely many column tails
  set δ₂ : ℝ := ε / 4 / P with hδ₂
  have hδ₂0 : 0 < δ₂ := div_pos hεq hP0
  set η : ℝ := ε / 4 / (P * (‖u‖ + 1)) with hη
  have hη0 : 0 < η := div_pos hεq (mul_pos hP0 hu1)
  have hva_cpt : IsCompactoid (v.comp a) := ha_cpt.comp_left v
  have hS'ev₁ : ∀ᶠ S' : Finset I in atTop,
      ‖(truncation S').comp (v.comp a) - v.comp a‖ ≤ δ₂ := by
    filter_upwards [Metric.tendsto_nhds.1 (tendsto_truncation_comp _ hva_cpt) δ₂ hδ₂0]
      with S' h
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (opNorm_nonneg _)] at h
    exact h.le
  have hS'ev₂ : ∀ᶠ S' : Finset I in atTop, ∀ j' ∈ S,
      ‖truncation S' (v (cSpace.single j' 1)) - v (cSpace.single j' 1)‖ ≤ η := by
    rw [Filter.eventually_all_finset]
    intro j' _
    exact eventually_norm_truncation_sub_le hη0
  obtain ⟨S', hS'₁, hS'₂⟩ := (hS'ev₁.and hS'ev₂).exists
  set b : c(J, R) →L[R] c(I, R) := (truncation S').comp v with hb_def
  have hb_rows : ∀ i ∉ S', ∀ j, matrixCoeff b i j = 0 := fun i hi j => by
    show (truncation S' (v (cSpace.single j 1))) i = 0
    rw [truncation_apply, if_neg hi]
  have hb_cpt : IsCompactoid b := isCompactoid_of_rows hb_rows
  have hb_norm : ‖b‖ ≤ ‖v‖ := by
    refine (opNorm_comp_le _ _).trans ?_
    have htr : ‖(truncation (R := R) S' : c(I, R) →L[R] c(I, R))‖ ≤ 1 :=
      opNorm_le_of_forall _ zero_le_one fun f => by
        rw [one_mul]; exact norm_truncation_apply_le S' f
    calc ‖(truncation (R := R) S' : c(I, R) →L[R] c(I, R))‖ * ‖v‖
        ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right htr (opNorm_nonneg v)
    _ = ‖v‖ := one_mul _
  -- the atomic identity for the row-supported pair
  have hatomic : charCoeff (a.comp b) n = charCoeff (b.comp a) n := by
    have h := congrArg (PowerSeries.coeff n) (charPowerSeries_comm_of_rows a b ha_rows hb_rows)
    rwa [charPowerSeries_coeff, charPowerSeries_coeff] at h
  -- operator norm bounds against KB
  have huv_n : ‖u.comp v‖ ≤ KB := (opNorm_comp_le _ _).trans (le_max_left _ _)
  have hav_n : ‖a.comp v‖ ≤ KB := (opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right ha_norm (opNorm_nonneg v)).trans (le_max_left _ _))
  have hab_n : ‖a.comp b‖ ≤ KB := (opNorm_comp_le _ _).trans
    ((mul_le_mul ha_norm hb_norm (opNorm_nonneg b) (opNorm_nonneg u)).trans (le_max_left _ _))
  have hvu_n : ‖v.comp u‖ ≤ KB := (opNorm_comp_le _ _).trans
    ((mul_comm ‖v‖ ‖u‖ ▸ le_max_left (‖u‖ * ‖v‖) 1))
  have hva_n : ‖v.comp a‖ ≤ KB := (opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left ha_norm (opNorm_nonneg v)).trans
      (mul_comm ‖v‖ ‖u‖ ▸ le_max_left (‖u‖ * ‖v‖) 1))
  have hba_n : ‖b.comp a‖ ≤ KB := (opNorm_comp_le _ _).trans
    ((mul_le_mul hb_norm ha_norm (opNorm_nonneg a) (opNorm_nonneg v)).trans
      (mul_comm ‖v‖ ‖u‖ ▸ le_max_left (‖u‖ * ‖v‖) 1))
  -- the max-power bound for T025 pairs
  have hpow : ∀ x y : ℝ, x ≤ KB → y ≤ KB → 0 ≤ x → max x y ^ (n - 1) ≤ P := by
    intro x y hx hy hx0
    exact pow_le_pow_left₀ (le_trans hx0 (le_max_left _ _)) (max_le hx hy) _
  -- d₁
  have hd₁ : ‖charCoeff (u.comp v) n - charCoeff (a.comp v) n‖ ≤ ε / 4 := by
    refine ((norm_charCoeff_sub_le _ _ (hu.comp_right v) (ha_cpt.comp_right v) hn1).trans ?_)
    have hdiff : ‖u.comp v - a.comp v‖ ≤ δ₁ * (‖v‖ + 1) := by
      rw [← ContinuousLinearMap.sub_comp]
      refine (opNorm_comp_le _ _).trans ?_
      have h1 : ‖u - a‖ ≤ δ₁ := by rw [opNorm_sub_comm]; exact hS₁
      exact mul_le_mul h1 (by linarith [opNorm_nonneg v]) (opNorm_nonneg v) hδ₁0.le
    calc max ‖u.comp v‖ ‖a.comp v‖ ^ (n - 1) * ‖u.comp v - a.comp v‖
        ≤ P * (δ₁ * (‖v‖ + 1)) :=
          mul_le_mul (hpow _ _ huv_n hav_n (opNorm_nonneg _)) hdiff (opNorm_nonneg _) hP0.le
    _ = ε / 4 := by rw [hδ₁]; field_simp
  -- d₄
  have hd₄ : ‖charCoeff (v.comp a) n - charCoeff (v.comp u) n‖ ≤ ε / 4 := by
    refine ((norm_charCoeff_sub_le _ _ (ha_cpt.comp_left v) (hu.comp_left v) hn1).trans ?_)
    have hdiff : ‖v.comp a - v.comp u‖ ≤ δ₁ * (‖v‖ + 1) := by
      rw [← ContinuousLinearMap.comp_sub]
      refine (opNorm_comp_le _ _).trans ?_
      have h1 : ‖a - u‖ ≤ δ₁ := hS₁
      calc ‖v‖ * ‖a - u‖ ≤ (‖v‖ + 1) * δ₁ :=
            mul_le_mul (by linarith [opNorm_nonneg v]) h1 (opNorm_nonneg _) (by linarith [opNorm_nonneg v])
      _ = δ₁ * (‖v‖ + 1) := mul_comm _ _
    calc max ‖v.comp a‖ ‖v.comp u‖ ^ (n - 1) * ‖v.comp a - v.comp u‖
        ≤ P * (δ₁ * (‖v‖ + 1)) :=
          mul_le_mul (hpow _ _ hva_n hvu_n (opNorm_nonneg _)) hdiff (opNorm_nonneg _) hP0.le
    _ = ε / 4 := by rw [hδ₁]; field_simp
  -- d₃
  have hd₃ : ‖charCoeff (b.comp a) n - charCoeff (v.comp a) n‖ ≤ ε / 4 := by
    refine ((norm_charCoeff_sub_le _ _ (isCompactoid_of_rows
      (fun i hi i' => apply_coord_eq_zero_of_row (hb_rows i hi) _)) hva_cpt hn1).trans ?_)
    have hdiff : ‖b.comp a - v.comp a‖ ≤ δ₂ := by
      have : b.comp a = (truncation S').comp (v.comp a) := ContinuousLinearMap.comp_assoc _ _ _
      rw [this]
      exact hS'₁
    calc max ‖b.comp a‖ ‖v.comp a‖ ^ (n - 1) * ‖b.comp a - v.comp a‖
        ≤ P * δ₂ :=
          mul_le_mul (hpow _ _ hba_n hva_n (opNorm_nonneg _)) hdiff (opNorm_nonneg _) hP0.le
    _ = ε / 4 := by rw [hδ₂]; field_simp
  -- d₂ — entrywise via the determinant telescope on the finite block
  have hd₂ : ‖charCoeff (a.comp v) n - charCoeff (a.comp b) n‖ ≤ ε / 4 := by
    have hav_rows : ∀ j ∉ S, ∀ j', matrixCoeff (a.comp v) j j' = 0 := fun j hj j' =>
      apply_coord_eq_zero_of_row (ha_rows j hj) _
    have hab_rows : ∀ j ∉ S, ∀ j', matrixCoeff (a.comp b) j j' = 0 := fun j hj j' =>
      apply_coord_eq_zero_of_row (ha_rows j hj) _
    rw [charCoeff_eq_sum_of_rows hav_rows n, charCoeff_eq_sum_of_rows hab_rows n,
      ← mul_sub, ← Finset.sum_sub_distrib]
    refine (norm_mul_le _ _).trans ?_
    rw [norm_neg_one_pow, one_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hεq.le fun T hT => ?_
    have hTcard : (T : Finset J).card = n := T.2
    have hTsub : (T : Finset J) ⊆ S :=
      (Finset.mem_powersetCard.1 (Finset.mem_subtype.1 hT)).1
    have hentry : ∀ p q : (T : Finset J),
        ‖matrixCoeff (a.comp v) (p : J) (q : J) - matrixCoeff (a.comp b) (p : J) (q : J)‖
          ≤ (‖u‖ + 1) * η := by
      intro p q
      rw [← matrixCoeff_sub, show a.comp v - a.comp b = a.comp (v - b) from
        (ContinuousLinearMap.comp_sub a v b).symm]
      show ‖(a ((v - b) (cSpace.single (q : J) 1))) (p : J)‖ ≤ _
      refine (cSpace.norm_apply_le _ _).trans ((le_opNorm a _).trans ?_)
      have hvb : (v - b) (cSpace.single (q : J) 1)
          = v (cSpace.single (q : J) 1) - truncation S' (v (cSpace.single (q : J) 1)) := rfl
      rw [hvb, norm_sub_rev]
      exact mul_le_mul (ha_norm.trans (by linarith)) (hS'₂ (q : J) (hTsub q.2))
        (norm_nonneg _) (by positivity)
    have hres := norm_det_sub_det_le
      (Matrix.of fun j i : (T : Finset J) => matrixCoeff (a.comp v) (j : J) (i : J))
      (Matrix.of fun j i : (T : Finset J) => matrixCoeff (a.comp b) (j : J) (i : J))
      KB ((‖u‖ + 1) * η) (le_trans zero_le_one hKB1) (by positivity)
      (fun p q => (norm_matrixCoeff_le _ _ _).trans hav_n)
      (fun p q => (norm_matrixCoeff_le _ _ _).trans hab_n)
      hentry (by rw [Fintype.card_coe, hTcard]; exact hn1)
    rw [Fintype.card_coe, hTcard] at hres
    refine hres.trans (le_of_eq ?_)
    rw [hη, ← hP]
    field_simp
  -- assemble the four quarters
  have hsplit : charCoeff (u.comp v) n - charCoeff (v.comp u) n
      = (charCoeff (u.comp v) n - charCoeff (a.comp v) n)
        + (charCoeff (a.comp v) n - charCoeff (a.comp b) n)
        + (charCoeff (b.comp a) n - charCoeff (v.comp a) n)
        + (charCoeff (v.comp a) n - charCoeff (v.comp u) n) := by
    rw [hatomic]
    ring
  rw [hsplit]
  calc ‖(charCoeff (u.comp v) n - charCoeff (a.comp v) n)
        + (charCoeff (a.comp v) n - charCoeff (a.comp b) n)
        + (charCoeff (b.comp a) n - charCoeff (v.comp a) n)
        + (charCoeff (v.comp a) n - charCoeff (v.comp u) n)‖
      ≤ ‖(charCoeff (u.comp v) n - charCoeff (a.comp v) n)
        + (charCoeff (a.comp v) n - charCoeff (a.comp b) n)
        + (charCoeff (b.comp a) n - charCoeff (v.comp a) n)‖
        + ‖charCoeff (v.comp a) n - charCoeff (v.comp u) n‖ := _root_.norm_add_le _ _
  _ ≤ ‖(charCoeff (u.comp v) n - charCoeff (a.comp v) n)
        + (charCoeff (a.comp v) n - charCoeff (a.comp b) n)‖
        + ‖charCoeff (b.comp a) n - charCoeff (v.comp a) n‖
        + ‖charCoeff (v.comp a) n - charCoeff (v.comp u) n‖ :=
      add_le_add (_root_.norm_add_le _ _) le_rfl
  _ ≤ ‖charCoeff (u.comp v) n - charCoeff (a.comp v) n‖
        + ‖charCoeff (a.comp v) n - charCoeff (a.comp b) n‖
        + ‖charCoeff (b.comp a) n - charCoeff (v.comp a) n‖
        + ‖charCoeff (v.comp a) n - charCoeff (v.comp u) n‖ :=
      add_le_add (add_le_add (_root_.norm_add_le _ _) le_rfl) le_rfl
  _ ≤ ε := by linarith [hd₁, hd₂, hd₃, hd₄]

/-- Basis-, norm- and conjugation-invariance ([Bel] Corollary II.1.18; [Buz07,
Lemma 2.5/Corollary 2.6]) — a formal consequence of the trace property.  This is what
extends `det(1 − Tu)` to compact endomorphisms of potentially ON-able modules. -/
theorem charPowerSeries_conj [IsTate R] {J : Type*} [DecidableEq J]
    (φ : c(I, R) ≃L[R] c(J, R)) (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) :
    charPowerSeries (((φ : c(I, R) →L[R] c(J, R)).comp u).comp
        (φ.symm : c(J, R) →L[R] c(I, R)))
      = charPowerSeries u := by
  have h := charPowerSeries_comm ((φ : c(I, R) →L[R] c(J, R)).comp u)
    (φ.symm : c(J, R) →L[R] c(I, R)) (hu.comp_left _)
  rw [h]
  congr 1
  rw [← ContinuousLinearMap.comp_assoc]
  rw [show (φ.symm : c(J, R) →L[R] c(I, R)).comp (φ : c(I, R) →L[R] c(J, R))
      = ContinuousLinearMap.id R (c(I, R)) from by
    ext f
    simp [ContinuousLinearMap.comp_apply]]
  exact ContinuousLinearMap.id_comp u

/-- Extension by zero ([Buz07, pp. 72–73]; [Bel] §II.1.6) — with `charPowerSeries_conj`,
the well-definedness of the determinant on modules with property (Pr). -/
theorem charPowerSeries_extendZero [IsTate R] {J : Type*} [DecidableEq J]
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (v : c(I ⊕ J, R) →L[R] c(I ⊕ J, R))
    (hII : ∀ j i, matrixCoeff v (Sum.inl j) (Sum.inl i) = matrixCoeff u j i)
    (hJrow : ∀ j q, matrixCoeff v (Sum.inr j) q = 0)
    (hJcol : ∀ p j, matrixCoeff v p (Sum.inr j) = 0) :
    charPowerSeries v = charPowerSeries u := by
  classical
  set emb : I ↪ I ⊕ J := ⟨Sum.inl, Sum.inl_injective⟩ with hembdef
  -- every minor of `v` meeting the `J`-block vanishes; the rest reindex along `inl`
  have hminor_eq : ∀ S : Finset I,
      minor v (S.map emb) = minor u S := by
    intro S
    have hbij : Function.Bijective (fun j : {x // x ∈ S} =>
        (⟨Sum.inl j.1, Finset.mem_map_of_mem emb j.2⟩ :
          {x // x ∈ S.map emb})) := by
      constructor
      · intro j j' h
        exact Subtype.ext (Sum.inl_injective (congrArg Subtype.val h))
      · rintro ⟨p, hp⟩
        obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hp
        exact ⟨⟨q, hq⟩, rfl⟩
    rw [show minor v (S.map emb)
        = (Matrix.of fun p q : {x // x ∈ S.map emb} =>
            matrixCoeff v (p : I ⊕ J) (q : I ⊕ J)).det from rfl,
      ← Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hbij)]
    congr 1
    refine Matrix.ext fun j i => ?_
    show matrixCoeff v (Sum.inl (j : I)) (Sum.inl (i : I)) = matrixCoeff u (j : I) (i : I)
    exact hII _ _
  refine PowerSeries.ext fun n => ?_
  rw [charPowerSeries_coeff, charPowerSeries_coeff, charCoeff, charCoeff]
  have hsum := (summable_minor u hu n).hasSum
  have htsum : (∑' T : {T : Finset (I ⊕ J) // T.card = n}, minor v (T : Finset (I ⊕ J)))
      = ∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I) :=
    ((hasSum_iff_hasSum_of_ne_zero_bij
    (f := fun T : {T : Finset (I ⊕ J) // T.card = n} => minor v (T : Finset (I ⊕ J)))
    (g := fun S : {S : Finset I // S.card = n} => minor u (S : Finset I))
    (fun S => ⟨(S.1 : Finset I).map emb, by
      rw [Finset.card_map]; exact S.1.2⟩)
    (fun S S' h => by
      apply Subtype.ext
      apply Subtype.ext
      exact Finset.map_injective _ (congrArg Subtype.val h))
    (fun T hT => by
      -- a nonvanishing minor has no `inr` element
      have hallinl : ∀ p ∈ (T : Finset (I ⊕ J)), ∃ q : I, Sum.inl q = p := by
        intro p hp
        rcases p with q | j
        · exact ⟨q, rfl⟩
        · exfalso
          apply hT
          show minor v (T : Finset (I ⊕ J)) = 0
          exact Matrix.det_eq_zero_of_row_eq_zero
            (⟨Sum.inr j, hp⟩ : {x // x ∈ (T : Finset (I ⊕ J))})
            fun i => hJrow j _
      set S₀ : Finset I :=
        (T : Finset (I ⊕ J)).preimage Sum.inl Sum.inl_injective.injOn with hS₀
      have hTmap : (T : Finset (I ⊕ J)) = S₀.map emb := by
        refine Finset.ext fun p => ?_
        rw [Finset.mem_map]
        constructor
        · intro hp
          obtain ⟨q, rfl⟩ := hallinl p hp
          exact ⟨q, Finset.mem_preimage.2 hp, rfl⟩
        · rintro ⟨q, hq, rfl⟩
          exact Finset.mem_preimage.1 hq
      have hS₀card : S₀.card = n := by
        have := T.2
        rw [hTmap, Finset.card_map] at this
        exact this
      have hgne : minor u S₀ ≠ 0 := by
        rw [← hminor_eq S₀, ← hTmap]
        exact hT
      exact ⟨⟨⟨S₀, hS₀card⟩, hgne⟩, Subtype.ext hTmap.symm⟩)
    (fun S => by
      show minor v ((S.1 : Finset I).map emb) = minor u (S.1 : Finset I)
      exact hminor_eq _)).2 hsum).tsum_eq
  rw [htsum]

end TraceProperty

end Fredholm

end TateFredholm

end
