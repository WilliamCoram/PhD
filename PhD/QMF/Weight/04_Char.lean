/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Weight.SlashAction

/-!
# Honest locally analytic characters and their weight data

[Jacobs, Def 1.27]: "Let κ : ℤ×_p → 𝒪×_p be a locally analytic character, i.e. a
continuous group homomorphism. … Note, that by κ(cz + d) we mean the power series
expansion of κ(cz + d) at zero."

This file supplies the constructor from the honest character: given κ (multiplicative
on units) together with **expansion data** — the series family and the fact that it
evaluates to `κ(cz + d)` on the closed unit ball — the `WeightSeries` fields
`col_zero_one` and `cocycle` become THEOREMS rather than data:

both sides of the cocycle are summable series on the closed ball; at a point `z`,
`κ(lin(δγ)(z)) = κ(lin γ (z))·κ(lin δ (w_γ z))` is the classical automorphy-factor
identity `j(δγ, z) = j(γ, z)·j(δ, γz)` (2×2 algebra) combined with multiplicativity of
κ; and two summable series agreeing on the closed unit ball are equal (Strassman-type
uniqueness — [Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Ch. IV]).
The thesis performs exactly this move pointwise at p. 29 ("κ(cx+d) = κ(4^ρ) = κ(4)^ρ").

Def 1.27's continuity of κ is subsumed by the expansion datum (the expansion is what
continuity-plus-local-analyticity buys; here it is taken as the data, exactly as the
thesis's phrase "by κ(cz + d) we mean the power series expansion" does).

## Main declarations

* `QMF.evalAt f z` — evaluation `∑' n, coeff n f · zⁿ` of a series at a point.
* `QMF.evalAt_eq_zero_iff_of_forall` (`eq_zero_of_forall_evalAt_eq_zero`) —
  **evaluation injectivity** on the closed unit ball (Strassman-type).
* `QMF.evalAt_compAn` — evaluation of an analytic substitution is the composition of
  evaluations.
* `QMF.ExpansionData` — the honest-character weight datum.
* `QMF.ExpansionData.toWeightSeries` — the constructor deriving the cocycle.
* `QMF.ExpansionData.col_eq_of_mem` — uniqueness of the expansion on the level.
* `QMF.AnalyticWeight U S ρ` — a character together with its expansion datum: **the
  weights** at which `QMF.Weight.Forms` is defined.
-/

open TateFredholm PowerSeries
open scoped TateFredholm Topology

namespace QMF

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Evaluation of a one-variable power series at a point: `∑' n, coeff n f · zⁿ`. -/
noncomputable def evalAt (f : PowerSeries K) (z : K) : K :=
  ∑' n, PowerSeries.coeff n f * z ^ n

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The evaluation terms are norm-summable on the closed unit ball. -/
theorem summable_norm_evalAt {f : PowerSeries K} (hf : AbsSummable f) {z : K}
    (hz : ‖z‖ ≤ 1) : Summable fun n => ‖PowerSeries.coeff n f * z ^ n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz))
    hf

omit [IsUltrametricDist K] in
theorem hasSum_evalAt {f : PowerSeries K} (hf : AbsSummable f) {z : K} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => PowerSeries.coeff n f * z ^ n) (evalAt f z) :=
  (Summable.of_norm (summable_norm_evalAt hf hz)).hasSum

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem evalAt_one (z : K) : evalAt (1 : PowerSeries K) z = 1 := by
  rw [evalAt, tsum_eq_single 0
    (fun n hn => by rw [PowerSeries.coeff_one, if_neg hn, zero_mul]),
    PowerSeries.coeff_one, if_pos rfl, pow_zero, mul_one]

omit [IsUltrametricDist K] in
private theorem evalAt_mul_of_summable_norm {f g : PowerSeries K} {z : K}
    (hf : Summable fun n => ‖PowerSeries.coeff n f * z ^ n‖)
    (hg : Summable fun n => ‖PowerSeries.coeff n g * z ^ n‖) :
    evalAt (f * g) z = evalAt f z * evalAt g z := by
  rw [evalAt, evalAt, evalAt,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring

omit [IsUltrametricDist K] in
theorem evalAt_mul {f g : PowerSeries K} (hf : AbsSummable f) (hg : AbsSummable g)
    {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt (f * g) z = evalAt f z * evalAt g z :=
  evalAt_mul_of_summable_norm (summable_norm_evalAt hf hz) (summable_norm_evalAt hg hz)

/-- **The ultrametric evaluation bound**: a summable series with coefficients of norm
`≤ 1` has values of norm `≤ 1` on the closed unit ball. -/
theorem norm_evalAt_le_one {f : PowerSeries K} (hf : AbsSummable f) (hc : CoeffLeOne f)
    {z : K} (hz : ‖z‖ ≤ 1) : ‖evalAt f z‖ ≤ 1 := by
  refine (norm_tsum_le_iSup ((Summable.of_norm
    (summable_norm_evalAt hf hz)).tendsto_cofinite_zero)).trans
    (Real.iSup_le (fun n => ?_) zero_le_one)
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (hc n) (by positivity) (pow_le_one₀ (norm_nonneg _) hz)

/-- Coefficient decay in the ultrametric sense: the coefficients tend to `0`.  This is
summability of the coefficients in `K` — strictly weaker than `AbsSummable`, and closed
under products and `compAn` (which `AbsSummable` is not obviously). -/
def TendstoCoeff (f : PowerSeries K) : Prop :=
  Filter.Tendsto (fun n => PowerSeries.coeff n f) Filter.cofinite (𝓝 0)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem AbsSummable.tendstoCoeff {f : PowerSeries K} (hf : AbsSummable f) :
    TendstoCoeff f :=
  tendsto_zero_iff_norm_tendsto_zero.mpr hf.tendsto_cofinite_zero

/-- The evaluation terms are summable on the closed ball, from coefficient decay
alone (nonarchimedean summability). -/
theorem TendstoCoeff.summable_terms {f : PowerSeries K} (hf : TendstoCoeff f) {z : K}
    (hz : ‖z‖ ≤ 1) : Summable fun n => PowerSeries.coeff n f * z ^ n :=
  summable_of_tendsto_cofinite (squeeze_zero_norm
    (fun n => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz))
    (tendsto_zero_iff_norm_tendsto_zero.mp hf))

theorem TendstoCoeff.hasSum_evalAt {f : PowerSeries K} (hf : TendstoCoeff f) {z : K}
    (hz : ‖z‖ ≤ 1) : HasSum (fun n => PowerSeries.coeff n f * z ^ n) (evalAt f z) :=
  (hf.summable_terms hz).hasSum

/-- Strassman-type vanishing from coefficient decay alone. -/
theorem TendstoCoeff.eq_zero_of_forall_evalAt_eq_zero {f : PowerSeries K}
    (hf : TendstoCoeff f) (h : ∀ z : K, ‖z‖ ≤ 1 → evalAt f z = 0) : f = 0 := by
  by_contra hne
  have hex : ∃ n, PowerSeries.coeff n f ≠ 0 := by
    by_contra hall
    exact hne (PowerSeries.ext fun n => not_not.mp fun hc => hall ⟨n, hc⟩)
  classical
  set n₀ := Nat.find hex with hn₀
  have hc0 : PowerSeries.coeff n₀ f ≠ 0 := Nat.find_spec hex
  have hmin : ∀ m, m < n₀ → PowerSeries.coeff m f = 0 := fun m hm =>
    not_not.mp (Nat.find_min hex hm)
  obtain ⟨C₀, hC₀⟩ := bddAbove_range_norm_of_tendsto_cofinite hf
  set C := max C₀ 1 with hCdef
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC : ∀ n, ‖PowerSeries.coeff n f‖ ≤ C := fun n =>
    (hC₀ ⟨n, rfl⟩).trans (le_max_left _ _)
  obtain ⟨z, hz0, hzlt⟩ := NormedField.exists_norm_lt K
    (lt_min one_pos (div_pos (norm_pos_iff.mpr hc0) hC0))
  have hz1 : ‖z‖ ≤ 1 := (hzlt.trans_le (min_le_left _ _)).le
  have hsum : Summable fun n => PowerSeries.coeff n f * z ^ n :=
    hf.summable_terms hz1
  have hsplit := Summable.tsum_eq_add_tsum_ite hsum n₀
  rw [show (∑' n, PowerSeries.coeff n f * z ^ n) = evalAt f z from rfl, h z hz1] at hsplit
  have hrest_eq : (∑' n, if n = n₀ then 0 else PowerSeries.coeff n f * z ^ n)
      = -(PowerSeries.coeff n₀ f * z ^ n₀) :=
    eq_neg_of_add_eq_zero_right hsplit.symm
  have hite : Filter.Tendsto (fun n => if n = n₀ then (0 : K)
      else PowerSeries.coeff n f * z ^ n) Filter.cofinite (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_)
      (tendsto_zero_iff_norm_tendsto_zero.mp (hf.summable_terms hz1).tendsto_cofinite_zero)
    split_ifs with hn
    · rw [norm_zero]
      positivity
    · exact le_rfl
  have hrest : ‖∑' n, if n = n₀ then 0 else PowerSeries.coeff n f * z ^ n‖
      < ‖PowerSeries.coeff n₀ f‖ * ‖z‖ ^ n₀ := by
    refine lt_of_le_of_lt (norm_tsum_le_iSup hite) ?_
    have hB0 : (0 : ℝ) ≤ C * ‖z‖ ^ (n₀ + 1) := by positivity
    refine lt_of_le_of_lt (Real.iSup_le (fun n => ?_) hB0) ?_
    · split_ifs with hn
      · rw [norm_zero]
        exact hB0
      · rcases Nat.lt_or_ge n n₀ with hlt | hge
        · rw [hmin n hlt, zero_mul, norm_zero]
          exact hB0
        · have hn' : n₀ + 1 ≤ n := by omega
          rw [norm_mul, norm_pow]
          calc ‖PowerSeries.coeff n f‖ * ‖z‖ ^ n ≤ C * ‖z‖ ^ n :=
                mul_le_mul_of_nonneg_right (hC n) (by positivity)
            _ ≤ C * ‖z‖ ^ (n₀ + 1) :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_of_le_one (norm_nonneg _) hz1 hn') hC0.le
    · calc C * ‖z‖ ^ (n₀ + 1) = (C * ‖z‖) * ‖z‖ ^ n₀ := by ring
        _ < ‖PowerSeries.coeff n₀ f‖ * ‖z‖ ^ n₀ := by
            refine mul_lt_mul_of_pos_right ?_ (pow_pos hz0 n₀)
            have := hzlt.trans_le (min_le_right _ _)
            rw [lt_div_iff₀ hC0] at this
            linarith [this]
  rw [hrest_eq, norm_neg, norm_mul, norm_pow] at hrest
  exact lt_irrefl _ hrest

/-- **Evaluation injectivity (Strassman-type)**: a summable series vanishing on the
closed unit ball is zero.  Elementary route [Koblitz, Ch. IV]: if `f ≠ 0`, take `n₀`
minimal with `coeff n₀ f ≠ 0`; for `0 < ‖z‖` small the ultrametric estimate forces
`‖evalAt f z‖ = ‖coeff n₀ f‖·‖z‖^n₀ ≠ 0`, and such `z` exist since the norm is
nontrivial. -/
theorem eq_zero_of_forall_evalAt_eq_zero {f : PowerSeries K} (hf : AbsSummable f)
    (h : ∀ z : K, ‖z‖ ≤ 1 → evalAt f z = 0) : f = 0 :=
  (AbsSummable.tendstoCoeff hf).eq_zero_of_forall_evalAt_eq_zero h

/-- Strassman uniqueness from coefficient decay alone. -/
theorem TendstoCoeff.evalAt_injOn {f g : PowerSeries K} (hf : TendstoCoeff f)
    (hg : TendstoCoeff g) (h : ∀ z : K, ‖z‖ ≤ 1 → evalAt f z = evalAt g z) :
    f = g := by
  have hfg : TendstoCoeff (f - g) := by
    have h0 := hf.sub hg
    rw [sub_zero] at h0
    exact h0.congr fun n => (map_sub (PowerSeries.coeff n) f g).symm
  refine sub_eq_zero.mp (hfg.eq_zero_of_forall_evalAt_eq_zero fun z hz => ?_)
  have h1 := (hf.hasSum_evalAt hz).sub (hg.hasSum_evalAt hz)
  have h2 : (fun n => PowerSeries.coeff n f * z ^ n - PowerSeries.coeff n g * z ^ n)
      = fun n => PowerSeries.coeff n (f - g) * z ^ n := by
    funext n
    rw [map_sub, sub_mul]
  rw [h2] at h1
  rw [evalAt, h1.tsum_eq, h z hz, sub_self]

/-- Summable series agreeing on the closed unit ball agree. -/
theorem evalAt_injOn {f g : PowerSeries K} (hf : AbsSummable f) (hg : AbsSummable g)
    (h : ∀ z : K, ‖z‖ ≤ 1 → evalAt f z = evalAt g z) : f = g :=
  (AbsSummable.tendstoCoeff hf).evalAt_injOn (AbsSummable.tendstoCoeff hg) h

omit [CompleteSpace K] in
private theorem tendsto_uncurry_cofinite {F w : PowerSeries K} (hF : AbsSummable F)
    (hw : CoeffLeOne w) (hwS : AbsSummable w) {z : K} (hz : ‖z‖ ≤ 1) :
    Filter.Tendsto (fun p : ℕ × ℕ =>
      PowerSeries.coeff p.1 F * (PowerSeries.coeff p.2 (w ^ p.1) * z ^ p.2))
      Filter.cofinite (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hSF : {i : ℕ | ¬ ‖PowerSeries.coeff i F‖ < ε}.Finite := by
    have h1 := hF.tendsto_cofinite_zero.eventually_mem (Iio_mem_nhds hε)
    rw [Filter.eventually_cofinite] at h1
    simpa using h1
  have hTfin : ∀ i : ℕ, {j : ℕ | ¬ ‖PowerSeries.coeff j (w ^ i) * z ^ j‖
      < ε / (‖PowerSeries.coeff i F‖ + 1)}.Finite := by
    intro i
    have hpos : 0 < ε / (‖PowerSeries.coeff i F‖ + 1) := div_pos hε (by positivity)
    have h2 := (summable_norm_evalAt (absSummable_pow hwS i) hz
      ).tendsto_cofinite_zero.eventually_mem (Iio_mem_nhds hpos)
    rw [Filter.eventually_cofinite] at h2
    simpa using h2
  refine Set.Finite.subset (Set.Finite.biUnion hSF fun i _ =>
    (Set.finite_singleton i).prod (hTfin i)) ?_
  rintro ⟨i, j⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  have hB1 : ‖PowerSeries.coeff j (w ^ i) * z ^ j‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (hw.pow i j) (by positivity) (pow_le_one₀ (norm_nonneg _) hz)
  have hiS : ¬ ‖PowerSeries.coeff i F‖ < ε := by
    intro hlt
    refine hp ?_
    rw [norm_mul]
    calc ‖PowerSeries.coeff i F‖ * ‖PowerSeries.coeff j (w ^ i) * z ^ j‖
        ≤ ‖PowerSeries.coeff i F‖ * 1 :=
          mul_le_mul_of_nonneg_left hB1 (norm_nonneg _)
      _ = ‖PowerSeries.coeff i F‖ := mul_one _
      _ < ε := hlt
  have hjT : ¬ ‖PowerSeries.coeff j (w ^ i) * z ^ j‖
      < ε / (‖PowerSeries.coeff i F‖ + 1) := by
    intro hlt
    refine hp ?_
    rw [norm_mul]
    calc ‖PowerSeries.coeff i F‖ * ‖PowerSeries.coeff j (w ^ i) * z ^ j‖
        ≤ (‖PowerSeries.coeff i F‖ + 1) * ‖PowerSeries.coeff j (w ^ i) * z ^ j‖ := by
          nlinarith [norm_nonneg (PowerSeries.coeff j (w ^ i) * z ^ j)]
      _ < (‖PowerSeries.coeff i F‖ + 1) * (ε / (‖PowerSeries.coeff i F‖ + 1)) :=
          mul_lt_mul_of_pos_left hlt (by positivity)
      _ = ε := by field_simp
  exact Set.mem_biUnion hiS (Set.mem_prod.mpr ⟨rfl, hjT⟩)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem evalAt_compAn_step1 {F w : PowerSeries K} {z : K} :
    evalAt (compAn F w) z
      = ∑' j, ∑' i, PowerSeries.coeff i F * (PowerSeries.coeff j (w ^ i) * z ^ j) := by
  rw [evalAt]
  refine tsum_congr fun j => ?_
  rw [coeff_compAn, ← tsum_mul_right]
  exact tsum_congr fun i => by ring

omit [IsUltrametricDist K] in
/-- Evaluation of a power of a summable series. -/
theorem evalAt_pow {w : PowerSeries K} (hwS : AbsSummable w) {z : K}
    (hz : ‖z‖ ≤ 1) (i : ℕ) : evalAt (w ^ i) z = evalAt w z ^ i := by
  induction i with
  | zero => rw [pow_zero, pow_zero, evalAt_one]
  | succ i ih => rw [pow_succ, pow_succ, evalAt_mul (absSummable_pow hwS i) hwS hz, ih]

omit [IsUltrametricDist K] in
private theorem evalAt_compAn_inner {F w : PowerSeries K} (hwS : AbsSummable w)
    {z : K} (hz : ‖z‖ ≤ 1) (i : ℕ) :
    (∑' j, PowerSeries.coeff i F * (PowerSeries.coeff j (w ^ i) * z ^ j))
      = PowerSeries.coeff i F * evalAt w z ^ i := by
  rw [tsum_mul_left]
  congr 1
  rw [← evalAt, evalAt_pow hwS hz i]

/-- Evaluation of the analytic substitution: `(F ∘ w)(z) = F(w(z))` for `w` with
coefficients of norm `≤ 1` and summable `F` (tsum-Fubini over `coeff_compAn`). -/
theorem evalAt_compAn {F w : PowerSeries K} (hF : AbsSummable F) (hw : CoeffLeOne w)
    (hwS : AbsSummable w) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt (compAn F w) z = evalAt F (evalAt w z) := by
  have huncurry : Summable (Function.uncurry fun i j : ℕ =>
      PowerSeries.coeff i F * (PowerSeries.coeff j (w ^ i) * z ^ j)) :=
    summable_of_tendsto_cofinite (tendsto_uncurry_cofinite hF hw hwS hz)
  rw [evalAt_compAn_step1, huncurry.tsum_comm,
    tsum_congr (evalAt_compAn_inner hwS hz)]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem evalAt_C (a z : K) : evalAt (PowerSeries.C a) z = a := by
  rw [evalAt, tsum_eq_single 0
    (fun n hn => by rw [PowerSeries.coeff_C, if_neg hn, zero_mul])]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem evalAt_X (z : K) : evalAt (PowerSeries.X : PowerSeries K) z = z := by
  rw [evalAt, tsum_eq_single 1
    (fun n hn => by rw [PowerSeries.coeff_X, if_neg hn, zero_mul])]
  simp

omit [IsUltrametricDist K] in
theorem evalAt_add {f g : PowerSeries K} (hf : AbsSummable f) (hg : AbsSummable g)
    {z : K} (hz : ‖z‖ ≤ 1) : evalAt (f + g) z = evalAt f z + evalAt g z := by
  refine HasSum.tsum_eq ?_
  have h := (hasSum_evalAt hf hz).add (hasSum_evalAt hg hz)
  simpa only [map_add, add_mul] using h

omit [IsUltrametricDist K] in
theorem evalAt_linX (γ : Matrix (Fin 2) (Fin 2) K) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt (linX γ) z = γ 1 0 * z + γ 1 1 := by
  rw [linX, evalAt_add (absSummable_C _)
      (absSummable_mul (absSummable_C _) absSummable_X) hz,
    evalAt_mul (absSummable_C _) absSummable_X hz, evalAt_C, evalAt_C, evalAt_X]
  ring

omit [IsUltrametricDist K] in
theorem evalAt_numX (γ : Matrix (Fin 2) (Fin 2) K) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt (numX γ) z = γ 0 0 * z + γ 0 1 := by
  rw [numX, evalAt_add (absSummable_C _)
      (absSummable_mul (absSummable_C _) absSummable_X) hz,
    evalAt_mul (absSummable_C _) absSummable_X hz, evalAt_C, evalAt_C, evalAt_X]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- On the closed ball a dominant-constant-term linear form does not vanish. -/
theorem lin_value_ne_zero {γ : Matrix (Fin 2) (Fin 2) K}
    (h10 : ‖γ 1 0‖ < ‖γ 1 1‖) {z : K} (hz : ‖z‖ ≤ 1) : γ 1 0 * z + γ 1 1 ≠ 0 := by
  intro h0
  have h1 : γ 1 1 = -(γ 1 0 * z) := eq_neg_of_add_eq_zero_right h0
  have hn := congrArg norm h1
  rw [norm_neg, norm_mul] at hn
  nlinarith [norm_nonneg z, norm_nonneg (γ 1 0)]

omit [IsUltrametricDist K] in
theorem evalAt_linX_inv {γ : Matrix (Fin 2) (Fin 2) K} (hd : γ 1 1 ≠ 0)
    (hlt : ‖γ 1 0‖ < ‖γ 1 1‖) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt (linX γ)⁻¹ z = (γ 1 0 * z + γ 1 1)⁻¹ := by
  have hmul := evalAt_mul (WeightSeries.absSummable_linX γ) (WeightSeries.absSummable_linX_inv hd hlt) hz
  rw [PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hd), evalAt_one,
    evalAt_linX γ hz] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

omit [IsUltrametricDist K] in
theorem evalAt_mobius {γ : Matrix (Fin 2) (Fin 2) K} (hd : γ 1 1 ≠ 0)
    (hlt : ‖γ 1 0‖ < ‖γ 1 1‖) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt (mobius γ) z = (γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1) := by
  rw [mobius, evalAt_mul (WeightSeries.absSummable_numX γ) (WeightSeries.absSummable_linX_inv hd hlt) hz,
    evalAt_numX γ hz, evalAt_linX_inv hd hlt hz, div_eq_mul_inv]

omit [CompleteSpace K] in
/-- `CoeffLeOne` is closed under products (ultrametric convolution bound). -/
theorem CoeffLeOne.mul {f g : PowerSeries K} (hf : CoeffLeOne f) (hg : CoeffLeOne g) :
    CoeffLeOne (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  have hne : (Finset.antidiagonal n).Nonempty := ⟨(0, n), by simp⟩
  refine (hne.norm_sum_le_sup'_norm _).trans (Finset.sup'_le hne _ fun p hp => ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hf p.1) (norm_nonneg _) (hg p.2)

/-- `CoeffLeOne` is preserved by analytic substitution along a `CoeffLeOne` inner
series, for a summable outer series. -/
theorem coeffLeOne_compAn {F w : PowerSeries K} (hF : AbsSummable F)
    (hF1 : CoeffLeOne F) (hw : CoeffLeOne w) : CoeffLeOne (compAn F w) := by
  intro n
  rw [coeff_compAn]
  have htend : Filter.Tendsto (fun i => PowerSeries.coeff i F
      * PowerSeries.coeff n (w ^ i)) Filter.cofinite (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ?_) hF.tendsto_cofinite_zero
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hw.pow i n)
  refine (norm_tsum_le_iSup htend).trans (Real.iSup_le (fun i => ?_) zero_le_one)
  rw [norm_mul]
  exact mul_le_one₀ (hF1 i) (norm_nonneg _) (hw.pow i n)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem summable_norm_evalAt_of_le {f : PowerSeries K} {C : ℝ}
    (hbd : ∀ n, ‖PowerSeries.coeff n f‖ ≤ C) {z : K} (hz : ‖z‖ < 1) :
    Summable fun n => ‖PowerSeries.coeff n f * z ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hbd n) (by positivity)

/-- **Bounded-coefficient Strassman**: a series with coefficients bounded by `C`
vanishing on the OPEN unit ball is zero.  (The `AbsSummable` closed-ball version is
`eq_zero_of_forall_evalAt_eq_zero`; this variant serves series — like the honest
cocycle's right-hand side — that are only coefficient-bounded.) -/
private theorem eq_zero_of_forall_evalAt_eq_zero_of_le {f : PowerSeries K} {C : ℝ}
    (hbd : ∀ n, ‖PowerSeries.coeff n f‖ ≤ C)
    (h : ∀ z : K, ‖z‖ < 1 → evalAt f z = 0) : f = 0 := by
  by_contra hne
  have hex : ∃ n, PowerSeries.coeff n f ≠ 0 := by
    by_contra hall
    exact hne (PowerSeries.ext fun n => not_not.mp fun hc => hall ⟨n, hc⟩)
  classical
  set n₀ := Nat.find hex with hn₀
  have hc0 : PowerSeries.coeff n₀ f ≠ 0 := Nat.find_spec hex
  have hmin : ∀ m, m < n₀ → PowerSeries.coeff m f = 0 := fun m hm =>
    not_not.mp (Nat.find_min hex hm)
  set C' := max C 1 with hC'def
  have hC0 : (0 : ℝ) < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC : ∀ n, ‖PowerSeries.coeff n f‖ ≤ C' := fun n =>
    (hbd n).trans (le_max_left _ _)
  obtain ⟨z, hz0, hzlt⟩ := NormedField.exists_norm_lt K
    (lt_min one_pos (div_pos (norm_pos_iff.mpr hc0) hC0))
  have hz1 : ‖z‖ < 1 := hzlt.trans_le (min_le_left _ _)
  have hsumn : Summable fun n => ‖PowerSeries.coeff n f * z ^ n‖ :=
    summable_norm_evalAt_of_le hC hz1
  have hsum : Summable fun n => PowerSeries.coeff n f * z ^ n := hsumn.of_norm
  have hsplit := Summable.tsum_eq_add_tsum_ite hsum n₀
  rw [show (∑' n, PowerSeries.coeff n f * z ^ n) = evalAt f z from rfl,
    h z hz1] at hsplit
  have hrest_eq : (∑' n, if n = n₀ then 0 else PowerSeries.coeff n f * z ^ n)
      = -(PowerSeries.coeff n₀ f * z ^ n₀) :=
    eq_neg_of_add_eq_zero_right hsplit.symm
  have hite : Summable fun n => ‖if n = n₀ then (0 : K)
      else PowerSeries.coeff n f * z ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsumn
    split_ifs with hn
    · rw [norm_zero]
      positivity
    · exact le_rfl
  have hrest : ‖∑' n, if n = n₀ then 0 else PowerSeries.coeff n f * z ^ n‖
      < ‖PowerSeries.coeff n₀ f‖ * ‖z‖ ^ n₀ := by
    refine lt_of_le_of_lt (norm_tsum_le_iSup
      (Summable.of_norm hite).tendsto_cofinite_zero) ?_
    have hB0 : (0 : ℝ) ≤ C' * ‖z‖ ^ (n₀ + 1) := by positivity
    refine lt_of_le_of_lt (Real.iSup_le (fun n => ?_) hB0) ?_
    · split_ifs with hn
      · rw [norm_zero]
        exact hB0
      · rcases Nat.lt_or_ge n n₀ with hlt | hge
        · rw [hmin n hlt, zero_mul, norm_zero]
          exact hB0
        · have hn' : n₀ + 1 ≤ n := by omega
          rw [norm_mul, norm_pow]
          calc ‖PowerSeries.coeff n f‖ * ‖z‖ ^ n ≤ C' * ‖z‖ ^ n :=
                mul_le_mul_of_nonneg_right (hC n) (by positivity)
            _ ≤ C' * ‖z‖ ^ (n₀ + 1) :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hn') hC0.le
    · calc C' * ‖z‖ ^ (n₀ + 1) = (C' * ‖z‖) * ‖z‖ ^ n₀ := by ring
        _ < ‖PowerSeries.coeff n₀ f‖ * ‖z‖ ^ n₀ := by
            refine mul_lt_mul_of_pos_right ?_ (pow_pos hz0 n₀)
            have h2 := hzlt.trans_le (min_le_right _ _)
            rw [lt_div_iff₀ hC0] at h2
            linarith [h2]
  rw [hrest_eq, norm_neg, norm_mul, norm_pow] at hrest
  exact lt_irrefl _ hrest

omit [IsUltrametricDist K] in
private theorem hasSum_evalAt_of_le {f : PowerSeries K} {C : ℝ}
    (hbd : ∀ n, ‖PowerSeries.coeff n f‖ ≤ C) {z : K} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n f * z ^ n) (evalAt f z) :=
  (summable_norm_evalAt_of_le hbd hz).of_norm.hasSum

private theorem evalAt_sub_of_le {f g : PowerSeries K} {C : ℝ}
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ C) (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ C)
    {z : K} (hz : ‖z‖ < 1) : evalAt (f - g) z = evalAt f z - evalAt g z := by
  refine HasSum.tsum_eq ?_
  have h := (hasSum_evalAt_of_le hf hz).sub (hasSum_evalAt_of_le hg hz)
  simpa only [map_sub, sub_mul] using h

/-- Coefficient-bounded series agreeing on the OPEN unit ball agree. -/
private theorem evalAt_injOn_of_le {f g : PowerSeries K} {C : ℝ}
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ C) (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ C)
    (h : ∀ z : K, ‖z‖ < 1 → evalAt f z = evalAt g z) : f = g := by
  have hsub : ∀ n, ‖PowerSeries.coeff n (f - g)‖ ≤ C := fun n => by
    rw [map_sub, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) ?_)
    rw [norm_neg]
    exact hg n
  refine sub_eq_zero.mp (eq_zero_of_forall_evalAt_eq_zero_of_le hsub fun z hz => ?_)
  rw [evalAt_sub_of_le hf hg hz, h z hz, sub_self]

omit [CompleteSpace K] in
/-- A field element within `r < 1` of `1` has norm exactly `1` (isosceles). -/
private theorem norm_eq_one_of_norm_sub_one_le' {u : K} {r : ℝ} (hr1 : r < 1)
    (hu : ‖u - 1‖ ≤ r) : ‖u‖ = 1 := by
  have h1 : ‖u - 1‖ ≠ ‖(1 : K)‖ := by
    rw [norm_one]
    exact ne_of_lt (hu.trans_lt hr1)
  calc ‖u‖ = ‖u - 1 + 1‖ := by rw [sub_add_cancel]
    _ = max ‖u - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
    _ = 1 := by rw [norm_one, max_eq_right (hu.trans hr1.le)]

variable (K) in
/-- **The `r`-ball of principal units** (`0 ≤ r < 1`): units of the field within `r`
of `1`.  The honest domain of [Jacobs, Def 1.27]'s locally analytic character —
`unitPow` is multiplicative exactly here (`unitPow_mul`'s hypotheses). -/
def oneUnits (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : Subgroup Kˣ where
  carrier := {u | ‖(u : K) - 1‖ ≤ r}
  one_mem' := by simpa using hr0
  mul_mem' := fun {u v} hu hv => by
    have hun : ‖(u : K)‖ = 1 := norm_eq_one_of_norm_sub_one_le' hr1 hu
    have hkey : ((u * v : Kˣ) : K) - 1
        = (u : K) * ((v : K) - 1) + ((u : K) - 1) := by
      rw [Units.val_mul]
      ring
    show ‖((u * v : Kˣ) : K) - 1‖ ≤ r
    rw [hkey]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hu)
    rw [norm_mul, hun, one_mul]
    exact hv
  inv_mem' := fun {u} hu => by
    have hun : ‖(u : K)‖ = 1 := norm_eq_one_of_norm_sub_one_le' hr1 hu
    have hkey : ((u⁻¹ : Kˣ) : K) - 1 = ((u : K))⁻¹ * (1 - (u : K)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, mul_one,
        inv_mul_cancel₀ (Units.ne_zero u)]
    show ‖((u⁻¹ : Kˣ) : K) - 1‖ ≤ r
    rw [hkey, norm_mul, norm_inv, hun, inv_one, one_mul, norm_sub_rev]
    exact hu

omit [CompleteSpace K] in
@[simp] theorem mem_oneUnits_iff {r : ℝ} {hr0 : 0 ≤ r} {hr1 : r < 1} {u : Kˣ} :
    u ∈ oneUnits K r hr0 hr1 ↔ ‖(u : K) - 1‖ ≤ r :=
  Iff.rfl

omit [CompleteSpace K] in
/-- Principal units have norm one. -/
theorem norm_eq_one_of_mem_oneUnits {r : ℝ} {hr0 : 0 ≤ r} {hr1 : r < 1} {u : Kˣ}
    (hu : u ∈ oneUnits K r hr0 hr1) : ‖(u : K)‖ = 1 :=
  norm_eq_one_of_norm_sub_one_le' hr1 hu

omit [CompleteSpace K] in
/-- **The level criterion**: for `‖c‖ ≤ r`, `‖d − 1‖ ≤ r` and `z` on the closed unit
ball, the unit `c·z + d` is a principal `r`-unit — the discharge lemma for
`ExpansionData.mem_level` at concrete levels. -/
theorem levelUnit_mem_oneUnits {r : ℝ} {hr0 : 0 ≤ r} {hr1 : r < 1} {c d z : K}
    (hc : ‖c‖ ≤ r) (hd : ‖d - 1‖ ≤ r) (hz : ‖z‖ ≤ 1)
    (hu : IsUnit (c * z + d)) : hu.unit ∈ oneUnits K r hr0 hr1 := by
  show ‖((hu.unit : Kˣ) : K) - 1‖ ≤ r
  rw [IsUnit.unit_spec, show c * z + d - 1 = c * z + (d - 1) from by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hd)
  rw [norm_mul]
  exact (mul_le_mul hc hz (norm_nonneg _) ((norm_nonneg c).trans hc)).trans_eq
    (mul_one r)

variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}

/-- **The honest-character weight datum** ([Jacobs, Def 1.27] verbatim): a character κ
multiplicative on units, together with the power-series expansion of `κ(cz + d)` at
zero for each level element, evaluating to κ on the closed unit ball. -/
structure ExpansionData (S : Submonoid (Matrix (Fin 2) (Fin 2) K)) (ρ : ℝ)
    (U : Subgroup Kˣ) (κ : U →* Kˣ) where
  bounds : LevelBounds S ρ
  /-- The expansion of `κ(c·x + d)` at zero. -/
  col : K → K → PowerSeries K
  rowDecay : ∀ {g}, g ∈ S → ∀ m : ℕ, ‖PowerSeries.coeff m (col (g 1 0) (g 1 1))‖ ≤ ρ ^ m
  /-- The level's values lie in the character's domain ([Jacobs, p. 29]: the thesis
  only ever evaluates κ at `cx + d` with `c ≡ 0`, `d ≡ 1 (mod 9)` — 1-units). -/
  mem_level : ∀ {g}, g ∈ S → ∀ z : K, ‖z‖ ≤ 1 →
    ∀ hu : IsUnit (g 1 0 * z + g 1 1), hu.unit ∈ U
  /-- The expansion evaluates to the character: for `‖z‖ ≤ 1` and `cz + d` a unit,
  `(κcol)(z) = κ(cz + d)`. -/
  eval : ∀ {g} (hg : g ∈ S) (z : K) (hz : ‖z‖ ≤ 1)
    (hu : IsUnit (g 1 0 * z + g 1 1)),
    evalAt (col (g 1 0) (g 1 1)) z = (κ ⟨hu.unit, mem_level hg z hz hu⟩ : K)

namespace ExpansionData

variable {U : Subgroup Kˣ} {κ : U →* Kˣ}

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem absSummable_col (E : ExpansionData S ρ U κ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : AbsSummable (E.col (g 1 0) (g 1 1)) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => E.rowDecay hg n)
    (summable_geometric_of_lt_one E.bounds.rho_nonneg E.bounds.rho_lt_one)

omit [IsUltrametricDist K] in
/-- The pointwise automorphy-factor cocycle on the closed ball:
`lin(δγ)(z) = lin δ (w_γ z) · lin γ (z)` — 2×2 matrix algebra evaluated. -/
theorem lin_eval_cocycle (E : ExpansionData S ρ U κ) {γ δ : Matrix (Fin 2) (Fin 2) K}
    (hγ : γ ∈ S) (_hδ : δ ∈ S) {z : K} (hz : ‖z‖ ≤ 1) :
    (δ * γ) 1 0 * z + (δ * γ) 1 1
      = (δ 1 0 * evalAt (mobius γ) z + δ 1 1) * (γ 1 0 * z + γ 1 1) := by
  have hd : γ 1 1 ≠ 0 := E.bounds.d_ne_zero hγ
  have hlt : ‖γ 1 0‖ < ‖γ 1 1‖ := by
    rw [E.bounds.d_unit hγ]
    exact (E.bounds.c_le hγ).trans_lt E.bounds.rho_lt_one
  have hne : γ 1 0 * z + γ 1 1 ≠ 0 := lin_value_ne_zero hlt hz
  rw [evalAt_mobius hd hlt hz, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  field_simp
  ring

private theorem col_zero_one' (E : ExpansionData S ρ U κ) : E.col 0 1 = 1 := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) K) ∈ S := one_mem S
  have h10 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [Matrix.one_apply_ne (by decide)]
  have h11 : (1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := Matrix.one_apply_eq _
  have habs : AbsSummable (E.col 0 1) := by
    have h := E.absSummable_col h1
    rwa [h10, h11] at h
  refine evalAt_injOn habs (by simpa using absSummable_C (1 : K)) fun z hz => ?_
  have hu : IsUnit ((1 : Matrix (Fin 2) (Fin 2) K) 1 0 * z
      + (1 : Matrix (Fin 2) (Fin 2) K) 1 1) := by
    rw [h10, h11, zero_mul, zero_add]
    exact isUnit_one
  have huval : (hu.unit : K) = 1 := by
    rw [IsUnit.unit_spec, h10, h11, zero_mul, zero_add]
  rw [evalAt_one, ← h10]
  nth_rewrite 1 [← h11]
  rw [E.eval h1 z hz hu,
    show (⟨hu.unit, E.mem_level h1 z hz hu⟩ : U) = 1 from
      Subtype.ext (Units.ext huval),
    map_one, Units.val_one]

private theorem cocycle' (E : ExpansionData S ρ U κ) {γ δ : Matrix (Fin 2) (Fin 2) K}
    (hγS : γ ∈ S) (hδS : δ ∈ S) :
    E.col ((δ * γ) 1 0) ((δ * γ) 1 1)
      = E.col (γ 1 0) (γ 1 1)
        * compAn (E.col (δ 1 0) (δ 1 1)) (mobius γ) := by
  have hδγS : δ * γ ∈ S := mul_mem hδS hγS
  have hone : ρ ≤ 1 := E.bounds.rho_lt_one.le
  have hργ : CoeffLeOne (E.col (γ 1 0) (γ 1 1)) := fun n =>
    (E.rowDecay hγS n).trans (pow_le_one₀ E.bounds.rho_nonneg hone)
  have hρδ : CoeffLeOne (E.col (δ 1 0) (δ 1 1)) := fun n =>
    (E.rowDecay hδS n).trans (pow_le_one₀ E.bounds.rho_nonneg hone)
  have hρδγ : CoeffLeOne (E.col ((δ * γ) 1 0) ((δ * γ) 1 1)) := fun n =>
    (E.rowDecay hδγS n).trans (pow_le_one₀ E.bounds.rho_nonneg hone)
  have hd : γ 1 1 ≠ 0 := E.bounds.d_ne_zero hγS
  have hlt : ‖γ 1 0‖ < ‖γ 1 1‖ := by
    rw [E.bounds.d_unit hγS]
    exact (E.bounds.c_le hγS).trans_lt E.bounds.rho_lt_one
  have hltδ : ‖δ 1 0‖ < ‖δ 1 1‖ := by
    rw [E.bounds.d_unit hδS]
    exact (E.bounds.c_le hδS).trans_lt E.bounds.rho_lt_one
  have hwc : CoeffLeOne (mobius γ) :=
    WeightSeries.coeffLeOne_mobius' (E.bounds.integral hγS 0 0)
      (E.bounds.integral hγS 0 1) (E.bounds.d_unit hγS)
      ((E.bounds.c_le hγS).trans hone)
  have hwS : AbsSummable (mobius γ) :=
    absSummable_mul (WeightSeries.absSummable_numX γ)
      (WeightSeries.absSummable_linX_inv hd hlt)
  have hcompbd : CoeffLeOne (compAn (E.col (δ 1 0) (δ 1 1)) (mobius γ)) :=
    coeffLeOne_compAn (E.absSummable_col hδS) hρδ hwc
  refine evalAt_injOn_of_le (C := 1) hρδγ (CoeffLeOne.mul hργ hcompbd)
    fun z hz => ?_
  have hz1 : ‖z‖ ≤ 1 := hz.le
  set z' := evalAt (mobius γ) z with hz'def
  have hz'1 : ‖z'‖ ≤ 1 := norm_evalAt_le_one hwS hwc hz1
  have hneγ : γ 1 0 * z + γ 1 1 ≠ 0 := lin_value_ne_zero hlt hz1
  have hneδ : δ 1 0 * z' + δ 1 1 ≠ 0 := lin_value_ne_zero hltδ hz'1
  have huγ : IsUnit (γ 1 0 * z + γ 1 1) := isUnit_iff_ne_zero.mpr hneγ
  have huδ : IsUnit (δ 1 0 * z' + δ 1 1) := isUnit_iff_ne_zero.mpr hneδ
  have hlin := E.lin_eval_cocycle hγS hδS hz1
  rw [← hz'def] at hlin
  have huδγ : IsUnit ((δ * γ) 1 0 * z + (δ * γ) 1 1) := by
    rw [hlin]
    exact huδ.mul huγ
  rw [E.eval hδγS z hz1 huδγ,
    evalAt_mul_of_summable_norm (summable_norm_evalAt (E.absSummable_col hγS) hz1)
      (summable_norm_evalAt_of_le hcompbd hz),
    E.eval hγS z hz1 huγ,
    evalAt_compAn (E.absSummable_col hδS) hwc hwS hz1, ← hz'def,
    E.eval hδS z' hz'1 huδ]
  have hunit : (⟨huδγ.unit, E.mem_level hδγS z hz1 huδγ⟩ : U)
      = ⟨huγ.unit, E.mem_level hγS z hz1 huγ⟩
        * ⟨huδ.unit, E.mem_level hδS z' hz'1 huδ⟩ := by
    refine Subtype.ext (Units.ext ?_)
    show ((huδγ.unit : Kˣ) : K) = ((huγ.unit * huδ.unit : Kˣ) : K)
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec, hlin]
    ring
  rw [hunit, map_mul, Units.val_mul]

/-- **The constructor** ([Jacobs, Def 1.27] made honest for every character with an
expansion): the `WeightSeries` whose cocycle is DERIVED from multiplicativity of κ via
evaluation injectivity. -/
noncomputable def toWeightSeries (E : ExpansionData S ρ U κ) : WeightSeries S ρ where
  bounds := E.bounds
  col := E.col
  col_zero_one := E.col_zero_one'
  rowDecay := E.rowDecay
  absSummable := fun hg => E.absSummable_col hg
  cocycle := fun hγ hδ => E.cocycle' hγ hδ

@[simp] theorem toWeightSeries_col (E : ExpansionData S ρ U κ) (c d : K) :
    E.toWeightSeries.col c d = E.col c d :=
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- On the level, `c·z + d` is a unit for every `z` on the closed unit ball
(`‖c‖ ≤ ρ < 1 = ‖d‖`). -/
theorem isUnit_lin (E : ExpansionData S ρ U κ) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S)
    {z : K} (hz : ‖z‖ ≤ 1) : IsUnit (g 1 0 * z + g 1 1) := by
  refine isUnit_iff_ne_zero.mpr (lin_value_ne_zero ?_ hz)
  rw [E.bounds.d_unit hg]
  exact (E.bounds.c_le hg).trans_lt E.bounds.rho_lt_one

/-- **Uniqueness of the expansion**: two expansion data for the same character agree on
the level (evaluation injectivity) — the expansion of `κ(c·z + d)` is determined by κ. -/
theorem col_eq_of_mem (E₁ E₂ : ExpansionData S ρ U κ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : E₁.col (g 1 0) (g 1 1) = E₂.col (g 1 0) (g 1 1) :=
  evalAt_injOn (E₁.absSummable_col hg) (E₂.absSummable_col hg) fun z hz => by
    rw [E₁.eval hg z hz (E₁.isUnit_lin hg hz), E₂.eval hg z hz (E₁.isUnit_lin hg hz)]

/-- Two expansion data for the same character give the same weight action. -/
theorem kappaSlash_toWeightSeries_eq (E₁ E₂ : ExpansionData S ρ U κ) (g : S) :
    E₁.toWeightSeries.kappaSlash g = E₂.toWeightSeries.kappaSlash g :=
  WeightSeries.kappaSlash_congr rfl (E₁.col_eq_of_mem E₂ g.2)

/-- Restriction of an expansion datum to a smaller level. -/
def restrict (E : ExpansionData S ρ U κ) {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    (hS : S' ≤ S) : ExpansionData S' ρ U κ where
  bounds := E.bounds.mono hS
  col := E.col
  rowDecay hg := E.rowDecay (hS hg)
  mem_level hg := E.mem_level (hS hg)
  eval hg := E.eval (hS hg)

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem restrict_col (E : ExpansionData S ρ U κ)
    {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} (hS : S' ≤ S) : (E.restrict hS).col = E.col :=
  rfl

/-- Restriction of an expansion datum to a finer level **and a smaller radius** `(S', ρ')`,
`S' ≤ S`: the expansions are unchanged; the finer decay `‖aₘ‖ ≤ ρ'^m` on `S'` is a
*hypothesis* — it is not implied by the `ρ`-decay, which records the radius and not the
integrality of the Taylor coefficients of `κ`. -/
def restrictRadius (E : ExpansionData S ρ U κ) {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    {ρ' : ℝ} (hS : S' ≤ S) (hb : LevelBounds S' ρ')
    (hdecay : ∀ {g}, g ∈ S' → ∀ m : ℕ, ‖PowerSeries.coeff m (E.col (g 1 0) (g 1 1))‖ ≤ ρ' ^ m) :
    ExpansionData S' ρ' U κ where
  bounds := hb
  col := E.col
  rowDecay := hdecay
  mem_level hg := E.mem_level (hS hg)
  eval hg := E.eval (hS hg)

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem restrictRadius_col (E : ExpansionData S ρ U κ)
    {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ' : ℝ} (hS : S' ≤ S) (hb : LevelBounds S' ρ')
    (hdecay : ∀ {g}, g ∈ S' → ∀ m : ℕ, ‖PowerSeries.coeff m (E.col (g 1 0) (g 1 1))‖ ≤ ρ' ^ m) :
    (E.restrictRadius hS hb hdecay).col = E.col :=
  rfl

end ExpansionData

variable {U : Subgroup Kˣ} {κ : U →* Kˣ}

/-- **A weight analytic at wild level `(S, ρ)`**: a character `κ : U →* Kˣ` of a subgroup of
units (typically the principal units `oneUnits`) **together with** its expansion datum — the
power series `κ(c·z + d)` at every level element, with its decay, and the fact that it
evaluates to `κ` ([Jacobs, Def 1.27]: "by `κ(cz + d)` we mean the power series expansion of
`κ(cz + d)` at zero"; [Buzzard, §8 p. 66]: "we will have to somehow single out one such
thickening, which we do (rather arbitrarily) in the definition below").  These are Buzzard's
"`t`-analytic weights", the input of `QMF.Weight.Forms`.

The expansion is carried as *data* rather than as a mere existence statement so that the
weight's action is computable by `rfl` from its column (no `Classical.choice`); it is
nevertheless determined by the character on the level (`ExpansionData.col_eq_of_mem`), so
two weights with the same character act identically (`kappaSlash_eq`).

The wild level is part of the *weight* (and not only of the level `U`) because
analyticity is a joint condition on `κ` and `α`: the action of `(a b; c d)` evaluates
`κ` on the disc `d + c·(closed unit ball)`, whose radius is the wild level, and the
weight-`κ` module `A_κ` (the right-`Σ_α`-module of Def 1.27) exists only for `α` beyond
the analyticity radius of `κ` — see the design note in `PhD/QMF/Weight/Forms.lean`.
`AnalyticWeight.restrict` passes to finer levels.

This is the public weight API; the underlying `WeightSeries` (the expansion with its
action-law facts) is the engine and is not meant to be used directly downstream. -/
structure AnalyticWeight (U : Subgroup Kˣ) (S : Submonoid (Matrix (Fin 2) (Fin 2) K))
    (ρ : ℝ) where
  /-- The character. -/
  toChar : U →* Kˣ
  /-- Its expansion datum at the level. -/
  expansion : ExpansionData S ρ U toChar

namespace AnalyticWeight

variable (κ : AnalyticWeight U S ρ)

/-- The weight datum (expansion of `κ(c·x + d)` with the action-law facts) of a weight.
Implementation detail: downstream code should use `kappaSlash` and the lemmas below. -/
noncomputable def toWeightSeries : WeightSeries S ρ :=
  κ.expansion.toWeightSeries

@[simp] theorem toWeightSeries_col (c d : K) : κ.toWeightSeries.col c d = κ.expansion.col c d :=
  rfl

/-- **The weight-`κ` action** of `g ∈ S` on the Tate algebra `c(ℕ, K)`
([Jacobs, Def 1.27]): `z^k ↦ κ(cz + d)/(cz + d)² · ((az + b)/(cz + d))^k`. -/
noncomputable def kappaSlash (g : S) : c(ℕ, K) →L[K] c(ℕ, K) :=
  κ.toWeightSeries.kappaSlash g

theorem kappaSlash_def (g : S) : κ.kappaSlash g = κ.toWeightSeries.kappaSlash g :=
  rfl

/-- **The action depends only on the character**: any other expansion datum for
`κ.toChar` gives the same action (the expansion is unique on the level,
`ExpansionData.col_eq_of_mem`). -/
theorem kappaSlash_eq (E : ExpansionData S ρ U κ.toChar) (g : S) :
    κ.kappaSlash g = E.toWeightSeries.kappaSlash g :=
  ExpansionData.kappaSlash_toWeightSeries_eq κ.expansion E g

/-- The identity acts trivially. -/
theorem kappaSlash_one : κ.kappaSlash 1 = ContinuousLinearMap.id K c(ℕ, K) :=
  κ.toWeightSeries.kappaSlash_one

/-- **The right-action law** ([Jacobs, Def 1.27]'s "easy check"). -/
theorem kappaSlash_mul (g h : S) :
    κ.kappaSlash (g * h) = (κ.kappaSlash h).comp (κ.kappaSlash g) :=
  κ.toWeightSeries.kappaSlash_mul g h

/-- **[Jacobs, Proposition 2.6]**: the matrix of `kappaSlash g` is the coefficient array
of the generating function `κ(cx+d)/((cx+d)(cx+d−axy−by))`. -/
theorem matrixCoeff_kappaSlash (g : S) (j i : ℕ) :
    matrixCoeff (κ.kappaSlash g) j i
      = MvPowerSeries.coeff (idx j i) (κ.toWeightSeries.genFun g.1) :=
  κ.toWeightSeries.matrixCoeff_kappaSlash g j i

/-- The Tate algebra as a right `S`-module via the weight-`κ` action — Def 1.27's `A_κ`. -/
@[instance_reducible]
noncomputable def kappaSlashAction : RightSlashAction S c(ℕ, K) :=
  κ.toWeightSeries.kappaSlashAction

/-- The weight action commutes with scalars. -/
theorem smulSlashClass :
    letI := κ.kappaSlashAction
    RightSlashAction.SMulSlashClass K S c(ℕ, K) :=
  κ.toWeightSeries.smulSlashClass

/-- **`U_ϖ` acts compactly** ([Jacobs, Lemma 2.7]; [Buzzard, Lemma 12.2] at the level of a
single matrix): the weight-`κ` action of `g ∈ S` with `‖det g‖ ≤ σ < 1`, `ρ ≤ σ`, is a
compactoid operator on the Tate algebra. -/
theorem isCompactoid_kappaSlash (g : S) {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1)
    (hdet : ‖g.1.det‖ ≤ σ) : IsCompactoid (κ.kappaSlash g) :=
  κ.toWeightSeries.isCompactoid_kappaSlash_of_norm_det_le g hρσ hσ hdet

/-- **Restriction to a finer level**: a weight analytic at `S` is analytic at every
`S' ≤ S` (same character, same expansion). -/
def restrict {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} (hS : S' ≤ S) :
    AnalyticWeight U S' ρ :=
  ⟨κ.toChar, κ.expansion.restrict hS⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem restrict_toChar {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} (hS : S' ≤ S) :
    (κ.restrict hS).toChar = κ.toChar :=
  rfl

/-- The restricted weight acts as the original on the finer level. -/
theorem kappaSlash_restrict {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} (hS : S' ≤ S)
    (g : S') : (κ.restrict hS).kappaSlash g = κ.kappaSlash ⟨g.1, hS g.2⟩ :=
  WeightSeries.kappaSlash_congr rfl rfl

/-- **Restriction to a finer level and a smaller radius**: a weight analytic at `(S, ρ)` is
analytic at `(S', ρ')` for `S' ≤ S` once the finer decay of
its expansions on `S'` is known ([Buzzard, §13 p. 79]: "the inclusion `B_r ⊆ B_{r'}` induces
an injection `A_{κ,r'} → A_{κ,r}`"). -/
def restrictRadius {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ' : ℝ} (hS : S' ≤ S)
    (hb : LevelBounds S' ρ')
    (hdecay : ∀ {g}, g ∈ S' → ∀ m : ℕ,
      ‖PowerSeries.coeff m (κ.expansion.col (g 1 0) (g 1 1))‖ ≤ ρ' ^ m) :
    AnalyticWeight U S' ρ' :=
  ⟨κ.toChar, κ.expansion.restrictRadius hS hb hdecay⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem restrictRadius_toChar {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ' : ℝ}
    (hS : S' ≤ S) (hb : LevelBounds S' ρ')
    (hdecay : ∀ {g}, g ∈ S' → ∀ m : ℕ,
      ‖PowerSeries.coeff m (κ.expansion.col (g 1 0) (g 1 1))‖ ≤ ρ' ^ m) :
    (κ.restrictRadius hS hb hdecay).toChar = κ.toChar :=
  rfl

/-- The radius-restricted weight acts as the original on the finer level. -/
theorem kappaSlash_restrictRadius {S' : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ' : ℝ}
    (hS : S' ≤ S) (hb : LevelBounds S' ρ')
    (hdecay : ∀ {g}, g ∈ S' → ∀ m : ℕ,
      ‖PowerSeries.coeff m (κ.expansion.col (g 1 0) (g 1 1))‖ ≤ ρ' ^ m) (g : S') :
    (κ.restrictRadius hS hb hdecay).kappaSlash g = κ.kappaSlash ⟨g.1, hS g.2⟩ :=
  WeightSeries.kappaSlash_congr rfl rfl

end AnalyticWeight

end QMF
