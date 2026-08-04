import PhD.TateFredholm.Pr

/-!
# Residue machinery for Serre's theorem

Sub-development for `isPotentiallyONable_of_uniformizer` (see `BaseChange.lean`),
produced by the `/develop --decompose` pass.  Source: [Bel] §II.1.4 (Hypothesis II.1.11,
Lemma II.1.12, Theorem II.1.13, p. 58); ultimately [Serre] Prop. 1.  The tree:
discreteness of the value group (`R1`), the unit ball and its residue field (`R2`–`R4`),
a quotient-free "residue basis" interface (`R5`), successive approximation
(`R6a`–`R6b`, the analytic heart), assembly over discrete norms (`R6`), and the
norm-rescaling step (`R7`) feeding the final theorem.
See `.mathlib-quality/decomposition.md` for source quotes and per-leaf verification. -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

section SerreResidue

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **R1.**  Discreteness: under the largest-norm-`< 1` hypothesis the value group is
`‖π‖^ℤ`.  [Bel] p. 58: "the set of non-zero norms `|R∗|` is the discrete subgroup
`|π|^ℤ`". -/
theorem exists_norm_eq_zpow (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖) {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hb : 1 < ‖π‖⁻¹ := (one_lt_inv₀ hπ0).2 hπ1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hxpos hb
  rw [inv_zpow] at hn1 hn2
  have hπne : π ≠ 0 := fun h => by simp [h] at hπ0
  set y := x * π ^ n with hy
  have hynorm : ‖y‖ = ‖x‖ * ‖π‖ ^ n := by rw [hy, norm_mul, norm_zpow]
  have hnpos : (0 : ℝ) < ‖π‖ ^ n := zpow_pos hπ0 n
  have hy1 : 1 ≤ ‖y‖ := by
    rw [hynorm]
    have := mul_le_mul_of_nonneg_right hn1 hnpos.le
    rwa [inv_mul_cancel₀ hnpos.ne'] at this
  have hy2 : ‖y‖ < ‖π‖⁻¹ := by
    rw [hynorm]
    calc ‖x‖ * ‖π‖ ^ n < (‖π‖ ^ (n + 1))⁻¹ * ‖π‖ ^ n :=
          mul_lt_mul_of_pos_right hn2 hnpos
    _ = ‖π‖ ^ n / ‖π‖ ^ (n + 1) := by rw [div_eq_mul_inv, mul_comm]
    _ = ‖π‖ ^ (n - (n + 1)) := (zpow_sub₀ hπ0.ne' n (n + 1)).symm
    _ = ‖π‖⁻¹ := by rw [show n - (n + 1) = -1 by ring, zpow_neg_one]
  have hyeq : ‖y‖ = 1 := by
    rcases lt_or_eq_of_le hy1 with hgt | heq
    · exfalso
      have h0y : (0 : ℝ) < ‖y‖ := lt_trans zero_lt_one hgt
      have hinv : ‖y⁻¹‖ < 1 := by
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hgt
      have hle := hπmax _ hinv
      rw [norm_inv] at hle
      have h1y : (1 : ℝ) ≤ ‖π‖ * ‖y‖ := by
        calc (1 : ℝ) = ‖y‖⁻¹ * ‖y‖ := (inv_mul_cancel₀ h0y.ne').symm
        _ ≤ ‖π‖ * ‖y‖ := mul_le_mul_of_nonneg_right hle h0y.le
      have hcon : ‖π‖⁻¹ ≤ ‖y‖ := by
        calc ‖π‖⁻¹ = ‖π‖⁻¹ * 1 := (mul_one _).symm
        _ ≤ ‖π‖⁻¹ * (‖π‖ * ‖y‖) := mul_le_mul_of_nonneg_left h1y (inv_pos.2 hπ0).le
        _ = ‖y‖ := by rw [← mul_assoc, inv_mul_cancel₀ hπ0.ne', one_mul]
      exact absurd hcon (not_le.2 hy2)
    · exact heq.symm
  refine ⟨-n, ?_⟩
  have hprod : ‖x‖ * ‖π‖ ^ n = 1 := by rw [← hynorm]; exact hyeq
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hprod

/-- **R2.**  The unit ball `K⁰ = {x : ‖x‖ ≤ 1}` is a subring ([Bel] p. 58: "`R⁰` the set
of elements of `R` such that `|r| ≤ 1`, which is a subring of `R`"). -/
def unitBall (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x : K | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    calc ‖a * b‖ = ‖a‖ * ‖b‖ := norm_mul a b
    _ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg b) zero_le_one
    _ = 1 := one_mul 1
  one_mem' := by
    show ‖(1 : K)‖ ≤ 1
    rw [norm_one]
  add_mem' := fun {a b} ha hb => by
    show ‖a + b‖ ≤ 1
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by
    show ‖(0 : K)‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rwa [norm_neg]

/-- **R3.**  Units of the unit ball are the norm-one elements. -/
theorem unitBall_isUnit_iff (x : unitBall K) : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖((u : unitBall K) : K)‖ ≤ 1 := (u : unitBall K).2
    have h2 : ‖(((u⁻¹ : (unitBall K)ˣ) : unitBall K) : K)‖ ≤ 1 :=
      ((u⁻¹ : (unitBall K)ˣ) : unitBall K).2
    have hprod : ((u : unitBall K) : K) * (((u⁻¹ : (unitBall K)ˣ) : unitBall K) : K) = 1 := by
      exact_mod_cast congrArg Subtype.val u.mul_inv
    have hnorm : ‖((u : unitBall K) : K)‖ * ‖(((u⁻¹ : (unitBall K)ˣ) : unitBall K) : K)‖
        = 1 := by rw [← norm_mul, hprod, norm_one]
    nlinarith [norm_nonneg ((u : unitBall K) : K),
      norm_nonneg (((u⁻¹ : (unitBall K)ˣ) : unitBall K) : K)]
  · intro hx
    have hxne : (x : K) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      exact zero_ne_one hx
    refine ⟨⟨x, ⟨(x : K)⁻¹, ?_⟩, ?_, ?_⟩, rfl⟩
    · show ‖(x : K)⁻¹‖ ≤ 1
      rw [norm_inv, hx, inv_one]
    · exact Subtype.ext (by simp [mul_inv_cancel₀ hxne])
    · exact Subtype.ext (by simp [inv_mul_cancel₀ hxne])

/-- **R4.**  `(π)` is a maximal ideal of `K⁰` (so `K⁰/(π)` is the residue *field*, via
`Ideal.Quotient.field`) — the general-`K` form of [Bel]'s "`M̃` has a basis over `𝔽_p`". -/
theorem isMaximal_span_pi (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖) :
    (Ideal.span {(⟨π, hπ1.le⟩ : unitBall K)}).IsMaximal := by
  set πO : unitBall K := ⟨π, hπ1.le⟩ with hπO
  have hmem : ∀ x : unitBall K, x ∈ Ideal.span {πO} ↔ ‖(x : K)‖ ≤ ‖π‖ := by
    intro x
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      show ‖((πO * c : unitBall K) : K)‖ ≤ ‖π‖
      calc ‖((πO * c : unitBall K) : K)‖ = ‖π * (c : K)‖ := rfl
      _ = ‖π‖ * ‖(c : K)‖ := norm_mul _ _
      _ ≤ ‖π‖ * 1 := mul_le_mul_of_nonneg_left c.2 hπ0.le
      _ = ‖π‖ := mul_one _
    · intro hx
      have hπne : π ≠ 0 := fun h => by simp [h] at hπ0
      refine ⟨⟨(x : K) / π, ?_⟩, ?_⟩
      · show ‖(x : K) / π‖ ≤ 1
        rw [norm_div]
        exact div_le_one_of_le₀ hx (norm_nonneg π)
      · refine Subtype.ext ?_
        show (x : K) = π * ((x : K) / π)
        field_simp
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h1
    have := (hmem 1).1 h1
    rw [OneMemClass.coe_one, norm_one] at this
    exact absurd this (not_le.2 hπ1)
  · intro J x hJ hxnot hxJ
    have hx1 : ‖(x : K)‖ = 1 := by
      have hxle : ‖(x : K)‖ ≤ 1 := x.2
      rcases lt_or_eq_of_le hxle with hlt | heq
      · exact absurd ((hmem x).2 (hπmax _ hlt)) hxnot
      · exact heq
    obtain ⟨u, hu⟩ := (unitBall_isUnit_iff x).2 hx1
    have h1eq : (1 : unitBall K) = ((u⁻¹ : (unitBall K)ˣ) : unitBall K) * x := by
      rw [← hu]
      exact u.inv_mul.symm
    rw [h1eq]
    exact J.mul_mem_left _ hxJ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
  [CompleteSpace E]

-- **R5** (`exists_residue_approx`) is stated below `exists_residueBasis`, which proves it.
-- It indexes by a subset of `E`, as Serre's residue-basis construction produces: an
-- `∃ (ι : Type _)` phrasing would bind a universe independent of `E` and be unprovable.

/-- Private helper for **R6a**: the unit-ball case.  Iterating the one-step approximation
`happrox` on the successively rescaled residuals `F n` (with `‖F n‖ ≤ 1`) produces cumulative
coefficient families `A n : ι →₀ K` whose per-index increments are `≤ ‖π‖ⁿ`; these are Cauchy in
the complete field `K`, and the limit family `a` is `C₀` (decay from the finite supports of the
`A n` plus the geometric tail bound `‖a i - (A n) i‖ ≤ ‖π‖ⁿ`) and sums to `m`. -/
private theorem exists_hasSum_of_norm_le_one (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    {ι : Type*} (e : ι → E) (he : ∀ i, ‖e i‖ = 1)
    (happrox : ∀ m : E, ‖m‖ ≤ 1 → ∃ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) ∧
      ‖m - a.sum fun i c => c • e i‖ ≤ ‖π‖) (m : E) (hm : ‖m‖ ≤ 1) :
    ∃ ac : c(ι, K), (∀ i, ‖ac i‖ ≤ 1) ∧ HasSum (fun i => ac i • e i) m := by
  classical
  have hπne : π ≠ 0 := fun h => by simp [h] at hπ0
  set L : (ι →₀ K) →ₗ[K] E := Finsupp.linearCombination K e with hL
  have hLapp : ∀ f : ι →₀ K, L f = f.sum (fun i x => x • e i) := fun f =>
    Finsupp.linearCombination_apply K f
  set cc : E → (ι →₀ K) := fun v => if h : ‖v‖ ≤ 1 then Classical.choose (happrox v h) else 0
    with hcc
  have hcc_spec : ∀ v : E, ‖v‖ ≤ 1 →
      (∀ i, ‖(cc v) i‖ ≤ 1) ∧ ‖v - L (cc v)‖ ≤ ‖π‖ := by
    intro v hv
    have hcv : cc v = Classical.choose (happrox v hv) := dif_pos hv
    have hspec := Classical.choose_spec (happrox v hv)
    rw [hcv, hLapp]
    exact ⟨hspec.1, hspec.2⟩
  set gg : E → E := fun v => π⁻¹ • (v - L (cc v)) with hgg
  set F : ℕ → E := fun n => gg^[n] m with hFdef
  have hF0 : F 0 = m := by simp [hFdef]
  have hFsucc : ∀ n, F (n + 1) = gg (F n) := fun n => by
    simp only [hFdef, Function.iterate_succ_apply']
  have hFle : ∀ n, ‖F n‖ ≤ 1 := by
    intro n
    induction n with
    | zero => rw [hF0]; exact hm
    | succ k ih =>
      rw [hFsucc]
      show ‖π⁻¹ • (F k - L (cc (F k)))‖ ≤ 1
      rw [norm_smul, norm_inv]
      calc ‖π‖⁻¹ * ‖F k - L (cc (F k))‖ ≤ ‖π‖⁻¹ * ‖π‖ :=
            mul_le_mul_of_nonneg_left (hcc_spec (F k) ih).2 (by positivity)
        _ = 1 := inv_mul_cancel₀ hπ0.ne'
  set bc : ℕ → (ι →₀ K) := fun n => cc (F n) with hbc
  have hbc1 : ∀ n i, ‖(bc n) i‖ ≤ 1 := fun n => (hcc_spec (F n) (hFle n)).1
  have hres : ∀ n, F n - L (bc n) = π • F (n + 1) := by
    intro n
    rw [hFsucc]
    show F n - L (bc n) = π • (π⁻¹ • (F n - L (cc (F n))))
    rw [smul_smul, mul_inv_cancel₀ hπne, one_smul]
  set A : ℕ → (ι →₀ K) := fun n => ∑ k ∈ Finset.range n, (π ^ k) • (bc k) with hA
  have hA0 : A 0 = 0 := by simp only [hA, Finset.range_zero, Finset.sum_empty]
  have hAsucc : ∀ k, A (k + 1) = A k + (π ^ k) • (bc k) := by
    intro k; simp only [hA, Finset.sum_range_succ]
  have hmLA : ∀ n, m - L (A n) = (π ^ n) • F n := by
    intro n
    induction n with
    | zero => rw [hA0, map_zero, sub_zero, pow_zero, one_smul, hF0]
    | succ k ih =>
      rw [hAsucc k, map_add, map_smul,
        show m - (L (A k) + (π ^ k) • L (bc k)) = (m - L (A k)) - (π ^ k) • L (bc k) from by abel,
        ih, ← smul_sub, hres k, smul_smul, ← pow_succ]
  have hAsucc_apply : ∀ k i, (A (k + 1)) i = (A k) i + (π ^ k) * (bc k) i := by
    intro k i
    rw [hAsucc k, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hincr : ∀ k i, ‖(A (k + 1)) i - (A k) i‖ ≤ ‖π‖ ^ k := by
    intro k i
    rw [hAsucc_apply, add_sub_cancel_left, norm_mul, norm_pow]
    calc ‖π‖ ^ k * ‖(bc k) i‖ ≤ ‖π‖ ^ k * 1 :=
          mul_le_mul_of_nonneg_left (hbc1 k i) (by positivity)
      _ = ‖π‖ ^ k := mul_one _
  have hcauchy : ∀ i, CauchySeq (fun n => (A n) i) := by
    intro i
    refine cauchySeq_of_le_geometric ‖π‖ 1 hπ1 (fun n => ?_)
    rw [one_mul, dist_eq_norm, norm_sub_rev]
    exact hincr n i
  choose a ha using fun i => cauchySeq_tendsto_of_complete (hcauchy i)
  have htail_fin : ∀ i n p, n ≤ p → ‖(A p) i - (A n) i‖ ≤ ‖π‖ ^ n := by
    intro i n p hnp
    induction p, hnp using Nat.le_induction with
    | base => rw [sub_self, norm_zero]; positivity
    | succ p hp ih =>
      rw [show (A (p + 1)) i - (A n) i
          = ((A (p + 1)) i - (A p) i) + ((A p) i - (A n) i) from by abel]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hincr p i).trans (pow_le_pow_of_le_one (norm_nonneg π) hπ1.le hp)
  have htail : ∀ i n, ‖a i - (A n) i‖ ≤ ‖π‖ ^ n := by
    intro i n
    refine le_of_tendsto (((ha i).sub_const ((A n) i)).norm) ?_
    filter_upwards [Filter.eventually_ge_atTop n] with p hp
    exact htail_fin i n p hp
  have ha1 : ∀ i, ‖a i‖ ≤ 1 := by
    intro i
    have h0 := htail i 0
    simpa only [hA0, Finsupp.zero_apply, sub_zero, pow_zero] using h0
  have hdecay : Tendsto (a : ι → K) cofinite (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ1
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (A n).support.finite_toSet (fun i hi => ?_)
    simp only [Set.mem_setOf_eq, not_lt] at hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro hAn0
    have hb : ‖a i‖ ≤ ‖π‖ ^ n := by
      have := htail i n; rwa [hAn0, sub_zero] at this
    exact absurd hi (not_le.2 (lt_of_le_of_lt hb hn))
  refine ⟨⟨⟨(a : Ix ι → K), continuous_of_discreteTopology⟩, ?_⟩, ?_, ?_⟩
  · rw [Filter.cocompact_eq_cofinite]; exact hdecay
  · intro i; exact ha1 i
  · show HasSum (fun i => a i • e i) m
    refine Metric.tendsto_atTop.2 (fun ε hε => ?_)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ1
    refine ⟨(A n).support, fun T hT => ?_⟩
    rw [dist_eq_norm]
    have hsub : (A n).support ⊆ T := hT
    have hLAn : L (A n) = ∑ i ∈ T, (A n) i • e i := by
      rw [hLapp]
      exact Finsupp.sum_of_support_subset (A n) hsub _ (fun i _ => zero_smul K (e i))
    have hmLAn : m - (∑ i ∈ T, (A n) i • e i) = (π ^ n) • F n := by
      rw [← hLAn]; exact hmLA n
    have hsum_sub : (∑ i ∈ T, (a i - (A n) i) • e i)
        = (∑ i ∈ T, a i • e i) - (∑ i ∈ T, (A n) i • e i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => sub_smul (a i) ((A n) i) (e i))
    have hdiff : (∑ i ∈ T, a i • e i) - m
        = (∑ i ∈ T, (a i - (A n) i) • e i) - (π ^ n) • F n := by
      rw [hsum_sub, ← hmLAn]; abel
    rw [hdiff]
    have hb1 : ‖∑ i ∈ T, (a i - (A n) i) • e i‖ ≤ ‖π‖ ^ n :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        (fun i _ => by rw [norm_smul, he i, mul_one]; exact htail i n)
    have hb2 : ‖(π ^ n) • F n‖ ≤ ‖π‖ ^ n := by
      rw [norm_smul, norm_pow]
      calc ‖π‖ ^ n * ‖F n‖ ≤ ‖π‖ ^ n * 1 :=
            mul_le_mul_of_nonneg_left (hFle n) (by positivity)
        _ = ‖π‖ ^ n := mul_one _
    calc ‖(∑ i ∈ T, (a i - (A n) i) • e i) - (π ^ n) • F n‖
        ≤ max ‖∑ i ∈ T, (a i - (A n) i) • e i‖ ‖(π ^ n) • F n‖ := by
          rw [sub_eq_add_neg]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans_eq (by rw [norm_neg])
      _ ≤ ‖π‖ ^ n := max_le hb1 hb2
      _ < ε := hn

/-- **R6a.**  Successive approximation (the analytic heart, [Bel] Lemma II.1.12 proof):
given a residue-approximating family, every vector has a `c(ι, K)`-expansion realising
its norm. -/
theorem exists_expansion_of_residue_approx (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hE : ∀ m : E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n)
    {ι : Type*} (e : ι → E) (he : ∀ i, ‖e i‖ = 1)
    (happrox : ∀ m : E, ‖m‖ ≤ 1 → ∃ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) ∧
      ‖m - a.sum fun i c => c • e i‖ ≤ ‖π‖) (m : E) :
    ∃ a : c(ι, K), HasSum (fun i => a i • e i) m ∧ (⨆ i, ‖a i‖) = ‖m‖ := by
  rcases eq_or_ne m 0 with rfl | hm0
  · refine ⟨0, ?_, ?_⟩
    · have hz : (fun i => (0 : c(ι, K)) i • e i) = fun _ : ι => (0 : E) := by
        funext i; show (0 : K) • e i = 0; rw [zero_smul]
      rw [hz]; exact hasSum_zero
    · rw [← cSpace.norm_eq_iSup, norm_zero, norm_zero]
  · have hπne : π ≠ 0 := fun h => by simp [h] at hπ0
    obtain ⟨n, hn⟩ := hE m hm0
    set s : K := π ^ n with hs
    have hs0 : s ≠ 0 := zpow_ne_zero n hπne
    have hsnorm : ‖s‖ = ‖π‖ ^ n := by rw [hs, norm_zpow]
    set m' : E := s⁻¹ • m with hm'
    have hm'1 : ‖m'‖ = 1 := by
      rw [hm', norm_smul, norm_inv, hsnorm, hn, inv_mul_cancel₀ (ne_of_gt (zpow_pos hπ0 n))]
    obtain ⟨ac', hac'_i, hac'_sum⟩ :=
      exists_hasSum_of_norm_le_one π hπ0 hπ1 e he happrox m' hm'1.le
    have hsummand_tendsto : Tendsto (fun i => ac' i • e i) cofinite (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have heq : (fun i => ‖ac' i • e i‖) = fun i => ‖ac' i‖ := by
        funext i; rw [norm_smul, he i, mul_one]
      rw [heq]
      simpa using (cSpace.tendsto_cofinite ac').norm
    have hsup_le : ⨆ i, ‖ac' i‖ ≤ 1 := by
      rcases isEmpty_or_nonempty ι with hι | hι
      · rw [Real.iSup_of_isEmpty]; exact zero_le_one
      · exact ciSup_le hac'_i
    have hm'_le : ‖m'‖ ≤ ⨆ i, ‖ac' i‖ := by
      have hle := norm_tsum_le_iSup hsummand_tendsto
      rw [hac'_sum.tsum_eq] at hle
      refine hle.trans_eq (iSup_congr (fun i => ?_))
      rw [norm_smul, he i, mul_one]
    have hsup_ac' : ⨆ i, ‖ac' i‖ = 1 := le_antisymm hsup_le (hm'1 ▸ hm'_le)
    refine ⟨s • ac', ?_, ?_⟩
    · have h1 : HasSum (fun i => s • (ac' i • e i)) (s • m') := hac'_sum.const_smul s
      have h2 : s • m' = m := by rw [hm', smul_smul, mul_inv_cancel₀ hs0, one_smul]
      have heq : (fun i => (s • ac') i • e i) = fun i => s • (ac' i • e i) := by
        funext i; show (s • ac' i) • e i = s • (ac' i • e i); rw [smul_assoc]
      rw [heq, ← h2]; exact h1
    · have hpull : ∀ i, ‖(s • ac') i‖ = ‖π‖ ^ n * ‖ac' i‖ := by
        intro i; show ‖s • ac' i‖ = ‖π‖ ^ n * ‖ac' i‖; rw [norm_smul, hsnorm]
      rw [iSup_congr hpull, ← Real.mul_iSup_of_nonneg (zpow_nonneg (norm_nonneg π) n),
        hsup_ac', mul_one, ← hn]

/-- Private helper for **R6b**: with residue independence, any (plain-function) coefficient
family `x` summing to `0` and with unit-ball entries has every entry of norm `≤ ‖π‖`.  Truncate
`x` to a finite set `S ∋ i` on which the partial sum is `< ‖π‖` (possible since the sum is `0`),
then apply the independence hypothesis to the finitely-supported truncation. -/
private theorem norm_coeff_le_of_hasSum_zero (π : K) (hπ0 : 0 < ‖π‖)
    {ι : Type*} (e : ι → E)
    (hindep : ∀ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) →
      ‖a.sum fun i c => c • e i‖ ≤ ‖π‖ → ∀ i, ‖a i‖ ≤ ‖π‖)
    (x : ι → K) (hx1 : ∀ i, ‖x i‖ ≤ 1) (hx : HasSum (fun i => x i • e i) 0) :
    ∀ i, ‖x i‖ ≤ ‖π‖ := by
  classical
  intro i
  obtain ⟨S₀, hS₀⟩ := Metric.tendsto_atTop.1 hx ‖π‖ hπ0
  set S : Finset ι := insert i S₀ with hSdef
  have hiS : i ∈ S := Finset.mem_insert_self i S₀
  have hpartial : ‖∑ j ∈ S, x j • e j‖ ≤ ‖π‖ := by
    have h := hS₀ S (Finset.subset_insert i S₀)
    rw [dist_zero_right] at h
    exact h.le
  have hfmem : ∀ j, (if j ∈ S then x j else 0) ≠ 0 → j ∈ S := by
    intro j hj
    by_contra h
    rw [if_neg h] at hj
    exact hj rfl
  set A : ι →₀ K := Finsupp.onFinset S (fun j => if j ∈ S then x j else 0) hfmem with hAdef
  have hAval : ∀ j, A j = if j ∈ S then x j else 0 := fun j => Finsupp.onFinset_apply
  have hA1 : ∀ j, ‖A j‖ ≤ 1 := by
    intro j
    rw [hAval j]
    split
    · exact hx1 j
    · rw [norm_zero]; exact zero_le_one
  have hsupp : A.support ⊆ S := by rw [hAdef]; exact Finsupp.support_onFinset_subset
  have hsum_eq : (A.sum fun j c => c • e j) = ∑ j ∈ S, x j • e j := by
    rw [Finsupp.sum_of_support_subset A hsupp _ (fun j _ => zero_smul K (e j))]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hAval j, if_pos hj]
  have hbound : ‖A.sum fun j c => c • e j‖ ≤ ‖π‖ := by rw [hsum_eq]; exact hpartial
  have hkey := hindep A hA1 hbound i
  rw [hAval i, if_pos hiS] at hkey
  exact hkey

/-- **R6b.**  Coefficient uniqueness from residue independence ([Bel] Lemma II.1.12,
converse direction of the expansion). -/
theorem expansion_unique_of_residue_indep (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    {ι : Type*} (e : ι → E)
    (hindep : ∀ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) →
      ‖a.sum fun i c => c • e i‖ ≤ ‖π‖ → ∀ i, ‖a i‖ ≤ ‖π‖)
    {a b : c(ι, K)} {m : E}
    (ha : HasSum (fun i => a i • e i) m) (hb : HasSum (fun i => b i • e i) m) :
    a = b := by
  classical
  -- The difference `a - b` (as a plain coefficient function) sums to `0`.
  have hd0 : HasSum (fun i => (a i - b i) • e i) 0 := by
    have h := ha.sub hb
    rw [sub_self] at h
    simpa only [← sub_smul] using h
  -- A uniform bound on the coefficient differences.
  set C : ℝ := ‖a‖ + ‖b‖ with hCdef
  have hbnd : ∀ i, ‖a i - b i‖ ≤ C := by
    intro i
    calc ‖a i - b i‖ ≤ ‖a i‖ + ‖b i‖ := norm_sub_le _ _
      _ ≤ ‖a‖ + ‖b‖ := add_le_add (cSpace.norm_apply_le a i) (cSpace.norm_apply_le b i)
  -- Scale down by a large power of a norm-`> 1` element so all coefficients are `≤ 1`.
  obtain ⟨w, hw⟩ := NormedField.exists_one_lt_norm K
  have hw0 : w ≠ 0 := by rintro rfl; rw [norm_zero] at hw; exact absurd hw (by norm_num)
  have hwi : ‖w⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hw
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖w⁻¹‖ ^ N * C ≤ 1 := by
    have htend : Tendsto (fun n : ℕ => ‖w⁻¹‖ ^ n * C) atTop (𝓝 (0 * C)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hwi).mul_const C
    rw [zero_mul] at htend
    obtain ⟨N, hN'⟩ := Metric.tendsto_atTop.1 htend 1 one_pos
    refine ⟨N, ?_⟩
    have h := hN' N le_rfl
    rw [dist_zero_right, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h.le
  set t : K := w⁻¹ ^ N with htdef
  have ht0 : t ≠ 0 := pow_ne_zero N (inv_ne_zero hw0)
  have htnorm : ‖t‖ = ‖w⁻¹‖ ^ N := by rw [htdef, norm_pow]
  set d₀ : ι → K := fun i => t * (a i - b i) with hd₀def
  have hd₀1 : ∀ i, ‖d₀ i‖ ≤ 1 := by
    intro i
    simp only [hd₀def]
    calc ‖t * (a i - b i)‖ = ‖t‖ * ‖a i - b i‖ := norm_mul _ _
      _ ≤ ‖w⁻¹‖ ^ N * C := by
          rw [htnorm]; exact mul_le_mul_of_nonneg_left (hbnd i) (by positivity)
      _ ≤ 1 := hN
  have hd₀sum : HasSum (fun i => d₀ i • e i) 0 := by
    have h := hd0.const_smul t
    rw [smul_zero] at h
    simpa only [hd₀def, smul_smul] using h
  -- Geometric decay: `‖d₀ i‖ ≤ ‖π‖ ^ n` for every `n`, obtained by rescaling and re-applying
  -- the truncation lemma.
  have hgeo : ∀ n : ℕ, ∀ i, ‖d₀ i‖ ≤ ‖π‖ ^ n := by
    intro n
    induction n with
    | zero => intro i; rw [pow_zero]; exact hd₀1 i
    | succ k ih =>
      have hpk0 : (0 : ℝ) < ‖π‖ ^ k := pow_pos hπ0 k
      set y : ι → K := fun i => (π ^ k)⁻¹ * d₀ i with hydef
      have hy1 : ∀ i, ‖y i‖ ≤ 1 := by
        intro i
        simp only [hydef]
        calc ‖(π ^ k)⁻¹ * d₀ i‖ = (‖π‖ ^ k)⁻¹ * ‖d₀ i‖ := by
              rw [norm_mul, norm_inv, norm_pow]
          _ ≤ (‖π‖ ^ k)⁻¹ * ‖π‖ ^ k := mul_le_mul_of_nonneg_left (ih i) (by positivity)
          _ = 1 := inv_mul_cancel₀ hpk0.ne'
      have hysum : HasSum (fun i => y i • e i) 0 := by
        have h := hd₀sum.const_smul ((π ^ k)⁻¹)
        rw [smul_zero] at h
        simpa only [hydef, smul_smul] using h
      have hykey := norm_coeff_le_of_hasSum_zero π hπ0 e hindep y hy1 hysum
      intro i
      have hyi := hykey i
      simp only [hydef] at hyi
      rw [norm_mul, norm_inv, norm_pow] at hyi
      have hstep : ‖d₀ i‖ ≤ ‖π‖ ^ k * ‖π‖ := by
        have h2 := mul_le_mul_of_nonneg_left hyi hpk0.le
        rwa [← mul_assoc, mul_inv_cancel₀ hpk0.ne', one_mul] at h2
      rw [pow_succ]; exact hstep
  -- Hence every coefficient difference is `0`.
  have hd₀0 : ∀ i, d₀ i = 0 := by
    intro i
    have hle : ‖d₀ i‖ ≤ 0 :=
      ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ1)
        (fun n => hgeo n i)
    exact norm_le_zero_iff.1 hle
  refine DFunLike.ext a b (fun i => ?_)
  have h := hd₀0 i
  simp only [hd₀def] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left ht0)

/-- Reindexing isometry of model spaces along a bijection of index types (same construction as
in `isONable_cSpace`, parameterised by the bijection). -/
private def cSpaceCongr {ι κ : Type*} (σ : ι ≃ κ) : c(ι, K) ≃ₗᵢ[K] c(κ, K) where
  toFun g := ⟨⟨fun x => g (σ.symm x), continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    exact (cSpace.tendsto_cofinite g).comp σ.symm.injective.tendsto_cofinite⟩
  invFun h := ⟨⟨fun i => h (σ i), continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    exact (cSpace.tendsto_cofinite h).comp σ.injective.tendsto_cofinite⟩
  map_add' g h := DFunLike.ext _ _ fun _ => rfl
  map_smul' r g := DFunLike.ext _ _ fun _ => rfl
  left_inv g := DFunLike.ext _ _ fun i => congrArg g (Equiv.symm_apply_apply σ i)
  right_inv h := DFunLike.ext _ _ fun x => congrArg h (Equiv.apply_symm_apply σ x)
  norm_map' g := by
    rw [cSpace.norm_eq_iSup, cSpace.norm_eq_iSup, iSup, iSup]
    congr 1
    exact σ.symm.surjective.range_comp fun i => ‖g i‖

/-- Private helper for **R6**: the residue-basis data assembles into an isometric `K`-linear
equivalence `E ≃ₗᵢ c(ι, K)`.  The forward map is the coefficient map from the
successive-approximation expansion (`R6a`); it is `K`-linear and injective by the uniqueness of
expansions (`R6b`), surjective with inverse `f ↦ ∑' i, f i • e i` (ultrametric completeness), and
norm-preserving because the expansion realises the norm. -/
private theorem nonempty_isometryEquiv_of_residue (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hE : ∀ m : E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n)
    {ι : Type*} (e : ι → E) (he : ∀ i, ‖e i‖ = 1)
    (happrox : ∀ m : E, ‖m‖ ≤ 1 → ∃ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) ∧
      ‖m - a.sum fun i c => c • e i‖ ≤ ‖π‖)
    (hindep : ∀ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) →
      ‖a.sum fun i c => c • e i‖ ≤ ‖π‖ → ∀ i, ‖a i‖ ≤ ‖π‖) :
    Nonempty (E ≃ₗᵢ[K] c(ι, K)) := by
  classical
  choose coef hcoef_sum hcoef_sup using
    fun m => exists_expansion_of_residue_approx π hπ0 hπ1 hE e he happrox m
  have hadd : ∀ (f g : c(ι, K)) (i : ι), (f + g) i = f i + g i := by
    intro f g i
    simpa only [cSpace.evalCLM_apply] using map_add (cSpace.evalCLM i) f g
  have hsmul : ∀ (r : K) (f : c(ι, K)) (i : ι), (r • f) i = r * f i := by
    intro r f i
    simpa only [cSpace.evalCLM_apply, smul_eq_mul] using map_smul (cSpace.evalCLM i) r f
  have hsummable : ∀ f : c(ι, K), Summable (fun i => f i • e i) := by
    intro f
    apply summable_of_tendsto_cofinite
    have heq : (fun i => ‖f i • e i‖) = fun i => ‖f i‖ := by
      funext i; rw [norm_smul, he i, mul_one]
    rw [tendsto_zero_iff_norm_tendsto_zero, heq]
    simpa using (cSpace.tendsto_cofinite f).norm
  have hrecon_sum : ∀ f : c(ι, K), HasSum (fun i => f i • e i) (∑' i, f i • e i) :=
    fun f => (hsummable f).hasSum
  have hcoef_add : ∀ m m', coef (m + m') = coef m + coef m' := by
    intro m m'
    refine expansion_unique_of_residue_indep π hπ0 hπ1 e hindep (hcoef_sum (m + m')) ?_
    have hfun : (fun i => (coef m + coef m') i • e i)
        = fun i => coef m i • e i + coef m' i • e i := by
      funext i; rw [hadd, add_smul]
    rw [hfun]; exact (hcoef_sum m).add (hcoef_sum m')
  have hcoef_smul : ∀ (r : K) m, coef (r • m) = r • coef m := by
    intro r m
    refine expansion_unique_of_residue_indep π hπ0 hπ1 e hindep (hcoef_sum (r • m)) ?_
    have hfun : (fun i => (r • coef m) i • e i) = fun i => r • (coef m i • e i) := by
      funext i; rw [hsmul, mul_smul]
    rw [hfun]; exact (hcoef_sum m).const_smul r
  have hleft : ∀ f, coef (∑' i, f i • e i) = f := fun f =>
    expansion_unique_of_residue_indep π hπ0 hπ1 e hindep (hcoef_sum _) (hrecon_sum f)
  have hright : ∀ m, (∑' i, coef m i • e i) = m := fun m => (hcoef_sum m).tsum_eq
  have hnorm : ∀ m, ‖coef m‖ = ‖m‖ := fun m => by
    rw [cSpace.norm_eq_iSup]; exact hcoef_sup m
  exact ⟨{
    toFun := coef
    invFun := fun f => ∑' i, f i • e i
    map_add' := hcoef_add
    map_smul' := hcoef_smul
    left_inv := hright
    right_inv := hleft
    norm_map' := hnorm }⟩

private theorem chain_fin {c : Set (Set E)} (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (t : Finset E) (ht : (↑t : Set E) ⊆ ⋃₀ c) : ∃ T ∈ c, (↑t : Set E) ⊆ T := by
  classical
  revert ht
  induction t using Finset.induction with
  | empty => intro _; obtain ⟨T, hT⟩ := hne; exact ⟨T, hT, by simp⟩
  | insert x t hx ih =>
    intro ht
    rw [Finset.coe_insert, Set.insert_subset_iff] at ht
    obtain ⟨Tx, hTxc, hxTx⟩ := ht.1
    obtain ⟨T, hTc, htT⟩ := ih ht.2
    rcases hc.total hTxc hTc with h | h
    · exact ⟨T, hTc, by rw [Finset.coe_insert, Set.insert_subset_iff]; exact ⟨h hxTx, htT⟩⟩
    · exact ⟨Tx, hTxc, by rw [Finset.coe_insert, Set.insert_subset_iff]; exact ⟨hxTx, htT.trans h⟩⟩

private theorem norm_eq_one_of_pi_lt (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) {m : E}
    (hlo : ‖π‖ < ‖m‖) (hhi : ‖m‖ ≤ 1) (hE : ∀ x : E, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n) :
    ‖m‖ = 1 := by
  have hm0 : m ≠ 0 := by intro h; rw [h, norm_zero] at hlo; exact absurd hlo (not_lt.2 hπ0.le)
  obtain ⟨k, hk⟩ := hE m hm0
  rcases lt_or_eq_of_le hhi with hlt | heq
  · exfalso
    rw [hk, ← Real.rpow_intCast ‖π‖ k] at hlt hlo
    have h1 : (0 : ℝ) < (k : ℝ) := by
      have hh : ‖π‖ ^ (k : ℝ) < ‖π‖ ^ (0 : ℝ) := by rw [Real.rpow_zero]; exact hlt
      exact (Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ0 hπ1).1 hh
    have h2 : (k : ℝ) < 1 := by
      have hh : ‖π‖ ^ (1 : ℝ) < ‖π‖ ^ (k : ℝ) := by rw [Real.rpow_one]; exact hlo
      exact (Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ0 hπ1).1 hh
    have hk0 : (0:ℤ) < k := by exact_mod_cast h1
    have hk1 : k < 1 := by exact_mod_cast h2
    omega
  · exact heq

private theorem exists_residueBasis (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hE : ∀ m : E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n) :
    ∃ s : Set E, (∀ x ∈ s, ‖x‖ = 1) ∧
      (∀ m : E, ‖m‖ ≤ 1 → ∃ a : s →₀ K, (∀ i, ‖a i‖ ≤ 1) ∧
        ‖m - a.sum fun i c => c • (i : E)‖ ≤ ‖π‖) ∧
      (∀ a : s →₀ K, (∀ i, ‖a i‖ ≤ 1) →
        ‖a.sum fun i c => c • (i : E)‖ ≤ ‖π‖ → ∀ i, ‖a i‖ ≤ ‖π‖) := by
  classical
  set L : (E →₀ K) →ₗ[K] E := Finsupp.linearCombination K (id : E → E) with hLdef
  have hLapp : ∀ A : E →₀ K, L A = A.sum (fun i c => c • i) := by
    intro A
    rw [hLdef, Finsupp.linearCombination_apply]
    show (∑ i ∈ A.support, A i • id i) = ∑ i ∈ A.support, A i • i
    exact Finset.sum_congr rfl (fun i _ => rfl)
  have hLsingle : ∀ (x : E) (c : K), L (Finsupp.single x c) = c • x := by
    intro x c; rw [hLapp, Finsupp.sum_single_index (zero_smul K x)]
  let P : Set E → Prop := fun S =>
    (∀ x ∈ S, ‖x‖ = 1) ∧
    (∀ A : E →₀ K, (↑A.support ⊆ S) → (∀ i, ‖A i‖ ≤ 1) →
      ‖L A‖ ≤ ‖π‖ → ∀ i, ‖A i‖ ≤ ‖π‖)
  obtain ⟨M, hMmax⟩ := zorn_subset {S | P S} (by
    intro c hcsub hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro x hx
      obtain ⟨T, hTc, hxT⟩ := hx
      exact (hcsub hTc).1 x hxT
    · intro A hAsub hA1 hAL i
      rcases c.eq_empty_or_nonempty with hce | hcne
      · rw [hce, Set.sUnion_empty] at hAsub
        have hA0 : A = 0 := by
          rw [← Finsupp.support_eq_empty, ← Finset.coe_eq_empty]
          exact Set.subset_empty_iff.mp hAsub
        rw [hA0, Finsupp.zero_apply, norm_zero]; exact hπ0.le
      · obtain ⟨T, hTc, hAT⟩ := chain_fin hchain hcne A.support hAsub
        exact (hcsub hTc).2 A hAT hA1 hAL i)
  have hMP : P M := hMmax.1
  refine ⟨M, hMP.1, ?_, ?_⟩
  · -- happrox
    intro m hm
    by_contra hcon
    push_neg at hcon
    have hmgt : ‖π‖ < ‖m‖ := by
      have h := hcon 0 (fun i => by rw [Finsupp.zero_apply, norm_zero]; exact zero_le_one)
      rwa [Finsupp.sum_zero_index, sub_zero] at h
    have hm1 : ‖m‖ = 1 := norm_eq_one_of_pi_lt π hπ0 hπ1 hmgt hm hE
    have hmM : m ∉ M := by
      intro hmM
      have h := hcon (Finsupp.single ⟨m, hmM⟩ 1) (fun i => by
        rw [Finsupp.single_apply]; split
        · rw [norm_one]
        · rw [norm_zero]; exact zero_le_one)
      rw [Finsupp.sum_single_index (zero_smul K ((⟨m, hmM⟩ : M) : E)), one_smul,
        show ((⟨m, hmM⟩ : M) : E) = m from rfl, sub_self, norm_zero] at h
      exact absurd h (not_lt.2 hπ0.le)
    have hPins : P (insert m M) := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Set.mem_insert_iff.mp hx with h | h
        · rw [h]; exact hm1
        · exact hMP.1 x h
      · intro A hAsub hA1 hAL i
        set cco : K := A m with hccodef
        set B : E →₀ K := A - Finsupp.single m cco with hBdef
        have hLB : L B = L A - cco • m := by rw [hBdef, map_sub, hLsingle]
        have hBsupp : ↑B.support ⊆ M := by
          intro x hx
          rw [Finset.mem_coe, Finsupp.mem_support_iff, hBdef, Finsupp.sub_apply,
            Finsupp.single_apply] at hx
          by_cases hxm : m = x
          · exact absurd (by rw [if_pos hxm, hccodef, hxm]; exact sub_self (A x)) hx
          · rw [if_neg hxm, sub_zero] at hx
            have hxins : x ∈ insert m M :=
              hAsub (by rw [Finset.mem_coe, Finsupp.mem_support_iff]; exact hx)
            rcases Set.mem_insert_iff.mp hxins with h | h
            · exact (hxm h.symm).elim
            · exact h
        have hB1 : ∀ x, ‖B x‖ ≤ 1 := by
          intro x
          rw [hBdef, Finsupp.sub_apply, Finsupp.single_apply]
          by_cases hxm : m = x
          · rw [if_pos hxm, hccodef, hxm, sub_self, norm_zero]; exact zero_le_one
          · rw [if_neg hxm, sub_zero]; exact hA1 x
        have hcco_le : ‖cco‖ ≤ ‖π‖ := by
          by_contra hcocon
          push_neg at hcocon
          have hcco1 : ‖cco‖ = 1 := by
            rcases lt_or_eq_of_le (show ‖cco‖ ≤ 1 by rw [hccodef]; exact hA1 m) with hlt | heq
            · exact absurd (hπmax cco hlt) (not_le.2 hcocon)
            · exact heq
          have hcco0 : cco ≠ 0 := by
            intro h; rw [h, norm_zero] at hcco1; exact zero_ne_one hcco1
          have hccinv : ‖cco⁻¹‖ = 1 := by rw [norm_inv, hcco1, inv_one]
          set A'' : E →₀ K := (-cco⁻¹) • B with hA''def
          have hA''supp : ↑A''.support ⊆ M :=
            (Finset.coe_subset.mpr Finsupp.support_smul).trans hBsupp
          have hA''1 : ∀ x, ‖A'' x‖ ≤ 1 := by
            intro x
            rw [hA''def, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_neg, hccinv, one_mul]
            exact hB1 x
          set a'' : M →₀ K := A''.subtypeDomain (· ∈ M) with ha''def
          have ha''1 : ∀ i, ‖a'' i‖ ≤ 1 := by
            intro i; rw [ha''def, Finsupp.subtypeDomain_apply]; exact hA''1 i
          have hsumeq : (a''.sum fun i c => c • (i:E)) = L A'' := by
            rw [ha''def, hLapp]
            exact Finsupp.sum_subtypeDomain_index (h := fun (x:E) (c:K) => c • x)
              (fun x hx => hA''supp (Finset.mem_coe.mpr hx))
          have hmA'' : m - L A'' = cco⁻¹ • L A := by
            have hLA'' : L A'' = (-cco⁻¹) • L B := by rw [hA''def, map_smul]
            rw [hLA'', hLB, neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hcco0, one_smul]
            abel
          have hfinal : ‖m - (a''.sum fun i c => c • (i:E))‖ ≤ ‖π‖ := by
            rw [hsumeq, hmA'', norm_smul, hccinv, one_mul]; exact hAL
          exact absurd (hcon a'' ha''1) (not_lt.2 hfinal)
        have hccom : ‖cco • m‖ ≤ ‖π‖ := by
          rw [norm_smul]
          calc ‖cco‖ * ‖m‖ ≤ ‖π‖ * 1 := mul_le_mul hcco_le hm (norm_nonneg m) hπ0.le
            _ = ‖π‖ := mul_one _
        have hLBle : ‖L B‖ ≤ ‖π‖ := by
          rw [hLB, sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hAL ?_)
          rw [norm_neg]; exact hccom
        have hBpi := hMP.2 B hBsupp hB1 hLBle
        by_cases hi : m = i
        · rw [← hi, ← hccodef]; exact hcco_le
        · have hAB : A i = B i := by
            rw [hBdef, Finsupp.sub_apply, Finsupp.single_apply, if_neg hi, sub_zero]
          rw [hAB]; exact hBpi i
    have hins : insert m M ⊆ M := hMmax.2 hPins (Set.subset_insert m M)
    exact hmM (hins (Set.mem_insert m M))
  · -- hindep
    intro a ha1 haL i
    set emb : M ↪ E := Function.Embedding.subtype (· ∈ M) with hembdef
    set A : E →₀ K := a.embDomain emb with hAdef
    have hAsupp : ↑A.support ⊆ M := by
      rw [hAdef, Finsupp.support_embDomain]
      intro x hx
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨j, _, rfl⟩ := hx
      exact j.2
    have hA1 : ∀ x, ‖A x‖ ≤ 1 := fun x => by
      rw [hAdef, Finsupp.embDomain_apply]
      split
      · exact ha1 _
      · rw [norm_zero]; exact zero_le_one
    have hAL2 : ‖L A‖ ≤ ‖π‖ := by
      rw [hAdef, hLdef, Finsupp.linearCombination_embDomain, Finsupp.linearCombination_apply]
      exact haL
    have hres := hMP.2 A hAsupp hA1 hAL2 (emb i)
    rw [hAdef, Finsupp.embDomain_apply_self] at hres
    exact hres

/-- **R5.**  Residue-basis interface (quotient-free phrasing): there is a family of
norm-one vectors whose residues mod `π` form a basis — spanning = one-step approximation,
independence = norms detect residues.  The index is a subset of `E` rather than an
existentially quantified type: `∃ ι : Type _` would bind a universe independent of `E`. -/
theorem exists_residue_approx (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hE : ∀ m : E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n) :
    ∃ (s : Set E) (e : s → E), (∀ i, ‖e i‖ = 1) ∧
      (∀ m : E, ‖m‖ ≤ 1 → ∃ a : s →₀ K, (∀ i, ‖a i‖ ≤ 1) ∧
        ‖m - a.sum fun i c => c • e i‖ ≤ ‖π‖) ∧
      (∀ a : s →₀ K, (∀ i, ‖a i‖ ≤ 1) →
        ‖a.sum fun i c => c • e i‖ ≤ ‖π‖ → ∀ i, ‖a i‖ ≤ ‖π‖) := by
  obtain ⟨s, hs1, happrox, hindep⟩ := exists_residueBasis π hπ0 hπ1 hπmax hE
  exact ⟨s, fun i => (i : E), fun i => hs1 i i.2, happrox, hindep⟩

/-- **R6.**  Assembly: a Banach space whose norms lie in `‖π‖^ℤ ∪ {0}` is ONable
([Bel] Lemma II.1.12, packaged for our iso-based `IsONable`). -/
theorem isONable_of_discrete_norms (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hE : ∀ m : E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n) :
    IsONable K E := by
  classical
  obtain ⟨s, hs1, happrox, hindep⟩ := exists_residueBasis π hπ0 hπ1 hπmax hE
  obtain ⟨Φ⟩ := nonempty_isometryEquiv_of_residue π hπ0 hπ1 hE (Subtype.val : s → E)
    (fun i => hs1 i.1 i.2) happrox hindep
  exact ⟨Set.range (Subtype.val : s → E),
    ⟨Φ.trans (cSpaceCongr (Equiv.ofInjective (Subtype.val : s → E) Subtype.coe_injective))⟩⟩

open Classical in
/-- **R7 data.**  The rescaled norm of [Bel] Theorem II.1.13's proof:
`‖m‖′ = inf {‖π‖^n : n ∈ ℤ, ‖m‖ ≤ ‖π‖^n}`, in closed form via the floor of a log
ratio (`0` at `m = 0`). -/
noncomputable def rescale (π : K) (m : E) : ℝ :=
  if m = 0 then 0 else ‖π‖ ^ (⌊Real.log ‖m‖ / Real.log ‖π‖⌋ : ℤ)

/-- The rescaled norm is nonnegative. -/
theorem rescale_nonneg (π : K) (m : E) : 0 ≤ rescale (E := E) π m := by
  rw [rescale]
  split
  · exact le_rfl
  · exact zpow_nonneg (norm_nonneg π) _

/-- The rescaled norm is monotone in the original norm. -/
theorem rescale_le_rescale (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) {a b : E}
    (ha : a ≠ 0) (h : ‖a‖ ≤ ‖b‖) : rescale π a ≤ rescale (E := E) π b := by
  have hb : b ≠ 0 := by
    intro hb0
    rw [hb0, norm_zero] at h
    exact ha (norm_le_zero_iff.1 h)
  have hlogπ : Real.log ‖π‖ < 0 := Real.log_neg hπ0 hπ1
  have hdiv : Real.log ‖b‖ / Real.log ‖π‖ ≤ Real.log ‖a‖ / Real.log ‖π‖ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonpos_right (Real.log_le_log (norm_pos_iff.2 ha) h)
      (inv_nonpos.2 hlogπ.le)
  rw [rescale, if_neg ha, rescale, if_neg hb, ← Real.rpow_intCast, ← Real.rpow_intCast]
  exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hπ0 hπ1).2
    (by exact_mod_cast Int.floor_le_floor hdiv)

/-- **R7a.**  Sandwich: `‖m‖ ≤ ‖m‖′ < ‖π‖⁻¹ ‖m‖` — the rescaled norm is equivalent to
the original ("a norm ... equivalent to `|·|`", [Bel] p. 58). -/
theorem le_rescale_and_rescale_lt (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) (m : E)
    (hm : m ≠ 0) :
    ‖m‖ ≤ rescale π m ∧ rescale π m < ‖π‖⁻¹ * ‖m‖ := by
  have hmpos : 0 < ‖m‖ := norm_pos_iff.2 hm
  have hlogπ : Real.log ‖π‖ < 0 := Real.log_neg hπ0 hπ1
  set L : ℝ := Real.log ‖m‖ / Real.log ‖π‖ with hL
  have hres : rescale (E := E) π m = ‖π‖ ^ ((⌊L⌋ : ℤ) : ℝ) := by
    rw [rescale, if_neg hm, ← Real.rpow_intCast]
  have hm_eq : ‖m‖ = ‖π‖ ^ L := by
    rw [Real.rpow_def_of_pos hπ0, hL, mul_comm, div_mul_cancel₀ _ hlogπ.ne,
      Real.exp_log hmpos]
  constructor
  · rw [hres]
    nth_rewrite 1 [hm_eq]
    exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hπ0 hπ1).2 (Int.floor_le L)
  · rw [hres]
    nth_rewrite 1 [hm_eq]
    rw [← Real.rpow_neg_one ‖π‖, ← Real.rpow_add hπ0]
    refine (Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ0 hπ1).2 ?_
    linarith [Int.lt_floor_add_one L]

/-- **R7b.**  The rescaled norm is ultrametric. -/
theorem rescale_add_le (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) (m n : E) :
    rescale π (m + n) ≤ max (rescale π m) (rescale π n) := by
  rcases eq_or_ne (m + n) 0 with h0 | h0
  · rw [h0, rescale, if_pos rfl]
    exact le_max_of_le_left (rescale_nonneg π m)
  · have hle := IsUltrametricDist.norm_add_le_max m n
    rcases le_total ‖m‖ ‖n‖ with hmn | hmn
    · exact le_max_of_le_right
        (rescale_le_rescale π hπ0 hπ1 h0 (hle.trans_eq (max_eq_right hmn)))
    · exact le_max_of_le_left
        (rescale_le_rescale π hπ0 hπ1 h0 (hle.trans_eq (max_eq_left hmn)))

/-- **R7c.**  The rescaled norm is exactly `K`-homogeneous (uses discreteness `R1`: every
scalar norm is a `‖π‖`-power). -/
theorem rescale_smul (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖) (c : K) (m : E) :
    rescale π (c • m) = ‖c‖ * rescale π m := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [rescale]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [rescale]
  have hcm : c • m ≠ 0 := smul_ne_zero hc hm
  have hmpos : 0 < ‖m‖ := norm_pos_iff.2 hm
  have hlogπne : Real.log ‖π‖ ≠ 0 := (Real.log_neg hπ0 hπ1).ne
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow π hπ0 hπ1 hπmax hc
  have hnorm : ‖c • m‖ = ‖π‖ ^ k * ‖m‖ := by rw [norm_smul, hk]
  have hlog : Real.log ‖c • m‖ / Real.log ‖π‖
      = (k : ℝ) + Real.log ‖m‖ / Real.log ‖π‖ := by
    rw [hnorm, Real.log_mul (zpow_pos hπ0 k).ne' hmpos.ne', Real.log_zpow, add_div,
      mul_div_cancel_right₀ _ hlogπne]
  rw [rescale, if_neg hcm, rescale, if_neg hm, hlog, Int.floor_intCast_add,
    zpow_add₀ hπ0.ne', hk]

end SerreResidue

end TateFredholm

end
