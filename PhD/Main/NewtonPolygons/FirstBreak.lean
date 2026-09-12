/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import PhD.Main.NewtonPolygons.CoeffVal
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.MulDistinguished
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassPrep

/-!
# First breaks and purity (blueprint §5.4–§5.6, and the §5.7 geometric core)

Refactor of the corresponding layer of `Test/test.lean` onto the `IsNewtonPolygonOf`
architecture:

* `HasFirstBreak f i m` — the constructed polygon's first segment has slope `m` and (nonzero)
  length `i`. Replaces the algorithm-output form
  `newtonPolygon (coeffVal K f) 0 = some (.nextVertex …)` of `Test/test.lean:153`; the bridge
  back to the algorithm is `hasFirstBreak_iff_newtonPolygon_zero`.
* `IsPureSeries f m` — the polygon of `f` is a single segment of slope `m`
  (`NewtonPolygon₀.IsPure`); blueprint Definition 5.4.
* the line bounds at the first break (`HasFirstBreak.slope_mul_le/lt`, `.norm_coeff_break_eq`)
  — the geometric core consumed by §5.6–§5.11.
* `firstBreak_gaussTerm_le/break_eq/lt` and `isMulDistinguished_of_hasFirstBreak` — the first
  break makes a polynomial `i`-distinguished at `c = exp m` (the §5.7 entry point into
  Martin's Weierstrass preparation; refactor of `Test/test.lean:689`, with the conclusion
  split one-lemma-per-part and packaged as `PowerSeries.IsMulDistinguished`).
* blueprint 5.6 (`isPureSeries_iff_distinguished`, `Test/test.lean:476`) and 5.5
  (`isPureSeries_of_irreducible`, `Test/test.lean:1175`).
-/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-! ### Driving the algorithm

`SpecConstruction.lean` keeps its step-inversion and walk lemmas private, so the pieces needed to
*drive* the algorithm on a concrete input are re-derived here: what each non-`nextVertex` output
says about the slope set, the anchor of a series with `a₀ ≠ 0`, and the fact that on a polynomial
a step with a point still ahead can only be a `nextVertex` (refactor of
`Test/test.lean:227–388`). -/

section StepInversion

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ] {w : ℕ → WithTop Γ} {i₀ : ℕ} {i₁ : Γ}

/-- If a step returns `.tail`, the slope set is empty. (The `⊤` arm of the final match cannot
fire: the chosen vertex lies in the achieving set, so its value is finite.) -/
private lemma slopeSet_eq_empty_of_nextStep_tail (h : nextStep w i₀ i₁ = .tail) :
    slopeSet w i₀ i₁ = ∅ := by
  by_contra hne
  simp_rw [nextStep] at h
  rw [if_neg hne] at h
  split_ifs at h with h1 h2 h3
  split at h
  · rename_i heq
    obtain ⟨k, hk, kfin, k₁, hk₁, hsl⟩ := h2.choose_spec.1
    have hnonempty : (achievingSet w i₀ i₁ h2.choose).Nonempty := ⟨k, hk, kfin, k₁, hk₁, hsl⟩
    have hmax := Finset.max'_mem (Set.not_infinite.mp h3).toFinset
      ((Set.not_infinite.mp h3).toFinset_nonempty.mpr hnonempty)
    exact ((Set.not_infinite.mp h3).mem_toFinset.mp hmax).2.1 heq
  · exact absurd h (by simp)

/-- If a step returns `.limitingRay`, the infimum of the slope set is not attained. -/
private lemma not_attained_of_nextStep_limitingRay {m : ℝ}
    (h : nextStep w i₀ i₁ = .limitingRay m) :
    ¬ ∃ m' ∈ slopeSet w i₀ i₁, m' = sInf (slopeSet w i₀ i₁) := by
  simp_rw [nextStep] at h
  split_ifs at h with h1 h2 h3 h4
  · split at h <;> exact absurd h (by simp)
  · exact h3

/-- If a step returns `.infiniteRay m`, the set of points achieving the slope `m` is infinite. -/
private lemma achievingSet_infinite_of_nextStep_infiniteRay {m : ℝ}
    (h : nextStep w i₀ i₁ = .infiniteRay m) : (achievingSet w i₀ i₁ m).Infinite := by
  simp_rw [nextStep] at h
  split_ifs at h with h1 h2 h3 h4
  · injection h with hh
    rwa [hh] at h4
  · split at h <;> exact absurd h (by simp)

/-- Step `n + 1` of the algorithm is the step out of the vertex produced by step `n`. -/
private lemma newtonPolygon_succ_eq' {n j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : newtonPolygon w n = some (.nextVertex j₀ j₁ l m)) :
    newtonPolygon w (n + 1) = some (nextStep w j₀ j₁) := by
  simp only [newtonPolygon, h]

/-- A finite nonzero length at index `n` forces a `nextVertex` output: the other four outputs
have length `0` or `⊤`. -/
private lemma exists_nextVertex_of_lengths_eq {n l : ℕ} (hl0 : l ≠ 0)
    (h : newtonPolygon_lengths w n = (l : WithTop ℕ)) :
    ∃ j₀ j₁ m, newtonPolygon w n = some (.nextVertex j₀ j₁ l m) := by
  rw [newtonPolygon_lengths] at h
  split at h
  · exact absurd (Nat.cast_injective h).symm hl0
  · rename_i S heq
    cases S with
    | tail => exact absurd (Nat.cast_injective h).symm hl0
    | unboundedBelow => exact absurd (Nat.cast_injective h).symm hl0
    | limitingRay m => exact absurd h.symm WithTop.coe_ne_top
    | infiniteRay m => exact absurd h.symm WithTop.coe_ne_top
    | nextVertex j₀ j₁ l' m => exact ⟨j₀, j₁, m, by rw [heq, Nat.cast_injective h]⟩

/-- The slope from `(x₀, y₀)` to `(x₁, y₁)` over `Γ = ℝ`. -/
private lemma slopeReal_real (x₀ x₁ : ℕ) (y₀ y₁ : ℝ) :
    slopeReal x₀ x₁ y₀ y₁ = (y₁ - y₀) / (x₁ - x₀) := by
  simp [slopeReal, Algebra.algebraMap_self]

end StepInversion

omit [IsUltrametricDist K] in
/-- Finiteness of the sequence value is nonvanishing of the coefficient. -/
private lemma finite_coeffVal_iff {f : PowerSeries K} {k : ℕ} :
    finite (coeffVal f) k ↔ PowerSeries.coeff k f ≠ 0 :=
  not_congr coeffVal_eq_top_iff

omit [IsUltrametricDist K] in
/-- Nonvanishing of a coefficient is insensitive to the coercion `K[X] → K⟦X⟧`. -/
private lemma coeff_coe_ne_zero_iff {f : Polynomial K} {k : ℕ} :
    PowerSeries.coeff k (f : PowerSeries K) ≠ 0 ↔ f.coeff k ≠ 0 := by
  rw [Polynomial.coeff_coe]

omit [IsUltrametricDist K] in
/-- Finiteness of the sequence value of a polynomial is nonvanishing of the coefficient. -/
private lemma finite_coeffVal_coe_iff {f : Polynomial K} {k : ℕ} :
    finite (coeffVal (f : PowerSeries K)) k ↔ f.coeff k ≠ 0 :=
  finite_coeffVal_iff.trans coeff_coe_ne_zero_iff

omit [IsUltrametricDist K] in
/-- The sequence value of a polynomial at a nonzero coefficient. -/
private lemma coeffVal_coe_of_ne_zero {f : Polynomial K} {k : ℕ} (h : f.coeff k ≠ 0) :
    coeffVal (f : PowerSeries K) k = ((-Real.log ‖f.coeff k‖ : ℝ) : WithTop ℝ) := by
  rw [coeffVal_of_ne_zero (coeff_coe_ne_zero_iff.mpr h), Polynomial.coeff_coe]

omit [IsUltrametricDist K] in
/-- Reading off the `y`-value carried by a finite sequence value of a polynomial. -/
private lemma eq_neg_log_of_coeffVal_eq {f : Polynomial K} {k : ℕ} {y : ℝ} (hk : f.coeff k ≠ 0)
    (h : coeffVal (f : PowerSeries K) k = (y : WithTop ℝ)) : y = -Real.log ‖f.coeff k‖ :=
  WithTop.coe_inj.mp (h.symm.trans (coeffVal_coe_of_ne_zero hk))

omit [IsUltrametricDist K] in
/-- The normalisation `a₀ = 1` transported along the coercion `K[X] → K⟦X⟧`. -/
private lemma coeff_coe_zero_eq_one {f : Polynomial K} (hf0 : f.coeff 0 = 1) :
    PowerSeries.coeff 0 (f : PowerSeries K) = 1 := (Polynomial.coeff_coe f 0).trans hf0

omit [IsUltrametricDist K] in
/-- With `a₀ ≠ 0` the algorithm starts at `(0, -log ‖a₀‖)`. -/
private lemma findFirstFinite_coeffVal_zero {f : PowerSeries K}
    (h : PowerSeries.coeff 0 f ≠ 0) :
    findFirstFinite (coeffVal f) 0 = some (0, -Real.log ‖PowerSeries.coeff 0 f‖) := by
  classical
  have hfin : finite (coeffVal f) 0 := finite_coeffVal_iff.mpr h
  have hex : ∃ i ≥ 0, finite (coeffVal f) i := ⟨0, le_refl _, hfin⟩
  have hzero : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr ⟨le_refl _, hfin⟩
  have h2 : coeffVal f (Nat.find hex)
      = ((-Real.log ‖PowerSeries.coeff 0 f‖ : ℝ) : WithTop ℝ) := by
    rw [hzero]; exact coeffVal_of_ne_zero h
  unfold findFirstFinite
  rw [dif_pos hex]
  have hchoose : (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose
      = -Real.log ‖PowerSeries.coeff 0 f‖ :=
    WithTop.coe_inj.mp ((Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose_spec.trans h2)
  rw [hchoose, hzero]

omit [IsUltrametricDist K] in
/-- Step `0` of the algorithm, for a series with `a₀ ≠ 0`. -/
private lemma newtonPolygon_coeffVal_zero_eq {f : PowerSeries K}
    (h : PowerSeries.coeff 0 f ≠ 0) :
    newtonPolygon (coeffVal f) 0
      = some (nextStep (coeffVal f) 0 (-Real.log ‖PowerSeries.coeff 0 f‖)) := by
  conv_lhs => rw [newtonPolygon, findFirstFinite_coeffVal_zero h]

omit [IsUltrametricDist K] in
/-- Under the normalisation `a₀ = 1` the algorithm starts at the origin. -/
private lemma newtonPolygon_zero_eq_of_coeff_zero_eq_one {f : PowerSeries K}
    (h0 : PowerSeries.coeff 0 f = 1) :
    newtonPolygon (coeffVal f) 0 = some (nextStep (coeffVal f) 0 0) := by
  rw [newtonPolygon_coeffVal_zero_eq (h0.trans_ne one_ne_zero), h0, norm_one, Real.log_one,
    neg_zero]

omit [IsUltrametricDist K] in
/-- The point set of a polynomial is finite, so the slope set out of any point is. -/
private lemma slopeSet_coe_finite (f : Polynomial K) (i₀ : ℕ) (i₁ : ℝ) :
    (slopeSet (coeffVal (f : PowerSeries K)) i₀ i₁).Finite := by
  refine Set.Finite.subset ((Set.finite_Iic f.natDegree).image
    (fun k : ℕ => slopeReal i₀ k i₁ (-Real.log ‖f.coeff k‖))) ?_
  rintro x ⟨j₀, hj₀, hfin, j₁, hj₁, rfl⟩
  have hcoeff : f.coeff j₀ ≠ 0 := finite_coeffVal_coe_iff.mp hfin
  exact ⟨j₀, Polynomial.le_natDegree_of_ne_zero hcoeff,
    by rw [eq_neg_log_of_coeffVal_eq hcoeff hj₁]⟩

omit [IsUltrametricDist K] in
/-- The achieving set of a polynomial is finite. -/
private lemma achievingSet_coe_finite (f : Polynomial K) (i₀ : ℕ) (i₁ m : ℝ) :
    (achievingSet (coeffVal (f : PowerSeries K)) i₀ i₁ m).Finite :=
  Set.Finite.subset (Set.finite_Iic f.natDegree) fun _ hj =>
    Polynomial.le_natDegree_of_ne_zero (finite_coeffVal_coe_iff.mp hj.2.1)

omit [IsUltrametricDist K] in
/-- Every nonzero coefficient right of the current vertex contributes its slope. -/
private lemma mem_slopeSet_coeffVal {f : Polynomial K} {i₀ k : ℕ} (i₁ : ℝ) (hk : i₀ < k)
    (hak : f.coeff k ≠ 0) :
    slopeReal i₀ k i₁ (-Real.log ‖f.coeff k‖) ∈ slopeSet (coeffVal (f : PowerSeries K)) i₀ i₁ :=
  ⟨k, hk, finite_coeffVal_coe_iff.mpr hak, _, coeffVal_coe_of_ne_zero hak, rfl⟩

omit [IsUltrametricDist K] in
/-- **A step of the algorithm on a polynomial, with a nonzero coefficient still ahead, is a
vertex.** The other four outputs are impossible: the slope set is nonempty (a point is ahead),
finite (the point set is finite), its infimum is attained, and the achieving set is finite. -/
private lemma exists_nextStep_coe_eq_nextVertex (f : Polynomial K) (i₀ : ℕ) (i₁ : ℝ) {k : ℕ}
    (hk : i₀ < k) (hak : f.coeff k ≠ 0) :
    ∃ j₀ j₁ l m, nextStep (coeffVal (f : PowerSeries K)) i₀ i₁ = .nextVertex j₀ j₁ l m := by
  have hne : (slopeSet (coeffVal (f : PowerSeries K)) i₀ i₁).Nonempty :=
    ⟨_, mem_slopeSet_coeffVal i₁ hk hak⟩
  cases h : nextStep (coeffVal (f : PowerSeries K)) i₀ i₁ with
  | tail => exact absurd (slopeSet_eq_empty_of_nextStep_tail h) hne.ne_empty
  | unboundedBelow =>
      exact absurd (unboundedBelow _ h) (not_not_intro (slopeSet_coe_finite f i₀ i₁).bddBelow)
  | limitingRay m =>
      exact absurd ⟨sInf _, hne.csInf_mem (slopeSet_coe_finite f i₀ i₁), rfl⟩
        (not_attained_of_nextStep_limitingRay h)
  | infiniteRay m =>
      exact absurd (achievingSet_infinite_of_nextStep_infiniteRay h)
        (Set.not_infinite.mpr (achievingSet_coe_finite f i₀ i₁ m))
  | nextVertex j₀ j₁ l m => exact ⟨j₀, j₁, l, m, rfl⟩

omit [IsUltrametricDist K] in
/-- With no nonzero coefficient ahead, the step is `.tail`. -/
private lemma nextStep_coe_eq_tail (f : Polynomial K) {i₀ : ℕ} (i₁ : ℝ)
    (h : ∀ k, i₀ < k → f.coeff k = 0) :
    nextStep (coeffVal (f : PowerSeries K)) i₀ i₁ = .tail := by
  have hempty : slopeSet (coeffVal (f : PowerSeries K)) i₀ i₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨j₀, hj₀, hfin, j₁, hj₁, rfl⟩
    exact finite_coeffVal_coe_iff.mp hfin (h j₀ hj₀)
  rw [nextStep, if_pos hempty]

omit [IsUltrametricDist K] in
/-- The data carried by a vertex of a polynomial's polygon: the vertex is a nonzero coefficient
within the degree, and its `y`-value is `-log ‖a_{j₀}‖`. -/
private lemma nextVertex_coe_data (f : Polynomial K) {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal (f : PowerSeries K)) i₀ i₁ = .nextVertex j₀ j₁ l m) :
    f.coeff j₀ ≠ 0 ∧ j₀ ≤ f.natDegree ∧ j₁ = -Real.log ‖f.coeff j₀‖ :=
  have hfin : f.coeff j₀ ≠ 0 := finite_coeffVal_coe_iff.mp (nextVertex_j₀Finite _ h)
  ⟨hfin, Polynomial.le_natDegree_of_ne_zero hfin,
    eq_neg_log_of_coeffVal_eq hfin (nextVertex_j₁_eq _ h)⟩

/-- **The Newton polygon of `f` has its first break at `(i, m·i)`** (relative to its starting
vertex): the constructed polygon's first segment has slope `m` and finite nonzero length `i`.
Blueprint §5.2's normalisation `a₀ = 1` anchors the polygon at the origin, recovering the
literal "break at `(i, m·i)`". -/
def HasFirstBreak (f : PowerSeries K) (i : ℕ) (m : ℝ) : Prop :=
  0 < i ∧ (newtonPolygon₀OfPowerSeries negLogNorm f).slopes 0 = (m : WithBotTop ℝ) ∧
    (newtonPolygon₀OfPowerSeries negLogNorm f).lengths 0 = (i : WithTop ℕ)

/-- **Blueprint Definition 5.4.** A power series is *pure of slope `m`* when its Newton polygon
is a single segment of slope `m`. -/
def IsPureSeries (f : PowerSeries K) (m : ℝ) : Prop :=
  (newtonPolygon₀OfPowerSeries negLogNorm f).IsPure m

-- The `IsUltrametricDist K` instance is a genuine binder of this bridge lemma's frozen
-- signature, even though this proof route does not use it.
set_option linter.unusedSectionVars false in
/-- Bridge to the step algorithm: under the normalisation `a₀ = 1`, a first break at `(i, m·i)`
is exactly a `nextVertex` output at step `0` with vertex `i` and slope `m`. -/
lemma hasFirstBreak_iff_newtonPolygon_zero {f : PowerSeries K}
    (h0 : PowerSeries.coeff 0 f = 1) {i : ℕ} {m : ℝ} :
    HasFirstBreak f i m ↔
      ∃ j₁ : ℝ, newtonPolygon (coeffVal f) 0 = some (.nextVertex i j₁ i m) := by
  constructor
  · rintro ⟨hi, hm, hl⟩
    have hm' : slopes' (newtonPolygon (coeffVal f) 0) = (m : WithBotTop ℝ) := hm
    have hl' : newtonPolygon_lengths (coeffVal f) 0 = (i : WithTop ℕ) := hl
    obtain ⟨j₀, j₁, m', hnp⟩ := exists_nextVertex_of_lengths_eq hi.ne' hl'
    have hstep : nextStep (coeffVal f) 0 0 = .nextVertex j₀ j₁ i m' :=
      Option.some_inj.mp ((newtonPolygon_zero_eq_of_coeff_zero_eq_one h0).symm.trans hnp)
    obtain rfl : j₀ = i := by have := nextVertex_l_eq _ hstep; omega
    obtain rfl : m' = m :=
      WithBotTop.coe_injective (by simpa only [hnp, slopes', slopes] using hm')
    exact ⟨j₁, hnp⟩
  · rintro ⟨j₁, hnp⟩
    obtain ⟨i₀, i₁, hstep⟩ := nextStep_nextVertex (coeffVal f) hnp
    refine ⟨lt_of_le_of_lt (Nat.zero_le i₀) (nextVertex_lt _ hstep), ?_, ?_⟩
    · show slopes' (newtonPolygon (coeffVal f) 0) = _
      rw [hnp]
      rfl
    · show newtonPolygon_lengths (coeffVal f) 0 = _
      simp only [newtonPolygon_lengths, hnp]

-- The `IsUltrametricDist K` instance is a genuine binder of this lemma's frozen signature,
-- even though this proof route does not use it.
set_option linter.unusedSectionVars false in
/-- Segment data of the constructed polygon is algorithm data: a finite nonzero length at
index `k` forces a `nextVertex` output, recovering the step equation from the textbook
slope/length/endpoint data. -/
lemma newtonPolygon_eq_nextVertex_of_segment_data {f : PowerSeries K} {k : ℕ} {m : ℝ}
    {l j₀ : ℕ} (hl0 : l ≠ 0)
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hl : (newtonPolygon₀OfPowerSeries negLogNorm f).lengths k = (l : WithTop ℕ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (k + 1) = ((j₀ : ℤ) : WithTop ℤ)) :
    ∃ j₁ : ℝ, newtonPolygon (coeffVal f) k = some (.nextVertex j₀ j₁ l m) := by
  have hm' : slopes' (newtonPolygon (coeffVal f) k) = (m : WithBotTop ℝ) := hm
  have hl' : newtonPolygon_lengths (coeffVal f) k = (l : WithTop ℕ) := hl
  have hj' : (newtonPolygon₀OfSeq (coeffVal f)).vertexX (k + 1) = ((j₀ : ℤ) : WithTop ℤ) := hj
  obtain ⟨p₀, p₁, m', hnp⟩ := exists_nextVertex_of_lengths_eq hl0 hl'
  obtain rfl : p₀ = j₀ := by
    have h1 := (newtonPolygon₀OfSeq_vertexX (coeffVal f) hnp).symm.trans hj'
    exact_mod_cast WithTop.coe_inj.mp h1
  obtain rfl : m' = m :=
    WithBotTop.coe_injective (by simpa only [hnp, slopes', slopes] using hm')
  exact ⟨p₁, hnp⟩

namespace HasFirstBreak

variable {f : PowerSeries K} {i : ℕ} {m : ℝ}

/-- The step form of a first break: the algorithm's step out of the origin. -/
private lemma nextStep_zero (h0 : PowerSeries.coeff 0 f = 1) (hb : HasFirstBreak f i m) :
    ∃ j₁ : ℝ, nextStep (coeffVal f) 0 0 = .nextVertex i j₁ i m := by
  obtain ⟨j₁, hnp⟩ := (hasFirstBreak_iff_newtonPolygon_zero h0).mp hb
  exact ⟨j₁, Option.some_inj.mp ((newtonPolygon_zero_eq_of_coeff_zero_eq_one h0).symm.trans hnp)⟩

/-- The break is a genuine coefficient: `aᵢ ≠ 0`. -/
lemma coeff_break_ne_zero (h0 : PowerSeries.coeff 0 f = 1) (hb : HasFirstBreak f i m) :
    PowerSeries.coeff i f ≠ 0 := by
  obtain ⟨j₁, hstep⟩ := nextStep_zero h0 hb
  exact finite_coeffVal_iff.mp (nextVertex_j₀Finite _ hstep)

/-- The break lies on the line `y = mx`: `-log ‖aᵢ‖ = m·i`. -/
lemma norm_coeff_break_eq (h0 : PowerSeries.coeff 0 f = 1) (hb : HasFirstBreak f i m) :
    -Real.log ‖PowerSeries.coeff i f‖ = m * i := by
  obtain ⟨j₁, hstep⟩ := nextStep_zero h0 hb
  have hiR : (0 : ℝ) < i := by exact_mod_cast hb.1
  have hj₁ : j₁ = -Real.log ‖PowerSeries.coeff i f‖ := by
    have h1 := nextVertex_j₁_eq _ hstep
    rw [coeffVal_of_ne_zero (coeff_break_ne_zero h0 hb)] at h1
    exact_mod_cast h1.symm
  have hslope := nextVertex_slope_eq_sInf' _ hstep
  rw [slopeReal_real, hj₁] at hslope
  push_cast at hslope
  rw [sub_zero, sub_zero, eq_div_iff hiR.ne'] at hslope
  exact hslope.symm

/-- **Points lie on/above the first segment's line**: `m·k ≤ -log ‖aₖ‖` for every nonzero
coefficient with `k > 0` (refactor of `firstBreak_slope_le`, `Test/test.lean:207`). -/
lemma slope_mul_le (h0 : PowerSeries.coeff 0 f = 1) (hb : HasFirstBreak f i m) {k : ℕ}
    (hk : 0 < k) (hak : PowerSeries.coeff k f ≠ 0) :
    m * k ≤ -Real.log ‖PowerSeries.coeff k f‖ := by
  obtain ⟨j₁, hstep⟩ := nextStep_zero h0 hb
  have h := nextStep_slope_le (coeffVal f) hstep hk (coeffVal_of_ne_zero hak)
  simpa only [Algebra.algebraMap_self, RingHom.id_apply, Nat.cast_zero, sub_zero] using h

/-- **Points beyond the break lie strictly above the line**: `m·t < -log ‖aₜ‖` for `t > i`
(refactor of the strict half of `distinguished_of_firstBreak`, `Test/test.lean:689`). -/
lemma slope_mul_lt (h0 : PowerSeries.coeff 0 f = 1) (hb : HasFirstBreak f i m) {t : ℕ}
    (ht : i < t) (hat : PowerSeries.coeff t f ≠ 0) :
    m * t < -Real.log ‖PowerSeries.coeff t f‖ := by
  obtain ⟨j₁, hstep⟩ := nextStep_zero h0 hb
  have h := nextStep_slope_lt (coeffVal f) hstep ht (coeffVal_of_ne_zero hat)
  simpa only [Algebra.algebraMap_self, RingHom.id_apply, Nat.cast_zero, sub_zero] using h

end HasFirstBreak

/-! ### The first break makes a polynomial distinguished (§5.7 geometric core)

`Test/test.lean:689` proved these three facts as one bundled conclusion; they are split
one-per-lemma here, with the `IsMulDistinguished` packaging feeding Martin's Weierstrass
preparation. -/

/-- Every Gauss-norm term of `f` at `c = exp m` is at most `1`. -/
lemma firstBreak_gaussTerm_le (f : Polynomial K) (hf0 : f.coeff 0 = 1) {i : ℕ} {m : ℝ}
    (hb : HasFirstBreak (f : PowerSeries K) i m) (k : ℕ) :
    ‖f.coeff k‖ * Real.exp m ^ k ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hf0]
  · by_cases hak : f.coeff k = 0
    · rw [hak, norm_zero, zero_mul]
      exact zero_le_one
    · refine (norm_mul_exp_pow_le_one_iff hak m k).mpr ?_
      have h := hb.slope_mul_le (coeff_coe_zero_eq_one hf0) hk (coeff_coe_ne_zero_iff.mpr hak)
      rwa [Polynomial.coeff_coe] at h

/-- The Gauss-norm term at the break equals `1`. -/
lemma firstBreak_gaussTerm_break_eq (f : Polynomial K) (hf0 : f.coeff 0 = 1) {i : ℕ} {m : ℝ}
    (hb : HasFirstBreak (f : PowerSeries K) i m) :
    ‖f.coeff i‖ * Real.exp m ^ i = 1 := by
  have hci : f.coeff i ≠ 0 :=
    coeff_coe_ne_zero_iff.mp (hb.coeff_break_ne_zero (coeff_coe_zero_eq_one hf0))
  refine (norm_mul_exp_pow_eq_one_iff hci m i).mpr ?_
  have h := hb.norm_coeff_break_eq (coeff_coe_zero_eq_one hf0)
  rwa [Polynomial.coeff_coe] at h

/-- Gauss-norm terms beyond the break are strictly below `1`. -/
lemma firstBreak_gaussTerm_lt (f : Polynomial K) (hf0 : f.coeff 0 = 1) {i : ℕ} {m : ℝ}
    (hb : HasFirstBreak (f : PowerSeries K) i m) {t : ℕ} (ht : i < t) :
    ‖f.coeff t‖ * Real.exp m ^ t < 1 := by
  by_cases hat : f.coeff t = 0
  · rw [hat, norm_zero, zero_mul]
    exact zero_lt_one
  · refine (norm_mul_exp_pow_lt_one_iff hat m t).mpr ?_
    have h := hb.slope_mul_lt (coeff_coe_zero_eq_one hf0) ht (coeff_coe_ne_zero_iff.mpr hat)
    rwa [Polynomial.coeff_coe] at h

/-- **The first break makes `f` `i`-distinguished at `c = exp m`**, in the multiplicative form
consumed by Martin's Weierstrass preparation. -/
theorem isMulDistinguished_of_hasFirstBreak (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    {i : ℕ} {m : ℝ} (hb : HasFirstBreak (f : PowerSeries K) i m) :
    PowerSeries.IsMulDistinguished (Real.exp m) (f : PowerSeries K) i := by
  have hci : PowerSeries.coeff i (f : PowerSeries K) ≠ 0 :=
    hb.coeff_break_ne_zero (coeff_coe_zero_eq_one hf0)
  have hbreak : ‖PowerSeries.coeff i (f : PowerSeries K)‖ * Real.exp m ^ i = 1 := by
    rw [Polynomial.coeff_coe]
    exact firstBreak_gaussTerm_break_eq f hf0 hb
  have hterm : ∀ k, ‖PowerSeries.coeff k (f : PowerSeries K)‖ * Real.exp m ^ k ≤ 1 := fun k => by
    rw [Polynomial.coeff_coe]
    exact firstBreak_gaussTerm_le f hf0 hb k
  have hbd : PowerSeries.HasGaussNorm norm (Real.exp m) (f : PowerSeries K) :=
    f.hasGaussNorm_toPowerSeries norm (Real.exp m) norm_zero
  refine ⟨(isUnit_iff_ne_zero.mpr hci).isNormMulUnit, ?_, fun t ht => ?_⟩
  · rw [hbreak]
    refine le_antisymm ?_ (hbreak ▸ PowerSeries.le_gaussNorm norm (Real.exp m) _ hbd i)
    rw [PowerSeries.gaussNorm_eq]
    exact ciSup_le hterm
  · rw [hbreak, Polynomial.coeff_coe]
    exact firstBreak_gaussTerm_lt f hf0 hb ht

/-! ### Blueprint 5.6 and 5.5 -/

-- The `IsUltrametricDist K` instance is a genuine binder of this lemma's frozen signature,
-- even though this proof route does not use it.
set_option linter.unusedSectionVars false in
/-- **Purity from coefficient bounds** (general start — no `a₀ = 1` normalisation): if every
Gauss-norm term of `g` at `c = exp m` is dominated by the constant term, with equality attained
at the top degree, then `g` is pure of slope `m`. (Refactor of `Test/test.lean:735`; VERIFY
the exact hypothesis set against [T] when proving.) -/
lemma isPureSeries_of_bounds (g : Polynomial K) (hg0 : g.coeff 0 ≠ 0)
    (hs : 0 < g.natDegree) (m : ℝ)
    (hle : ∀ k, ‖g.coeff k‖ * Real.exp m ^ k ≤ ‖g.coeff 0‖)
    (heq : ‖g.coeff g.natDegree‖ * Real.exp m ^ g.natDegree = ‖g.coeff 0‖) :
    IsPureSeries (g : PowerSeries K) m := by
  set s := g.natDegree
  set ν₀ : ℝ := -Real.log ‖g.coeff 0‖ with hν₀
  have hlead : g.coeff s ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr fun h => hg0 (by rw [h, Polynomial.coeff_zero])
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hνs : -Real.log ‖g.coeff s‖ - ν₀ = m * s :=
    (norm_mul_exp_pow_eq_norm_iff hlead hg0 m s).mp heq
  -- the first step is a vertex …
  obtain ⟨j₀, j₁, l, m', hv⟩ := exists_nextStep_coe_eq_nextVertex g 0 ν₀ hs hlead
  have hsn : slopeReal 0 s ν₀ (-Real.log ‖g.coeff s‖) = m := by
    rw [slopeReal_real]
    push_cast
    rw [sub_zero, hνs]
    exact mul_div_cancel_right₀ m hsR.ne'
  have hmem_s : slopeReal 0 s ν₀ (-Real.log ‖g.coeff s‖)
      ∈ slopeSet (coeffVal (g : PowerSeries K)) 0 ν₀ := mem_slopeSet_coeffVal ν₀ hs hlead
  have hlb : ∀ x ∈ slopeSet (coeffVal (g : PowerSeries K)) 0 ν₀, m ≤ x := by
    rintro x ⟨k, hk, kfin, k₁, hk₁, rfl⟩
    have hak : g.coeff k ≠ 0 := finite_coeffVal_coe_iff.mp kfin
    have hkR : (0 : ℝ) < (k : ℝ) - ((0 : ℕ) : ℝ) := by
      push_cast
      simpa using (Nat.cast_pos.mpr hk : (0 : ℝ) < (k : ℝ))
    rw [slopeReal_real, eq_neg_log_of_coeffVal_eq hak hk₁, le_div_iff₀ hkR]
    have h := (norm_mul_exp_pow_le_norm_iff hak hg0 m k).mp (hle k)
    push_cast
    linarith
  -- … whose slope is `m` …
  have hsInf : sInf (slopeSet (coeffVal (g : PowerSeries K)) 0 ν₀) = m :=
    le_antisymm (hsn ▸ csInf_le (slopeSet_coe_finite g 0 ν₀).bddBelow hmem_s)
      (le_csInf ⟨_, hmem_s⟩ hlb)
  rw [show m' = m from (nextVertex_slope_eq_sInf'' _ hv).trans hsInf] at hv
  -- … and whose vertex is the top coefficient (it is the maximal achiever)
  obtain rfl : j₀ = s := by
    refine le_antisymm (nextVertex_coe_data g hv).2.1 ?_
    have hmemach : s ∈ achievingSet (coeffVal (g : PowerSeries K)) 0 ν₀
        (sInf (slopeSet (coeffVal (g : PowerSeries K)) 0 ν₀)) :=
      ⟨hs, finite_coeffVal_coe_iff.mpr hlead, _, coeffVal_coe_of_ne_zero hlead,
        hsInf.trans hsn.symm⟩
    rw [nextVertex_j₀_eq_max _ hv]
    exact Finset.le_max' _ s ((nextVertex_finite _ hv).mem_toFinset.mpr hmemach)
  -- conclude purity: the second step has no point ahead, so it is `tail`
  have h0eq : newtonPolygon (coeffVal (g : PowerSeries K)) 0
      = some (.nextVertex s j₁ l m) := by
    rw [newtonPolygon_coeffVal_zero_eq (coeff_coe_ne_zero_iff.mpr hg0), Polynomial.coeff_coe,
      ← hν₀, hv]
  have htail : nextStep (coeffVal (g : PowerSeries K)) s j₁ = .tail :=
    nextStep_coe_eq_tail g j₁ fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt hk
  refine ⟨?_, ?_⟩
  · show slopes' (newtonPolygon (coeffVal (g : PowerSeries K)) 0) = _
    rw [h0eq]
    rfl
  · show slopes' (newtonPolygon (coeffVal (g : PowerSeries K)) (0 + 1)) = _
    rw [newtonPolygon_succ_eq' h0eq, htail]
    rfl

/-- **Blueprint Proposition 5.6.** With `a₀ = 1` and `n = natDegree f ≥ 1`, `f` is pure of
slope `m` iff at `c = exp m` its Gauss norm is `1` and is realised by the top coefficient
(refactor of `Test/test.lean:476`). -/
theorem isPureSeries_iff_distinguished (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (hn : 0 < f.natDegree) (m c : ℝ) (hc : c = Real.exp m) :
    IsPureSeries (f : PowerSeries K) m ↔
      (PowerSeries.gaussNorm norm c (f : PowerSeries K)
          = ‖PowerSeries.coeff f.natDegree (f : PowerSeries K)‖ * c ^ f.natDegree
        ∧ PowerSeries.gaussNorm norm c (f : PowerSeries K) = 1) := by
  subst hc
  set n := f.natDegree with hn_def
  have hlead : f.coeff n ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr fun h =>
    one_ne_zero (by rw [← hf0, h, Polynomial.coeff_zero])
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := coeff_coe_zero_eq_one hf0
  have hbd : PowerSeries.HasGaussNorm norm (Real.exp m) (f : PowerSeries K) :=
    f.hasGaussNorm_toPowerSeries norm (Real.exp m) norm_zero
  constructor
  · -- pure ⟹ distinguished
    rintro ⟨hs0, hs1⟩
    obtain ⟨j₀, j₁, l, m', hv⟩ := exists_nextStep_coe_eq_nextVertex f 0 (0 : ℝ) hn hlead
    have h0eq : newtonPolygon (coeffVal (f : PowerSeries K)) 0
        = some (.nextVertex j₀ j₁ l m') := by
      rw [newtonPolygon_zero_eq_of_coeff_zero_eq_one hf0', hv]
    have hm' : m' = m := by
      have h : slopes' (newtonPolygon (coeffVal (f : PowerSeries K)) 0) = (m : WithBotTop ℝ) := hs0
      rw [h0eq] at h
      exact WithBotTop.coe_injective h
    rw [hm'] at hv h0eq
    -- the vertex is the top coefficient: otherwise there is a second slope
    obtain rfl : j₀ = n := by
      refine le_antisymm (nextVertex_coe_data f hv).2.1 ?_
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨k₀, k₁, l₂, m₂, hv₂⟩ := exists_nextStep_coe_eq_nextVertex f j₀ j₁ hlt hlead
      have h : slopes' (newtonPolygon (coeffVal (f : PowerSeries K)) (0 + 1))
          = (⊤ : WithBotTop ℝ) := hs1
      rw [newtonPolygon_succ_eq' h0eq, hv₂] at h
      exact WithBotTop.coe_ne_top m₂ h
    -- so the polygon has its first break at `n`, and §5.7 bounds every Gauss-norm term
    obtain rfl : l = n := by have := nextVertex_l_eq _ hv; omega
    have hb : HasFirstBreak (f : PowerSeries K) n m :=
      (hasFirstBreak_iff_newtonPolygon_zero hf0').mpr ⟨j₁, h0eq⟩
    have hgauss : PowerSeries.gaussNorm norm (Real.exp m) (f : PowerSeries K) = 1 := by
      refine le_antisymm ?_ ?_
      · rw [PowerSeries.gaussNorm_eq]
        refine ciSup_le fun k => ?_
        rw [Polynomial.coeff_coe]
        exact firstBreak_gaussTerm_le f hf0 hb k
      · have h0 := PowerSeries.le_gaussNorm norm (Real.exp m) (f : PowerSeries K) hbd 0
        simpa [hf0'] using h0
    exact ⟨by rw [hgauss, Polynomial.coeff_coe, firstBreak_gaussTerm_break_eq f hf0 hb], hgauss⟩
  · -- distinguished ⟹ pure: the general-start criterion, with `‖a₀‖ = 1`
    rintro ⟨htop, hone⟩
    refine isPureSeries_of_bounds f (by rw [hf0]; exact one_ne_zero) hn m ?_ ?_
    · intro k
      rw [hf0, norm_one]
      have h := PowerSeries.le_gaussNorm norm (Real.exp m) (f : PowerSeries K) hbd k
      rw [hone, Polynomial.coeff_coe] at h
      exact h
    · rw [hf0, norm_one]
      have h := htop.symm.trans hone
      rwa [Polynomial.coeff_coe] at h

/-- **Degree-only shadow of blueprint Theorem 5.7.** With `a₀ = 1` and a first break at
`(i, mi)`, `f` factors as `f = g * h` with `g.natDegree = i`.

The full §5.7 statement (`exists_factorisation_of_firstBreak'`, which additionally records
purity of `g` and the dominance of `h`'s constant coefficient) lives *downstream* in
`PhD.Main.NewtonPolygons.PolynomialRoots`, so it cannot be used here; only the two factors and the
degree of the first are needed for 5.5, and those come directly off
`isMulDistinguished_of_hasFirstBreak` and Martin's Weierstrass preparation. -/
private theorem exists_factorisation_natDegree_of_hasFirstBreak [CompleteSpace K]
    (f : Polynomial K) (hf0 : f.coeff 0 = 1) {i : ℕ} {m : ℝ}
    (hb : HasFirstBreak (f : PowerSeries K) i m) :
    ∃ g h : Polynomial K, f = g * h ∧ g.natDegree = i := by
  haveI : Fact (0 < Real.exp m) := ⟨Real.exp_pos m⟩
  obtain ⟨ω, ⟨e, ⟨-, hωd, -, -, hgeq⟩, -⟩, -⟩ :=
    PowerSeries.Restricted.weierstrassPreparation_polynomial_of_isMulDistinguished
      (g₀ := f) (isMulDistinguished_of_hasFirstBreak f hf0 hb)
  refine ⟨ω, e, ?_, Polynomial.natDegree_eq_of_degree_eq_some hωd⟩
  rw [← map_mul] at hgeq
  exact (Polynomial.toRestricted_injective _ hgeq).trans (mul_comm e ω)

/-- **Blueprint Proposition 5.5.** Irreducible polynomials (with `a₀ = 1`) are pure of some
slope (refactor of `Test/test.lean:1175`; the proof factors through §5.7, whence
`[CompleteSpace K]`). -/
theorem isPureSeries_of_irreducible [CompleteSpace K] (f : Polynomial K)
    (hf0 : f.coeff 0 = 1) (hn : 0 < f.natDegree) (hirr : Irreducible f) :
    ∃ m : ℝ, IsPureSeries (f : PowerSeries K) m := by
  have hf_ne : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hn
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := coeff_coe_zero_eq_one hf0
  have hlead : f.coeff f.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf_ne
  obtain ⟨j₀, j₁, l, m, hv⟩ := exists_nextStep_coe_eq_nextVertex f 0 (0 : ℝ) hn hlead
  obtain rfl : j₀ = l := by have := nextVertex_l_eq _ hv; omega
  have hbreak : HasFirstBreak (f : PowerSeries K) j₀ m :=
    (hasFirstBreak_iff_newtonPolygon_zero hf0').mpr
      ⟨j₁, by rw [newtonPolygon_zero_eq_of_coeff_zero_eq_one hf0', hv]⟩
  obtain ⟨-, hj₀le, -⟩ := nextVertex_coe_data f hv
  rcases eq_or_lt_of_le hj₀le with heq | hlt
  · -- the single segment reaches the top degree: `f` is pure of slope `m`
    refine ⟨m, isPureSeries_of_bounds f (hf0.trans_ne one_ne_zero) hn m (fun k => ?_) ?_⟩
    · rw [hf0, norm_one]
      exact firstBreak_gaussTerm_le f hf0 hbreak k
    · rw [hf0, norm_one, ← heq]
      exact firstBreak_gaussTerm_break_eq f hf0 hbreak
  · -- an interior break: §5.7 gives a proper factorisation, contradicting irreducibility
    obtain ⟨g, h, hfeq, hdeg⟩ := exists_factorisation_natDegree_of_hasFirstBreak f hf0 hbreak
    obtain ⟨hg_ne, hh_ne⟩ := mul_ne_zero_iff.mp (hfeq ▸ hf_ne)
    have hdegs := Polynomial.natDegree_mul hg_ne hh_ne
    rw [← hfeq, hdeg] at hdegs
    rcases hirr.isUnit_or_isUnit hfeq with hu | hu
    · exact absurd hu (Polynomial.not_isUnit_of_natDegree_pos g (hdeg ▸ hbreak.1))
    · exact absurd hu (Polynomial.not_isUnit_of_natDegree_pos h (by omega))
