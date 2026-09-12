import PhD.ToPR.NewtonPolygon
import PhD.ToPR.GaussNorm
import PhD.ToPR.Restricted
import PhD.WeierstrassPrep.WPrep_gen
import PhD.Main.Test.addVals2
import PhD.Main.Test.DivValueGroup
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Newton polygons over an ultrametric normed field (blueprint §5.4 – §5.14)

**SUPERSEDED (2026-08-04).** Every result of this file (blueprint §5.4–§5.14) has been
re-proved on the modern `IsNewtonPolygonOf` spec architecture in `PhD/Main/NewtonPolygons/`
(`CoeffVal`, `FirstBreak`, `PolynomialRoots`, `RadiusOfConvergence`, `PowerSeriesZeros`),
sorry-free on standard axioms and free of the deprecated `addVals2`/`DivValueGroup`/
`WeierstrassPrep` dependencies.  This file is kept as reference history per the project's
keep-PR'd-history convention; do not import it from new code.

Refactor of `NPtest.lean` on top of the additive-valuation API of `addVals2.lean`.

## The base field

`K` is a nontrivially normed field whose distance is ultrametric:
`[NontriviallyNormedField K] [IsUltrametricDist K]`.  Mathlib attaches to such a `K` the canonical
valuation `NormedField.valuation : Valuation K ℝ≥0`, `x ↦ ‖x‖₊`, **and a `Valuation.RankOne`
instance for it** (the hom is the inclusion of the value group into `ℝ≥0`; nontriviality of the
norm gives nontriviality of the valuation).  So "the valuation is rank one" is not an extra
hypothesis here: it holds by instance search, and the `RankOne.addVal` machinery of `addVals2`
applies to `K` with no further assumptions.

## The additive valuation, and the choice of base `p = e`

From `addVals2`, the rank-one valuation carries a real-valued additive valuation

  `RankOne.addVal : AddValuation K (WithTop ℝ)`,  `x ↦ - log ‖x‖`  (with `⊤` at `0`),

abbreviated `addVal` below; the Newton polygon is built from it.  The norm is recovered as

  `‖x‖ = exp (-(addVal x)) = (exp 1) ^ (-(addVal x))`   (`norm_eq_exp_neg_addVal`),

i.e. **the base of the norm is `p = e = Real.exp 1`**, the base implicit in the natural logarithm.

Why this is the canonical choice.  Rank one only says the value group `‖Kˣ‖₊` embeds in `ℝ≥0`; in
general it carries no distinguished element, hence no distinguished base:

* *discretely valued* (`ℚ_p`-style, `IsRankOneDiscrete`): the value group is cyclic and
  `p = ‖ϖ‖⁻¹` (inverse norm of a uniformizer) *is* canonical — but we do not assume discreteness;
* *dense rational rank one* (`ℂ_p`-style, `RatRankLeOne`): no generator exists, so a base is a
  genuine *choice* (a `ratToNNReal` factorization in `addVals2`), not a canonical fact;
* *general rank one* (value group e.g. `⟨2, 2^√2⟩ ⊆ ℝ>0`): not even a rational normalisation
  exists.

Under our hypotheses the only canonical structure is the norm itself, and the only base-free
logarithm of it is the natural one.  Any other base is either an arbitrary parameter (what
`NPtest.lean` did, threading `(p : ℝ) (hp : 1 < p)` through every statement) or extra data.
Taking `e` removes the parameter and the ad-hoc `negLogb` bridge entirely: the additive valuation
is a bona fide `AddValuation` out of the box, with `map_mul`/`map_add`/`map_zero`/`map_one` for
free.

## Scale invariance of the polygon

Changing the base from `e` to any `p > 1` multiplies every coefficient valuation, hence every
slope, by `log p`; break positions (`x`-coordinates), segment lengths, and purity are unchanged.
The base is visible only through the bridge `c = p ^ m` of §5.6 – §5.10, which here reads
`c = exp m`.

## Recovering an honest `p` later

Nothing is lost for the `p`-adic case: when `K` is discretely valued, add
`[(NormedField.valuation (K := K)).IsRankOneDiscrete]` and use `normAddValZ` from `addVals2`
(`‖x‖ = p ^ (-d)` with `d : ℤ` at the canonical `p = ‖ϖ‖⁻¹`, via
`norm_eq_base_zpow_neg_normAddValZ`).  The two normalisations differ by the scalar `log p` along
the inclusion chain `WithTop ℤ → WithTop ℚ → WithTop ℝ` set up in `addVals2`
(`addValQ_eq_map_addValZ`, `RankOne.addVal_eq_map_addValQ`); on `ℚ_p` the `ℤ`-valued valuation is
Mathlib's `vₚ` (`normAddValZ_padic`).
-/

open Valuation NormedField DivisibleValueGroup

namespace NewtonPolygon

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

/-! ### The additive valuation `x ↦ - log ‖x‖` -/

/-- The **canonical additive valuation** of an ultrametric normed field: `RankOne.addVal` of the
canonical valuation `NormedField.valuation`, i.e. `x ↦ - log ‖x‖ : WithTop ℝ` with `⊤` at `0`.
A bona fide `AddValuation`, so the whole additive-valuation API is available. -/
noncomputable def addValuation : AddValuation K (WithTop ℝ) :=
  RankOne.addVal (NormedField.valuation (K := K))

/-- The additive valuation as a plain function (this is what the Newton-polygon algorithm
consumes). -/
noncomputable def addVal (a : K) : WithTop ℝ :=
  RankOne.addVal (NormedField.valuation (K := K)) a

@[simp] theorem addValuation_apply (a : K) : addValuation K a = addVal K a := rfl

@[simp] theorem addVal_zero : addVal K 0 = ⊤ := AddValuation.map_zero (addValuation K)

@[simp] theorem addVal_one : addVal K 1 = 0 := AddValuation.map_one (addValuation K)

theorem addVal_of_ne_zero {a : K} (ha : a ≠ 0) :
    addVal K a = ((- Real.log ‖a‖ : ℝ) : WithTop ℝ) := by
  unfold addVal
  rw [RankOne.addVal_apply_of_ne_zero _ ha, valuation_norm_eq]

theorem addVal_eq_top_iff (a : K) : addVal K a = ⊤ ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, addVal_zero]⟩
  by_contra ha
  rw [addVal_of_ne_zero K ha] at h
  exact WithTop.coe_ne_top h

/-- **The norm is the base to the power of minus the additive valuation**, at the canonical base
`p = e`: if `addVal a = r` then `‖a‖ = exp (-r)`. -/
theorem norm_eq_exp_neg_addVal {a : K} {r : ℝ} (hr : addVal K a = (r : WithTop ℝ)) :
    ‖a‖ = Real.exp (-r) := by
  have ha : a ≠ 0 := by
    intro h
    rw [h, addVal_zero] at hr
    exact WithTop.top_ne_coe hr
  rw [addVal_of_ne_zero K ha, WithTop.coe_inj] at hr
  rw [← hr, neg_neg, Real.exp_log (norm_pos_iff.mpr ha)]

/-- `norm_eq_exp_neg_addVal` written with `rpow`, exhibiting the base: `‖a‖ = p ^ (-v(a))` with
`p = Real.exp 1`. -/
theorem norm_eq_exp_one_rpow_neg_addVal {a : K} {r : ℝ} (hr : addVal K a = (r : WithTop ℝ)) :
    ‖a‖ = Real.exp 1 ^ (-r) := by
  rw [Real.exp_one_rpow]
  exact norm_eq_exp_neg_addVal K hr

/-! ### The input to the algorithm

Since `‖a‖ = 0 ↔ a = 0`, an index outside the support of `f` is sent to `⊤` automatically — no
extra case split. -/

/-- The valuation sequence fed to the Newton-polygon algorithm. -/
noncomputable def coeffVal (f : PowerSeries K) : ℕ → WithTop ℝ :=
  fun i => addVal K (PowerSeries.coeff i f)

theorem coeffVal_zero_finite (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1) :
    coeffVal K f 0 = ((0 : ℝ) : WithTop ℝ) := by
  simp only [coeffVal, hf0]
  rw [addVal_one]
  rfl

@[simp] theorem slopeReal_real (x₀ x₁ : ℕ) (y₀ y₁ : ℝ) :
    slopeReal x₀ x₁ y₀ y₁ = (y₁ - y₀) / (x₁ - x₀) := by
  simp [slopeReal, Algebra.algebraMap_self]

/-! ### Reading the first break off the algorithm -/

-- this should probably be based on a construction that details the points of a newton polygon

/-- **The Newton polygon of `f` has its first break at `(j₀, j₁)`**, reached by a first segment of
projected length `l` and slope `m`.  The blueprint's normalisation `a₀ = 1` (start at the origin)
is captured by taking the length equal to `j₀`. -/
def HasFirstBreak (f : PowerSeries K) (j₀ : ℕ) (j₁ : ℝ) (l : ℕ) (m : ℝ) : Prop :=
  newtonPolygon (coeffVal K f) 0 = some (.nextVertex j₀ j₁ l m)

theorem findFirstFinite_zero (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1) :
    findFirstFinite (coeffVal K f) 0 = some (0, 0) := by
  classical
  have hfin : finite (coeffVal K f) 0 := by
    show coeffVal K f 0 ≠ ⊤
    rw [coeffVal_zero_finite K f hf0]
    exact WithTop.coe_ne_top
  have hex : ∃ i ≥ 0, finite (coeffVal K f) i := ⟨0, le_refl _, hfin⟩
  have hzero : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr ⟨le_refl _, hfin⟩
  have h2 : coeffVal K f (Nat.find hex) = ((0 : ℝ) : WithTop ℝ) := by
    rw [hzero]
    exact coeffVal_zero_finite K f hf0
  unfold findFirstFinite
  rw [dif_pos hex]
  have hchoose : (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose = (0 : ℝ) :=
    WithTop.coe_inj.mp
      ((Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose_spec.trans h2)
  rw [hchoose, hzero]

/-- With `a₀ = 1` the algorithm starts at the origin, so step `0` is `nextStep … 0 0`. -/
theorem newtonPolygon_zero_eq (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1) :
    newtonPolygon (coeffVal K f) 0 = nextStep (coeffVal K f) 0 0 := by
  conv_lhs => rw [newtonPolygon, findFirstFinite_zero K f hf0]

/-- **Geometric core, at an arbitrary vertex.**  If a step of the algorithm outputs the segment
from `(i₀, i₁)` to `(j₀, j₁)` of slope `m`, then every later finite point lies on/above the line
of slope `m` through `(i₀, i₁)`: `m·(k - i₀) ≤ ν(aₖ) - i₁` for all `k > i₀`.  This is the
geometric input to the segment-by-segment root count (5.11). -/
theorem step_slope_le (f : PowerSeries K) {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (hstep : nextStep (coeffVal K f) i₀ i₁ = .nextVertex j₀ j₁ l m)
    {k : ℕ} (hk : i₀ < k) (hak : PowerSeries.coeff k f ≠ 0) :
    m * (k - i₀ : ℝ) ≤ - Real.log ‖PowerSeries.coeff k f‖ - i₁ := by
  set vk : ℝ := - Real.log ‖PowerSeries.coeff k f‖ with hvk
  have hmem : ((vk - i₁) / (k - i₀ : ℝ)) ∈ slopeSet (coeffVal K f) i₀ i₁ := by
    refine ⟨k, hk, ?_, vk, ?_, ?_⟩
    · show coeffVal K f k ≠ ⊤
      simp only [coeffVal]
      rw [ne_eq, addVal_eq_top_iff]
      exact hak
    · simp only [coeffVal]
      rw [addVal_of_ne_zero K hak]
    · rw [slopeReal_real]
  have hle : m ≤ (vk - i₁) / (k - i₀ : ℝ) := by
    rw [nextVertex_slope_eq_sInf'' _ hstep]
    exact csInf_le (nextVertex_bddBelow _ hstep) hmem
  have hki : (0 : ℝ) < (k : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hk)
  rw [le_div_iff₀ hki] at hle
  linarith

/-- **Geometric core.**  Every later finite point lies on/above the first segment of slope `m`,
i.e. `m·k ≤ ν(aₖ)` for all `k > 0`.  The origin case of `step_slope_le`. -/
theorem firstBreak_slope_le (f : PowerSeries K) {j₀ l : ℕ} {j₁ m : ℝ}
    (hbreak : nextStep (coeffVal K f) 0 0 = .nextVertex j₀ j₁ l m)
    {k : ℕ} (hk : 0 < k) (hak : PowerSeries.coeff k f ≠ 0) :
    m * k ≤ - Real.log ‖PowerSeries.coeff k f‖ := by
  have h := step_slope_le K f hbreak hk hak
  push_cast at h
  linarith

/-! ### Inversion lemmas for the algorithm (generic in `Γ`)

`NewtonPolygon.lean`'s API extracts data *from* a known constructor; here we add the three
missing inversions — what each non-`nextVertex` output says about the slope set — needed to
*drive* the algorithm on concrete inputs (polynomials). -/

section StepInversion

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ] {w : ℕ → WithTop Γ} {i₀ : ℕ} {i₁ : Γ}

/-- If a step returns `.tail`, the slope set is empty.  (The `⊤` arm of the final match cannot
fire: the chosen vertex lies in the achieving set, so its value is finite.) -/
lemma slopeSet_eq_empty_of_nextStep_tail (h : nextStep w i₀ i₁ = .tail) :
    slopeSet w i₀ i₁ = ∅ := by
  by_contra hne
  simp_rw [nextStep] at h
  rw [if_neg hne] at h
  split_ifs at h with h1 h2 h3
  split at h
  · rename_i heq
    obtain ⟨k, hk, kfin, k₁, hk₁, hsl⟩ := (of_not_not (not_not_intro h2)).choose_spec.1
    have hnonempty :
        (achievingSet w i₀ i₁ (of_not_not (not_not_intro h2)).choose).Nonempty :=
      ⟨k, hk, kfin, k₁, hk₁, hsl⟩
    have hmax := Finset.max'_mem (Set.not_infinite.mp h3).toFinset
      ((Set.not_infinite.mp h3).toFinset_nonempty.mpr hnonempty)
    exact ((Set.not_infinite.mp h3).mem_toFinset.mp hmax).2.1 heq
  · exact absurd h (by simp)

/-- If a step returns `.limitingRay`, the infimum of the slope set is not attained. -/
lemma not_attained_of_nextStep_limitingRay {m : ℝ}
    (h : nextStep w i₀ i₁ = .limitingRay m) :
    ¬ ∃ m' ∈ slopeSet w i₀ i₁, m' = sInf (slopeSet w i₀ i₁) := by
  simp_rw [nextStep] at h
  split_ifs at h with h1 h2 h3 h4
  · split at h <;> exact absurd h (by simp)
  · exact h3

/-- If a step returns `.infiniteRay m`, the set of points achieving the slope `m` is infinite. -/
lemma achievingSet_infinite_of_nextStep_infiniteRay {m : ℝ}
    (h : nextStep w i₀ i₁ = .infiniteRay m) :
    (achievingSet w i₀ i₁ m).Infinite := by
  simp_rw [nextStep] at h
  split_ifs at h with h1 h2 h3 h4
  · injection h with hh
    rwa [hh] at h4
  · split at h <;> exact absurd h (by simp)

/-- Evaluating the polygon at step `1`, given the vertex at step `0`. -/
lemma newtonPolygon_one_eq {j₀ : ℕ} {j₁ : Γ} {l : ℕ} {m : ℝ}
    (h0 : newtonPolygon w 0 = some (.nextVertex j₀ j₁ l m)) :
    newtonPolygon w 1 = some (nextStep w j₀ j₁) := by
  show newtonPolygon w (0 + 1) = some (nextStep w j₀ j₁)
  rw [newtonPolygon, h0]

end StepInversion

/-! ### Driving the algorithm on polynomials

For a polynomial the point set is finite, so with points still ahead the algorithm can only
output a `nextVertex`, and with none ahead it outputs `.tail`.  Together with the inversion
lemmas above this pins down the polygon of a polynomial completely. -/

section PolynomialInput

variable (f : Polynomial K)

theorem coeffVal_coe_eq_top_iff (k : ℕ) :
    coeffVal K (f : PowerSeries K) k = ⊤ ↔ f.coeff k = 0 := by
  simp only [coeffVal, Polynomial.coeff_coe, addVal_eq_top_iff]

theorem finite_coeffVal_coe_iff (k : ℕ) :
    finite (coeffVal K (f : PowerSeries K)) k ↔ f.coeff k ≠ 0 :=
  not_congr (coeffVal_coe_eq_top_iff K f k)

theorem coeffVal_coe_of_ne_zero {k : ℕ} (h : f.coeff k ≠ 0) :
    coeffVal K (f : PowerSeries K) k = ((- Real.log ‖f.coeff k‖ : ℝ) : WithTop ℝ) := by
  simp only [coeffVal, Polynomial.coeff_coe]
  exact addVal_of_ne_zero K h

theorem slopeSet_coe_finite (i₀ : ℕ) (i₁ : ℝ) :
    (slopeSet (coeffVal K (f : PowerSeries K)) i₀ i₁).Finite := by
  apply Set.Finite.subset ((Set.finite_Iic f.natDegree).image
    (fun k : ℕ => slopeReal i₀ k i₁ (- Real.log ‖f.coeff k‖)))
  rintro x ⟨j₀, hj₀, hfin, j₁, hj₁, rfl⟩
  have hcoeff : f.coeff j₀ ≠ 0 := (finite_coeffVal_coe_iff K f j₀).mp hfin
  have hj₁' : j₁ = - Real.log ‖f.coeff j₀‖ := by
    have h2 := coeffVal_coe_of_ne_zero K f hcoeff
    rw [hj₁] at h2
    exact_mod_cast h2
  exact ⟨j₀, Polynomial.le_natDegree_of_ne_zero hcoeff, by rw [hj₁']⟩

theorem achievingSet_coe_finite (i₀ : ℕ) (i₁ m : ℝ) :
    (achievingSet (coeffVal K (f : PowerSeries K)) i₀ i₁ m).Finite :=
  Set.Finite.subset (Set.finite_Iic f.natDegree) fun j hj =>
    Polynomial.le_natDegree_of_ne_zero ((finite_coeffVal_coe_iff K f j).mp hj.2.1)

theorem mem_slopeSet_coe {i₀ k : ℕ} (i₁ : ℝ) (hk : i₀ < k) (hak : f.coeff k ≠ 0) :
    slopeReal i₀ k i₁ (- Real.log ‖f.coeff k‖)
      ∈ slopeSet (coeffVal K (f : PowerSeries K)) i₀ i₁ :=
  ⟨k, hk, (finite_coeffVal_coe_iff K f k).mpr hak, - Real.log ‖f.coeff k‖,
    coeffVal_coe_of_ne_zero K f hak, rfl⟩

/-- **A step of the algorithm on a polynomial, with a finite point still ahead, is a vertex.**
The other four outputs are impossible: the slope set is nonempty (a point is ahead), finite
(the point set is finite), its infimum is attained, and the achieving set is finite. -/
theorem exists_nextStep_coe_eq_nextVertex {i₀ : ℕ} (i₁ : ℝ) {k : ℕ} (hk : i₀ < k)
    (hak : f.coeff k ≠ 0) :
    ∃ j₀ j₁ l m, nextStep (coeffVal K (f : PowerSeries K)) i₀ i₁ = .nextVertex j₀ j₁ l m := by
  have hne : (slopeSet (coeffVal K (f : PowerSeries K)) i₀ i₁).Nonempty :=
    ⟨_, mem_slopeSet_coe K f i₁ hk hak⟩
  cases h : nextStep (coeffVal K (f : PowerSeries K)) i₀ i₁ with
  | tail => exact absurd (slopeSet_eq_empty_of_nextStep_tail h) hne.ne_empty
  | unboundedBelow =>
      exact absurd (unboundedBelow _ h)
        (not_not_intro (slopeSet_coe_finite K f i₀ i₁).bddBelow)
  | limitingRay m =>
      exact absurd ⟨sInf _, hne.csInf_mem (slopeSet_coe_finite K f i₀ i₁), rfl⟩
        (not_attained_of_nextStep_limitingRay h)
  | infiniteRay m =>
      exact absurd (achievingSet_infinite_of_nextStep_infiniteRay h)
        (Set.not_infinite.mpr (achievingSet_coe_finite K f i₀ i₁ m))
  | nextVertex j₀ j₁ l m => exact ⟨j₀, j₁, l, m, rfl⟩

/-- With no finite point ahead, the step is `.tail`. -/
theorem nextStep_coe_eq_tail {i₀ : ℕ} (i₁ : ℝ) (h : ∀ k, i₀ < k → f.coeff k = 0) :
    nextStep (coeffVal K (f : PowerSeries K)) i₀ i₁ = .tail := by
  have hempty : slopeSet (coeffVal K (f : PowerSeries K)) i₀ i₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨j₀, hj₀, hfin, j₁, hj₁, rfl⟩
    exact (finite_coeffVal_coe_iff K f j₀).mp hfin (h j₀ hj₀)
  rw [nextStep, if_pos hempty]

/-- The data carried by a vertex of a polynomial polygon: the vertex is a nonzero coefficient
within the degree, and its `y`-value is `ν(a_{j₀})`. -/
theorem nextVertex_coe_data {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal K (f : PowerSeries K)) i₀ i₁ = .nextVertex j₀ j₁ l m) :
    f.coeff j₀ ≠ 0 ∧ j₀ ≤ f.natDegree ∧ j₁ = - Real.log ‖f.coeff j₀‖ := by
  have hfin : f.coeff j₀ ≠ 0 :=
    (finite_coeffVal_coe_iff K f j₀).mp (nextVertex_j₀Finite _ h)
  refine ⟨hfin, Polynomial.le_natDegree_of_ne_zero hfin, ?_⟩
  have h1 := nextVertex_j₁_eq _ h
  rw [coeffVal_coe_of_ne_zero K f hfin] at h1
  exact_mod_cast h1.symm

/-- The polygon of a polynomial with `a₀ ≠ 0` starts at `(0, ν(a₀))` (general-start version of
`findFirstFinite_zero`, which assumed `a₀ = 1`). -/
theorem findFirstFinite_coe_zero (hg0 : f.coeff 0 ≠ 0) :
    findFirstFinite (coeffVal K (f : PowerSeries K)) 0
      = some (0, - Real.log ‖f.coeff 0‖) := by
  classical
  have hfin : finite (coeffVal K (f : PowerSeries K)) 0 :=
    (finite_coeffVal_coe_iff K f 0).mpr hg0
  have hex : ∃ i ≥ 0, finite (coeffVal K (f : PowerSeries K)) i := ⟨0, le_refl _, hfin⟩
  have hzero : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr ⟨le_refl _, hfin⟩
  have h2 : coeffVal K (f : PowerSeries K) (Nat.find hex)
      = ((- Real.log ‖f.coeff 0‖ : ℝ) : WithTop ℝ) := by
    rw [hzero]
    exact coeffVal_coe_of_ne_zero K f hg0
  unfold findFirstFinite
  rw [dif_pos hex]
  have hchoose : (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose
      = - Real.log ‖f.coeff 0‖ :=
    WithTop.coe_inj.mp
      ((Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose_spec.trans h2)
  rw [hchoose, hzero]

/-- With `a₀ ≠ 0` the algorithm starts at `(0, ν(a₀))`. -/
theorem newtonPolygon_coe_zero_eq (hg0 : f.coeff 0 ≠ 0) :
    newtonPolygon (coeffVal K (f : PowerSeries K)) 0
      = nextStep (coeffVal K (f : PowerSeries K)) 0 (- Real.log ‖f.coeff 0‖) := by
  conv_lhs => rw [newtonPolygon, findFirstFinite_coe_zero K f hg0]

end PolynomialInput

end NewtonPolygon

/-!
## 5.4  Pure polynomials

"Only one slope" on the packaged `NewtonPolygon`: the `0`-th slope is the real number `m`, and
there is no further (finite) slope.  (As slopes are increasing and `⊤` is absorbing, `slopes 1 = ⊤`
already forces `slopes n = ⊤` for all `n ≥ 1`.)
-/

/-- **Blueprint Definition 5.4.**  A Newton polygon is *pure of slope `m`* when it is a single
segment: its first slope is `m` and it has no later slope. -/
def NewtonPolygon.IsPure (NP : NewtonPolygon) (m : ℝ) : Prop :=
  NP.slopes 0 = (m : WithTopBot ℝ) ∧ NP.slopes 1 = ⊤

namespace NewtonPolygon

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- A power series `f` is *pure of slope `m`* if the Newton polygon built from its coefficient
valuations is pure of slope `m`. -/
def IsPureSeries (f : PowerSeries K) (m : ℝ) : Prop :=
  (NP' (coeffVal K f)).IsPure m

/-!
## 5.5  Irreducible polynomials are pure

Stated and proved **after 5.7 below**, on whose factorisation the proof depends ("a break at an
interior point gives a proper factor").  See `isPureSeries_of_irreducible`. -/

/-!
## 5.6  Purity ↔ distinguished

At `c = exp m` (the bridge `c = p ^ m` at the canonical base `p = e`), `f` is pure of slope `m`
iff its Gauss norm is `1` and is realised by the top coefficient `b_n` (`|f|_c = ‖b_n‖ c^n = 1`),
i.e. `f` is `n`-distinguished.  **Proved in full.**

Two hypotheses are added to the original statement, both from the blueprint's standing
normalisation `f = 1 + a₁x + ⋯ + aₙxⁿ` of §5.2: `a₀ = 1` (which anchors the polygon at the
origin) and `0 < natDegree f`.  Without them the statement is false: for `f = 1` the right-hand
side holds for every `m` but the polygon has no segment at all (`slopes 0 = ⊤`). -/

omit [IsUltrametricDist K] in
/-- `‖a‖ (eᵐ)ᵏ = exp (log ‖a‖ + mk)`: the basic dictionary between Gauss-norm terms at
`c = exp m` and heights of polygon points. -/
private lemma term_eq_exp {a : K} (ha : a ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k = Real.exp (Real.log ‖a‖ + m * k) := by
  rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr ha), ← Real.exp_nat_mul, mul_comm m (k : ℝ)]

omit [IsUltrametricDist K] in
/-- The term at `k` is `≤ 1` iff the point `(k, ν(a))` lies on/above the line `y = mx`. -/
private lemma term_le_one_iff {a : K} (ha : a ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k ≤ 1 ↔ m * k ≤ - Real.log ‖a‖ := by
  rw [term_eq_exp K ha m k, Real.exp_le_one_iff]
  constructor <;> intro h <;> linarith

omit [IsUltrametricDist K] in
/-- The term at `k` is `= 1` iff the point `(k, ν(a))` lies on the line `y = mx`. -/
private lemma term_eq_one_iff {a : K} (ha : a ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k = 1 ↔ - Real.log ‖a‖ = m * k := by
  rw [term_eq_exp K ha m k, Real.exp_eq_one_iff]
  constructor <;> intro h <;> linarith

omit [IsUltrametricDist K] in
/-- The Gauss-norm terms of a polynomial are bounded above (only finitely many are nonzero). -/
private lemma coe_terms_bddAbove (f : Polynomial K) {c : ℝ} (_hc : 0 ≤ c) :
    BddAbove (Set.range fun k => ‖PowerSeries.coeff k (f : PowerSeries K)‖ * c ^ k) := by
  classical
  have hne : (Finset.range (f.natDegree + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  refine ⟨(Finset.range (f.natDegree + 1)).sup' hne (fun k => ‖f.coeff k‖ * c ^ k), ?_⟩
  rintro x ⟨k, rfl⟩
  dsimp only
  rw [Polynomial.coeff_coe]
  by_cases hk : k ≤ f.natDegree
  · exact Finset.le_sup' (fun k => ‖f.coeff k‖ * c ^ k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [not_le] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, norm_zero, zero_mul]
    calc (0 : ℝ) ≤ ‖f.coeff 0‖ * c ^ 0 := by positivity
      _ ≤ _ := Finset.le_sup' (fun k => ‖f.coeff k‖ * c ^ k)
        (Finset.mem_range.mpr (Nat.succ_pos _))

/-- **Blueprint Proposition 5.6.**  With the normalisation `a₀ = 1` and `n = natDegree f ≥ 1`,
`f` is pure of slope `m` iff at `c = exp m` its Gauss norm is `1` and is realised by the top
coefficient: `|f|_c = ‖bₙ‖ cⁿ = 1`, i.e. `f` is `n`-distinguished. -/
theorem isPureSeries_iff_distinguished (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (hn : 0 < f.natDegree) (m : ℝ) (c : ℝ) (hc : c = Real.exp m) :
    IsPureSeries K (f : PowerSeries K) m ↔
      (PowerSeries.gaussNorm norm c (f : PowerSeries K)
          = ‖PowerSeries.coeff f.natDegree (f : PowerSeries K)‖ * c ^ f.natDegree
        ∧ PowerSeries.gaussNorm norm c (f : PowerSeries K) = 1) := by
  subst hc
  set n := f.natDegree with hn_def
  have hf_ne : f ≠ 0 := fun h => one_ne_zero (by rw [← hf0, h, Polynomial.coeff_zero])
  have hlead : f.coeff n ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf_ne
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe]; exact hf0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · -- pure ⟹ distinguished
    rintro ⟨hs0, hs1⟩
    -- the first step is a vertex `(j₀, j₁)` of slope `m' = m`
    obtain ⟨j₀, j₁, l, m', hv⟩ :=
      exists_nextStep_coe_eq_nextVertex K f (0 : ℝ) hn hlead
    have h0eq : newtonPolygon (coeffVal K (f : PowerSeries K)) 0
        = some (Step.nextVertex j₀ j₁ l m') := by
      rw [newtonPolygon_zero_eq K _ hf0', hv]
    have hm' : m' = m := by
      have h := hs0
      rw [show (NP' (coeffVal K (f : PowerSeries K))).slopes 0
          = slopes' (newtonPolygon (coeffVal K (f : PowerSeries K)) 0) from rfl, h0eq] at h
      have h2 : (m' : WithTopBot ℝ) = (m : WithTopBot ℝ) := h
      exact_mod_cast h2
    rw [hm'] at hv h0eq
    obtain ⟨hcj₀, hj₀le, hj₁val⟩ := nextVertex_coe_data K f hv
    -- the vertex is the top coefficient: otherwise there is a second slope
    have hj₀n : j₀ = n := by
      refine le_antisymm hj₀le ?_
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨k₀, k₁, l₂, m₂, hv₂⟩ :=
        exists_nextStep_coe_eq_nextVertex K f j₁ hlt hlead
      have h := hs1
      rw [show (NP' (coeffVal K (f : PowerSeries K))).slopes 1
          = slopes' (newtonPolygon (coeffVal K (f : PowerSeries K)) 1) from rfl,
        newtonPolygon_one_eq h0eq, hv₂] at h
      have h2 : (m₂ : WithTopBot ℝ) = ⊤ := h
      simp at h2
    subst hj₀n
    -- the top point lies on the line: `ν(aₙ) = m·n`
    have hslope := nextVertex_slope_eq_sInf' _ hv
    rw [slopeReal_real] at hslope
    have hνn : - Real.log ‖f.coeff n‖ = m * n := by
      rw [hj₁val, eq_div_iff (by push_cast; simpa using hnR.ne')] at hslope
      push_cast at hslope
      linarith
    -- assemble the Gauss-norm facts
    have htn : ‖f.coeff n‖ * Real.exp m ^ n = 1 := (term_eq_one_iff K hlead m n).mpr hνn
    have hterm_le : ∀ k, ‖PowerSeries.coeff k (f : PowerSeries K)‖ * Real.exp m ^ k ≤ 1 := by
      intro k
      rw [Polynomial.coeff_coe]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [hf0]
      · by_cases hak : f.coeff k = 0
        · rw [hak, norm_zero, zero_mul]
          exact zero_le_one
        · refine (term_le_one_iff K hak m k).mpr ?_
          have h := firstBreak_slope_le K (f : PowerSeries K) hv hk
            (by rwa [Polynomial.coeff_coe])
          rwa [Polynomial.coeff_coe] at h
    have hgauss : PowerSeries.gaussNorm norm (Real.exp m) (f : PowerSeries K) = 1 := by
      rw [PowerSeries.gaussNorm_eq]
      refine le_antisymm (ciSup_le hterm_le) ?_
      have h0 : ‖PowerSeries.coeff 0 (f : PowerSeries K)‖ * Real.exp m ^ 0 = 1 := by
        simp [hf0']
      calc (1 : ℝ) = ‖PowerSeries.coeff 0 (f : PowerSeries K)‖ * Real.exp m ^ 0 := h0.symm
        _ ≤ _ := le_ciSup (coe_terms_bddAbove K f (Real.exp_nonneg m)) 0
    refine ⟨?_, hgauss⟩
    rw [hgauss, Polynomial.coeff_coe, htn]
  · -- distinguished ⟹ pure
    rintro ⟨htop, hone⟩
    have htn : ‖f.coeff n‖ * Real.exp m ^ n = 1 := by
      have h := htop.symm.trans hone
      rwa [Polynomial.coeff_coe] at h
    have hνn : - Real.log ‖f.coeff n‖ = m * n := (term_eq_one_iff K hlead m n).mp htn
    -- every term is `≤ 1`, i.e. every point lies on/above the line `y = mx`
    have hterm_le : ∀ k, ‖PowerSeries.coeff k (f : PowerSeries K)‖ * Real.exp m ^ k ≤ 1 := by
      intro k
      rw [← hone, PowerSeries.gaussNorm_eq]
      exact le_ciSup (coe_terms_bddAbove K f (Real.exp_nonneg m)) k
    have hν : ∀ k, 0 < k → f.coeff k ≠ 0 → m * k ≤ - Real.log ‖f.coeff k‖ := by
      intro k _ hak
      refine (term_le_one_iff K hak m k).mp ?_
      have h := hterm_le k
      rwa [Polynomial.coeff_coe] at h
    -- drive the algorithm: the first step is a vertex …
    obtain ⟨j₀, j₁, l, m', hv⟩ :=
      exists_nextStep_coe_eq_nextVertex K f (0 : ℝ) hn hlead
    obtain ⟨hcj₀, hj₀le, hj₁val⟩ := nextVertex_coe_data K f hv
    -- … whose slope is `m` …
    have hsn : slopeReal 0 n (0 : ℝ) (- Real.log ‖f.coeff n‖) = m := by
      rw [slopeReal_real, hνn]
      push_cast
      rw [sub_zero, sub_zero]
      exact mul_div_cancel_right₀ m hnR.ne'
    have hmem_n : slopeReal 0 n (0 : ℝ) (- Real.log ‖f.coeff n‖)
        ∈ slopeSet (coeffVal K (f : PowerSeries K)) 0 (0 : ℝ) :=
      mem_slopeSet_coe K f (0 : ℝ) hn hlead
    have hlb : ∀ x ∈ slopeSet (coeffVal K (f : PowerSeries K)) 0 (0 : ℝ), m ≤ x := by
      rintro x ⟨k, hk, kfin, k₁, hk₁, rfl⟩
      have hak : f.coeff k ≠ 0 := (finite_coeffVal_coe_iff K f k).mp kfin
      have hk₁' : k₁ = - Real.log ‖f.coeff k‖ := by
        have h2 := coeffVal_coe_of_ne_zero K f hak
        rw [hk₁] at h2
        exact_mod_cast h2
      have hkR : (0 : ℝ) < (k : ℝ) - ((0 : ℕ) : ℝ) := by
        push_cast
        simpa using (Nat.cast_pos.mpr hk : (0 : ℝ) < (k : ℝ))
      rw [slopeReal_real, hk₁', le_div_iff₀ hkR]
      have h := hν k hk hak
      push_cast
      linarith
    have hsInf : sInf (slopeSet (coeffVal K (f : PowerSeries K)) 0 (0 : ℝ)) = m := by
      refine le_antisymm ?_ (le_csInf ⟨_, hmem_n⟩ hlb)
      calc sInf _ ≤ slopeReal 0 n (0 : ℝ) (- Real.log ‖f.coeff n‖) :=
            csInf_le (slopeSet_coe_finite K f 0 0).bddBelow hmem_n
        _ = m := hsn
    have hm' : m' = m := (nextVertex_slope_eq_sInf'' _ hv).trans hsInf
    rw [hm'] at hv
    -- … and whose vertex is the top coefficient (it is the maximal achiever)
    have hj₀n : j₀ = n := by
      refine le_antisymm hj₀le ?_
      have hmemach : n ∈ achievingSet (coeffVal K (f : PowerSeries K)) 0 (0 : ℝ)
          (sInf (slopeSet (coeffVal K (f : PowerSeries K)) 0 (0 : ℝ))) := by
        refine ⟨hn, (finite_coeffVal_coe_iff K f n).mpr hlead,
          - Real.log ‖f.coeff n‖, coeffVal_coe_of_ne_zero K f hlead, ?_⟩
        rw [hsInf]
        exact hsn.symm
      rw [nextVertex_j₀_eq_max _ hv]
      exact Finset.le_max' _ n ((nextVertex_finite _ hv).mem_toFinset.mpr hmemach)
    subst hj₀n
    -- conclude purity
    have h0eq : newtonPolygon (coeffVal K (f : PowerSeries K)) 0
        = some (Step.nextVertex n j₁ l m) := by
      rw [newtonPolygon_zero_eq K _ hf0', hv]
    have htail : nextStep (coeffVal K (f : PowerSeries K)) n j₁ = .tail :=
      nextStep_coe_eq_tail K f j₁ fun k hk =>
        Polynomial.coeff_eq_zero_of_natDegree_lt hk
    refine ⟨?_, ?_⟩
    · show slopes' (newtonPolygon (coeffVal K (f : PowerSeries K)) 0) = _
      rw [h0eq]
      rfl
    · show slopes' (newtonPolygon (coeffVal K (f : PowerSeries K)) 1) = _
      rw [newtonPolygon_one_eq h0eq, htail]
      rfl

/-!
## 5.7  Factorisation at the first break

The blueprint factors `f` over `ℂ_p`; "no zeros in the closed ball of radius `p^m`" refers to
roots in `ℂ_p`.  We measure roots in the **algebraic closure** `AlgebraicClosure K`, with a chosen
valuation `w : Valuation (AlgebraicClosure K) ℝ≥0` extending the norm (`hw`).  (Completeness of
the closure is *not* assumed yet — it is needed only later, for power series.)

The proof is assembled from four pieces, of which three are proved below:

1. `distinguished_of_firstBreak` (**proved**): the first break at `(i, mi)` makes `f`
   `i`-distinguished at `c = exp m` — every Gauss-norm term is `≤ 1`, the term at `i` is `1`,
   and every term beyond `i` is `< 1` (slopes strictly increase after a vertex).
2. `weierstrassPreparation_polynomial_divisible` (**proved**, imported from
   `PhD/WeierstrassPrep/WPrep_gen.lean`): polynomial Weierstrass preparation *at Gauss-norm
   parameter `c`*, for any `c` in the **divisible closure of the value group** of `K`
   (`MemDivisibleValueGroup`, imported from the same file; see `PhD/Main/Test/DivValueGroup.lean`
   for its structural description as the divisible hull of the exponent group, used to
   construct memberships below).  It is threaded into the proofs
   below through the private `exists_factor_aux`, which unbundles it into coefficient norms
   (with `dominant_const_of_isUnit_toRestricted` translating unit-ness of the factor `e`).
   This step requires `[CompleteSpace K]` — genuinely: over the *incomplete* `ℚ` with the
   `5`-adic norm, `X² − 5X + 125` is irreducible with a two-slope polygon, so no such
   factorisation can exist (see the module docstring of `WPrep_gen.lean`).  Since slope radii
   always lie in the divisible closure (`memDivisibleValueGroup_exp_slope`) and it is dense
   (`exists_memDivisibleValueGroup_between`), no further hypotheses appear and everything
   applies over discretely valued fields such as `ℚ_p`.
3. `isPureSeries_of_bounds` (**proved**): the produced factor `ω` is pure of slope `m` — the
   general-start version of 5.6's "distinguished ⟹ pure" direction (no `a₀ = 1` normalisation).
4. `aeval_ne_zero_of_dominant_const` (**proved**): the unit factor `e`, whose constant
   coefficient strictly dominates, has no zeros in the closed ball of radius `c`.

As in 5.8 – 5.10, the blueprint's standing normalisation `a₀ = 1` is added as a hypothesis. -/

omit [IsUltrametricDist K] in
/-- The term at `k` is `< 1` iff the point `(k, ν(a))` lies strictly above the line `y = mx`. -/
private lemma term_lt_one_iff {a : K} (ha : a ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k < 1 ↔ m * k < - Real.log ‖a‖ := by
  rw [term_eq_exp K ha m k, Real.exp_lt_one_iff]
  constructor <;> intro h <;> linarith

omit [IsUltrametricDist K] in
/-- Comparison with a reference coefficient: `‖a‖ (eᵐ)ᵏ ≤ ‖b‖` iff `(k, ν(a))` lies on/above
the line of slope `m` through `(0, ν(b))`. -/
private lemma term_le_norm_iff {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k ≤ ‖b‖ ↔ m * k ≤ - Real.log ‖a‖ - - Real.log ‖b‖ := by
  rw [term_eq_exp K ha m k,
    show ‖b‖ = Real.exp (Real.log ‖b‖) from (Real.exp_log (norm_pos_iff.mpr hb)).symm,
    Real.exp_le_exp, Real.log_exp]
  constructor <;> intro h <;> linarith

omit [IsUltrametricDist K] in
private lemma term_eq_norm_iff {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k = ‖b‖ ↔ - Real.log ‖a‖ - - Real.log ‖b‖ = m * k := by
  rw [term_eq_exp K ha m k,
    show ‖b‖ = Real.exp (Real.log ‖b‖) from (Real.exp_log (norm_pos_iff.mpr hb)).symm,
    Real.exp_eq_exp, Real.log_exp]
  constructor <;> intro h <;> linarith

/-- **The first break makes `f` `i`-distinguished at `c = exp m`.**  Every Gauss-norm term is
`≤ 1`, the term at the break is `= 1`, and every term beyond the break is `< 1` (after the
vertex the slopes strictly increase, so later points lie strictly above the line `y = mx`). -/
theorem distinguished_of_firstBreak (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    {i : ℕ} {j₁ m : ℝ} (hbreak : HasFirstBreak K (f : PowerSeries K) i j₁ i m) :
    (∀ k, ‖f.coeff k‖ * Real.exp m ^ k ≤ 1) ∧
      ‖f.coeff i‖ * Real.exp m ^ i = 1 ∧
      ∀ t, i < t → ‖f.coeff t‖ * Real.exp m ^ t < 1 := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe]; exact hf0
  have hv : nextStep (coeffVal K (f : PowerSeries K)) 0 0 = .nextVertex i j₁ i m :=
    Option.some_inj.mp ((newtonPolygon_zero_eq K _ hf0').symm.trans hbreak)
  have hipos : 0 < i := nextVertex_lt _ hv
  have hiR : (0 : ℝ) < i := by exact_mod_cast hipos
  obtain ⟨hci, hile, hj₁val⟩ := nextVertex_coe_data K f hv
  have hslope := nextVertex_slope_eq_sInf' _ hv
  rw [slopeReal_real] at hslope
  have hνi : - Real.log ‖f.coeff i‖ = m * i := by
    rw [hj₁val, eq_div_iff (by push_cast; simpa using hiR.ne')] at hslope
    push_cast at hslope
    linarith
  refine ⟨?_, (term_eq_one_iff K hci m i).mpr hνi, ?_⟩
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hf0]
    · by_cases hak : f.coeff k = 0
      · rw [hak, norm_zero, zero_mul]; exact zero_le_one
      · refine (term_le_one_iff K hak m k).mpr ?_
        have h := firstBreak_slope_le K (f : PowerSeries K) hv hk
          (by rwa [Polynomial.coeff_coe])
        rwa [Polynomial.coeff_coe] at h
  · intro t ht
    by_cases hat : f.coeff t = 0
    · rw [hat, norm_zero, zero_mul]; exact zero_lt_one
    · refine (term_lt_one_iff K hat m t).mpr ?_
      obtain ⟨k₀, k₁, l₂, m₂, hv₂⟩ := exists_nextStep_coe_eq_nextVertex K f j₁ ht hat
      have hmm : m < m₂ := slopes_increasing_nextVertex _ hv hv₂
      have hstep := step_slope_le K (f : PowerSeries K) hv₂ ht
        (by rwa [Polynomial.coeff_coe])
      rw [Polynomial.coeff_coe] at hstep
      have htiR : (0 : ℝ) < (t : ℝ) - i := by
        rw [sub_pos]; exact_mod_cast ht
      have hj₁mi : j₁ = m * i := by rw [hj₁val]; exact hνi
      nlinarith [hstep, mul_pos (sub_pos.mpr hmm) htiR, hj₁mi]

/-- **Purity from coefficient bounds** (general start — no `a₀ = 1` normalisation): if every
Gauss-norm term of `g` at `c = exp m` is dominated by the constant term, with equality attained
at the top degree `s = natDegree g ≥ 1`, then `g` is pure of slope `m`.  This is how purity of
the Weierstrass factor `ω` is established. -/
theorem isPureSeries_of_bounds (g : Polynomial K) (hg0 : g.coeff 0 ≠ 0)
    (hs : 0 < g.natDegree) (m : ℝ)
    (hle : ∀ k, ‖g.coeff k‖ * Real.exp m ^ k ≤ ‖g.coeff 0‖)
    (htop : ‖g.coeff g.natDegree‖ * Real.exp m ^ g.natDegree = ‖g.coeff 0‖) :
    IsPureSeries K (g : PowerSeries K) m := by
  set s := g.natDegree with hs_def
  set ν₀ : ℝ := - Real.log ‖g.coeff 0‖ with hν₀
  have hg_ne : g ≠ 0 := fun h => hg0 (by rw [h, Polynomial.coeff_zero])
  have hlead : g.coeff s ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg_ne
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hνs : - Real.log ‖g.coeff s‖ - ν₀ = m * s := (term_eq_norm_iff K hlead hg0 m s).mp htop
  have hν : ∀ k, 0 < k → g.coeff k ≠ 0 → m * k ≤ - Real.log ‖g.coeff k‖ - ν₀ := fun k _ hak =>
    (term_le_norm_iff K hak hg0 m k).mp (hle k)
  obtain ⟨j₀, j₁, l, m', hv⟩ := exists_nextStep_coe_eq_nextVertex K g ν₀ hs hlead
  obtain ⟨hcj₀, hj₀le, hj₁val⟩ := nextVertex_coe_data K g hv
  have hsn : slopeReal 0 s ν₀ (- Real.log ‖g.coeff s‖) = m := by
    rw [slopeReal_real]
    push_cast
    rw [sub_zero, show - Real.log ‖g.coeff s‖ - ν₀ = m * s from hνs]
    exact mul_div_cancel_right₀ m hsR.ne'
  have hmem_s : slopeReal 0 s ν₀ (- Real.log ‖g.coeff s‖)
      ∈ slopeSet (coeffVal K (g : PowerSeries K)) 0 ν₀ :=
    mem_slopeSet_coe K g ν₀ hs hlead
  have hlb : ∀ x ∈ slopeSet (coeffVal K (g : PowerSeries K)) 0 ν₀, m ≤ x := by
    rintro x ⟨k, hk, kfin, k₁, hk₁, rfl⟩
    have hak : g.coeff k ≠ 0 := (finite_coeffVal_coe_iff K g k).mp kfin
    have hk₁' : k₁ = - Real.log ‖g.coeff k‖ := by
      have h2 := coeffVal_coe_of_ne_zero K g hak
      rw [hk₁] at h2
      exact_mod_cast h2
    have hkR : (0 : ℝ) < (k : ℝ) - ((0 : ℕ) : ℝ) := by
      push_cast
      simpa using (Nat.cast_pos.mpr hk : (0 : ℝ) < (k : ℝ))
    rw [slopeReal_real, hk₁', le_div_iff₀ hkR]
    have h := hν k hk hak
    push_cast
    linarith
  have hsInf : sInf (slopeSet (coeffVal K (g : PowerSeries K)) 0 ν₀) = m := by
    refine le_antisymm ?_ (le_csInf ⟨_, hmem_s⟩ hlb)
    calc sInf _ ≤ slopeReal 0 s ν₀ (- Real.log ‖g.coeff s‖) :=
          csInf_le (slopeSet_coe_finite K g 0 ν₀).bddBelow hmem_s
      _ = m := hsn
  have hm' : m' = m := (nextVertex_slope_eq_sInf'' _ hv).trans hsInf
  rw [hm'] at hv
  have hj₀s : j₀ = s := by
    refine le_antisymm hj₀le ?_
    have hmemach : s ∈ achievingSet (coeffVal K (g : PowerSeries K)) 0 ν₀
        (sInf (slopeSet (coeffVal K (g : PowerSeries K)) 0 ν₀)) := by
      refine ⟨hs, (finite_coeffVal_coe_iff K g s).mpr hlead,
        - Real.log ‖g.coeff s‖, coeffVal_coe_of_ne_zero K g hlead, ?_⟩
      rw [hsInf]
      exact hsn.symm
    rw [nextVertex_j₀_eq_max _ hv]
    exact Finset.le_max' _ s ((nextVertex_finite _ hv).mem_toFinset.mpr hmemach)
  subst hj₀s
  have h0eq : newtonPolygon (coeffVal K (g : PowerSeries K)) 0
      = some (Step.nextVertex s j₁ l m) := by
    rw [newtonPolygon_coe_zero_eq K g hg0, hv]
  have htail : nextStep (coeffVal K (g : PowerSeries K)) s j₁ = .tail :=
    nextStep_coe_eq_tail K g j₁ fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt hk
  refine ⟨?_, ?_⟩
  · show slopes' (newtonPolygon (coeffVal K (g : PowerSeries K)) 0) = _
    rw [h0eq]
    rfl
  · show slopes' (newtonPolygon (coeffVal K (g : PowerSeries K)) 1) = _
    rw [newtonPolygon_one_eq h0eq, htail]
    rfl

omit [IsUltrametricDist K] in
/-- **A polynomial whose constant term strictly dominates has no zeros in the closed ball of
radius `c`.**  This is the shape of the unit factor of a Weierstrass preparation
(`0`-distinguished); elementary ultrametric estimate, as in 5.9. -/
theorem aeval_ne_zero_of_dominant_const {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (e : Polynomial K) {c : ℝ}
    (hdom : ∀ k, 1 ≤ k → ‖e.coeff k‖ * c ^ k < ‖e.coeff 0‖)
    {x : L} (hx : (w x : ℝ) ≤ c) :
    Polynomial.aeval x e ≠ 0 := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (w x).coe_nonneg hx
  have he0 : e.coeff 0 ≠ 0 := by
    intro h
    have h1 := hdom 1 le_rfl
    rw [h, norm_zero] at h1
    exact absurd h1 (not_lt.mpr (mul_nonneg (norm_nonneg _) (pow_nonneg hc0 1)))
  have hsub : w (Polynomial.aeval x e - algebraMap K L (e.coeff 0)) < ‖e.coeff 0‖₊ := by
    have h1 : Polynomial.aeval x e - algebraMap K L (e.coeff 0)
        = Polynomial.aeval x (e - Polynomial.C (e.coeff 0)) := by
      rw [_root_.map_sub, Polynomial.aeval_C]
    rw [h1, Polynomial.aeval_eq_sum_range]
    refine w.map_sum_lt (by simpa using he0) fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h00 : (e - Polynomial.C (e.coeff 0)).coeff 0 = 0 := by simp
      rw [h00, zero_smul, w.map_zero]
      exact pos_iff_ne_zero.mpr (by simpa using he0)
    · have hco : (e - Polynomial.C (e.coeff 0)).coeff k = e.coeff k := by
        simp [Polynomial.coeff_C, hk.ne']
      rw [hco, Algebra.smul_def, w.map_mul, w.map_pow, hw, ← NNReal.coe_lt_coe]
      push_cast
      calc ‖e.coeff k‖ * (w x : ℝ) ^ k
          ≤ ‖e.coeff k‖ * c ^ k := by gcongr
        _ < ‖e.coeff 0‖ := hdom k hk
  intro h0
  rw [h0, zero_sub, w.map_neg, hw] at hsub
  exact lt_irrefl _ hsub

omit [IsUltrametricDist K] in
/-- **A polynomial whose constant term (weakly) dominates every term has no zeros in the *open*
ball of radius `c`.**  This is the shape of the pure factor `g` of 5.7: its polygon starts at
`(0, ν(g₀))` with slope `m`, so `‖gₖ‖ cᵏ ≤ ‖g₀‖` at `c = exp m`, and strictness is recovered
from `w x < c`.  Used for the root count 5.10: no root of `g` lies strictly inside the ball. -/
theorem aeval_ne_zero_of_dominant_lt {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (g : Polynomial K) {c : ℝ} (hg0 : g.coeff 0 ≠ 0)
    (hdom : ∀ k, 1 ≤ k → ‖g.coeff k‖ * c ^ k ≤ ‖g.coeff 0‖)
    {x : L} (hx : (w x : ℝ) < c) :
    Polynomial.aeval x g ≠ 0 := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (w x).coe_nonneg hx.le
  have hsub : w (Polynomial.aeval x g - algebraMap K L (g.coeff 0)) < ‖g.coeff 0‖₊ := by
    have h1 : Polynomial.aeval x g - algebraMap K L (g.coeff 0)
        = Polynomial.aeval x (g - Polynomial.C (g.coeff 0)) := by
      rw [_root_.map_sub, Polynomial.aeval_C]
    rw [h1, Polynomial.aeval_eq_sum_range]
    refine w.map_sum_lt (by simpa using hg0) fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h00 : (g - Polynomial.C (g.coeff 0)).coeff 0 = 0 := by simp
      rw [h00, zero_smul, w.map_zero]
      exact pos_iff_ne_zero.mpr (by simpa using hg0)
    · have hco : (g - Polynomial.C (g.coeff 0)).coeff k = g.coeff k := by
        simp [Polynomial.coeff_C, hk.ne']
      rw [hco, Algebra.smul_def, w.map_mul, w.map_pow, hw]
      by_cases hgk : g.coeff k = 0
      · rw [hgk]
        have hpos : (0 : NNReal) < ‖g.coeff 0‖₊ := pos_iff_ne_zero.mpr (by simpa using hg0)
        simpa using hpos
      · rw [← NNReal.coe_lt_coe]
        push_cast
        calc ‖g.coeff k‖ * (w x : ℝ) ^ k
            < ‖g.coeff k‖ * c ^ k :=
              mul_lt_mul_of_pos_left
                (pow_lt_pow_left₀ hx (w x).coe_nonneg hk.ne') (norm_pos_iff.mpr hgk)
          _ ≤ ‖g.coeff 0‖ := hdom k hk
  intro h0
  rw [h0, zero_sub, w.map_neg, hw] at hsub
  exact lt_irrefl _ hsub

omit [NontriviallyNormedField K] [IsUltrametricDist K] in
/-- If a multiset of `ℝ≥0` has all elements `≥ c` and product exactly `c ^ card`, every element
equals `c` (the pigeonhole behind "all roots of a pure polynomial have the same absolute
value"). -/
private lemma eq_of_prod_eq_pow_card {S : Multiset NNReal} {c : NNReal} (hc : 0 < c)
    (hall : ∀ y ∈ S, c ≤ y) (hprod : S.prod = c ^ Multiset.card S)
    {y : NNReal} (hy : y ∈ S) : y = c := by
  by_contra hne
  have hlt : c < y := lt_of_le_of_ne (hall y hy) (Ne.symm hne)
  have hcons : y ::ₘ S.erase y = S := Multiset.cons_erase hy
  have hpow : ∀ T : Multiset NNReal, (∀ z ∈ T, c ≤ z) → c ^ Multiset.card T ≤ T.prod := by
    intro T
    induction T using Multiset.induction with
    | empty => intro _; simp
    | cons a t ih =>
        intro hT
        rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
        exact mul_le_mul' (hT a (Multiset.mem_cons_self a t))
          (ih fun z hz => hT z (Multiset.mem_cons_of_mem hz))
  have hS : S.prod = y * (S.erase y).prod := by
    conv_lhs => rw [← hcons]
    rw [Multiset.prod_cons]
  have hcard' : Multiset.card (S.erase y) = Multiset.card S - 1 :=
    Multiset.card_erase_of_mem hy
  have hcardpos : 0 < Multiset.card S := Multiset.card_pos_iff_exists_mem.mpr ⟨y, hy⟩
  have hle := hpow (S.erase y) fun z hz => hall z (Multiset.mem_of_mem_erase hz)
  rw [hcard'] at hle
  have h1 : c ^ Multiset.card S < S.prod := by
    calc c ^ Multiset.card S = c * c ^ (Multiset.card S - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ < y * c ^ (Multiset.card S - 1) :=
          mul_lt_mul_of_pos_right hlt (pow_pos hc _)
      _ ≤ y * (S.erase y).prod := mul_le_mul_right hle y
      _ = S.prod := hS.symm
  rw [hprod] at h1
  exact lt_irrefl _ h1

-- `MemDivisibleValueGroup K c` is imported from `PhD.WeierstrassPrep.WPrep_gen`; its
-- structural home is `PhD.Main.Test.DivValueGroup`: `c` lies in the **divisible closure of the
-- value group** of `K`, i.e. its exponent `log c` lies in the divisible hull
-- `(logValueGroup K).divisibleHull` of the exponent group
-- (`memDivisibleValueGroup_iff_log`, with the witness form
-- `memDivisibleValueGroup_iff_exists_log` used below).  Over `ℚ_p` this is `p^ℚ` — it
-- contains every slope radius `exp m` (`memDivisibleValueGroup_exp_slope`) and is dense in
-- the positive reals (`exists_memDivisibleValueGroup_between`), neither of which holds for
-- `p^ℤ` itself.

/-- **Slope radii lie in the divisible closure of the value group**: if the `k`-th segment of
the polygon of `f` has slope `m` and runs from `(i₀, ν(a_{i₀}))` to `(j₀, ν(a_{j₀}))`, then
`(exp m) ^ (j₀ - i₀) = ‖a_{i₀} / a_{j₀}‖`.  This is what lets 5.5 – 5.11 apply over a
*discretely* valued `K` such as `ℚ_p`, where slope radii like `p^(1/2)` are not norms of
elements. -/
theorem memDivisibleValueGroup_exp_slope (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    {k j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K (f : PowerSeries K)) k = some (.nextVertex j₀ j₁ l m)) :
    MemDivisibleValueGroup K (Real.exp m) := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe]; exact hf0
  obtain ⟨i₀, i₁, hstep, hci₀, hi₁val⟩ :
      ∃ (i₀ : ℕ) (i₁ : ℝ),
        nextStep (coeffVal K (f : PowerSeries K)) i₀ i₁ = .nextVertex j₀ j₁ l m ∧
        f.coeff i₀ ≠ 0 ∧ i₁ = - Real.log ‖f.coeff i₀‖ := by
    rcases k with _ | a
    · have hv : nextStep (coeffVal K (f : PowerSeries K)) 0 0 = .nextVertex j₀ j₁ l m :=
        Option.some_inj.mp ((newtonPolygon_zero_eq K _ hf0').symm.trans hseg)
      exact ⟨0, 0, hv, by rw [hf0]; exact one_ne_zero,
        by rw [hf0, norm_one, Real.log_one, neg_zero]⟩
    · obtain ⟨i₀, i₁, l', m', hprev⟩ := nextStep_nextVertex' _ hseg
      have hstep := nextStep_nextVertex'' _ hseg hprev
      obtain ⟨p₀, p₁, hprevstep⟩ := nextStep_nextVertex _ hprev
      obtain ⟨hci₀, -, hi₁val⟩ := nextVertex_coe_data K f hprevstep
      exact ⟨i₀, i₁, hstep, hci₀, hi₁val⟩
  obtain ⟨hcj₀, -, hj₁val⟩ := nextVertex_coe_data K f hstep
  have hij : i₀ < j₀ := nextVertex_lt _ hstep
  have hijR : (0 : ℝ) < (j₀ : ℝ) - i₀ := by rw [sub_pos]; exact_mod_cast hij
  have hslope := nextVertex_slope_eq_sInf' _ hstep
  rw [slopeReal_real] at hslope
  have hmn : m * ((j₀ : ℝ) - i₀) = j₁ - i₁ := by
    rw [eq_div_iff hijR.ne'] at hslope
    linarith
  rw [memDivisibleValueGroup_iff_exists_log (Real.exp_pos m)]
  refine ⟨j₀ - i₀, by omega, f.coeff i₀ / f.coeff j₀, div_ne_zero hci₀ hcj₀, ?_⟩
  rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hci₀) (norm_ne_zero_iff.mpr hcj₀),
    Real.log_exp, nsmul_eq_mul, Nat.cast_sub hij.le]
  rw [hj₁val, hi₁val] at hmn
  linarith [hmn]

omit [IsUltrametricDist K] in
/-- **The divisible closure of the value group is dense in the positive reals**: between any
`0 ≤ a < b` there is a radius some power of which is a norm.  (Take `‖t‖^q` for `1 < ‖t‖` and
a suitable rational `q`.)  This is what supplies the intermediate radii of
`card_roots_lt_slope` over a discretely valued `K`. -/
theorem exists_memDivisibleValueGroup_between {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ c : ℝ, MemDivisibleValueGroup K c ∧ a < c ∧ c < b := by
  obtain ⟨t, ht⟩ := NormedField.exists_one_lt_norm K
  have ht0 : (0 : ℝ) < ‖t‖ := lt_trans one_pos ht
  have hb0 : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  set a' : ℝ := max a (b / 2) with ha'
  have ha'0 : 0 < a' := lt_of_lt_of_le (half_pos hb0) (le_max_right _ _)
  have ha'b : a' < b := max_lt hab (half_lt_self hb0)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Real.logb_lt_logb ht ha'0 ha'b)
  refine ⟨‖t‖ ^ (q : ℝ), ?_, ?_, ?_⟩
  · rw [memDivisibleValueGroup_iff_exists_log (Real.rpow_pos_of_pos ht0 _)]
    refine ⟨q.den, q.den_pos.ne', t ^ q.num,
      zpow_ne_zero _ (norm_pos_iff.mp ht0), ?_⟩
    rw [norm_zpow, Real.log_zpow, Real.log_rpow ht0, nsmul_eq_mul, Rat.cast_def]
    have hden : ((q.den : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_pos.ne'
    field_simp
  · have h1 := (Real.rpow_lt_rpow_left_iff ht).mpr hq1
    rw [Real.rpow_logb ht0 (ne_of_gt ht) ha'0] at h1
    exact lt_of_le_of_lt (le_max_left _ _) h1
  · have h2 := (Real.rpow_lt_rpow_left_iff ht).mpr hq2
    rwa [Real.rpow_logb ht0 (ne_of_gt ht) hb0] at h2

/-- **Weierstrass preparation at radius `c`, unbundled into coefficient norms.**  An
`s`-distinguished polynomial factors as `f = e·ω` with `ω` monic of degree `s` whose Gauss
terms are all at most `cˢ`, and `e` with strictly dominant constant coefficient.

This threads `weierstrassPreparation_polynomial_divisible` and
`dominant_const_of_isUnit_toRestricted` from `PhD/WeierstrassPrep/WPrep_gen.lean` — see that
file for the proof strategy (rescaling for value-group radii; spectral extension and descent
for the divisible closure; see also its module docstring for why `[CompleteSpace K]` is
genuinely necessary).  The translation here is pure bookkeeping: over a field the unit
condition of `distinguishedGen` is nonvanishing, and unit-ness in the `c`-restricted ring is
the dominant-constant-coefficient condition. -/
private theorem exists_factor_aux [CompleteSpace K] (f : Polynomial K) {c : ℝ} (hc : 0 < c)
    (hcval : MemDivisibleValueGroup K c) {s : ℕ}
    (hcs : f.coeff s ≠ 0)
    (hle : ∀ k, ‖f.coeff k‖ * c ^ k ≤ ‖f.coeff s‖ * c ^ s)
    (hlt : ∀ t, s < t → ‖f.coeff t‖ * c ^ t < ‖f.coeff s‖ * c ^ s) :
    ∃ ω e : Polynomial K,
      f = e * ω ∧ ω.natDegree = s ∧ ω.Monic ∧
      (∀ k, ‖ω.coeff k‖ * c ^ k ≤ c ^ s) ∧
      ∀ k, 1 ≤ k → ‖e.coeff k‖ * c ^ k < ‖e.coeff 0‖ := by
  haveI : StrongPos (fun _ : Unit ↦ c) := ⟨fun _ => hc⟩
  have hcoe : ∀ v : ℕ, PowerSeries.coeff v (Polynomial.toRestricted c f).1 = f.coeff v :=
    fun v => Polynomial.coeff_coe f v
  have hdist : distinguishedGen norm c (Polynomial.toRestricted c f).1 s := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hcoe]
      exact isUnit_iff_ne_zero.mpr hcs
    · rw [hcoe]
      refine le_antisymm ?_ ?_
      · rw [PowerSeries.gaussNorm_eq]
        refine ciSup_le fun k => ?_
        rw [hcoe]
        exact hle k
      · have h := PowerSeries.le_gaussNorm norm c (Polynomial.toRestricted c f).1
          (Restricted.hasGaussNorm c (Polynomial.toRestricted c f)) s
        rwa [hcoe] at h
    · intro t ht
      rw [hcoe, hcoe]
      exact hlt t ht
  obtain ⟨ω, ⟨e, ⟨ωm, ωd, ωn, he, hgeq⟩, -⟩, -⟩ :=
    weierstrassPreparation_polynomial_divisible hcval f s hdist
  have hnat : ω.natDegree = s := Polynomial.natDegree_eq_of_degree_eq_some ωd
  refine ⟨ω, e, ?_, hnat, ωm, ?_, dominant_const_of_isUnit_toRestricted hcval he⟩
  · rw [← Polynomial.toRestricted_mul] at hgeq
    exact Polynomial.coe_inj.mp (congrArg Subtype.val hgeq)
  · intro k
    have h := PowerSeries.le_gaussNorm norm c (Polynomial.toRestricted c ω).1
      (Restricted.hasGaussNorm c (Polynomial.toRestricted c ω)) k
    rwa [show PowerSeries.coeff k (Polynomial.toRestricted c ω).1 = ω.coeff k from
      Polynomial.coeff_coe ω k, ← Restricted.norm_eq, ωn] at h

/-- **Blueprint Theorem 5.7, valuation-free core.**  With the first break at `(i, mi)` and
`a₀ = 1`, `f = g · h` where `g` has degree `i` and is pure of slope `m`, and the constant
coefficient of `h` strictly dominates at `c = exp m` (whence `h` has no zeros in any closed ball
of radius `exp m`, in any valued extension — see `exists_factorisation_of_firstBreak`). -/
theorem exists_factorisation_of_firstBreak' [CompleteSpace K] (f : Polynomial K)
    (hf0 : f.coeff 0 = 1)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak K (f : PowerSeries K) i j₁ i m) :
    ∃ g h : Polynomial K,
      f = g * h ∧ g.natDegree = i ∧ IsPureSeries K (g : PowerSeries K) m ∧
      (∀ k, ‖g.coeff k‖ * Real.exp m ^ k ≤ ‖g.coeff 0‖) ∧
      ‖g.coeff g.natDegree‖ * Real.exp m ^ g.natDegree = ‖g.coeff 0‖ ∧
      ∀ k, 1 ≤ k → ‖h.coeff k‖ * Real.exp m ^ k < ‖h.coeff 0‖ := by
  obtain ⟨hall, hti, hbeyond⟩ := distinguished_of_firstBreak K f hf0 hbreak
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe]; exact hf0
  have hv : nextStep (coeffVal K (f : PowerSeries K)) 0 0 = .nextVertex i j₁ i m :=
    Option.some_inj.mp ((newtonPolygon_zero_eq K _ hf0').symm.trans hbreak)
  have hipos : 0 < i := nextVertex_lt _ hv
  have hci : f.coeff i ≠ 0 := (nextVertex_coe_data K f hv).1
  have hle : ∀ k, ‖f.coeff k‖ * Real.exp m ^ k ≤ ‖f.coeff i‖ * Real.exp m ^ i := by
    intro k; rw [hti]; exact hall k
  have hlt : ∀ t, i < t → ‖f.coeff t‖ * Real.exp m ^ t < ‖f.coeff i‖ * Real.exp m ^ i := by
    intro t ht; rw [hti]; exact hbeyond t ht
  have hval : MemDivisibleValueGroup K (Real.exp m) :=
    memDivisibleValueGroup_exp_slope K f hf0 hbreak
  obtain ⟨ω, e, hfeq, hωdeg, hωmonic, hωdom, hedom⟩ :=
    exists_factor_aux K f (Real.exp_pos m) hval hci hle hlt
  -- Gauss multiplicativity pins the constant coefficient of `ω`: `‖ω₀‖ = exp m ^ i`, so the
  -- factor is normalised at both ends
  haveI : StrongPos (fun _ : Unit ↦ Real.exp m) := ⟨fun _ => Real.exp_pos m⟩
  haveI : NormMulClass (PowerSeries.Restricted K (Real.exp m)) :=
    MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ Real.exp m)
  have hωs1 : ω.coeff i = 1 := by rw [← hωdeg]; exact hωmonic.coeff_natDegree
  have hcoeF : ∀ v : ℕ, PowerSeries.coeff v (Polynomial.toRestricted (Real.exp m) f).1
      = f.coeff v := fun v => Polynomial.coeff_coe f v
  have hnF : ‖Polynomial.toRestricted (Real.exp m) f‖ = 1 := by
    refine le_antisymm ?_ ?_
    · rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
      refine ciSup_le fun k => ?_
      rw [hcoeF]
      exact hall k
    · have h := PowerSeries.le_gaussNorm norm (Real.exp m)
        (Polynomial.toRestricted (Real.exp m) f).1
        (Restricted.hasGaussNorm (Real.exp m) (Polynomial.toRestricted (Real.exp m) f)) 0
      rw [hcoeF, hf0, norm_one, pow_zero, mul_one, ← Restricted.norm_eq] at h
      exact h
  have hcoeE : ∀ v : ℕ, PowerSeries.coeff v (Polynomial.toRestricted (Real.exp m) e).1
      = e.coeff v := fun v => Polynomial.coeff_coe e v
  have hnE : ‖Polynomial.toRestricted (Real.exp m) e‖ = ‖e.coeff 0‖ := by
    refine le_antisymm ?_ ?_
    · rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
      refine ciSup_le fun k => ?_
      rw [hcoeE]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [pow_zero, mul_one]
      · exact (hedom k hk).le
    · have h := PowerSeries.le_gaussNorm norm (Real.exp m)
        (Polynomial.toRestricted (Real.exp m) e).1
        (Restricted.hasGaussNorm (Real.exp m) (Polynomial.toRestricted (Real.exp m) e)) 0
      rw [hcoeE, pow_zero, mul_one, ← Restricted.norm_eq] at h
      exact h
  have hcoeW : ∀ v : ℕ, PowerSeries.coeff v (Polynomial.toRestricted (Real.exp m) ω).1
      = ω.coeff v := fun v => Polynomial.coeff_coe ω v
  have hnW : ‖Polynomial.toRestricted (Real.exp m) ω‖ = Real.exp m ^ i := by
    refine le_antisymm ?_ ?_
    · rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
      refine ciSup_le fun k => ?_
      rw [hcoeW]
      exact hωdom k
    · have h := PowerSeries.le_gaussNorm norm (Real.exp m)
        (Polynomial.toRestricted (Real.exp m) ω).1
        (Restricted.hasGaussNorm (Real.exp m) (Polynomial.toRestricted (Real.exp m) ω)) i
      rw [hcoeW, hωs1, norm_one, one_mul, ← Restricted.norm_eq] at h
      exact h
  have h1 : (1 : ℝ) = ‖e.coeff 0‖ * Real.exp m ^ i := by
    rw [← hnF, hfeq, Polynomial.toRestricted_mul, norm_mul, hnE, hnW]
  have hω0norm : ‖ω.coeff 0‖ = Real.exp m ^ i := by
    have hf00 : e.coeff 0 * ω.coeff 0 = 1 := by
      have h2 := Polynomial.mul_coeff_zero e ω
      rw [← hfeq, hf0] at h2
      exact h2.symm
    have h2 : ‖e.coeff 0‖ * ‖ω.coeff 0‖ = 1 := by rw [← norm_mul, hf00, norm_one]
    have he0 : ‖e.coeff 0‖ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h2
      exact zero_ne_one h2
    apply mul_left_cancel₀ he0
    rw [h2, ← h1]
  have hω0 : ω.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hω0norm
    exact (pow_pos (Real.exp_pos m) i).ne' hω0norm.symm
  have hωle : ∀ k, ‖ω.coeff k‖ * Real.exp m ^ k ≤ ‖ω.coeff 0‖ := fun k => by
    rw [hω0norm]
    exact hωdom k
  have hωtop : ‖ω.coeff i‖ * Real.exp m ^ i = ‖ω.coeff 0‖ := by
    rw [hωs1, norm_one, one_mul, hω0norm]
  exact ⟨ω, e, by rw [hfeq, mul_comm], hωdeg,
    isPureSeries_of_bounds K ω hω0 (by rw [hωdeg]; exact hipos) m hωle
      (by rw [hωdeg]; exact hωtop),
    hωle, by rw [hωdeg]; exact hωtop, hedom⟩

/-- **Blueprint Theorem 5.7.**  With the first break at `(i, mi)` and `a₀ = 1` (the blueprint's
standing normalisation, added to the original statement as in 5.8 – 5.10), `f = g · h` with `g`
pure of slope `m` of degree `i`, and `h` without zeros in the closed ball of radius
`c = exp m` of the algebraic closure. -/
theorem exists_factorisation_of_firstBreak [CompleteSpace K] (f : Polynomial K)
    (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak K (f : PowerSeries K) i j₁ i m)
    (c : ℝ) (hc : c = Real.exp m) :
    ∃ g h : Polynomial K,
      f = g * h ∧
      g.natDegree = i ∧
      IsPureSeries K (g : PowerSeries K) m ∧
      (∀ x : AlgebraicClosure K, (w x : ℝ) ≤ c → Polynomial.aeval x h ≠ 0) := by
  subst hc
  obtain ⟨g, h, hfeq, hdeg, hpure, -, -, hdom⟩ :=
    exists_factorisation_of_firstBreak' K f hf0 hbreak
  exact ⟨g, h, hfeq, hdeg, hpure, fun x hx =>
    aeval_ne_zero_of_dominant_const K w hw h hdom hx⟩

/-- **Blueprint Proposition 5.5.**  Irreducible polynomials (with the standing normalisation
`a₀ = 1`, without which the statement fails — `f = X` is irreducible with slope-free polygon)
are pure of some slope.  If the first vertex is interior, 5.7 produces a proper factorisation
contradicting irreducibility; so the first segment reaches the top degree and the polygon is
that single segment. -/
theorem isPureSeries_of_irreducible [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (hf : Irreducible f) :
    ∃ m : ℝ, IsPureSeries K (f : PowerSeries K) m := by
  have hf_ne : f ≠ 0 := fun h => one_ne_zero (by rw [← hf0, h, Polynomial.coeff_zero])
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe]; exact hf0
  have hn : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h
    · exfalso
      apply hf.not_isUnit
      have hC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      rw [hC, hf0, map_one]
      exact isUnit_one
    · exact h
  have hlead : f.coeff f.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf_ne
  obtain ⟨j₀, j₁, l, m, hv⟩ := exists_nextStep_coe_eq_nextVertex K f (0 : ℝ) hn hlead
  have hl : l = j₀ := by
    have := nextVertex_l_eq _ hv
    omega
  rw [hl] at hv
  have hbreak : HasFirstBreak K (f : PowerSeries K) j₀ j₁ j₀ m := by
    show newtonPolygon _ 0 = _
    rw [newtonPolygon_zero_eq K _ hf0', hv]
  obtain ⟨hcj₀, hj₀le, -⟩ := nextVertex_coe_data K f hv
  rcases eq_or_lt_of_le hj₀le with heq | hlt
  · -- the single segment reaches the top degree: pure
    refine ⟨m, ?_, ?_⟩
    · show slopes' (newtonPolygon (coeffVal K (f : PowerSeries K)) 0) = _
      rw [newtonPolygon_zero_eq K _ hf0', hv]
      rfl
    · show slopes' (newtonPolygon (coeffVal K (f : PowerSeries K)) 1) = _
      have h0eq : newtonPolygon (coeffVal K (f : PowerSeries K)) 0
          = some (Step.nextVertex j₀ j₁ j₀ m) := by
        rw [newtonPolygon_zero_eq K _ hf0', hv]
      rw [newtonPolygon_one_eq h0eq,
        nextStep_coe_eq_tail K f j₁ fun k hk =>
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      rfl
  · -- an interior break: a proper factorisation, contradicting irreducibility
    exfalso
    obtain ⟨g, h, hfeq, hdeg, -, -, -, -⟩ :=
      exists_factorisation_of_firstBreak' K f hf0 hbreak
    have hg_ne : g ≠ 0 := fun hg => hf_ne (by rw [hfeq, hg, zero_mul])
    have hh_ne : h ≠ 0 := fun hh => hf_ne (by rw [hfeq, hh, mul_zero])
    have hdegs := Polynomial.natDegree_mul hg_ne hh_ne
    rw [← hfeq, hdeg] at hdegs
    rcases hf.isUnit_or_isUnit hfeq with hu | hu
    · exact Polynomial.not_isUnit_of_natDegree_pos g
        (by rw [hdeg]; exact nextVertex_lt _ hv) hu
    · exact Polynomial.not_isUnit_of_natDegree_pos h (by omega) hu

/-!
## 5.8  Gauss-norm bound below the first slope

With the first break at `(i, mi)` and `a₀ = 1` (the blueprint normalisation `f = 1 + a₁x + …`),
for any positive `c` strictly below `exp m` the Gauss norm is `1` and `f` differs from `1` by
something of Gauss norm `< 1`.  **Proved in full.** -/

/-- **Per-coefficient bound below the first slope.**  With the first break at `(i, mi)` and
`a₀ = 1`, for `0 < c < exp m` every coefficient with `k ≥ 1` satisfies
`‖aₖ‖ c^k ≤ exp (log c - m)` — a *uniform* bound `< 1`.  The analytic core of 5.8, extracted so
that 5.9 can reuse it term by term. -/
theorem coeff_mul_pow_le_of_lt_firstBreak (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak K f i j₁ i m)
    {c : ℝ} (hc0 : 0 < c) (hc : c < Real.exp m) {k : ℕ} (hk : 1 ≤ k) :
    ‖PowerSeries.coeff k f‖ * c ^ k ≤ Real.exp (Real.log c - m) := by
  have hbreak' : nextStep (coeffVal K f) 0 0 = .nextVertex i j₁ i m :=
    Option.some_inj.mp ((newtonPolygon_zero_eq K f hf0).symm.trans hbreak)
  have hL2 : Real.log c < m := (Real.log_lt_iff_lt_exp hc0).mpr hc
  by_cases hak : PowerSeries.coeff k f = 0
  · simp only [hak, norm_zero, zero_mul]
    exact le_of_lt (Real.exp_pos _)
  · have hck : c ^ k = Real.exp ((k : ℝ) * Real.log c) := by
      rw [Real.exp_nat_mul, Real.exp_log hc0]
    have hprod : ‖PowerSeries.coeff k f‖ * c ^ k
        = Real.exp (Real.log ‖PowerSeries.coeff k f‖ + (k : ℝ) * Real.log c) := by
      rw [Real.exp_add, ← hck, Real.exp_log (norm_pos_iff.mpr hak)]
    rw [hprod, Real.exp_le_exp]
    have hL1 := firstBreak_slope_le K f hbreak' hk hak
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [hL1, hL2, hk1]

theorem gaussNorm_eq_one_of_lt_firstBreak (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak K f i j₁ i m)
    (c : ℝ) (hc0 : 0 < c) (hc : c < Real.exp m) :
    PowerSeries.gaussNorm norm c f = 1 ∧ PowerSeries.gaussNorm norm c (f - 1) < 1 := by
  set B : ℝ := Real.exp (Real.log c - m) with hB
  have hL2 : Real.log c < m := (Real.log_lt_iff_lt_exp hc0).mpr hc
  have hBlt : B < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hBpos : 0 < B := Real.exp_pos _
  -- per-coefficient bound for `k ≥ 1`
  have term_le_B : ∀ k, 1 ≤ k → ‖PowerSeries.coeff k f‖ * c ^ k ≤ B := fun k hk =>
    coeff_mul_pow_le_of_lt_firstBreak K f hf0 hbreak hc0 hc hk
  -- `gaussNorm f = 1`
  have hsup1 : PowerSeries.gaussNorm norm c f = 1 := by
    rw [PowerSeries.gaussNorm_eq]
    have term_le_one : ∀ k, ‖PowerSeries.coeff k f‖ * c ^ k ≤ 1 := by
      intro k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp [hf0]
      · exact le_trans (term_le_B k hk) (le_of_lt hBlt)
    have hbdd : BddAbove (Set.range fun k => ‖PowerSeries.coeff k f‖ * c ^ k) :=
      ⟨1, by rintro _ ⟨k, rfl⟩; exact term_le_one k⟩
    refine le_antisymm (ciSup_le term_le_one) ?_
    have h0 : ‖PowerSeries.coeff 0 f‖ * c ^ 0 = 1 := by simp [hf0]
    calc (1 : ℝ) = ‖PowerSeries.coeff 0 f‖ * c ^ 0 := h0.symm
      _ ≤ _ := le_ciSup hbdd 0
  -- `gaussNorm (f - 1) < 1`
  have hsup2 : PowerSeries.gaussNorm norm c (f - 1) < 1 := by
    rw [PowerSeries.gaussNorm_eq]
    have term_le : ∀ k, ‖PowerSeries.coeff k (f - 1)‖ * c ^ k ≤ B := by
      intro k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have : PowerSeries.coeff 0 (f - 1) = 0 := by
          rw [_root_.map_sub, hf0, PowerSeries.coeff_one]
          simp
        simp only [this, norm_zero, zero_mul]
        exact le_of_lt hBpos
      · have hcoe : PowerSeries.coeff k (f - 1) = PowerSeries.coeff k f := by
          rw [_root_.map_sub, PowerSeries.coeff_one]
          simp [hk.ne']
        rw [hcoe]
        exact term_le_B k hk
    calc (⨆ k, ‖PowerSeries.coeff k (f - 1)‖ * c ^ k) ≤ B := ciSup_le term_le
      _ < 1 := hBlt
  exact ⟨hsup1, hsup2⟩

/-!
## 5.9  No zeros below the first slope

With the first break at `(i, mi)` and `a₀ = 1`, `f` has no zeros in the closed ball of radius
`c`, for any positive `c` strictly below `exp m`.  Zeros are measured in an arbitrary field
extension `L/K` carrying a valuation `w` extending the norm (the blueprint's `ℂ_p`; taking
`L = AlgebraicClosure K` recovers the setting of 5.7).  **Proved in full**: each term of
`f(x) - 1` is bounded by the per-coefficient bound of 5.8, so `w (f(x) - 1) < 1` by the
ultrametric inequality and hence `f(x) ≠ 0`. -/
theorem aeval_ne_zero_of_lt_firstBreak {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak K (f : PowerSeries K) i j₁ i m)
    {c : ℝ} (hc0 : 0 < c) (hc : c < Real.exp m)
    {x : L} (hx : (w x : ℝ) ≤ c) :
    Polynomial.aeval x f ≠ 0 := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe]
    exact hf0
  have hBlt : Real.exp (Real.log c - m) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith [(Real.log_lt_iff_lt_exp hc0).mpr hc])
  -- `w (f(x) - 1) < 1`: every term of `f - 1` has valuation `< 1` on the closed ball
  have hsub : w (Polynomial.aeval x f - 1) < 1 := by
    have h1 : Polynomial.aeval x f - 1 = Polynomial.aeval x (f - 1) := by
      rw [_root_.map_sub, _root_.map_one]
    rw [h1, Polynomial.aeval_eq_sum_range]
    refine w.map_sum_lt one_ne_zero fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h00 : (f - 1).coeff 0 = 0 := by simp [hf0]
      simp [h00]
    · have hco : (f - 1).coeff k = f.coeff k := by
        simp [Polynomial.coeff_one, hk.ne']
      rw [hco, Algebra.smul_def, w.map_mul, w.map_pow, hw, ← NNReal.coe_lt_coe]
      push_cast
      have hterm : ‖f.coeff k‖ * c ^ k ≤ Real.exp (Real.log c - m) := by
        have h := coeff_mul_pow_le_of_lt_firstBreak K (f : PowerSeries K) hf0' hbreak hc0 hc hk
        rwa [Polynomial.coeff_coe] at h
      calc ‖f.coeff k‖ * (w x : ℝ) ^ k
          ≤ ‖f.coeff k‖ * c ^ k := by gcongr
        _ ≤ Real.exp (Real.log c - m) := hterm
        _ < 1 := hBlt
  intro h0
  rw [h0, zero_sub, w.map_neg, w.map_one] at hsub
  exact lt_irrefl _ hsub

/-!
## 5.10  Root counting at the first slope

Two halves, both proved.  **First half:** `f` has no roots of absolute value `< exp m` — an
immediate corollary of 5.9, since any such root lies in a closed ball of radius `c < exp m`
(at `x = 0` use `f(0) = a₀ = 1`).  **Second half:** `f` has *exactly* `i` roots of absolute
value `exp m` (with multiplicity, in the algebraic closure) — via the factorisation 5.7 and the
product-of-root-norms argument, using the imported Weierstrass preparation (whence
`[CompleteSpace K]`, as in 5.5 and 5.7). -/

/-- **Blueprint Proposition 5.10, first half.**  No roots of absolute value strictly below
`exp m`. -/
theorem aeval_ne_zero_of_norm_lt_firstBreak {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak K (f : PowerSeries K) i j₁ i m)
    {x : L} (hx : (w x : ℝ) < Real.exp m) :
    Polynomial.aeval x f ≠ 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, hf0]
  · have hc0 : (0 : ℝ) < (w x : ℝ) := by
      exact_mod_cast pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hx0)
    exact aeval_ne_zero_of_lt_firstBreak K w hw f hf0 hbreak hc0 hx le_rfl

open Classical in
/-- **Blueprint Proposition 5.10, second half.**  `f` has exactly `i` roots of absolute value
`exp m`, counted with multiplicity in the algebraic closure.

Following the blueprint: `f = g · h` with `g` pure of degree `i` (5.7); the roots of `h` all lie
strictly outside the closed ball (`aeval_ne_zero_of_dominant_const`); the roots of `g` lie on
the sphere — none inside (`aeval_ne_zero_of_dominant_lt`), and since the product of their
absolute values is `‖g₀/g_i‖ = (exp m)^i` while each is `≥ exp m`, all equal `exp m`
(`eq_of_prod_eq_pow_card`). -/
theorem card_roots_firstBreak [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {i : ℕ} {j₁ : ℝ} {m : ℝ} (hbreak : HasFirstBreak K (f : PowerSeries K) i j₁ i m) :
    (Multiset.filter (fun x => (w x : ℝ) = Real.exp m)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = i := by
  obtain ⟨g, h, hfeq, hdeg, -, hgle, hgtop, hdom⟩ :=
    exists_factorisation_of_firstBreak' K f hf0 hbreak
  have hf_ne : f ≠ 0 := fun h0 => one_ne_zero (by rw [← hf0, h0, Polynomial.coeff_zero])
  have hg_ne : g ≠ 0 := fun h0 => hf_ne (by rw [hfeq, h0, zero_mul])
  have hh_ne : h ≠ 0 := fun h0 => hf_ne (by rw [hfeq, h0, mul_zero])
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h0
    have h1 : (g * h).coeff 0 = g.coeff 0 * h.coeff 0 := Polynomial.mul_coeff_zero g h
    rw [← hfeq, hf0, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hφinj : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
    (algebraMap K (AlgebraicClosure K)).injective
  have hgmap_ne : g.map (algebraMap K (AlgebraicClosure K)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hφinj).mpr hg_ne
  have hhmap_ne : h.map (algebraMap K (AlgebraicClosure K)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hφinj).mpr hh_ne
  have hroots : (f.map (algebraMap K (AlgebraicClosure K))).roots
      = (g.map (algebraMap K (AlgebraicClosure K))).roots
        + (h.map (algebraMap K (AlgebraicClosure K))).roots := by
    rw [hfeq, Polynomial.map_mul, Polynomial.roots_mul (mul_ne_zero hgmap_ne hhmap_ne)]
  -- the roots of `h` lie strictly outside the closed ball of radius `exp m`
  have hh0 : Multiset.filter (fun x => (w x : ℝ) = Real.exp m)
      (h.map (algebraMap K (AlgebraicClosure K))).roots = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx hxc
    have hx0 : Polynomial.aeval x h = 0 := by
      have hroot := (Polynomial.mem_roots hhmap_ne).mp hx
      have h2 : Polynomial.eval x (h.map (algebraMap K (AlgebraicClosure K))) = 0 := hroot
      rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h2
    exact aeval_ne_zero_of_dominant_const K w hw h hdom (le_of_eq hxc) hx0
  -- no root of `g` lies strictly inside the ball …
  have hlow : ∀ x ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots,
      Real.exp m ≤ (w x : ℝ) := by
    intro x hx
    by_contra hlt
    rw [not_le] at hlt
    have hx0 : Polynomial.aeval x g = 0 := by
      have hroot := (Polynomial.mem_roots hgmap_ne).mp hx
      have h2 : Polynomial.eval x (g.map (algebraMap K (AlgebraicClosure K))) = 0 := hroot
      rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h2
    exact aeval_ne_zero_of_dominant_lt K w hw g hg0 (fun k _ => hgle k) hlt hx0
  -- … and the product of the root norms is `(exp m) ^ deg g`, so all lie on the sphere
  have hsplits : (g.map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hcards : Multiset.card (g.map (algebraMap K (AlgebraicClosure K))).roots
      = g.natDegree := by
    rw [← Polynomial.natDegree_map (algebraMap K (AlgebraicClosure K)) (p := g)]
    exact hsplits.natDegree_eq_card_roots.symm
  have hlead_ne : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg_ne
  have hwid : ‖g.coeff 0‖₊
      = ‖g.leadingCoeff‖₊
        * ((g.map (algebraMap K (AlgebraicClosure K))).roots.map w).prod := by
    have hcoeff0 := hsplits.coeff_zero_eq_leadingCoeff_mul_prod_roots
    calc ‖g.coeff 0‖₊
        = w ((g.map (algebraMap K (AlgebraicClosure K))).coeff 0) := by
          rw [Polynomial.coeff_map, hw]
      _ = w ((-1) ^ (g.map (algebraMap K (AlgebraicClosure K))).natDegree)
          * w ((g.map (algebraMap K (AlgebraicClosure K))).leadingCoeff)
          * w ((g.map (algebraMap K (AlgebraicClosure K))).roots.prod) := by
          rw [hcoeff0, w.map_mul, w.map_mul]
      _ = ‖g.leadingCoeff‖₊
          * ((g.map (algebraMap K (AlgebraicClosure K))).roots.map w).prod := by
          rw [w.map_pow, w.map_neg, w.map_one, one_pow, one_mul,
            Polynomial.leadingCoeff_map, hw, map_multiset_prod]
  have hexp0 : (0 : ℝ) ≤ Real.exp m := (Real.exp_pos m).le
  have hgtopn : ‖g.leadingCoeff‖₊ * Real.toNNReal (Real.exp m) ^ g.natDegree
      = ‖g.coeff 0‖₊ := by
    rw [← NNReal.coe_inj]
    push_cast
    rw [Real.coe_toNNReal _ hexp0]
    exact hgtop
  have hlcn : ‖g.leadingCoeff‖₊ ≠ 0 := by simpa using hlead_ne
  have hprodn : ((g.map (algebraMap K (AlgebraicClosure K))).roots.map w).prod
      = Real.toNNReal (Real.exp m)
        ^ Multiset.card ((g.map (algebraMap K (AlgebraicClosure K))).roots.map w) := by
    have h2 : ‖g.leadingCoeff‖₊
        * ((g.map (algebraMap K (AlgebraicClosure K))).roots.map w).prod
        = ‖g.leadingCoeff‖₊ * Real.toNNReal (Real.exp m) ^ g.natDegree := by
      rw [← hwid, ← hgtopn]
    have h3 := mul_left_cancel₀ hlcn h2
    rw [h3, Multiset.card_map, hcards]
  have hall_roots : ∀ x ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots,
      (w x : ℝ) = Real.exp m := by
    intro x hx
    have hcn_pos : 0 < Real.toNNReal (Real.exp m) := by
      rw [Real.toNNReal_pos]
      exact Real.exp_pos m
    have hge : ∀ y ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots.map w,
        Real.toNNReal (Real.exp m) ≤ y := by
      intro y hy
      obtain ⟨x', hx', rfl⟩ := Multiset.mem_map.mp hy
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hexp0]
      exact hlow x' hx'
    have hxeq := eq_of_prod_eq_pow_card hcn_pos hge hprodn (Multiset.mem_map_of_mem w hx)
    rw [← Real.coe_toNNReal (Real.exp m) hexp0, ← hxeq]
  rw [hroots, Multiset.filter_add, Multiset.card_add, hh0, Multiset.card_zero, add_zero,
    Multiset.filter_eq_self.mpr hall_roots, hcards, hdeg]

/-!
## 5.11  Root counting along the whole polygon

Blueprint 5.11: if `m₁ < ⋯ < m_r` are the slopes of the Newton polygon of `f` with projected
lengths `i₁, …, i_r`, then for each `k` the polynomial `f` has exactly `i_k` roots of absolute
value `exp m_k` (with multiplicity, in the algebraic closure).  We phrase the hypothesis on the
raw algorithm output, as with `HasFirstBreak`: "the `k`-th segment has slope `m` and projected
length `l`" is `newtonPolygon … k = some (.nextVertex j₀ j₁ l m)`.  For a *polynomial* every
segment of the polygon is a `nextVertex` (the point set is finite), so this covers all slopes;
at `k = 0` with the normalisation `a₀ = 1` it specialises to 5.10.

Proved in full (via the imported Weierstrass preparation, so under `[CompleteSpace K]` like
5.5 – 5.10), but **not** by the blueprint's induction over segments: instead the two counts

* `#{roots with w ≤ exp m} = j₀`  (`card_roots_le_slope`), and
* `#{roots with w < exp m} = i₀`  (`card_roots_lt_slope`, `i₀ = j₀ - l` the segment's start)

are computed directly, and their difference is the sphere count `l`.  Each count comes from one
application of Weierstrass preparation, at radius `exp m` for the first and at a radius `c'`
strictly between `exp m_{k-1}` and `exp m` (chosen above the norms of the finitely many smaller
roots) for the second: at such radii `f` is distinguished at the vertex `(j₀, ·)` resp.
`(i₀, ·)`, by convexity of the polygon.  The convexity inputs are `step_slope_le` (forwards) and
`vertex_line_le` (backwards along the polygon, by induction on the segment index). -/

omit [IsUltrametricDist K] in
/-- Two-position comparison of Gauss-norm terms at radius `c`:
`‖a‖ cᵗ ≤ ‖b‖ cˢ` iff `(t, ν(a))` lies on/above the line of slope `log c` through `(s, ν(b))`. -/
private lemma term_le_term_iff' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {c : ℝ} (hc : 0 < c)
    (t s : ℕ) :
    ‖a‖ * c ^ t ≤ ‖b‖ * c ^ s ↔
      Real.log c * ((t : ℝ) - s) ≤ - Real.log ‖a‖ - - Real.log ‖b‖ := by
  rw [show c = Real.exp (Real.log c) from (Real.exp_log hc).symm,
    term_eq_exp K ha _ t, term_eq_exp K hb _ s, Real.exp_le_exp, Real.log_exp]
  have hexp : Real.log c * ((t : ℝ) - s) = Real.log c * t - Real.log c * s := by ring
  constructor <;> intro h <;> linarith [hexp]

omit [IsUltrametricDist K] in
private lemma term_lt_term_iff' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {c : ℝ} (hc : 0 < c)
    (t s : ℕ) :
    ‖a‖ * c ^ t < ‖b‖ * c ^ s ↔
      Real.log c * ((t : ℝ) - s) < - Real.log ‖a‖ - - Real.log ‖b‖ := by
  rw [show c = Real.exp (Real.log c) from (Real.exp_log hc).symm,
    term_eq_exp K ha _ t, term_eq_exp K hb _ s, Real.exp_lt_exp, Real.log_exp]
  have hexp : Real.log c * ((t : ℝ) - s) = Real.log c * t - Real.log c * s := by ring
  constructor <;> intro h <;> linarith [hexp]

/-- **Backwards convexity of the polygon.**  Every finite point of the polygon — before *or*
after — lies on/above the line through the `a`-th vertex `(j₀, j₁)` with the `a`-th slope `m`.
Backwards this is by induction along the segments: the earlier segments have smaller slopes, so
walking back from the vertex the points rise relative to the `m`-line. -/
theorem vertex_line_le (f : Polynomial K) (hf0 : f.coeff 0 = 1) :
    ∀ (a : ℕ) {j₀ l : ℕ} {j₁ m : ℝ},
      newtonPolygon (coeffVal K (f : PowerSeries K)) a = some (.nextVertex j₀ j₁ l m) →
      ∀ t, f.coeff t ≠ 0 →
        m * ((t : ℝ) - (j₀ : ℝ)) ≤ - Real.log ‖f.coeff t‖ - j₁ := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe]; exact hf0
  intro a
  induction a with
  | zero =>
      intro j₀ l j₁ m hseg t ht
      have hv : nextStep (coeffVal K (f : PowerSeries K)) 0 0 = .nextVertex j₀ j₁ l m :=
        Option.some_inj.mp ((newtonPolygon_zero_eq K _ hf0').symm.trans hseg)
      have hj₀pos : 0 < j₀ := nextVertex_lt _ hv
      have hj₀R : (0 : ℝ) < (j₀ : ℝ) := by exact_mod_cast hj₀pos
      have hslope := nextVertex_slope_eq_sInf' _ hv
      rw [slopeReal_real] at hslope
      have hj₁ : j₁ = m * j₀ := by
        rw [eq_div_iff (by push_cast; simpa using hj₀R.ne')] at hslope
        push_cast at hslope
        linarith
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · have hν0 : - Real.log ‖f.coeff 0‖ = 0 := by
          rw [hf0, norm_one, Real.log_one, neg_zero]
        rw [hν0]
        have hexp : m * (((0 : ℕ) : ℝ) - (j₀ : ℝ)) = -(m * j₀) := by
          push_cast
          ring
        linarith [hexp, hj₁]
      · have hfb := firstBreak_slope_le K (f : PowerSeries K) hv htpos
          (by rwa [Polynomial.coeff_coe])
        rw [Polynomial.coeff_coe] at hfb
        have hexp : m * ((t : ℝ) - (j₀ : ℝ)) = m * t - m * j₀ := by ring
        linarith [hexp, hj₁, hfb]
  | succ a ih =>
      intro j₀ l j₁ m hseg t ht
      obtain ⟨i₀, i₁, l', m', hprev⟩ := nextStep_nextVertex' _ hseg
      have hstep : nextStep (coeffVal K (f : PowerSeries K)) i₀ i₁ = .nextVertex j₀ j₁ l m :=
        nextStep_nextVertex'' _ hseg hprev
      have hij : i₀ < j₀ := nextVertex_lt _ hstep
      have hijR : (0 : ℝ) < (j₀ : ℝ) - i₀ := by
        rw [sub_pos]; exact_mod_cast hij
      have hslope := nextVertex_slope_eq_sInf' _ hstep
      rw [slopeReal_real] at hslope
      have hline : j₁ = i₁ + m * ((j₀ : ℝ) - i₀) := by
        rw [eq_div_iff hijR.ne'] at hslope
        linarith
      have key : m * ((t : ℝ) - i₀) ≤ - Real.log ‖f.coeff t‖ - i₁ := by
        rcases Nat.lt_or_ge i₀ t with hti | hti
        · have h1 := step_slope_le K (f : PowerSeries K) hstep hti
            (by rwa [Polynomial.coeff_coe])
          rwa [Polynomial.coeff_coe] at h1
        · have h1 := ih hprev t ht
          have hts : ((t : ℝ) - i₀) ≤ 0 := by
            rw [sub_nonpos]; exact_mod_cast hti
          obtain ⟨p₀, p₁, hprevstep⟩ := nextStep_nextVertex _ hprev
          have hmm : m' < m := slopes_increasing_nextVertex _ hprevstep hstep
          nlinarith [h1, mul_nonneg (sub_nonneg.mpr hmm.le) (neg_nonneg.mpr hts)]
      have hexp : m * ((t : ℝ) - (j₀ : ℝ)) = m * ((t : ℝ) - i₀) - m * ((j₀ : ℝ) - i₀) := by
        ring
      linarith [key, hline, hexp]

/-- Beyond the `a`-th vertex the points lie **strictly** above the `a`-th slope line (the next
slope is strictly bigger). -/
theorem vertex_line_lt (f : Polynomial K) {a j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K (f : PowerSeries K)) a = some (.nextVertex j₀ j₁ l m))
    {t : ℕ} (htj : j₀ < t) (hat : f.coeff t ≠ 0) :
    m * ((t : ℝ) - (j₀ : ℝ)) < - Real.log ‖f.coeff t‖ - j₁ := by
  obtain ⟨p₀, p₁, hst⟩ := nextStep_nextVertex _ hseg
  obtain ⟨k₀, k₁, l₂, m₂, hv₂⟩ := exists_nextStep_coe_eq_nextVertex K f j₁ htj hat
  have hmm : m < m₂ := slopes_increasing_nextVertex _ hst hv₂
  have h1 := step_slope_le K (f : PowerSeries K) hv₂ htj (by rwa [Polynomial.coeff_coe])
  rw [Polynomial.coeff_coe] at h1
  have hts : (0 : ℝ) < (t : ℝ) - j₀ := by rw [sub_pos]; exact_mod_cast htj
  nlinarith [h1, mul_pos (sub_pos.mpr hmm) hts]

omit [IsUltrametricDist K] in
/-- **A polynomial whose top term dominates at radius `c` has no zeros outside the closed ball
of radius `c`** — the mirror of `aeval_ne_zero_of_dominant_const`, used for the Weierstrass
factor `ω` (its roots are exactly the small roots). -/
theorem aeval_ne_zero_of_dominant_top {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (g : Polynomial K) {c : ℝ} (hc : 0 < c) {s : ℕ} (hdeg : g.natDegree = s)
    (hgs : g.coeff s ≠ 0)
    (hdom : ∀ t, ‖g.coeff t‖ * c ^ t ≤ ‖g.coeff s‖ * c ^ s)
    {x : L} (hx : c < (w x : ℝ)) :
    Polynomial.aeval x g ≠ 0 := by
  have hwx : (0 : ℝ) < (w x : ℝ) := lt_trans hc hx
  have hwxn : w x ≠ 0 := by
    intro h
    rw [h] at hwx
    simp at hwx
  have htop_ne : (‖g.coeff s‖₊ * w x ^ s : NNReal) ≠ 0 :=
    mul_ne_zero (by simpa using hgs) (pow_ne_zero _ hwxn)
  have hsub : w (Polynomial.aeval x g - algebraMap K L (g.coeff s) * x ^ s)
      < ‖g.coeff s‖₊ * w x ^ s := by
    have h1 : Polynomial.aeval x g - algebraMap K L (g.coeff s) * x ^ s
        = Polynomial.aeval x (g - Polynomial.monomial s (g.coeff s)) := by
      rw [_root_.map_sub, Polynomial.aeval_monomial]
    rw [h1, Polynomial.aeval_eq_sum_range]
    refine w.map_sum_lt htop_ne fun k _ => ?_
    have hcm : (g - Polynomial.monomial s (g.coeff s)).coeff k
        = if s = k then 0 else g.coeff k := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_monomial]
      split_ifs with h
      · subst h
        exact sub_self _
      · rw [sub_zero]
    rcases eq_or_ne s k with rfl | hsk
    · rw [hcm, if_pos rfl, zero_smul, w.map_zero]
      exact pos_iff_ne_zero.mpr htop_ne
    · rw [hcm, if_neg hsk]
      by_cases hgk : g.coeff k = 0
      · rw [hgk, zero_smul, w.map_zero]
        exact pos_iff_ne_zero.mpr htop_ne
      · have hks : k < s :=
          lt_of_le_of_ne (hdeg ▸ Polynomial.le_natDegree_of_ne_zero hgk) (Ne.symm hsk)
        rw [Algebra.smul_def, w.map_mul, w.map_pow, hw, ← NNReal.coe_lt_coe]
        push_cast
        refine (term_lt_term_iff' K hgk hgs hwx k s).mpr ?_
        have hd := (term_le_term_iff' K hgk hgs hc k s).mp (hdom k)
        have hlog : Real.log c < Real.log (w x : ℝ) := Real.log_lt_log hc hx
        have hks' : ((k : ℝ) - s) < 0 := by
          rw [sub_lt_zero]; exact_mod_cast hks
        nlinarith [hd, mul_neg_of_pos_of_neg (sub_pos.mpr hlog) hks']
  intro h0
  rw [h0, zero_sub, w.map_neg, w.map_mul, w.map_pow, hw] at hsub
  exact lt_irrefl _ hsub

open Classical in
/-- **The number of roots in the closed ball of radius `c` of an `s`-distinguished polynomial
is `s`.**  One application of Weierstrass preparation at radius `c`: `f = e·ω` with
`deg ω = s`; the roots of `e` lie strictly outside the ball, the roots of `ω` inside. -/
theorem card_roots_le_of_distinguished [CompleteSpace K] (f : Polynomial K)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {c : ℝ} (hc : 0 < c) (hcval : MemDivisibleValueGroup K c)
    {s : ℕ} (hcs : f.coeff s ≠ 0)
    (hle : ∀ k, ‖f.coeff k‖ * c ^ k ≤ ‖f.coeff s‖ * c ^ s)
    (hlt : ∀ t, s < t → ‖f.coeff t‖ * c ^ t < ‖f.coeff s‖ * c ^ s) :
    (Multiset.filter (fun x => (w x : ℝ) ≤ c)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = s := by
  obtain ⟨ω, e, hfeq, hωdeg, hωmonic, hωdom', hedom⟩ :=
    exists_factor_aux K f hc hcval hcs hle hlt
  have hf_ne : f ≠ 0 := fun h0 => hcs (by rw [h0, Polynomial.coeff_zero])
  have hω_ne : ω ≠ 0 := fun h0 => hf_ne (by rw [hfeq, h0, mul_zero])
  have he_ne : e ≠ 0 := fun h0 => hf_ne (by rw [hfeq, h0, zero_mul])
  have hωs : ω.coeff s ≠ 0 := by
    have hne := Polynomial.leadingCoeff_ne_zero.mpr hω_ne
    rw [← Polynomial.coeff_natDegree, hωdeg] at hne
    exact hne
  have hωdom : ∀ t, ‖ω.coeff t‖ * c ^ t ≤ ‖ω.coeff s‖ * c ^ s := by
    intro t
    rw [show ω.coeff s = 1 from by rw [← hωdeg]; exact hωmonic.coeff_natDegree, norm_one,
      one_mul]
    exact hωdom' t
  have hφinj : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
    (algebraMap K (AlgebraicClosure K)).injective
  have hωmap_ne : ω.map (algebraMap K (AlgebraicClosure K)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hφinj).mpr hω_ne
  have hemap_ne : e.map (algebraMap K (AlgebraicClosure K)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hφinj).mpr he_ne
  have hroots : (f.map (algebraMap K (AlgebraicClosure K))).roots
      = (e.map (algebraMap K (AlgebraicClosure K))).roots
        + (ω.map (algebraMap K (AlgebraicClosure K))).roots := by
    rw [hfeq, Polynomial.map_mul, Polynomial.roots_mul (mul_ne_zero hemap_ne hωmap_ne)]
  rw [hroots, Multiset.filter_add, Multiset.card_add]
  have he0 : Multiset.filter (fun x => (w x : ℝ) ≤ c)
      (e.map (algebraMap K (AlgebraicClosure K))).roots = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx hxc
    have hx0 : Polynomial.aeval x e = 0 := by
      have hroot := (Polynomial.mem_roots hemap_ne).mp hx
      have h2 : Polynomial.eval x (e.map (algebraMap K (AlgebraicClosure K))) = 0 := hroot
      rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h2
    exact aeval_ne_zero_of_dominant_const K w hw e hedom hxc hx0
  have hωall : ∀ x ∈ (ω.map (algebraMap K (AlgebraicClosure K))).roots, (w x : ℝ) ≤ c := by
    intro x hx
    by_contra hgt
    rw [not_le] at hgt
    have hx0 : Polynomial.aeval x ω = 0 := by
      have hroot := (Polynomial.mem_roots hωmap_ne).mp hx
      have h2 : Polynomial.eval x (ω.map (algebraMap K (AlgebraicClosure K))) = 0 := hroot
      rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h2
    exact aeval_ne_zero_of_dominant_top K w hw ω hc hωdeg hωs hωdom hgt hx0
  rw [he0, Multiset.card_zero, zero_add, Multiset.filter_eq_self.mpr hωall]
  have hsplits : (ω.map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  rw [← hsplits.natDegree_eq_card_roots, Polynomial.natDegree_map, hωdeg]

open Classical in
/-- **The closed-ball count at the `k`-th slope**: `f` has exactly `j₀` roots (the vertex
`x`-coordinate) of absolute value `≤ exp m`.  By polygon convexity (`vertex_line_le`,
`vertex_line_lt`), `f` is `j₀`-distinguished at radius `exp m`. -/
theorem card_roots_le_slope [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {k j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K (f : PowerSeries K)) k = some (.nextVertex j₀ j₁ l m)) :
    (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp m)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = j₀ := by
  obtain ⟨p₀, p₁, hst⟩ := nextStep_nextVertex _ hseg
  obtain ⟨hcj₀, hj₀le, hj₁val⟩ := nextVertex_coe_data K f hst
  refine card_roots_le_of_distinguished K f w hw (Real.exp_pos m)
    (memDivisibleValueGroup_exp_slope K f hf0 hseg) hcj₀ ?_ ?_
  · intro t
    by_cases hat : f.coeff t = 0
    · rw [hat, norm_zero, zero_mul]
      positivity
    · refine (term_le_term_iff' K hat hcj₀ (Real.exp_pos m) t j₀).mpr ?_
      rw [Real.log_exp]
      have h1 := vertex_line_le K f hf0 k hseg t hat
      rwa [hj₁val] at h1
  · intro t htj
    by_cases hat : f.coeff t = 0
    · rw [hat, norm_zero, zero_mul]
      exact mul_pos (norm_pos_iff.mpr hcj₀) (pow_pos (Real.exp_pos m) j₀)
    · refine (term_lt_term_iff' K hat hcj₀ (Real.exp_pos m) t j₀).mpr ?_
      rw [Real.log_exp]
      have h1 := vertex_line_lt K f hseg htj hat
      rwa [hj₁val] at h1

open Classical in
/-- **The open-ball count at the `k`-th slope**: `f` has exactly `j₀ - l` roots (the segment's
*start*) of absolute value `< exp m`.  For `k = 0` this is 5.10's first half; for `k ≥ 1`, pick
a radius `c'` strictly between `exp m_{k-1}` and `exp m` lying above the norms of the finitely
many roots below the sphere: `f` is `i₀`-distinguished at `c'` (strictly on both sides of `i₀`,
by `vertex_line_le` backwards and `step_slope_le` forwards), and the closed `c'`-ball catches
exactly the roots with `w < exp m`. -/
theorem card_roots_lt_slope [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {k j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K (f : PowerSeries K)) k = some (.nextVertex j₀ j₁ l m)) :
    (Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = j₀ - l := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe]; exact hf0
  have hf_ne : f ≠ 0 := fun h0 => one_ne_zero (by rw [← hf0, h0, Polynomial.coeff_zero])
  have hfmap_ne : f.map (algebraMap K (AlgebraicClosure K)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K (AlgebraicClosure K)).injective).mpr hf_ne
  rcases k with _ | a
  · -- first segment: no roots below the first slope (5.10, first half)
    have hv : nextStep (coeffVal K (f : PowerSeries K)) 0 0 = .nextVertex j₀ j₁ l m :=
      Option.some_inj.mp ((newtonPolygon_zero_eq K _ hf0').symm.trans hseg)
    have hl : l = j₀ := by
      have := nextVertex_l_eq _ hv
      omega
    rw [hl] at hv
    have hempty : Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
        ((f.map (algebraMap K (AlgebraicClosure K))).roots) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx hxc
      have hx0 : Polynomial.aeval x f = 0 := by
        have hroot := (Polynomial.mem_roots hfmap_ne).mp hx
        have h2 : Polynomial.eval x (f.map (algebraMap K (AlgebraicClosure K))) = 0 := hroot
        rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h2
      have hbreak : HasFirstBreak K (f : PowerSeries K) j₀ j₁ j₀ m := by
        show newtonPolygon _ 0 = _
        rw [newtonPolygon_zero_eq K _ hf0', hv]
      exact aeval_ne_zero_of_norm_lt_firstBreak K w hw f hf0 hbreak hxc hx0
    rw [hempty, Multiset.card_zero]
    omega
  · -- later segment: count the closed ball at a radius just below `exp m`
    obtain ⟨i₀, i₁, l', m', hprev⟩ := nextStep_nextVertex' _ hseg
    have hstep : nextStep (coeffVal K (f : PowerSeries K)) i₀ i₁ = .nextVertex j₀ j₁ l m :=
      nextStep_nextVertex'' _ hseg hprev
    obtain ⟨p₀, p₁, hprevstep⟩ := nextStep_nextVertex _ hprev
    have hmm : m' < m := slopes_increasing_nextVertex _ hprevstep hstep
    obtain ⟨hci₀, hi₀le, hi₁val⟩ := nextVertex_coe_data K f hprevstep
    have hi₀j₀ : i₀ < j₀ := nextVertex_lt _ hstep
    have hl : l = j₀ - i₀ := nextVertex_l_eq _ hstep
    -- choose the intermediate radius `c'`
    set F : Finset ℝ := insert (Real.exp m')
      (((f.map (algebraMap K (AlgebraicClosure K))).roots.toFinset.image
        (fun x => (w x : ℝ))).filter (fun r => r < Real.exp m)) with hF
    have hFne : F.Nonempty := ⟨Real.exp m', Finset.mem_insert_self _ _⟩
    have hFlt : ∀ r ∈ F, r < Real.exp m := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact Real.exp_lt_exp.mpr hmm
      · exact (Finset.mem_filter.mp hr).2
    obtain ⟨c', hc'div, hc'1, hc'2⟩ := exists_memDivisibleValueGroup_between K
      (le_of_lt (lt_of_lt_of_le (Real.exp_pos m')
        (Finset.le_max' F _ (Finset.mem_insert_self _ _))))
      (hFlt _ (F.max'_mem hFne))
    have hm'c' : Real.exp m' < c' :=
      lt_of_le_of_lt (Finset.le_max' F _ (Finset.mem_insert_self _ _)) hc'1
    have hc'pos : 0 < c' := lt_trans (Real.exp_pos m') hm'c'
    have hroots_le : ∀ x ∈ (f.map (algebraMap K (AlgebraicClosure K))).roots,
        (w x : ℝ) < Real.exp m → (w x : ℝ) ≤ c' := by
      intro x hx hxlt
      refine le_of_lt (lt_of_le_of_lt (Finset.le_max' F _ ?_) hc'1)
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ (Multiset.mem_toFinset.mpr hx), hxlt⟩)
    have hμm : Real.log c' < m := (Real.log_lt_iff_lt_exp hc'pos).mpr hc'2
    have hm'μ : m' < Real.log c' := by
      have h := Real.log_lt_log (Real.exp_pos m') hm'c'
      rwa [Real.log_exp] at h
    -- `f` is `i₀`-distinguished at radius `c'`, strictly away from `i₀`
    have hstrict : ∀ t, f.coeff t ≠ 0 → t ≠ i₀ →
        Real.log c' * ((t : ℝ) - i₀)
          < - Real.log ‖f.coeff t‖ - - Real.log ‖f.coeff i₀‖ := by
      intro t hat htne
      rcases Nat.lt_or_ge t i₀ with hti | hti
      · have h1 := vertex_line_le K f hf0 a hprev t hat
        rw [hi₁val] at h1
        have hts : ((t : ℝ) - i₀) < 0 := by
          rw [sub_lt_zero]; exact_mod_cast hti
        nlinarith [h1, mul_neg_of_pos_of_neg (sub_pos.mpr hm'μ) hts]
      · have hti' : i₀ < t := lt_of_le_of_ne hti (Ne.symm htne)
        have h1 := step_slope_le K (f : PowerSeries K) hstep hti'
          (by rwa [Polynomial.coeff_coe])
        rw [Polynomial.coeff_coe, hi₁val] at h1
        have hts : (0 : ℝ) < ((t : ℝ) - i₀) := by
          rw [sub_pos]; exact_mod_cast hti'
        nlinarith [h1, mul_pos (sub_pos.mpr hμm) hts]
    have hle' : ∀ t, ‖f.coeff t‖ * c' ^ t ≤ ‖f.coeff i₀‖ * c' ^ i₀ := by
      intro t
      by_cases hat : f.coeff t = 0
      · rw [hat, norm_zero, zero_mul]
        positivity
      · rcases eq_or_ne t i₀ with rfl | htne
        · exact le_refl _
        · exact le_of_lt ((term_lt_term_iff' K hat hci₀ hc'pos t i₀).mpr
            (hstrict t hat htne))
    have hlt' : ∀ t, i₀ < t → ‖f.coeff t‖ * c' ^ t < ‖f.coeff i₀‖ * c' ^ i₀ := by
      intro t ht
      by_cases hat : f.coeff t = 0
      · rw [hat, norm_zero, zero_mul]
        exact mul_pos (norm_pos_iff.mpr hci₀) (pow_pos hc'pos i₀)
      · exact (term_lt_term_iff' K hat hci₀ hc'pos t i₀).mpr (hstrict t hat ht.ne')
    have hcount := card_roots_le_of_distinguished K f w hw hc'pos hc'div hci₀ hle' hlt'
    have hfe : Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
        ((f.map (algebraMap K (AlgebraicClosure K))).roots)
        = Multiset.filter (fun x => (w x : ℝ) ≤ c')
          ((f.map (algebraMap K (AlgebraicClosure K))).roots) := by
      refine Multiset.filter_congr fun x hx => ?_
      exact ⟨fun h => hroots_le x hx h, fun h => lt_of_le_of_lt h hc'2⟩
    rw [hfe, hcount]
    omega

open Classical in
/-- **Blueprint Theorem 5.11.**  If the `k`-th segment of the Newton polygon of `f` has slope
`m` and projected length `l`, then `f` has exactly `l` roots of absolute value `exp m`, counted
with multiplicity in the algebraic closure: the closed-ball count `j₀` minus the open-ball
count `j₀ - l`. -/
theorem card_roots_slope [CompleteSpace K] (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)
    {k j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K (f : PowerSeries K)) k = some (.nextVertex j₀ j₁ l m)) :
    (Multiset.filter (fun x => (w x : ℝ) = Real.exp m)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card = l := by
  have hle_count := card_roots_le_slope K f hf0 w hw hseg
  have hlt_count := card_roots_lt_slope K f hf0 w hw hseg
  obtain ⟨p₀, p₁, hst⟩ := nextStep_nextVertex _ hseg
  have hl := nextVertex_l_eq _ hst
  have hplt := nextVertex_lt _ hst
  have hsum : (Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
        ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card
      + (Multiset.filter (fun x => (w x : ℝ) = Real.exp m)
        ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card
      = (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp m)
        ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card := by
    have h := congrArg Multiset.card
      (Multiset.filter_add_filter (fun x => (w x : ℝ) < Real.exp m)
        (fun x => (w x : ℝ) = Real.exp m)
        ((f.map (algebraMap K (AlgebraicClosure K))).roots))
    rw [Multiset.card_add, Multiset.card_add] at h
    have h1 : Multiset.filter
          (fun x => (w x : ℝ) < Real.exp m ∨ (w x : ℝ) = Real.exp m)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots)
        = Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp m)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots) :=
      Multiset.filter_congr fun x _ =>
        (le_iff_lt_or_eq (a := ((w x : ℝ))) (b := Real.exp m)).symm
    have h2 : Multiset.filter
          (fun x => (w x : ℝ) < Real.exp m ∧ (w x : ℝ) = Real.exp m)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots) = 0 :=
      Multiset.filter_eq_nil.mpr fun x _ h => absurd h.2 (ne_of_lt h.1)
    rw [h1, h2, Multiset.card_zero, add_zero] at h
    exact h
  omega

/-!
## 5.12 – 5.14  Power series: radius of convergence, Weierstrass factorisation, zeros

All proved; these are the power-series results the polynomial theory above feeds into.
Formalisation decisions, recorded here once:

* **Convergence is genuine convergence.**  `radiusOfConvergence L f` is the honest radius of
  convergence: the supremum of the norms of the points of a complete ultrametric extension
  `L/K` at which the series `∑ aₖ xᵏ` is genuinely `Summable`.  The radius is *relative to
  `L`* of necessity: over `L = ℚ_p` no point has norm strictly between consecutive powers of
  `p`, so the supremum over points of `L` can undershoot the analytic radius — the blueprint's
  radius is the one over a norm-dense extension such as `ℂ_p`, and the statements below that
  need points arbitrarily close to a prescribed radius carry a norm-density hypothesis
  `hdense`.  The correspondence with the project's restricted-ness predicate
  `PowerSeries.IsRestricted c` (from `PhD.ToPR.Restricted`, defined via the **cofinite**
  filter — `isRestricted_iff`) is proved below: a restricted series converges on the whole
  closed ball (`summable_of_isRestricted`), convergence at a point makes the series restricted
  at its norm (`isRestricted_of_summable`), and at a point of norm exactly `c` the two are
  *equivalent* (`isRestricted_iff_summable`) — restricted power series of parameter `c` are
  exactly those converging on the closed ball of radius `c`.  Hypotheses of 5.13/5.14 are
  phrased with `IsRestricted`; through this correspondence they say precisely "`f` converges
  on the closed ball".
* **5.12** ("the radius of convergence is `exp (sup of slopes)`") is stated in radius form as
  its two inequality halves (`ofReal_exp_le_radiusOfConvergence`, which needs `hdense`, and
  `radiusOfConvergence_le_ofReal_exp`, which does not), each derived from a per-radius
  workhorse about restricted-ness (`isRestricted_of_lt_slope`,
  `not_isRestricted_of_slopes_le` — the polygon-analytic content).  Sharpness requires
  infinitely many nonzero coefficients: for a *polynomial* the radius is `∞` while the slopes
  are bounded, so the blueprint equality genuinely needs the support to be infinite.
* **5.13** phrases "the right endpoint `N` of the `k`-th segment" on the raw algorithm output
  as usual, and clause (5) ("the polygon of `g` is the part of the polygon of `f` on
  `[0, N]`") as: the two algorithms agree at every index `≤ k`.  One deviation: the
  blueprint's bound `|f - g|_c < 1` is correct only on the *first* segment (`k = 0`, where
  `|f|_c = 1`); the proved clause is the scale-correct `|f - g|_c < |f|_c`, with
  `|h - 1|_c < 1` (also proved) carrying the blueprint's intent.  The factorisation is
  normalised by `g(0) = 1` instead of monicity of `g`.
* **5.14** counts zeros of the *series*.  Evaluation of `f` at a point needs a complete valued
  extension (the blueprint's `ℂ_p`), so zeros are phrased via `HasSum` over a complete
  ultrametric normed field `L` extending `K` isometrically; `AlgebraicClosure K` is *not*
  complete, hence the change of setting relative to 5.7 – 5.11.  Multiplicity of a zero of a
  series is not defined here; instead `hasSum_zero_iff_aeval_eq_zero` identifies the zeros of
  `f` in the ball with the roots of the polynomial factor `g` of 5.13 — through it, the
  blueprint's count "`i_j` zeros of absolute value `exp m_j`" *with* multiplicity is exactly
  `card_roots_slope` (5.11) applied to `g`, whose polygon agrees with that of `f` by 5.13(5).
  The remaining half, "no other zeros in the ball" (`norm_eq_exp_slope_of_hasSum_zero`),
  says every zero in the ball lies on a sphere `exp μ_a` for one of the first `k + 1` slopes.
-/

/-! ### The radius of convergence, and convergence on closed balls -/

omit [IsUltrametricDist K] in
/-- Restricted-ness is monotone in the radius. -/
theorem isRestricted_of_le (f : PowerSeries K) {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c ≤ c')
    (h : PowerSeries.IsRestricted c' f) : PowerSeries.IsRestricted c f := by
  rw [PowerSeries.isRestricted_iff] at h ⊢
  refine squeeze_zero (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg hc k))
    (fun k => ?_) h
  gcongr


omit [IsUltrametricDist K] in
/-- **A restricted power series converges on the closed ball**: for `f` restricted of
parameter `c`, the series `∑ aₖ xᵏ` genuinely converges at every point of norm `≤ c` of every
complete ultrametric extension of `K`. -/
theorem summable_of_isRestricted {f : PowerSeries K} {c : ℝ}
    (hf : PowerSeries.IsRestricted c f)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ ≤ c) :
    Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
    tendsto_zero_iff_norm_tendsto_zero]
  rw [PowerSeries.isRestricted_iff] at hf
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hf
  rw [norm_mul, norm_pow, hL]
  gcongr

omit [IsUltrametricDist K] in
/-- **Restricted power series of parameter `c` are exactly those converging on the closed
ball of radius `c`**: at a point of norm exactly `c` in a complete ultrametric extension,
genuine convergence of the series is equivalent to restricted-ness.  (Together with
`summable_of_isRestricted`, which handles the rest of the ball.) -/
theorem isRestricted_iff_summable {f : PowerSeries K} {c : ℝ}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ = c) :
    PowerSeries.IsRestricted c f ↔
      Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k) := by
  refine ⟨fun hf => summable_of_isRestricted K hf hL hx.le, fun hs => ?_⟩
  rw [PowerSeries.isRestricted_iff]
  have h0 := hs.tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero] at h0
  refine h0.congr fun k => ?_
  rw [norm_mul, norm_pow, hL, hx]

omit [IsUltrametricDist K] in
/-- Genuine convergence at a point makes the series restricted at that point's norm. -/
theorem isRestricted_of_summable {f : PowerSeries K}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (h : Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k)) :
    PowerSeries.IsRestricted ‖x‖ f :=
  (isRestricted_iff_summable K hL rfl).mpr h

omit [IsUltrametricDist K] in
/-- **The radius of convergence** of `f` over a complete ultrametric extension `L` of `K`:
the supremum of the norms of the points of `L` at which the series `∑ aₖ xᵏ` genuinely
converges.  Relative to `L` of necessity: over `L = ℚ_p` the attainable norms are only the
powers of `p`, so this supremum can undershoot the analytic radius; over a norm-dense
extension (`ℂ_p`) it is the blueprint's radius of convergence. -/
noncomputable def radiusOfConvergence (L : Type*) [NontriviallyNormedField L]
    [IsUltrametricDist L] [CompleteSpace L] [Algebra K L] (f : PowerSeries K) : ENNReal :=
  ⨆ (x : L) (_ : Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k)),
    (‖x‖₊ : ENNReal)

omit [IsUltrametricDist K] in
/-- Points of convergence bound the radius of convergence from below. -/
theorem le_radiusOfConvergence_of_summable {f : PowerSeries K}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L]
    {x : L} (h : Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k)) :
    (‖x‖₊ : ENNReal) ≤ radiusOfConvergence K L f :=
  le_iSup₂ (f := fun (x : L)
    (_ : Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k)) =>
      ((‖x‖₊ : ENNReal))) x h

omit [IsUltrametricDist K] in
/-- **Points strictly inside the radius of convergence converge.**  (At the boundary both
behaviours occur — `∑ xⁿ` diverges on its boundary sphere while `∑ pⁿ² xⁿ` converges on
its — so `<` cannot be improved to `≤`.) -/
theorem summable_of_lt_radiusOfConvergence {f : PowerSeries K}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (h : (‖x‖₊ : ENNReal) < radiusOfConvergence K L f) :
    Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k) := by
  rw [radiusOfConvergence, lt_iSup_iff] at h
  obtain ⟨y, h⟩ := h
  rw [lt_iSup_iff] at h
  obtain ⟨hy, hlt⟩ := h
  have hyx : ‖x‖ ≤ ‖y‖ := by exact_mod_cast hlt.le
  exact summable_of_isRestricted K (isRestricted_of_summable K hL hy) hL hyx

omit [IsUltrametricDist K] in
/-- Radii strictly below the radius of convergence are restricted. -/
theorem isRestricted_of_lt_radiusOfConvergence {f : PowerSeries K} {c : ℝ} (hc : 0 ≤ c)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (h : ENNReal.ofReal c < radiusOfConvergence K L f) :
    PowerSeries.IsRestricted c f := by
  rw [radiusOfConvergence, lt_iSup_iff] at h
  obtain ⟨y, h⟩ := h
  rw [lt_iSup_iff] at h
  obtain ⟨hy, hlt⟩ := h
  have hcy : c ≤ ‖y‖ := by
    have h2 := hlt.le
    rw [show ((‖y‖₊ : ENNReal)) = ENNReal.ofReal ‖y‖ by
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg y)).mp h2
  exact isRestricted_of_le K f hc hcy (isRestricted_of_summable K hL hy)

omit [IsUltrametricDist K] in
/-- Over an extension with **dense norms**, restricted radii bound the radius of convergence
from below.  Some density is necessary: over `L = ℚ_p` there are no points with norm strictly
between consecutive powers of `p`. -/
theorem le_radiusOfConvergence_of_isRestricted {f : PowerSeries K} {c : ℝ}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (hdense : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a < b → ∃ x : L, a < ‖x‖ ∧ ‖x‖ < b)
    (h : PowerSeries.IsRestricted c f) :
    ENNReal.ofReal c ≤ radiusOfConvergence K L f := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hrc : (r : ℝ) < c := by
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp hr
  obtain ⟨x, hx1, hx2⟩ := hdense r.coe_nonneg hrc
  have hsx := summable_of_isRestricted K h hL hx2.le
  calc (r : ENNReal) ≤ (‖x‖₊ : ENNReal) := by exact_mod_cast hx1.le
    _ ≤ _ := le_radiusOfConvergence_of_summable K hsx

/-! ### 5.12: the radius of convergence off the polygon -/

/-- Any step at a successor index is produced by `nextStep` at the previous vertex. -/
private lemma exists_nextStep_of_succ {w : ℕ → WithTop ℝ} {b : ℕ} {s : Step ℝ}
    (hs : newtonPolygon w (b + 1) = some s) :
    ∃ (p₀ : ℕ) (p₁ : ℝ), nextStep w p₀ p₁ = s := by
  have h1 : ∃ (i₀ l : ℕ) (i₁ m : ℝ), newtonPolygon w b = some (.nextVertex i₀ i₁ l m) := by
    unfold newtonPolygon at hs
    split at hs
    · rename_i _ i₀ i₁ l m
      grind
    · trivial
  obtain ⟨i₀, l, i₁, m, hb⟩ := h1
  refine ⟨i₀, i₁, ?_⟩
  unfold newtonPolygon at hs
  simp_rw [hb, Option.some.injEq] at hs
  exact hs

/-- Points beyond the base of a step lie on/above the line with slope `sInf slopeSet` — the
common core of `step_slope_le` and its ray analogues. -/
private lemma slope_le_of_sInf (f : PowerSeries K) {i₀ : ℕ} {i₁ m : ℝ}
    (hbdd : BddBelow (slopeSet (coeffVal K f) i₀ i₁))
    (hm : m = sInf (slopeSet (coeffVal K f) i₀ i₁))
    {k : ℕ} (hk : i₀ < k) (hak : PowerSeries.coeff k f ≠ 0) :
    m * ((k : ℝ) - i₀) ≤ - Real.log ‖PowerSeries.coeff k f‖ - i₁ := by
  set vk : ℝ := - Real.log ‖PowerSeries.coeff k f‖ with hvk
  have hmem : ((vk - i₁) / ((k : ℝ) - i₀)) ∈ slopeSet (coeffVal K f) i₀ i₁ := by
    refine ⟨k, hk, ?_, vk, ?_, ?_⟩
    · show coeffVal K f k ≠ ⊤
      simp only [coeffVal]
      rw [ne_eq, addVal_eq_top_iff]
      exact hak
    · simp only [coeffVal]
      rw [addVal_of_ne_zero K hak]
    · rw [slopeReal_real]
  have hle : m ≤ (vk - i₁) / ((k : ℝ) - i₀) := by
    rw [hm]
    exact csInf_le hbdd hmem
  have hki : (0 : ℝ) < (k : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hk)
  rw [le_div_iff₀ hki] at hle
  linarith

/-- **Workhorse for 5.12, convergence half.**  If `μ` is any slope of the polygon of `f`
(of a vertex, a limiting ray, or an infinite ray), then `f` is restricted for — converges on
the closed ball of — every radius `c < exp μ`. -/
theorem isRestricted_of_lt_slope (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1)
    {a : ℕ} {s : Step ℝ} (hs : newtonPolygon (coeffVal K f) a = some s)
    {μ : ℝ} (hμ : _root_.slopes s = (μ : WithTopBot ℝ))
    {c : ℝ} (hc0 : 0 < c) (hc : c < Real.exp μ) :
    PowerSeries.IsRestricted c f := by
  -- a base point `(p₀, p₁)` producing the step
  obtain ⟨p₀, p₁, hst⟩ : ∃ (p₀ : ℕ) (p₁ : ℝ), nextStep (coeffVal K f) p₀ p₁ = s := by
    rcases a with _ | b
    · exact ⟨0, 0, Option.some_inj.mp ((newtonPolygon_zero_eq K f hf0).symm.trans hs)⟩
    · exact exists_nextStep_of_succ hs
  -- the slope `μ` bounds the slope set below
  obtain ⟨hbdd, hsInf⟩ : BddBelow (slopeSet (coeffVal K f) p₀ p₁) ∧
      μ = sInf (slopeSet (coeffVal K f) p₀ p₁) := by
    rcases s with _ | _ | m' | m' | ⟨j₀, j₁, l, m'⟩
    · exact absurd hμ (by simp [_root_.slopes])
    · exact absurd hμ (by simp [_root_.slopes])
    · have hmμ : m' = μ := by
        have := hμ
        simp only [_root_.slopes] at this
        exact_mod_cast this
      exact ⟨limitingRay_bddBelow _ hst, hmμ ▸ limitingRay_slope_eq_sInf _ hst⟩
    · have hmμ : m' = μ := by
        have := hμ
        simp only [_root_.slopes] at this
        exact_mod_cast this
      exact ⟨infiniteRay_bddBelow _ hst, hmμ ▸ infiniteRay_slope_eq_sInf _ hst⟩
    · have hmμ : m' = μ := by
        have := hμ
        simp only [_root_.slopes] at this
        exact_mod_cast this
      exact ⟨nextVertex_bddBelow _ hst, hmμ ▸ nextVertex_slope_eq_sInf'' _ hst⟩
  -- geometric decay beyond `p₀`
  rw [PowerSeries.isRestricted_iff']
  set r : ℝ := c / Real.exp μ with hr
  have hr0 : (0 : ℝ) < r := div_pos hc0 (Real.exp_pos μ)
  have hr1 : r < 1 := (div_lt_one (Real.exp_pos μ)).mpr hc
  have hrexp : r = Real.exp (Real.log c - μ) := by
    rw [Real.exp_sub, Real.exp_log hc0, hr]
  have hgeo : Filter.Tendsto (fun k : ℕ => Real.exp (μ * p₀ - p₁) * r ^ k)
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul (Real.exp (μ * p₀ - p₁))
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun k => mul_nonneg (norm_nonneg _) (pow_nonneg hc0.le k))
    ?_ hgeo
  rw [Filter.eventually_atTop]
  refine ⟨p₀ + 1, fun k hk => ?_⟩
  by_cases hak : PowerSeries.coeff k f = 0
  · rw [hak, norm_zero, zero_mul]
    positivity
  · have hline := slope_le_of_sInf K f hbdd hsInf (by omega : p₀ < k) hak
    have hnorm_pos : (0 : ℝ) < ‖PowerSeries.coeff k f‖ := norm_pos_iff.mpr hak
    calc ‖PowerSeries.coeff k f‖ * c ^ k
        = Real.exp (Real.log ‖PowerSeries.coeff k f‖ + k * Real.log c) := by
          have h1 : (c : ℝ) ^ k = Real.exp (k * Real.log c) := by
            rw [Real.exp_nat_mul, Real.exp_log hc0]
          rw [Real.exp_add, Real.exp_log hnorm_pos, h1]
      _ ≤ Real.exp (μ * p₀ - p₁ + k * (Real.log c - μ)) := by
          rw [Real.exp_le_exp]
          nlinarith [hline]
      _ = Real.exp (μ * p₀ - p₁) * r ^ k := by
          rw [Real.exp_add, hrexp, ← Real.exp_nat_mul]

/-- Any vertex of the polygon at a successor index sits above the previous vertex. -/
private lemma newtonPolygon_succ_eq {w : ℕ → WithTop ℝ} {a j₀ l : ℕ} {j₁ m : ℝ}
    (h : newtonPolygon w a = some (.nextVertex j₀ j₁ l m)) :
    newtonPolygon w (a + 1) = some (nextStep w j₀ j₁) := by
  conv_lhs => rw [newtonPolygon, h]

/-- **Workhorse for 5.12, sharpness half.**  If `f` has infinitely many nonzero coefficients
and every slope of its polygon is `≤ m`, then `f` is not restricted for any radius
`c > exp m`. -/
theorem not_isRestricted_of_slopes_le (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    (hinf : {k : ℕ | PowerSeries.coeff k f ≠ 0}.Infinite)
    {m : ℝ} (hm : ∀ (a : ℕ) (s : Step ℝ), newtonPolygon (coeffVal K f) a = some s →
      ∀ μ : ℝ, _root_.slopes s = (μ : WithTopBot ℝ) → μ ≤ m)
    {c : ℝ} (hc : Real.exp m < c) :
    ¬ PowerSeries.IsRestricted c f := by
  classical
  have hc0 : (0 : ℝ) < c := (Real.exp_pos m).trans hc
  have hlogc : m < Real.log c := (Real.lt_log_iff_exp_lt hc0).mpr hc
  -- an infinite set of terms `≥ 1` defeats restricted-ness
  have key : ∀ S : Set ℕ, S.Infinite →
      (∀ k ∈ S, (1 : ℝ) ≤ ‖PowerSeries.coeff k f‖ * c ^ k) →
      ¬ PowerSeries.IsRestricted c f := by
    intro S hS hSbound hres
    rw [PowerSeries.isRestricted_iff] at hres
    have hev := hres.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    rw [Filter.eventually_cofinite] at hev
    exact (hS.mono fun k hk => not_lt.mpr (hSbound k hk)) hev
  -- terms through the additive valuation
  have hterm : ∀ (k : ℕ) (y : ℝ), coeffVal K f k = ((y : ℝ) : WithTop ℝ) →
      ‖PowerSeries.coeff k f‖ * c ^ k = Real.exp (-y + k * Real.log c) := by
    intro k y hy
    have hak : PowerSeries.coeff k f ≠ 0 := by
      intro h0
      rw [coeffVal, h0, addVal_zero] at hy
      exact WithTop.top_ne_coe hy
    have hyval : y = - Real.log ‖PowerSeries.coeff k f‖ := by
      rw [coeffVal, addVal_of_ne_zero K hak] at hy
      exact_mod_cast hy.symm
    have h1 : (c : ℝ) ^ k = Real.exp (k * Real.log c) := by
      rw [Real.exp_nat_mul, Real.exp_log hc0]
    rw [Real.exp_add, h1, hyval, neg_neg, Real.exp_log (norm_pos_iff.mpr hak)]
  -- every polygon vertex lies under the line of slope `m` through the origin
  have hchain : ∀ (a : ℕ) (j₀' l' : ℕ) (j₁' μ' : ℝ),
      newtonPolygon (coeffVal K f) a = some (.nextVertex j₀' j₁' l' μ') →
      coeffVal K f j₀' = ((j₁' : ℝ) : WithTop ℝ) ∧ j₁' ≤ m * j₀' := by
    intro a
    induction a with
    | zero =>
      intro j₀' l' j₁' μ' hstep0
      have hv : nextStep (coeffVal K f) 0 0 = .nextVertex j₀' j₁' l' μ' :=
        Option.some_inj.mp ((newtonPolygon_zero_eq K f hf0).symm.trans hstep0)
      refine ⟨nextVertex_j₁_eq _ hv, ?_⟩
      have hslope := nextVertex_slope_eq_sInf' _ hv
      rw [slopeReal_real] at hslope
      have hj₀pos : (0 : ℝ) < (j₀' : ℝ) := by exact_mod_cast nextVertex_lt _ hv
      have hj₁ : j₁' = μ' * j₀' := by
        rw [eq_div_iff (by push_cast; simpa using hj₀pos.ne')] at hslope
        push_cast at hslope
        linarith
      have hμm : μ' ≤ m := hm 0 _ hstep0 μ' rfl
      nlinarith [hj₀pos.le]
    | succ a ih =>
      intro j₀' l' j₁' μ' hstepa
      obtain ⟨i₀, i₁, li, mi, hprev⟩ := nextStep_nextVertex' _ hstepa
      have hv : nextStep (coeffVal K f) i₀ i₁ = .nextVertex j₀' j₁' l' μ' :=
        nextStep_nextVertex'' _ hstepa hprev
      refine ⟨nextVertex_j₁_eq _ hv, ?_⟩
      have hih := (ih _ _ _ _ hprev).2
      have hslope := nextVertex_slope_eq_sInf' _ hv
      rw [slopeReal_real] at hslope
      have hlt : i₀ < j₀' := nextVertex_lt _ hv
      have hltR : (0 : ℝ) < (j₀' : ℝ) - i₀ := by
        rw [sub_pos]; exact_mod_cast hlt
      have hline : j₁' = i₁ + μ' * ((j₀' : ℝ) - i₀) := by
        rw [eq_div_iff hltR.ne'] at hslope
        linarith
      have hμm : μ' ≤ m := hm (a + 1) _ hstepa μ' rfl
      nlinarith [hih, mul_nonneg (sub_nonneg.mpr hμm) hltR.le]
  by_cases hall : ∀ a : ℕ, ∃ (j₀ l : ℕ) (j₁ μ : ℝ),
      newtonPolygon (coeffVal K f) a = some (.nextVertex j₀ j₁ l μ)
  · -- infinitely many vertices: their terms are all `≥ 1`
    choose j₀ l j₁ μ hstep using hall
    apply key (Set.range j₀)
    · have hmono : StrictMono j₀ := strictMono_nat_of_lt_succ fun a =>
        nextVertex_lt _ (nextStep_nextVertex'' _ (hstep (a + 1)) (hstep a))
      exact Set.infinite_range_of_injective hmono.injective
    · rintro k ⟨a, rfl⟩
      rw [hterm _ _ (hchain a _ _ _ _ (hstep a)).1,
        show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_le_exp]
      nlinarith [(hchain a _ _ _ _ (hstep a)).2,
        mul_nonneg (Nat.cast_nonneg (j₀ a) : (0 : ℝ) ≤ (j₀ a : ℝ))
          (sub_nonneg.mpr hlogc.le)]
  · -- a terminal step exists; take the least one, with its base point on the chain
    push Not at hall
    have hex : ∃ a, ∀ (j₀ l : ℕ) (j₁ μ : ℝ),
        newtonPolygon (coeffVal K f) a ≠ some (.nextVertex j₀ j₁ l μ) := hall
    have hbspec := Nat.find_spec hex
    have hbmin : ∀ a < Nat.find hex, ∃ (j₀ l : ℕ) (j₁ μ : ℝ),
        newtonPolygon (coeffVal K f) a = some (.nextVertex j₀ j₁ l μ) := by
      intro a ha
      by_contra hcon
      push Not at hcon
      exact Nat.find_min hex ha hcon
    obtain ⟨p₀, p₁, hstb, hp₁⟩ : ∃ (p₀ : ℕ) (p₁ : ℝ),
        newtonPolygon (coeffVal K f) (Nat.find hex)
          = some (nextStep (coeffVal K f) p₀ p₁) ∧ p₁ ≤ m * p₀ := by
      cases hfind : Nat.find hex with
      | zero =>
        refine ⟨0, 0, ?_, by norm_num⟩
        exact newtonPolygon_zero_eq K f hf0
      | succ a =>
        obtain ⟨i₀, li, i₁, μi, hveq⟩ := hbmin a (hfind.symm ▸ Nat.lt_succ_self a)
        exact ⟨i₀, i₁, newtonPolygon_succ_eq hveq, (hchain a i₀ li i₁ μi hveq).2⟩
    -- the slope of every finite point beyond `p₀`, as a total function
    set sl : ℕ → ℝ :=
      fun k => (- Real.log ‖PowerSeries.coeff k f‖ - p₁) / ((k : ℝ) - p₀) with hsl
    have hslopeSet : slopeSet (coeffVal K f) p₀ p₁ =
        sl '' {k | p₀ < k ∧ PowerSeries.coeff k f ≠ 0} := by
      ext x
      constructor
      · rintro ⟨k, hk, hfin, y, hy, hx⟩
        have hak : PowerSeries.coeff k f ≠ 0 := by
          intro h0
          apply hfin
          show coeffVal K f k = ⊤
          rw [coeffVal, h0, addVal_zero]
        have hyval : y = - Real.log ‖PowerSeries.coeff k f‖ := by
          rw [coeffVal, addVal_of_ne_zero K hak] at hy
          exact_mod_cast hy.symm
        refine ⟨k, ⟨hk, hak⟩, ?_⟩
        simp only [hsl]
        rw [hx, slopeReal_real, hyval]
      · rintro ⟨k, ⟨hk, hak⟩, rfl⟩
        refine ⟨k, hk, ?_, - Real.log ‖PowerSeries.coeff k f‖, ?_, ?_⟩
        · show coeffVal K f k ≠ ⊤
          simp only [coeffVal]
          rw [ne_eq, addVal_eq_top_iff]
          exact hak
        · simp only [coeffVal]
          rw [addVal_of_ne_zero K hak]
        · rw [slopeReal_real]
    -- kill machine: infinitely many points of slope `≤ t₀ < log c` defeat restricted-ness
    have hkill : ∀ t₀ : ℝ, t₀ < Real.log c →
        {k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧ sl k ≤ t₀}.Infinite →
        ¬ PowerSeries.IsRestricted c f := by
      intro t₀ ht₀ hSinf
      obtain ⟨k₀, hk₀⟩ := exists_nat_ge ((p₁ - t₀ * p₀) / (Real.log c - t₀))
      apply key ({k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧ sl k ≤ t₀} ∩ Set.Ici k₀)
      · have heq : {k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧ sl k ≤ t₀} ∩ Set.Ici k₀ =
            {k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧ sl k ≤ t₀} \ Set.Iio k₀ := by
          ext k
          simp [not_lt]
        rw [heq]
        exact hSinf.diff (Set.finite_Iio k₀)
      · rintro k ⟨⟨⟨hk, hak⟩, hslk⟩, hk₀'⟩
        have hcv : coeffVal K f k
            = ((- Real.log ‖PowerSeries.coeff k f‖ : ℝ) : WithTop ℝ) := by
          rw [coeffVal, addVal_of_ne_zero K hak]
        rw [hterm k _ hcv, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm,
          Real.exp_le_exp]
        have hkp : (0 : ℝ) < (k : ℝ) - p₀ := sub_pos.mpr (by exact_mod_cast hk)
        have h1 : - Real.log ‖PowerSeries.coeff k f‖ - p₁ ≤ t₀ * ((k : ℝ) - p₀) := by
          have := hslk
          simp only [hsl] at this
          rw [div_le_iff₀ hkp] at this
          exact this
        have h2 : p₁ - t₀ * p₀ ≤ (k : ℝ) * (Real.log c - t₀) := by
          have h3 : p₁ - t₀ * p₀ ≤ (k₀ : ℝ) * (Real.log c - t₀) := by
            rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log c - t₀)] at hk₀
            exact hk₀
          have h4 : (k₀ : ℝ) ≤ k := by exact_mod_cast hk₀'
          nlinarith [h3, h4]
        nlinarith [h1, h2]
    -- case on the terminal step
    rcases hsb : nextStep (coeffVal K f) p₀ p₁ with _ | _ | mr | mr | ⟨j₀', j₁', l', μ'⟩
    · -- tail: finite support, contradicting `hinf`
      refine absurd (Set.Finite.subset (Set.finite_Iic p₀) fun k hk => ?_) hinf
      rw [Set.mem_Iic]
      by_contra hgt
      rw [not_le] at hgt
      have hak : PowerSeries.coeff k f ≠ 0 := hk
      have hmem : ((- Real.log ‖PowerSeries.coeff k f‖ - p₁) / ((k : ℝ) - p₀)) ∈
          slopeSet (coeffVal K f) p₀ p₁ := by
        refine ⟨k, hgt, ?_, - Real.log ‖PowerSeries.coeff k f‖, ?_, ?_⟩
        · show coeffVal K f k ≠ ⊤
          simp only [coeffVal]
          rw [ne_eq, addVal_eq_top_iff]
          exact hak
        · simp only [coeffVal]
          rw [addVal_of_ne_zero K hak]
        · rw [slopeReal_real]
      rw [slopeSet_eq_empty_of_nextStep_tail hsb] at hmem
      exact hmem
    · -- unbounded below: arbitrarily steep points give arbitrarily large terms
      have hnb := unboundedBelow _ hsb
      refine hkill (Real.log c - 1) (by linarith) ?_
      by_contra hfin
      rw [Set.not_infinite] at hfin
      apply hnb
      have hsub : slopeSet (coeffVal K f) p₀ p₁ ⊆
          sl '' {k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧ sl k ≤ Real.log c - 1} ∪
          Set.Ici (Real.log c - 1) := by
        rw [hslopeSet]
        rintro x ⟨k, hkS, rfl⟩
        by_cases hlt : sl k ≤ Real.log c - 1
        · exact Or.inl ⟨k, ⟨hkS, hlt⟩, rfl⟩
        · exact Or.inr (le_of_lt (not_le.mp hlt))
      exact BddBelow.mono hsub ((hfin.image sl).bddBelow.union bddBelow_Ici)
    · -- limiting ray of slope `mr ≤ m`: slopes accumulate at `mr` from above
      have hbddb := limitingRay_bddBelow _ hsb
      have hne := limitingRay_nonempty _ hsb
      have hsinf := limitingRay_slope_eq_sInf _ hsb
      have hnat := not_attained_of_nextStep_limitingRay hsb
      have hμm : mr ≤ m := hm _ _ (by rw [hstb, hsb]) mr rfl
      set δ : ℝ := (Real.log c - m) / 2 with hδdef
      have hδ : 0 < δ := by rw [hδdef]; linarith
      refine hkill (mr + δ) (by rw [hδdef]; linarith) ?_
      by_contra hfin
      rw [Set.not_infinite] at hfin
      obtain ⟨ε, hε0, hεδ, hgap⟩ : ∃ ε, 0 < ε ∧ ε ≤ δ ∧
          ∀ k, (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) → sl k ≤ mr + δ → mr + ε ≤ sl k := by
        by_cases hFe : {k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧ sl k ≤ mr + δ} = ∅
        · refine ⟨δ, hδ, le_rfl, fun k hk hsk => ?_⟩
          exact absurd
            (show k ∈ {k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧ sl k ≤ mr + δ}
              from ⟨hk, hsk⟩)
            (Set.eq_empty_iff_forall_notMem.mp hFe k)
        · have hFne : {k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧
              sl k ≤ mr + δ}.Nonempty := Set.nonempty_iff_ne_empty.mpr hFe
          have hTne : (hfin.toFinset.image sl).Nonempty :=
            ⟨sl hFne.choose, Finset.mem_image_of_mem _
              (hfin.mem_toFinset.mpr hFne.choose_spec)⟩
          have hμmin : mr < (hfin.toFinset.image sl).min' hTne := by
            obtain ⟨kst, hkmem, hkeq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hTne)
            rw [← hkeq]
            have hkS := hfin.mem_toFinset.mp hkmem
            have hslmem : sl kst ∈ slopeSet (coeffVal K f) p₀ p₁ := by
              rw [hslopeSet]
              exact ⟨kst, hkS.1, rfl⟩
            have hge : mr ≤ sl kst := by
              rw [hsinf]
              exact csInf_le hbddb hslmem
            rcases eq_or_lt_of_le hge with heq | hlt
            · exact absurd ⟨sl kst, hslmem, by rw [← heq, hsinf]⟩ hnat
            · exact hlt
          refine ⟨min ((hfin.toFinset.image sl).min' hTne - mr) δ,
            lt_min (by linarith) hδ, min_le_right _ _, ?_⟩
          intro k hk hsk
          have hmin := Finset.min'_le (hfin.toFinset.image sl) (sl k)
            (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr ⟨hk, hsk⟩))
          have := min_le_left ((hfin.toFinset.image sl).min' hTne - mr) δ
          linarith
      have hlt : sInf (slopeSet (coeffVal K f) p₀ p₁) < mr + ε := by
        rw [← hsinf]
        linarith
      obtain ⟨x, hxmem, hxlt⟩ := (csInf_lt_iff hbddb hne).mp hlt
      rw [hslopeSet] at hxmem
      obtain ⟨k, hkS, rfl⟩ := hxmem
      have hkin : sl k ≤ mr + δ := by linarith
      have := hgap k hkS hkin
      linarith
    · -- infinite ray of slope `mr ≤ m`: infinitely many points on the ray
      have hach := achievingSet_infinite_of_nextStep_infiniteRay hsb
      have hμm : mr ≤ m := hm _ _ (by rw [hstb, hsb]) mr rfl
      refine hkill m (by linarith) (hach.mono ?_)
      rintro k ⟨hk, hfin, y, hy, hslope⟩
      have hak : PowerSeries.coeff k f ≠ 0 := by
        intro h0
        apply hfin
        show coeffVal K f k = ⊤
        rw [coeffVal, h0, addVal_zero]
      have hyval : y = - Real.log ‖PowerSeries.coeff k f‖ := by
        rw [coeffVal, addVal_of_ne_zero K hak] at hy
        exact_mod_cast hy.symm
      refine ⟨⟨hk, hak⟩, ?_⟩
      rw [slopeReal_real] at hslope
      have hslk : sl k = mr := by
        simp only [hsl]
        rw [← hyval, ← hslope]
      rw [hslk]
      exact hμm
    · -- a vertex: contradicts minimality
      exact absurd (by rw [hstb, hsb]) (hbspec j₀' l' j₁' μ')

/-- **Blueprint Theorem 5.12, lower half.**  Over an extension with dense norms (`ℂ_p`),
every slope `μ` of the polygon pushes the radius of convergence up to at least `exp μ`;
ranging over the slopes, the radius is at least `exp (sup of the slopes)`. -/
theorem ofReal_exp_le_radiusOfConvergence (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {a : ℕ} {s : Step ℝ} (hs : newtonPolygon (coeffVal K f) a = some s)
    {μ : ℝ} (hμ : _root_.slopes s = (μ : WithTopBot ℝ))
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (hdense : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a < b → ∃ x : L, a < ‖x‖ ∧ ‖x‖ < b) :
    ENNReal.ofReal (Real.exp μ) ≤ radiusOfConvergence K L f := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hrc : (r : ℝ) < Real.exp μ := by
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp hr
  obtain ⟨x, hx1, hx2⟩ := hdense r.coe_nonneg hrc
  have hres := isRestricted_of_lt_slope K f hf0 hs hμ
    (lt_of_le_of_lt r.coe_nonneg hx1) hx2
  have hsx := summable_of_isRestricted K hres hL le_rfl
  calc (r : ENNReal) ≤ (‖x‖₊ : ENNReal) := by exact_mod_cast hx1.le
    _ ≤ _ := le_radiusOfConvergence_of_summable K hsx

/-- **Blueprint Theorem 5.12, upper half.**  If `f` has infinitely many nonzero coefficients
and every slope of its polygon is `≤ m`, then over *any* complete ultrametric extension the
radius of convergence is at most `exp m`; at `m = sup of the slopes` this is the sharp bound.
(No density is needed for this half.) -/
theorem radiusOfConvergence_le_ofReal_exp (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    (hinf : {k : ℕ | PowerSeries.coeff k f ≠ 0}.Infinite)
    {m : ℝ} (hm : ∀ (a : ℕ) (s : Step ℝ), newtonPolygon (coeffVal K f) a = some s →
      ∀ μ : ℝ, _root_.slopes s = (μ : WithTopBot ℝ) → μ ≤ m)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) :
    radiusOfConvergence K L f ≤ ENNReal.ofReal (Real.exp m) := by
  rw [radiusOfConvergence]
  refine iSup₂_le fun x hx => ?_
  by_contra hgt
  rw [not_le, show ((‖x‖₊ : ENNReal)) = ENNReal.ofReal ‖x‖ by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]] at hgt
  have hxm : Real.exp m < ‖x‖ :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_pos m).le).mp hgt
  exact not_isRestricted_of_slopes_le K f hf0 hinf hm hxm
    (isRestricted_of_summable K hL hx)

/-- Data of a finite point of the valuation sequence. -/
private lemma coeffVal_eq_coe_iff {f : PowerSeries K} {t : ℕ} {y : ℝ}
    (h : coeffVal K f t = ((y : ℝ) : WithTop ℝ)) :
    PowerSeries.coeff t f ≠ 0 ∧ y = - Real.log ‖PowerSeries.coeff t f‖ := by
  have hak : PowerSeries.coeff t f ≠ 0 := by
    intro h0
    rw [coeffVal, h0, addVal_zero] at h
    exact WithTop.top_ne_coe h
  refine ⟨hak, ?_⟩
  rw [coeffVal, addVal_of_ne_zero K hak] at h
  exact_mod_cast h.symm

/-- Series form of `memDivisibleValueGroup_exp_slope`: slope radii of the polygon of a
*power series* lie in the divisible closure of the value group. -/
theorem memDivisibleValueGroup_exp_slope' (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {k j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K f) k = some (.nextVertex j₀ j₁ l m)) :
    MemDivisibleValueGroup K (Real.exp m) := by
  obtain ⟨i₀, i₁, hstep, hci₀, hi₁val⟩ :
      ∃ (i₀ : ℕ) (i₁ : ℝ),
        nextStep (coeffVal K f) i₀ i₁ = .nextVertex j₀ j₁ l m ∧
        PowerSeries.coeff i₀ f ≠ 0 ∧ i₁ = - Real.log ‖PowerSeries.coeff i₀ f‖ := by
    rcases k with _ | a
    · have hv : nextStep (coeffVal K f) 0 0 = .nextVertex j₀ j₁ l m :=
        Option.some_inj.mp ((newtonPolygon_zero_eq K f hf0).symm.trans hseg)
      exact ⟨0, 0, hv, by rw [hf0]; exact one_ne_zero,
        by rw [hf0, norm_one, Real.log_one, neg_zero]⟩
    · obtain ⟨i₀, i₁, l', m', hprev⟩ := nextStep_nextVertex' _ hseg
      have hstep := nextStep_nextVertex'' _ hseg hprev
      obtain ⟨p₀, p₁, hprevstep⟩ := nextStep_nextVertex _ hprev
      obtain ⟨hci₀, hi₁val⟩ := coeffVal_eq_coe_iff K (nextVertex_j₁_eq _ hprevstep)
      exact ⟨i₀, i₁, hstep, hci₀, hi₁val⟩
  obtain ⟨hcj₀, hj₁val⟩ := coeffVal_eq_coe_iff K (nextVertex_j₁_eq _ hstep)
  have hij : i₀ < j₀ := nextVertex_lt _ hstep
  have hijR : (0 : ℝ) < (j₀ : ℝ) - i₀ := by rw [sub_pos]; exact_mod_cast hij
  have hslope := nextVertex_slope_eq_sInf' _ hstep
  rw [slopeReal_real] at hslope
  have hmn : m * ((j₀ : ℝ) - i₀) = j₁ - i₁ := by
    rw [eq_div_iff hijR.ne'] at hslope
    linarith
  rw [memDivisibleValueGroup_iff_exists_log (Real.exp_pos m)]
  refine ⟨j₀ - i₀, by omega, PowerSeries.coeff i₀ f / PowerSeries.coeff j₀ f,
    div_ne_zero hci₀ hcj₀, ?_⟩
  rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hci₀) (norm_ne_zero_iff.mpr hcj₀),
    Real.log_exp, nsmul_eq_mul, Nat.cast_sub hij.le]
  rw [hj₁val, hi₁val] at hmn
  linarith [hmn]

/-- Series form of `vertex_line_le`: every finite point lies on/above the line through the
`a`-th vertex with the `a`-th slope. -/
private theorem vertex_line_le' (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1) :
    ∀ (a : ℕ) {j₀ l : ℕ} {j₁ m : ℝ},
      newtonPolygon (coeffVal K f) a = some (.nextVertex j₀ j₁ l m) →
      ∀ t, PowerSeries.coeff t f ≠ 0 →
        m * ((t : ℝ) - (j₀ : ℝ)) ≤ - Real.log ‖PowerSeries.coeff t f‖ - j₁ := by
  intro a
  induction a with
  | zero =>
      intro j₀ l j₁ m hseg t ht
      have hv : nextStep (coeffVal K f) 0 0 = .nextVertex j₀ j₁ l m :=
        Option.some_inj.mp ((newtonPolygon_zero_eq K f hf0).symm.trans hseg)
      have hj₀pos : 0 < j₀ := nextVertex_lt _ hv
      have hj₀R : (0 : ℝ) < (j₀ : ℝ) := by exact_mod_cast hj₀pos
      have hslope := nextVertex_slope_eq_sInf' _ hv
      rw [slopeReal_real] at hslope
      have hj₁ : j₁ = m * j₀ := by
        rw [eq_div_iff (by push_cast; simpa using hj₀R.ne')] at hslope
        push_cast at hslope
        linarith
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · have hν0 : - Real.log ‖PowerSeries.coeff 0 f‖ = 0 := by
          rw [hf0, norm_one, Real.log_one, neg_zero]
        rw [hν0]
        have hexp : m * (((0 : ℕ) : ℝ) - (j₀ : ℝ)) = -(m * j₀) := by
          push_cast
          ring
        linarith [hexp, hj₁]
      · have hfb := firstBreak_slope_le K f hv htpos ht
        have hexp : m * ((t : ℝ) - (j₀ : ℝ)) = m * t - m * j₀ := by ring
        linarith [hexp, hj₁, hfb]
  | succ a ih =>
      intro j₀ l j₁ m hseg t ht
      obtain ⟨i₀, i₁, l', m', hprev⟩ := nextStep_nextVertex' _ hseg
      have hstep : nextStep (coeffVal K f) i₀ i₁ = .nextVertex j₀ j₁ l m :=
        nextStep_nextVertex'' _ hseg hprev
      have hij : i₀ < j₀ := nextVertex_lt _ hstep
      have hijR : (0 : ℝ) < (j₀ : ℝ) - i₀ := by
        rw [sub_pos]; exact_mod_cast hij
      have hslope := nextVertex_slope_eq_sInf' _ hstep
      rw [slopeReal_real] at hslope
      have hline : j₁ = i₁ + m * ((j₀ : ℝ) - i₀) := by
        rw [eq_div_iff hijR.ne'] at hslope
        linarith
      have key : m * ((t : ℝ) - i₀) ≤ - Real.log ‖PowerSeries.coeff t f‖ - i₁ := by
        rcases Nat.lt_or_ge i₀ t with hti | hti
        · exact step_slope_le K f hstep hti ht
        · have h1 := ih hprev t ht
          have hts : ((t : ℝ) - i₀) ≤ 0 := by
            rw [sub_nonpos]; exact_mod_cast hti
          obtain ⟨p₀, p₁, hprevstep⟩ := nextStep_nextVertex _ hprev
          have hmm : m' < m := slopes_increasing_nextVertex _ hprevstep hstep
          nlinarith [h1, mul_nonneg (sub_nonneg.mpr hmm.le) (neg_nonneg.mpr hts)]
      have hexp : m * ((t : ℝ) - (j₀ : ℝ)) = m * ((t : ℝ) - i₀) - m * ((j₀ : ℝ) - i₀) := by
        ring
      linarith [key, hline, hexp]

/-- Series form of `vertex_line_lt`: beyond the `a`-th vertex, finite points lie strictly
above the `a`-th slope line (through the next step of the algorithm). -/
private theorem vertex_line_lt' (f : PowerSeries K) {a j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K f) a = some (.nextVertex j₀ j₁ l m))
    {t : ℕ} (htj : j₀ < t) (hat : PowerSeries.coeff t f ≠ 0) :
    m * ((t : ℝ) - (j₀ : ℝ)) < - Real.log ‖PowerSeries.coeff t f‖ - j₁ := by
  obtain ⟨p₀, p₁, hst⟩ := nextStep_nextVertex _ hseg
  have hnext := newtonPolygon_succ_eq hseg
  have htR : (0 : ℝ) < (t : ℝ) - j₀ := sub_pos.mpr (by exact_mod_cast htj)
  rcases hsn : nextStep (coeffVal K f) j₀ j₁ with _ | _ | m' | m' | ⟨q₀, q₁, l', m'⟩
  · exfalso
    have hmem : ((- Real.log ‖PowerSeries.coeff t f‖ - j₁) / ((t : ℝ) - j₀)) ∈
        slopeSet (coeffVal K f) j₀ j₁ := by
      refine ⟨t, htj, ?_, - Real.log ‖PowerSeries.coeff t f‖, ?_, ?_⟩
      · show coeffVal K f t ≠ ⊤
        simp only [coeffVal]
        rw [ne_eq, addVal_eq_top_iff]
        exact hat
      · simp only [coeffVal]
        rw [addVal_of_ne_zero K hat]
      · rw [slopeReal_real]
    rw [slopeSet_eq_empty_of_nextStep_tail hsn] at hmem
    exact hmem
  · exact absurd (by rw [hnext, hsn]) (nextStep_unboundedBelow' (coeffVal K f) a)
  · -- limiting ray: the slope only weakly increases, but is never attained, so the point's
    -- slope is strictly above it
    have hmm' : m ≤ m' := slopes_increasing_limitingRay _ hst hsn
    have hsinf := limitingRay_slope_eq_sInf _ hsn
    have hnat := not_attained_of_nextStep_limitingRay hsn
    have hmem : ((- Real.log ‖PowerSeries.coeff t f‖ - j₁) / ((t : ℝ) - j₀)) ∈
        slopeSet (coeffVal K f) j₀ j₁ := by
      refine ⟨t, htj, ?_, - Real.log ‖PowerSeries.coeff t f‖, ?_, ?_⟩
      · show coeffVal K f t ≠ ⊤
        simp only [coeffVal]
        rw [ne_eq, addVal_eq_top_iff]
        exact hat
      · simp only [coeffVal]
        rw [addVal_of_ne_zero K hat]
      · rw [slopeReal_real]
    have hge : m' ≤ (- Real.log ‖PowerSeries.coeff t f‖ - j₁) / ((t : ℝ) - j₀) := by
      rw [hsinf]
      exact csInf_le (limitingRay_bddBelow _ hsn) hmem
    have hne : (- Real.log ‖PowerSeries.coeff t f‖ - j₁) / ((t : ℝ) - j₀) ≠ m' := by
      intro heq
      exact hnat ⟨_, hmem, by rw [heq, hsinf]⟩
    have hgt : m' < (- Real.log ‖PowerSeries.coeff t f‖ - j₁) / ((t : ℝ) - j₀) :=
      lt_of_le_of_ne hge (Ne.symm hne)
    rw [lt_div_iff₀ htR] at hgt
    nlinarith [mul_le_mul_of_nonneg_right hmm' htR.le]
  · have hmm' : m < m' := slopes_increasing_infiniteRay _ hst hsn
    have hline := slope_le_of_sInf K f (infiniteRay_bddBelow _ hsn)
      (infiniteRay_slope_eq_sInf _ hsn) htj hat
    nlinarith [hline, mul_lt_mul_of_pos_right hmm' htR]
  · have hmm' : m < m' := slopes_increasing_nextVertex _ hst hsn
    have hline := slope_le_of_sInf K f (nextVertex_bddBelow _ hsn)
      (nextVertex_slope_eq_sInf'' _ hsn) htj hat
    nlinarith [hline, mul_lt_mul_of_pos_right hmm' htR]

/-- The Gauss norm is monotone in the radius (on series restricted at the larger radius). -/
private lemma gaussNorm_le_of_radius_le {x : PowerSeries K} {c c' : ℝ} (hc'0 : 0 ≤ c')
    (hcc : c' ≤ c) (hx : PowerSeries.IsRestricted c x) :
    PowerSeries.gaussNorm norm c' x ≤ PowerSeries.gaussNorm norm c x := by
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun t => ?_
  calc ‖PowerSeries.coeff t x‖ * c' ^ t ≤ ‖PowerSeries.coeff t x‖ * c ^ t := by gcongr
    _ ≤ _ := PowerSeries.le_gaussNorm norm c x
        (Restricted.hasGaussNorm c (⟨x, hx⟩ : PowerSeries.Restricted K c)) t

/-- **Congruence of the algorithm at one step.**  If the slope set of `w₁` from `(p₀, p₁)` is
bounded below by `m` and its achieving set at `m` coincides with that of `w₂`, then `w₁`'s
step from `(p₀, p₁)` outputs the same vertex as `w₂`'s. -/
private lemma nextStep_congr {w₁ w₂ : ℕ → WithTop ℝ} {p₀ j₀ l : ℕ} {p₁ j₁ m : ℝ}
    (h : nextStep w₂ p₀ p₁ = .nextVertex j₀ j₁ l m)
    (hlb : ∀ x ∈ slopeSet w₁ p₀ p₁, m ≤ x)
    (hach : achievingSet w₁ p₀ p₁ m = achievingSet w₂ p₀ p₁ m) :
    nextStep w₁ p₀ p₁ = .nextVertex j₀ j₁ l m := by
  have hsInf₂ : m = sInf (slopeSet w₂ p₀ p₁) := nextVertex_slope_eq_sInf'' _ h
  have hj₀mem₂ : j₀ ∈ achievingSet w₂ p₀ p₁ m := by
    have := nextVertex_j₀Mem _ h
    rwa [← hsInf₂] at this
  have hj₀mem₁ : j₀ ∈ achievingSet w₁ p₀ p₁ m := hach ▸ hj₀mem₂
  obtain ⟨hj₀gt, hj₀fin, y₁, hy₁, hsl₁⟩ := hj₀mem₁
  have hm_mem : m ∈ slopeSet w₁ p₀ p₁ := ⟨j₀, hj₀gt, hj₀fin, y₁, hy₁, hsl₁⟩
  have hbdd₁ : BddBelow (slopeSet w₁ p₀ p₁) := ⟨m, hlb⟩
  have hsInf₁ : sInf (slopeSet w₁ p₀ p₁) = m :=
    le_antisymm (csInf_le hbdd₁ hm_mem) (le_csInf ⟨m, hm_mem⟩ hlb)
  have hfin₂ : (achievingSet w₂ p₀ p₁ m).Finite := by
    have := nextVertex_finite _ h
    rwa [← hsInf₂] at this
  have hfin₁ : (achievingSet w₁ p₀ p₁ m).Finite := hach ▸ hfin₂
  -- the value at `j₀` is the one on the line: `y₁ = j₁`
  have hy₁val : y₁ = j₁ := by
    obtain ⟨-, -, y₂, hy₂, hsl₂⟩ := hj₀mem₂
    have hj₂ : w₂ j₀ = ((j₁ : ℝ) : WithTop ℝ) := nextVertex_j₁_eq _ h
    have hy₂j : y₂ = j₁ := by
      rw [hy₂] at hj₂
      exact_mod_cast hj₂
    rw [slopeReal_real] at hsl₁ hsl₂
    have hgt : (0 : ℝ) < (j₀ : ℝ) - p₀ := sub_pos.mpr (by exact_mod_cast hj₀gt)
    rw [hy₂j] at hsl₂
    have h3 := hsl₁.symm.trans hsl₂
    field_simp at h3
    linarith
  rcases hs₁ : nextStep w₁ p₀ p₁ with _ | _ | m₁ | m₁ | ⟨q₀, q₁, l₁, m₁⟩
  · rw [slopeSet_eq_empty_of_nextStep_tail hs₁] at hm_mem
    exact hm_mem.elim
  · exact absurd hbdd₁ (unboundedBelow _ hs₁)
  · exact absurd ⟨m, hm_mem, hsInf₁.symm⟩ (not_attained_of_nextStep_limitingRay hs₁)
  · have hm₁ : m₁ = m := (infiniteRay_slope_eq_sInf _ hs₁).trans hsInf₁
    have h2 := achievingSet_infinite_of_nextStep_infiniteRay hs₁
    rw [hm₁] at h2
    exact (h2 hfin₁).elim
  · have hm₁ : m₁ = m := (nextVertex_slope_eq_sInf'' _ hs₁).trans hsInf₁
    subst hm₁
    have hq₀le : q₀ ≤ j₀ := by
      have h2 := nextVertex_j₀_eq_max _ h
      have hq₀mem : q₀ ∈ achievingSet w₁ p₀ p₁ m₁ := by
        have := nextVertex_j₀Mem _ hs₁
        rwa [hsInf₁] at this
      have hq₀₂ : q₀ ∈ achievingSet w₂ p₀ p₁ (sInf (slopeSet w₂ p₀ p₁)) := by
        rw [← hsInf₂]
        exact hach ▸ hq₀mem
      rw [h2]
      exact Finset.le_max' _ _ ((nextVertex_finite _ h).mem_toFinset.mpr hq₀₂)
    have hj₀le : j₀ ≤ q₀ := by
      have h2 := nextVertex_j₀_eq_max _ hs₁
      have hj₀₁ : j₀ ∈ achievingSet w₁ p₀ p₁ (sInf (slopeSet w₁ p₀ p₁)) := by
        rw [hsInf₁]
        exact hach ▸ hj₀mem₂
      rw [h2]
      exact Finset.le_max' _ _ ((nextVertex_finite _ hs₁).mem_toFinset.mpr hj₀₁)
    have hq₀ : q₀ = j₀ := le_antisymm hq₀le hj₀le
    subst hq₀
    have hq₁ : q₁ = y₁ := by
      have h2 := nextVertex_j₁_eq _ hs₁
      rw [hy₁] at h2
      exact_mod_cast h2.symm
    have hl₁ : l₁ = l := by
      rw [nextVertex_l_eq _ hs₁, nextVertex_l_eq _ h]
    rw [hq₁, hy₁val, hl₁]

/-- **Blueprint Proposition 5.13** (power-series Weierstrass factorisation along the polygon).
If the `k`-th segment of the polygon of `f` ends at `x = j₀` with slope `m`, and `f` converges
on the closed ball of radius `c = exp m`, then `f = g · h` with `g` a polynomial of degree
`j₀` normalised by `g₀ = 1`, `h` a power series converging on the ball with `|h - 1|_c < 1`,
`|f - g|_c < |f|_c`, and the polygon of `g` is the portion of the polygon of `f` over
`[0, j₀]` (the two algorithms agree at every index `≤ k`).

Deviation from the blueprint: its clause `|f - g|_c < 1` holds only for the *first* segment,
where `|f|_c = 1`; for `k ≥ 1` the Gauss norm of `f` exceeds `1` and the correct (and here
proved) bound is `|f - g|_c = |f|_c · |h - 1|_c < |f|_c`. -/
theorem exists_weierstrass_factorisation [CompleteSpace K] (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {k j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K f) k = some (.nextVertex j₀ j₁ l m))
    (hconv : PowerSeries.IsRestricted (Real.exp m) f) :
    ∃ (g : Polynomial K) (h : PowerSeries K),
      f = (g : PowerSeries K) * h ∧
      g.natDegree = j₀ ∧
      g.coeff 0 = 1 ∧
      PowerSeries.gaussNorm norm (Real.exp m) (f - (g : PowerSeries K))
        < PowerSeries.gaussNorm norm (Real.exp m) f ∧
      PowerSeries.IsRestricted (Real.exp m) h ∧
      PowerSeries.gaussNorm norm (Real.exp m) (h - 1) < 1 ∧
      ∀ a, a ≤ k → newtonPolygon (coeffVal K (g : PowerSeries K)) a
        = newtonPolygon (coeffVal K f) a := by
  classical
  have hc0 : (0 : ℝ) < Real.exp m := Real.exp_pos m
  haveI : StrongPos (fun _ : Unit ↦ Real.exp m) := ⟨fun _ => hc0⟩
  haveI : NormMulClass (PowerSeries.Restricted K (Real.exp m)) :=
    MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ Real.exp m)
  obtain ⟨p₀, p₁, hst⟩ := nextStep_nextVertex _ hseg
  obtain ⟨haj₀, hj₁val⟩ := coeffVal_eq_coe_iff K (nextVertex_j₁_eq _ hst)
  -- the Gauss terms are dominated by the `j₀`-th, strictly beyond it
  have hterm_le : ∀ t, ‖PowerSeries.coeff t f‖ * Real.exp m ^ t
      ≤ ‖PowerSeries.coeff j₀ f‖ * Real.exp m ^ j₀ := by
    intro t
    by_cases hat : PowerSeries.coeff t f = 0
    · rw [hat, norm_zero, zero_mul]
      positivity
    · refine (term_le_term_iff' K hat haj₀ hc0 t j₀).mpr ?_
      rw [Real.log_exp]
      have h1 := vertex_line_le' K f hf0 k hseg t hat
      rwa [hj₁val] at h1
  have hterm_lt : ∀ t, j₀ < t → ‖PowerSeries.coeff t f‖ * Real.exp m ^ t
      < ‖PowerSeries.coeff j₀ f‖ * Real.exp m ^ j₀ := by
    intro t htj
    by_cases hat : PowerSeries.coeff t f = 0
    · rw [hat, norm_zero, zero_mul]
      exact mul_pos (norm_pos_iff.mpr haj₀) (pow_pos hc0 j₀)
    · refine (term_lt_term_iff' K hat haj₀ hc0 t j₀).mpr ?_
      rw [Real.log_exp]
      have h1 := vertex_line_lt' K f hseg htj hat
      rwa [hj₁val] at h1
  -- `f` is `j₀`-distinguished at `exp m`
  have hdist : distinguishedGen norm (Real.exp m) f j₀ := by
    refine ⟨isUnit_iff_ne_zero.mpr haj₀, ?_, hterm_lt⟩
    refine le_antisymm ?_ ?_
    · rw [PowerSeries.gaussNorm_eq]
      exact ciSup_le hterm_le
    · exact PowerSeries.le_gaussNorm norm _ f
        (Restricted.hasGaussNorm _ (⟨f, hconv⟩ : PowerSeries.Restricted K (Real.exp m))) j₀
  -- Weierstrass preparation over `K`, series form
  obtain ⟨ω, e, ωm, ωd, ωn, he, hgeq⟩ :=
    weierstrassPreparation_exists_divisible
      (memDivisibleValueGroup_exp_slope' K f hf0 hseg)
      (⟨f, hconv⟩ : PowerSeries.Restricted K (Real.exp m)) j₀ hdist
  have hnat : ω.natDegree = j₀ := Polynomial.natDegree_eq_of_degree_eq_some ωd
  have hfeq : f = e.1 * (ω : PowerSeries K) := by
    have h1 := congrArg Subtype.val hgeq
    exact h1
  -- constant coefficients
  have hcoeff0 : PowerSeries.coeff 0 e.1 * ω.coeff 0 = 1 := by
    have h1 := congrArg (PowerSeries.coeff 0) hfeq
    rw [hf0, PowerSeries.coeff_mul] at h1
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Polynomial.coeff_coe] at h1
    exact h1.symm
  have hω₀ : ω.coeff 0 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hcoeff0
    exact zero_ne_one hcoeff0
  -- the normalised factor `g` and unit part `h`
  set g : Polynomial K := Polynomial.C (ω.coeff 0)⁻¹ * ω with hgdef
  set h : PowerSeries K := PowerSeries.C (ω.coeff 0) * e.1 with hhdef
  have hg0 : g.coeff 0 = 1 := by
    rw [hgdef, Polynomial.coeff_C_mul, inv_mul_cancel₀ hω₀]
  have hgdeg : g.natDegree = j₀ := by
    rw [hgdef, Polynomial.natDegree_C_mul (inv_ne_zero hω₀), hnat]
  have hfgh : f = (g : PowerSeries K) * h := by
    rw [hgdef, hhdef, Polynomial.coe_mul, Polynomial.coe_C, hfeq]
    have hCC : (PowerSeries.C (ω.coeff 0)⁻¹ : PowerSeries K) *
        PowerSeries.C (ω.coeff 0) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hω₀, map_one]
    calc e.1 * (ω : PowerSeries K)
        = (PowerSeries.C (ω.coeff 0)⁻¹ * PowerSeries.C (ω.coeff 0)) *
            (e.1 * (ω : PowerSeries K)) := by rw [hCC, one_mul]
      _ = PowerSeries.C (ω.coeff 0)⁻¹ * (ω : PowerSeries K) *
            (PowerSeries.C (ω.coeff 0) * e.1) := by ring
  have hh0 : PowerSeries.coeff 0 h = 1 := by
    rw [hhdef, PowerSeries.coeff_C_mul, mul_comm]
    exact hcoeff0
  have hhres : PowerSeries.IsRestricted (Real.exp m) h := by
    rw [hhdef]
    exact PowerSeries.isRestricted.mul _ (PowerSeries.isRestricted_C _ _) e.2
  -- `h` as a unit of the restricted ring, with strictly dominant constant coefficient
  set H : PowerSeries.Restricted K (Real.exp m) :=
    PowerSeries.Restricted.C (Real.exp m) (ω.coeff 0) * e with hHdef
  have hHval : H.1 = h := rfl
  have hHunit : IsUnit H :=
    (PowerSeries.Restricted.C_isUnit _ (isUnit_iff_ne_zero.mpr hω₀)).mul he
  have hhdom : ∀ t, 1 ≤ t → ‖PowerSeries.coeff t h‖ * Real.exp m ^ t < 1 := by
    intro t ht
    have h1 := dominant_const_of_isUnit
      (memDivisibleValueGroup_exp_slope' K f hf0 hseg) hHunit t ht
    rwa [hHval, hh0, norm_one] at h1
  -- `|h − 1| < 1`, by attainment of the Gauss norm
  have hsub_res : PowerSeries.IsRestricted (Real.exp m) (h - 1) := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add _ hhres
      (PowerSeries.isRestricted.neg _ (PowerSeries.isRestricted_one _))
  have hh1norm : PowerSeries.gaussNorm norm (Real.exp m) (h - 1) < 1 := by
    obtain ⟨t, ht⟩ := Restricted.gaussNorm_achieved' (Real.exp m) hc0.le
      (⟨h - 1, hsub_res⟩ : PowerSeries.Restricted K (Real.exp m))
    rw [show PowerSeries.gaussNorm norm (Real.exp m) (h - 1)
        = ‖PowerSeries.coeff t (h - 1)‖ * Real.exp m ^ t from ht.symm]
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · rw [_root_.map_sub, hh0, PowerSeries.coeff_one, if_pos rfl, sub_self, norm_zero,
        zero_mul]
      norm_num
    · have h2 : PowerSeries.coeff t (h - 1) = PowerSeries.coeff t h := by
        rw [_root_.map_sub, PowerSeries.coeff_one, if_neg htpos.ne', sub_zero]
      rw [h2]
      exact hhdom t htpos
  -- `|f − g| < |f|`, by Gauss multiplicativity
  set G : PowerSeries.Restricted K (Real.exp m) := Polynomial.toRestricted (Real.exp m) g
    with hGdef
  set F : PowerSeries.Restricted K (Real.exp m) := ⟨f, hconv⟩ with hFdef
  have hFGH : F = G * H := by
    apply Subtype.ext
    exact hfgh
  have hnorm_one : ‖(1 : PowerSeries.Restricted K (Real.exp m))‖ = 1 := by
    rw [← PowerSeries.Restricted.C_one (S := K) (Real.exp m), PowerSeries.Restricted.norm_C,
      norm_one]
  have hH1lt : ‖(H - 1 : PowerSeries.Restricted K (Real.exp m))‖ < 1 := by
    have h1 : (H - 1 : PowerSeries.Restricted K (Real.exp m)).1 = h - 1 := rfl
    rw [Restricted.norm_eq, h1]
    exact hh1norm
  have hHnorm : ‖H‖ = 1 := by
    have h2 : H = 1 + (H - 1) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hnorm_one]; exact (ne_of_lt hH1lt).symm), hnorm_one]
    exact max_eq_left hH1lt.le
  have hFne : F ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z : PowerSeries.Restricted K (Real.exp m) =>
      PowerSeries.coeff 0 z.1) h0
    dsimp only at h1
    rw [hf0, show ((0 : PowerSeries.Restricted K (Real.exp m))).1 = (0 : PowerSeries K)
      from rfl, map_zero] at h1
    exact one_ne_zero h1
  have hFpos : (0 : ℝ) < ‖F‖ := norm_pos_iff.mpr hFne
  have hGnorm : ‖G‖ = ‖F‖ := by
    rw [hFGH, norm_mul, hHnorm, mul_one]
  have hfg_lt : PowerSeries.gaussNorm norm (Real.exp m) (f - (g : PowerSeries K))
      < PowerSeries.gaussNorm norm (Real.exp m) f := by
    have h1 : F - G = G * (H - 1) := by rw [hFGH]; ring
    have h2 : ‖F - G‖ < ‖F‖ := by
      rw [h1, norm_mul]
      calc ‖G‖ * ‖H - 1‖ < ‖G‖ * 1 :=
            mul_lt_mul_of_pos_left hH1lt (by rw [hGnorm]; exact hFpos)
        _ = ‖F‖ := by rw [mul_one, hGnorm]
    have e1 : PowerSeries.gaussNorm norm (Real.exp m) (f - (g : PowerSeries K))
        = ‖F - G‖ := by
      have h3 : ((F - G : PowerSeries.Restricted K (Real.exp m))).1
          = f - (g : PowerSeries K) := rfl
      rw [Restricted.norm_eq, h3]
    have e2 : PowerSeries.gaussNorm norm (Real.exp m) f = ‖F‖ := by
      have h3 : (F : PowerSeries.Restricted K (Real.exp m)).1 = f := rfl
      rw [Restricted.norm_eq, h3]
    rw [e1, e2]
    exact h2
  -- the polygons agree at every index `≤ k`
  have hpoly : ∀ a, a ≤ k → newtonPolygon (coeffVal K (g : PowerSeries K)) a
      = newtonPolygon (coeffVal K f) a := by
    -- the chain of f-vertices below the k-th, with slopes at most `m`
    have hfchain : ∀ b a, a + b = k → ∃ (v₀ lv : ℕ) (v₁ μ : ℝ),
        newtonPolygon (coeffVal K f) a = some (.nextVertex v₀ v₁ lv μ) ∧ μ ≤ m := by
      intro b
      induction b with
      | zero =>
        intro a ha
        rw [Nat.add_zero] at ha
        subst ha
        exact ⟨j₀, l, j₁, m, hseg, le_rfl⟩
      | succ b ih =>
        intro a ha
        obtain ⟨v₀, lv, v₁, μ, hv, hμ⟩ := ih (a + 1) (by omega)
        obtain ⟨i₀, i₁, li, mi, hprev⟩ := nextStep_nextVertex' _ hv
        have hstep := nextStep_nextVertex'' _ hv hprev
        obtain ⟨q₀, q₁, hq⟩ := nextStep_nextVertex _ hprev
        exact ⟨i₀, li, i₁, mi, hprev,
          (slopes_increasing_nextVertex _ hq hstep).le.trans hμ⟩
    -- congruence certificates at any chain vertex
    have hcert : ∀ (b : ℕ), ∀ {v₀ : ℕ} {v₁ : ℝ} {u₀ lu : ℕ} {u₁ μ' : ℝ},
        newtonPolygon (coeffVal K f) b = some (.nextVertex u₀ u₁ lu μ') → μ' ≤ m →
        nextStep (coeffVal K f) v₀ v₁ = .nextVertex u₀ u₁ lu μ' →
        (∀ x ∈ slopeSet (coeffVal K (g : PowerSeries K)) v₀ v₁, μ' ≤ x) ∧
        achievingSet (coeffVal K (g : PowerSeries K)) v₀ v₁ μ'
          = achievingSet (coeffVal K f) v₀ v₁ μ' := by
      intro b v₀ v₁ u₀ lu u₁ μ' hu hμm hq
      obtain ⟨hu₀ne, hu₁val⟩ := coeffVal_eq_coe_iff K (nextVertex_j₁_eq _ hq)
      have hc'0 : (0 : ℝ) < Real.exp μ' := Real.exp_pos μ'
      have hc'le : Real.exp μ' ≤ Real.exp m := Real.exp_le_exp.mpr hμm
      haveI : StrongPos (fun _ : Unit ↦ Real.exp μ') := ⟨fun _ => hc'0⟩
      haveI : NormMulClass (PowerSeries.Restricted K (Real.exp μ')) :=
        MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ Real.exp μ')
      -- geometry of the step: `(v₀, v₁)` sits on the `u₀`-line
      have hvu : v₀ < u₀ := nextVertex_lt _ hq
      have hvuR : (0 : ℝ) < (u₀ : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast hvu)
      have hslq := nextVertex_slope_eq_sInf' _ hq
      rw [slopeReal_real] at hslq
      have hv₁ : u₁ = v₁ + μ' * ((u₀ : ℝ) - v₀) := by
        rw [eq_div_iff hvuR.ne'] at hslq
        linarith
      -- f-terms at radius `exp μ'` are dominated by the `u₀`-term `A`
      have hApos : 0 < ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ :=
        mul_pos (norm_pos_iff.mpr hu₀ne) (pow_pos hc'0 u₀)
      have hfle : ∀ t, ‖PowerSeries.coeff t f‖ * Real.exp μ' ^ t
          ≤ ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
        intro t
        by_cases hat : PowerSeries.coeff t f = 0
        · rw [hat, norm_zero, zero_mul]
          exact hApos.le
        · refine (term_le_term_iff' K hat hu₀ne hc'0 t u₀).mpr ?_
          rw [Real.log_exp]
          have h1 := vertex_line_le' K f hf0 b hu t hat
          rwa [hu₁val] at h1
      -- restrictedness at radius `exp μ'`
      have hfres : PowerSeries.IsRestricted (Real.exp μ') f :=
        isRestricted_of_le K f hc'0.le hc'le hconv
      have hgres : PowerSeries.IsRestricted (Real.exp μ') (g : PowerSeries K) :=
        Polynomial.IsRestricted _ g
      have hdres : PowerSeries.IsRestricted (Real.exp μ') (f - (g : PowerSeries K)) := by
        rw [sub_eq_add_neg]
        exact PowerSeries.isRestricted.add _ hfres (PowerSeries.isRestricted.neg _ hgres)
      have hhres' : PowerSeries.IsRestricted (Real.exp μ') h :=
        isRestricted_of_le K h hc'0.le hc'le hhres
      -- the global coefficient estimate at radius `exp μ'`
      set H' : PowerSeries.Restricted K (Real.exp μ') := ⟨h, hhres'⟩ with hH'def
      set F' : PowerSeries.Restricted K (Real.exp μ') := ⟨f, hfres⟩ with hF'def
      set G' : PowerSeries.Restricted K (Real.exp μ') :=
        Polynomial.toRestricted (Real.exp μ') g with hG'def
      have hH'1lt : ‖H' - 1‖ < 1 := by
        have h3 : (H' - 1).1 = h - 1 := rfl
        rw [Restricted.norm_eq, h3]
        exact lt_of_le_of_lt (gaussNorm_le_of_radius_le K hc'0.le hc'le hsub_res) hh1norm
      have hF'norm : ‖F'‖ = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
        refine le_antisymm ?_ ?_
        · rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
          exact ciSup_le hfle
        · rw [Restricted.norm_eq]
          exact PowerSeries.le_gaussNorm norm (Real.exp μ') f
            (Restricted.hasGaussNorm _ F') u₀
      have hE : ∀ t, ‖PowerSeries.coeff t f - PowerSeries.coeff t (g : PowerSeries K)‖ *
          Real.exp μ' ^ t
          < ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
        have hFGH' : F' = G' * H' := Subtype.ext hfgh
        have hnorm_one' : ‖(1 : PowerSeries.Restricted K (Real.exp μ'))‖ = 1 := by
          rw [← PowerSeries.Restricted.C_one (S := K) (Real.exp μ'),
            PowerSeries.Restricted.norm_C, norm_one]
        have hH'norm : ‖H'‖ = 1 := by
          have h8 : H' = 1 + (H' - 1) := by ring
          rw [h8, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
            (by rw [hnorm_one']; exact (ne_of_lt hH'1lt).symm), hnorm_one']
          exact max_eq_left hH'1lt.le
        have hG'norm : ‖G'‖ = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
          rw [← hF'norm, hFGH', norm_mul, hH'norm, mul_one]
        intro t
        have h3 : PowerSeries.coeff t f - PowerSeries.coeff t (g : PowerSeries K)
            = PowerSeries.coeff t (f - (g : PowerSeries K)) := (_root_.map_sub _ _ _).symm
        rw [h3]
        have h4 := PowerSeries.le_gaussNorm norm (Real.exp μ') (f - (g : PowerSeries K))
          (Restricted.hasGaussNorm _ (F' - G')) t
        refine lt_of_le_of_lt h4 ?_
        have h5 : PowerSeries.gaussNorm norm (Real.exp μ') (f - (g : PowerSeries K))
            = ‖F' - G'‖ := by
          have h6 : (F' - G').1 = f - (g : PowerSeries K) := rfl
          rw [Restricted.norm_eq, h6]
        rw [h5]
        have h7 : F' - G' = G' * (H' - 1) := by rw [hFGH']; ring
        calc ‖F' - G'‖ = ‖G'‖ * ‖H' - 1‖ := by rw [h7, norm_mul]
          _ < ‖G'‖ * 1 := by
              refine mul_lt_mul_of_pos_left hH'1lt ?_
              rw [hG'norm]
              exact hApos
          _ = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by rw [mul_one, hG'norm]
      -- (T1) nonzero g-coefficients lie on/above the line
      have hgle : ∀ t, ‖PowerSeries.coeff t (g : PowerSeries K)‖ * Real.exp μ' ^ t
          ≤ ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
        intro t
        have h3 : ‖PowerSeries.coeff t (g : PowerSeries K)‖
            ≤ max ‖PowerSeries.coeff t f‖
              ‖PowerSeries.coeff t f - PowerSeries.coeff t (g : PowerSeries K)‖ := by
          have h4 := IsUltrametricDist.norm_add_le_max (PowerSeries.coeff t f)
            (PowerSeries.coeff t (g : PowerSeries K) - PowerSeries.coeff t f)
          rw [add_sub_cancel] at h4
          rwa [norm_sub_rev] at h4
        calc ‖PowerSeries.coeff t (g : PowerSeries K)‖ * Real.exp μ' ^ t
            ≤ max ‖PowerSeries.coeff t f‖
                ‖PowerSeries.coeff t f - PowerSeries.coeff t (g : PowerSeries K)‖ *
              Real.exp μ' ^ t := by
              exact mul_le_mul_of_nonneg_right h3 (pow_pos hc'0 t).le
          _ = max (‖PowerSeries.coeff t f‖ * Real.exp μ' ^ t)
              (‖PowerSeries.coeff t f - PowerSeries.coeff t (g : PowerSeries K)‖ *
                Real.exp μ' ^ t) := by
              rw [max_mul_of_nonneg _ _ (pow_pos hc'0 t).le]
          _ ≤ ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ :=
              max_le (hfle t) (hE t).le
      -- the two certificates
      constructor
      · -- lower bound on the g-slope set
        rintro x ⟨t, ht, htfin, y, hy, hx⟩
        obtain ⟨hgt_ne, hyval⟩ := coeffVal_eq_coe_iff K hy
        have htR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast ht)
        rw [hx, slopeReal_real, le_div_iff₀ htR]
        -- from (T1): μ'(t − u₀) ≤ ν_g(t) − u₁
        have h3 := (term_le_term_iff' K hgt_ne hu₀ne hc'0 t u₀).mp (hgle t)
        rw [Real.log_exp] at h3
        rw [hyval]
        -- combine with the line through (v₀, v₁)
        rw [hu₁val] at hv₁
        linarith [h3, hv₁]
      · -- the achieving sets agree
        ext t
        simp only [achievingSet, Set.mem_setOf_eq]
        constructor
        · rintro ⟨ht, htfin, y, hy, hslope⟩
          obtain ⟨hgt_ne, hyval⟩ := coeffVal_eq_coe_iff K hy
          have htR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast ht)
          rw [slopeReal_real, eq_comm, div_eq_iff htR.ne'] at hslope
          -- `t` is on the line: the g-term equals `A`
          have hgeq_term : ‖PowerSeries.coeff t (g : PowerSeries K)‖ * Real.exp μ' ^ t
              = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
            rw [term_eq_exp K hgt_ne μ' t, term_eq_exp K hu₀ne μ' u₀, Real.exp_eq_exp]
            have h4 : Real.log ‖PowerSeries.coeff t (g : PowerSeries K)‖ = - y := by
              rw [hyval]; ring
            have h5 : Real.log ‖PowerSeries.coeff u₀ f‖ = - u₁ := by
              rw [hu₁val]; ring
            rw [h4, h5]
            linarith [hslope, hv₁]
          -- the f-coefficient has the same norm (isosceles)
          have hdiff_lt : ‖PowerSeries.coeff t f -
              PowerSeries.coeff t (g : PowerSeries K)‖ <
              ‖PowerSeries.coeff t (g : PowerSeries K)‖ := by
            have h4 := hE t
            rw [← hgeq_term] at h4
            exact lt_of_mul_lt_mul_right h4 (pow_pos hc'0 t).le
          have hfnorm : ‖PowerSeries.coeff t f‖
              = ‖PowerSeries.coeff t (g : PowerSeries K)‖ := by
            have h4 : PowerSeries.coeff t f = PowerSeries.coeff t (g : PowerSeries K) +
                (PowerSeries.coeff t f - PowerSeries.coeff t (g : PowerSeries K)) := by ring
            rw [h4, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
              (ne_of_gt hdiff_lt), max_eq_left hdiff_lt.le]
          have hft_ne : PowerSeries.coeff t f ≠ 0 := by
            intro h0
            rw [h0, norm_zero] at hfnorm
            exact (norm_pos_iff.mpr hgt_ne).ne' hfnorm.symm
          refine ⟨ht, ?_, - Real.log ‖PowerSeries.coeff t f‖, ?_, ?_⟩
          · show coeffVal K f t ≠ ⊤
            simp only [coeffVal]
            rw [ne_eq, addVal_eq_top_iff]
            exact hft_ne
          · simp only [coeffVal]
            rw [addVal_of_ne_zero K hft_ne]
          · rw [slopeReal_real, eq_comm, div_eq_iff htR.ne', hfnorm]
            rw [hyval] at hslope
            linarith [hslope]
        · rintro ⟨ht, htfin, y, hy, hslope⟩
          obtain ⟨hft_ne, hyval⟩ := coeffVal_eq_coe_iff K hy
          have htR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast ht)
          rw [slopeReal_real, eq_comm, div_eq_iff htR.ne'] at hslope
          have hfeq_term : ‖PowerSeries.coeff t f‖ * Real.exp μ' ^ t
              = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
            rw [term_eq_exp K hft_ne μ' t, term_eq_exp K hu₀ne μ' u₀, Real.exp_eq_exp]
            have h4 : Real.log ‖PowerSeries.coeff t f‖ = - y := by
              rw [hyval]; ring
            have h5 : Real.log ‖PowerSeries.coeff u₀ f‖ = - u₁ := by
              rw [hu₁val]; ring
            rw [h4, h5]
            linarith [hslope, hv₁]
          have hdiff_lt : ‖PowerSeries.coeff t f -
              PowerSeries.coeff t (g : PowerSeries K)‖ < ‖PowerSeries.coeff t f‖ := by
            have h4 := hE t
            rw [← hfeq_term] at h4
            exact lt_of_mul_lt_mul_right h4 (pow_pos hc'0 t).le
          have hgnorm : ‖PowerSeries.coeff t (g : PowerSeries K)‖
              = ‖PowerSeries.coeff t f‖ := by
            have h4 : PowerSeries.coeff t (g : PowerSeries K) = PowerSeries.coeff t f -
                (PowerSeries.coeff t f - PowerSeries.coeff t (g : PowerSeries K)) := by ring
            rw [h4, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
              (by rw [norm_neg]; exact ne_of_gt hdiff_lt), norm_neg,
              max_eq_left hdiff_lt.le]
          have hgt_ne : PowerSeries.coeff t (g : PowerSeries K) ≠ 0 := by
            intro h0
            rw [h0, norm_zero] at hgnorm
            exact (norm_pos_iff.mpr hft_ne).ne' hgnorm.symm
          refine ⟨ht, ?_, - Real.log ‖PowerSeries.coeff t (g : PowerSeries K)‖, ?_, ?_⟩
          · show coeffVal K (g : PowerSeries K) t ≠ ⊤
            simp only [coeffVal]
            rw [ne_eq, addVal_eq_top_iff]
            exact hgt_ne
          · simp only [coeffVal]
            rw [addVal_of_ne_zero K hgt_ne]
          · rw [slopeReal_real, eq_comm, div_eq_iff htR.ne', hgnorm]
            rw [hyval] at hslope
            linarith [hslope]
    -- upward induction along the polygon
    intro a
    induction a with
    | zero =>
      intro _
      obtain ⟨v₀, lv, v₁, μ, hv, hμ⟩ := hfchain k 0 (by omega)
      have hg0' : PowerSeries.coeff 0 (g : PowerSeries K) = 1 := by
        rw [Polynomial.coeff_coe]
        exact hg0
      have hstep0 : nextStep (coeffVal K f) 0 0 = .nextVertex v₀ v₁ lv μ :=
        Option.some_inj.mp ((newtonPolygon_zero_eq K f hf0).symm.trans hv)
      obtain ⟨hlb, hach⟩ := hcert 0 hv hμ hstep0
      rw [newtonPolygon_zero_eq K _ hg0', newtonPolygon_zero_eq K f hf0, hstep0]
      exact congrArg _ (nextStep_congr hstep0 hlb hach)
    | succ a ih =>
      intro ha
      have hprev_eq := ih (by omega)
      obtain ⟨v₀, lv, v₁, μ, hv, hμ⟩ := hfchain (k - a) a (by omega)
      obtain ⟨u₀, lu, u₁, μ', hu, hμ'⟩ := hfchain (k - (a + 1)) (a + 1) (by omega)
      have hstep : nextStep (coeffVal K f) v₀ v₁ = .nextVertex u₀ u₁ lu μ' :=
        nextStep_nextVertex'' _ hu hv
      obtain ⟨hlb, hach⟩ := hcert (a + 1) hu hμ' hstep
      rw [newtonPolygon_succ_eq (hprev_eq.trans hv), newtonPolygon_succ_eq hv, hstep]
      exact congrArg _ (nextStep_congr hstep hlb hach)
  exact ⟨g, h, hfgh, hgdeg, hg0, hfg_lt, hhres, hh1norm, hpoly⟩

omit [IsUltrametricDist K] in
/-- **A polynomial whose `s`-th term strictly dominates at the point's own radius is nonzero
there.**  Between consecutive slope spheres the polygon-vertex coefficient dominates strictly,
so a polynomial has no zeros strictly between the spheres of consecutive slope radii. -/
private theorem aeval_ne_zero_of_dominant_at {L : Type*} [Field L] [Algebra K L]
    (w : Valuation L NNReal) (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊)
    (g : Polynomial K) {s : ℕ} (hgs : g.coeff s ≠ 0) {x : L} (hx0 : w x ≠ 0)
    (hdom : ∀ t, t ≠ s → ‖g.coeff t‖ * (w x : ℝ) ^ t < ‖g.coeff s‖ * (w x : ℝ) ^ s) :
    Polynomial.aeval x g ≠ 0 := by
  have htop_ne : (‖g.coeff s‖₊ * w x ^ s : NNReal) ≠ 0 :=
    mul_ne_zero (by simpa using hgs) (pow_ne_zero _ hx0)
  have hsub : w (Polynomial.aeval x g - algebraMap K L (g.coeff s) * x ^ s)
      < ‖g.coeff s‖₊ * w x ^ s := by
    have h1 : Polynomial.aeval x g - algebraMap K L (g.coeff s) * x ^ s
        = Polynomial.aeval x (g - Polynomial.monomial s (g.coeff s)) := by
      rw [_root_.map_sub, Polynomial.aeval_monomial]
    rw [h1, Polynomial.aeval_eq_sum_range]
    refine w.map_sum_lt htop_ne fun k _ => ?_
    have hcm : (g - Polynomial.monomial s (g.coeff s)).coeff k
        = if s = k then 0 else g.coeff k := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_monomial]
      split_ifs with h
      · subst h
        exact sub_self _
      · rw [sub_zero]
    rcases eq_or_ne s k with rfl | hsk
    · rw [hcm, if_pos rfl, zero_smul, w.map_zero]
      exact pos_iff_ne_zero.mpr htop_ne
    · rw [hcm, if_neg hsk]
      by_cases hgk : g.coeff k = 0
      · rw [hgk, zero_smul, w.map_zero]
        exact pos_iff_ne_zero.mpr htop_ne
      · rw [Algebra.smul_def, w.map_mul, w.map_pow, hw, ← NNReal.coe_lt_coe]
        push_cast
        exact hdom k (Ne.symm hsk)
  intro h0
  rw [h0, zero_sub, w.map_neg, w.map_mul, w.map_pow, hw] at hsub
  exact lt_irrefl _ hsub

set_option maxHeartbeats 1000000 in
/-- **Blueprint Corollary 5.14, counting half.**  In the closed ball of radius `exp m` the
zeros of `f` are exactly the roots of the polynomial factor `g` of 5.13 (any `g` with the
5.13 properties).  Zero counts *with multiplicity* then transfer to `g`: combined with
`card_roots_slope` (5.11) for `g` — whose polygon is that of `f` over `[0, j₀]` by 5.13(5) —
this gives the blueprint's "`f` has exactly `i_j` zeros of absolute value `exp m_j` for each
slope `m_j`, and no others in the ball". -/
theorem hasSum_zero_iff_aeval_eq_zero (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {k j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K f) k = some (.nextVertex j₀ j₁ l m))
    (hconv : PowerSeries.IsRestricted (Real.exp m) f)
    (g : Polynomial K) (h : PowerSeries K)
    (hfeq : f = (g : PowerSeries K) * h)
    (hdeg : g.natDegree = j₀)
    (hhconv : PowerSeries.IsRestricted (Real.exp m) h)
    (hh1 : PowerSeries.gaussNorm norm (Real.exp m) (h - 1) < 1)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ ≤ Real.exp m) :
    HasSum (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) 0 ↔
      Polynomial.aeval x g = 0 := by
  classical
  haveI : NonarchimedeanRing L :=
    { toIsTopologicalRing := inferInstance
      is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
  -- the factor series converge on the ball
  have hsh : Summable (fun j => algebraMap K L (PowerSeries.coeff j h) * x ^ j) :=
    summable_of_isRestricted K hhconv hL hx
  have hG : HasSum (fun i => algebraMap K L (g.coeff i) * x ^ i) (Polynomial.aeval x g) := by
    have h1 : ∀ i ∉ Finset.range (g.natDegree + 1),
        algebraMap K L (g.coeff i) * x ^ i = 0 := by
      intro i hi
      rw [Finset.mem_range, not_lt] at hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul]
    have h2 : HasSum (fun i => algebraMap K L (g.coeff i) * x ^ i)
        (∑ i ∈ Finset.range (g.natDegree + 1), algebraMap K L (g.coeff i) * x ^ i) :=
      hasSum_sum_of_ne_finset_zero h1
    have h3 : ∑ i ∈ Finset.range (g.natDegree + 1), algebraMap K L (g.coeff i) * x ^ i
        = Polynomial.aeval x g := by
      rw [Polynomial.aeval_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm
    rwa [h3] at h2
  set H : L := ∑' j, algebraMap K L (PowerSeries.coeff j h) * x ^ j with hHdef
  -- `H` is a unit: `|H − 1| < 1` since every term of `h − 1` is small on the ball
  have hs1res : PowerSeries.IsRestricted (Real.exp m) (h - 1) := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add _ hhconv
      (PowerSeries.isRestricted.neg _ (PowerSeries.isRestricted_one _))
  have hone : HasSum
      (fun j => algebraMap K L (PowerSeries.coeff j (1 : PowerSeries K)) * x ^ j) 1 := by
    have h1 : ∀ j ≠ 0, algebraMap K L (PowerSeries.coeff j (1 : PowerSeries K)) * x ^ j = 0 := by
      intro j hj
      rw [PowerSeries.coeff_one, if_neg hj, map_zero, zero_mul]
    have h2 : HasSum
        (fun j : ℕ => algebraMap K L (PowerSeries.coeff j (1 : PowerSeries K)) * x ^ j)
        (algebraMap K L (PowerSeries.coeff 0 (1 : PowerSeries K)) * x ^ 0) :=
      hasSum_single 0 h1
    simpa [PowerSeries.coeff_one] using h2
  have hsub : HasSum (fun j => algebraMap K L (PowerSeries.coeff j (h - 1)) * x ^ j)
      (H - 1) := by
    have h1 : (fun j => algebraMap K L (PowerSeries.coeff j (h - 1)) * x ^ j)
        = fun j => algebraMap K L (PowerSeries.coeff j h) * x ^ j
          - algebraMap K L (PowerSeries.coeff j (1 : PowerSeries K)) * x ^ j := by
      funext j
      rw [_root_.map_sub, _root_.map_sub, sub_mul]
    rw [h1]
    exact hsh.hasSum.sub hone
  have hH1lt : ‖H - 1‖ < 1 := by
    refine lt_of_le_of_lt (le_of_tendsto (continuous_norm.tendsto _ |>.comp hsub) ?_) hh1
    refine Filter.Eventually.of_forall fun s => ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ?_ fun j _ => ?_
    · exact le_trans (by positivity) (PowerSeries.le_gaussNorm norm (Real.exp m) (h - 1)
        (Restricted.hasGaussNorm _
          (⟨h - 1, hs1res⟩ : PowerSeries.Restricted K (Real.exp m))) 0)
    · rw [norm_mul, norm_pow, hL]
      calc ‖PowerSeries.coeff j (h - 1)‖ * ‖x‖ ^ j
          ≤ ‖PowerSeries.coeff j (h - 1)‖ * Real.exp m ^ j := by gcongr
        _ ≤ _ := PowerSeries.le_gaussNorm norm (Real.exp m) (h - 1)
            (Restricted.hasGaussNorm _
              (⟨h - 1, hs1res⟩ : PowerSeries.Restricted K (Real.exp m))) j
  have hHne : H ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg, norm_one] at hH1lt
    exact lt_irrefl 1 hH1lt
  -- the Cauchy product identity for the coefficients of `f`
  have hterm : ∀ t, algebraMap K L (PowerSeries.coeff t f) * x ^ t
      = ∑ kl ∈ Finset.antidiagonal t,
        (algebraMap K L (g.coeff kl.1) * x ^ kl.1) *
        (algebraMap K L (PowerSeries.coeff kl.2 h) * x ^ kl.2) := by
    intro t
    rw [hfeq, PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.mem_antidiagonal] at hkl
    rw [_root_.map_mul, Polynomial.coeff_coe, ← hkl, pow_add]
    ring
  have hjoint : Summable (fun p : ℕ × ℕ =>
      (algebraMap K L (g.coeff p.1) * x ^ p.1) *
      (algebraMap K L (PowerSeries.coeff p.2 h) * x ^ p.2)) :=
    hG.summable.mul_of_nonarchimedean hsh
  have hsF : Summable (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) :=
    summable_of_isRestricted K hconv hL hx
  have hprod : (∑' t, algebraMap K L (PowerSeries.coeff t f) * x ^ t)
      = Polynomial.aeval x g * H := by
    rw [hHdef, ← hG.tsum_eq,
      Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hG.summable hsh hjoint]
    exact tsum_congr hterm
  constructor
  · intro hzero
    have h0 : Polynomial.aeval x g * H = 0 := by
      rw [← hprod, hzero.tsum_eq]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 hHne
  · intro hzero
    have h0 : (∑' t, algebraMap K L (PowerSeries.coeff t f) * x ^ t) = 0 := by
      rw [hprod, hzero, zero_mul]
    rw [← h0]
    exact hsF.hasSum
/-- **Blueprint Corollary 5.14, "no other zeros" half.**  Let `L/K` be a *complete*
ultrametric extension (the blueprint's `ℂ_p`) and suppose `f` converges on the closed ball of
radius `exp m`, the `k`-th slope.  Then every zero of `f` in that ball lies on a sphere of
radius `exp μ` for one of the first `k + 1` slopes `μ`. -/
theorem norm_eq_exp_slope_of_hasSum_zero [CompleteSpace K] (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {k j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal K f) k = some (.nextVertex j₀ j₁ l m))
    (hconv : PowerSeries.IsRestricted (Real.exp m) f)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ ≤ Real.exp m)
    -- x is a zero
    (hzero : HasSum (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) 0) :
    ∃ (a i₀ l' : ℕ) (i₁ μ : ℝ), a ≤ k ∧
      newtonPolygon (coeffVal K f) a = some (.nextVertex i₀ i₁ l' μ) ∧
      ‖x‖ = Real.exp μ := by
  classical
  -- the Weierstrass factorisation along the polygon, and `x` as a root of its polynomial part
  obtain ⟨g, h, hfeq, hdeg, hg0, hfg, hhconv, hh1, hpoly⟩ :=
    exists_weierstrass_factorisation K f hf0 hseg hconv
  have hgzero : Polynomial.aeval x g = 0 :=
    (hasSum_zero_iff_aeval_eq_zero K f hf0 hseg hconv g h hfeq hdeg hhconv hh1 hL hx).mp hzero
  -- the norm of `L` as a valuation
  set w : Valuation L NNReal :=
    { toFun := fun y => ‖y‖₊
      map_zero' := nnnorm_zero
      map_one' := nnnorm_one
      map_mul' := fun a b => nnnorm_mul a b
      map_add_le_max' := fun a b => IsUltrametricDist.nnnorm_add_le_max a b } with hwdef
  have hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊ := fun a =>
    NNReal.coe_injective (by simpa using hL a)
  have hwx : (w x : ℝ) = ‖x‖ := rfl
  -- the chain of vertices of `f` below the `k`-th
  have hfchain : ∀ b a, a + b = k → ∃ (v₀ lv : ℕ) (v₁ μ : ℝ),
      newtonPolygon (coeffVal K f) a = some (.nextVertex v₀ v₁ lv μ) := by
    intro b
    induction b with
    | zero =>
      intro a ha
      rw [Nat.add_zero] at ha
      subst ha
      exact ⟨j₀, l, j₁, m, hseg⟩
    | succ b ih =>
      intro a ha
      obtain ⟨v₀, lv, v₁, μ, hv⟩ := ih (a + 1) (by omega)
      obtain ⟨i₀, i₁, li, mi, hprev⟩ := nextStep_nextVertex' _ hv
      exact ⟨i₀, li, i₁, mi, hprev⟩
  by_contra hnot
  push Not at hnot
  -- the middle-window contradiction: between two consecutive slope radii the vertex dominates
  have hmid : ∀ a, a + 1 ≤ k → ∀ {v₀ lv : ℕ} {v₁ μ : ℝ},
      newtonPolygon (coeffVal K f) a = some (.nextVertex v₀ v₁ lv μ) →
      Real.exp μ < ‖x‖ → ∀ {u₀ lu : ℕ} {u₁ μ' : ℝ},
      newtonPolygon (coeffVal K f) (a + 1) = some (.nextVertex u₀ u₁ lu μ') →
      ‖x‖ < Real.exp μ' → False := by
    intro a ha v₀ lv v₁ μ hv hxgt u₀ lu u₁ μ' hu hxlt
    -- transfer both vertices to the polygon of `g`
    have hgv : newtonPolygon (coeffVal K (g : PowerSeries K)) a
        = some (.nextVertex v₀ v₁ lv μ) := (hpoly a (by omega)).trans hv
    have hgu : newtonPolygon (coeffVal K (g : PowerSeries K)) (a + 1)
        = some (.nextVertex u₀ u₁ lu μ') := (hpoly (a + 1) ha).trans hu
    -- data of the vertex `(v₀, v₁)` on `g`
    obtain ⟨p₀, p₁, hpv⟩ := nextStep_nextVertex _ hgv
    obtain ⟨hgV, -, hyval⟩ := nextVertex_coe_data K g hpv
    -- the step from `(v₀, v₁)` to `(u₀, u₁)` on `g`, and the line relation
    have hstep : nextStep (coeffVal K (g : PowerSeries K)) v₀ v₁
        = .nextVertex u₀ u₁ lu μ' := nextStep_nextVertex'' _ hgu hgv
    have hvu : v₀ < u₀ := nextVertex_lt _ hstep
    have hvuR : (0 : ℝ) < (u₀ : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast hvu)
    have hslope := nextVertex_slope_eq_sInf' _ hstep
    rw [slopeReal_real] at hslope
    have hu₁ : u₁ = v₁ + μ' * ((u₀ : ℝ) - v₀) := by
      rw [eq_div_iff hvuR.ne'] at hslope
      linarith
    -- the point's radius sits strictly between the slope radii
    have hr0 : (0 : ℝ) < ‖x‖ := lt_trans (Real.exp_pos μ) hxgt
    have hlogl : μ < Real.log ‖x‖ := (Real.lt_log_iff_exp_lt hr0).mpr hxgt
    have hlogr : Real.log ‖x‖ < μ' := (Real.log_lt_iff_lt_exp hr0).mpr hxlt
    -- strict dominance of the `v₀`-th coefficient of `g` at radius `‖x‖`
    have hdom : ∀ t, t ≠ v₀ →
        ‖g.coeff t‖ * (w x : ℝ) ^ t < ‖g.coeff v₀‖ * (w x : ℝ) ^ v₀ := by
      intro t ht
      rw [hwx]
      by_cases hgt : g.coeff t = 0
      · rw [hgt, norm_zero, zero_mul]
        exact mul_pos (norm_pos_iff.mpr hgV) (pow_pos hr0 v₀)
      · rw [show ‖x‖ = Real.exp (Real.log ‖x‖) from (Real.exp_log hr0).symm]
        refine (term_lt_term_iff' K hgt hgV (Real.exp_pos _) t v₀).mpr ?_
        rw [Real.log_exp, ← hyval]
        rcases Nat.lt_or_ge t v₀ with htv | htv
        · -- below the vertex: the `a`-th line with slope `μ < log ‖x‖`
          have hline := vertex_line_le K g hg0 a hgv t hgt
          have htvR : ((t : ℝ) - v₀) < 0 := sub_neg.mpr (by exact_mod_cast htv)
          nlinarith [hline, mul_lt_mul_of_neg_right hlogl htvR]
        · -- above the vertex: the `(a+1)`-th line with slope `μ' > log ‖x‖`
          have htv' : v₀ < t := lt_of_le_of_ne htv (Ne.symm ht)
          have hline := vertex_line_le K g hg0 (a + 1) hgu t hgt
          have htvR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast htv')
          have h2 : μ' * ((t : ℝ) - v₀) ≤ - Real.log ‖g.coeff t‖ - v₁ := by
            nlinarith [hline, hu₁]
          nlinarith [h2, mul_lt_mul_of_pos_right hlogr htvR]
    have hwx0 : w x ≠ 0 := by
      intro h0
      have h1 : (w x : ℝ) = 0 := by rw [h0]; rfl
      rw [hwx] at h1
      exact hr0.ne' h1
    exact aeval_ne_zero_of_dominant_at K w hw g hgV hwx0 hdom hgzero
  -- walk down the polygon to locate the window containing `‖x‖`
  have hstepdown : ∀ b a, a + b = k →
      (∃ (v₀ lv : ℕ) (v₁ μ : ℝ),
        newtonPolygon (coeffVal K f) a = some (.nextVertex v₀ v₁ lv μ) ∧
        Real.exp μ < ‖x‖) → False := by
    intro b
    induction b with
    | zero =>
      rintro a ha ⟨v₀, lv, v₁, μ, hv, hxgt⟩
      rw [Nat.add_zero] at ha
      subst ha
      rw [hseg] at hv
      have h2 := Option.some_inj.mp hv
      injection h2 with h3 h4 h5 h6
      subst h6
      exact absurd hx (not_le.mpr hxgt)
    | succ b ih =>
      rintro a ha ⟨v₀, lv, v₁, μ, hv, hxgt⟩
      obtain ⟨u₀, lu, u₁, μ', hu⟩ := hfchain (k - (a + 1)) (a + 1) (by omega)
      rcases lt_trichotomy ‖x‖ (Real.exp μ') with hlt | heq | hgt
      · exact hmid a (by omega) hv hxgt hu hlt
      · exact hnot (a + 1) u₀ lu u₁ μ' (by omega) hu heq
      · exact ih (a + 1) (by omega) ⟨u₀, lu, u₁, μ', hu, hgt⟩
  -- the first window: below the first slope the constant term of `g` dominates
  obtain ⟨V₀, lv, y₀, μ₀, hv0⟩ := hfchain k 0 (by omega)
  rcases lt_trichotomy ‖x‖ (Real.exp μ₀) with hlt | heq | hgt
  · have hgv : newtonPolygon (coeffVal K (g : PowerSeries K)) 0
        = some (.nextVertex V₀ y₀ lv μ₀) := (hpoly 0 (by omega)).trans hv0
    have hg0' : PowerSeries.coeff 0 (g : PowerSeries K) = 1 := by
      rw [Polynomial.coeff_coe]
      exact hg0
    have hv0g : nextStep (coeffVal K (g : PowerSeries K)) 0 0
        = .nextVertex V₀ y₀ lv μ₀ :=
      Option.some_inj.mp ((newtonPolygon_zero_eq K _ hg0').symm.trans hgv)
    have hV₀pos : 0 < V₀ := nextVertex_lt _ hv0g
    have hV₀R : (0 : ℝ) < (V₀ : ℝ) := by exact_mod_cast hV₀pos
    have hslope := nextVertex_slope_eq_sInf' _ hv0g
    rw [slopeReal_real] at hslope
    have hy₀ : y₀ = μ₀ * V₀ := by
      rw [eq_div_iff (by push_cast; simpa using hV₀R.ne')] at hslope
      push_cast at hslope
      linarith
    have hg0ne : g.coeff 0 ≠ 0 := by
      rw [hg0]
      exact one_ne_zero
    have hdom : ∀ t, 1 ≤ t → ‖g.coeff t‖ * Real.exp μ₀ ^ t ≤ ‖g.coeff 0‖ := by
      intro t ht
      by_cases hgt : g.coeff t = 0
      · rw [hgt, norm_zero, zero_mul, hg0, norm_one]
        norm_num
      · have h1 := (term_le_term_iff' K hgt hg0ne (Real.exp_pos μ₀) t 0).mpr ?_
        · simpa using h1
        · rw [Real.log_exp, hg0, norm_one, Real.log_one]
          have hline := vertex_line_le K g hg0 0 hgv t hgt
          push_cast
          nlinarith [hline, hy₀]
    exact aeval_ne_zero_of_dominant_lt K w hw g hg0ne hdom
      (by rw [hwx]; exact hlt) hgzero
  · exact hnot 0 V₀ lv y₀ μ₀ (by omega) hv0 heq
  · exact hstepdown k 0 (by omega) ⟨V₀, lv, y₀, μ₀, hv0, hgt⟩


end NewtonPolygon
