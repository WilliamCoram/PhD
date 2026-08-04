/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import PhD.NewtonPolygons.CoeffVal
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Complete
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The radius of convergence of a power series and its Newton polygon (blueprint §5.12)

Refactored from `PhD/Test/test.lean` lines 1969–2550 onto the `negLogNorm`/`coeffVal` valuation
bridge and the `ForMathlib` restricted-power-series API; all proofs are complete.

Two layers:

* **Infrastructure** ([T] 1969–2099): the correspondence between the project's restricted-ness
  predicate `PowerSeries.IsRestricted c f` (cofinite decay of `‖aₖ‖ cᵏ`) and genuine
  convergence of the series `∑ aₖ xᵏ` on closed balls of a complete ultrametric extension
  `L/K`, together with the honest radius of convergence `radiusOfConvergence L f` — the
  supremum of the norms of points of `L` at which the series converges.  The radius is
  *relative to `L`* of necessity: over `L = ℚ_p` the attainable norms are only powers of `p`,
  so the supremum can undershoot the analytic radius; statements needing points arbitrarily
  close to a prescribed radius carry a norm-density hypothesis `hdense`.

* **§5.12** ("the radius of convergence is `exp (sup of slopes)`"), in radius form as its two
  inequality halves (`ofReal_exp_le_radiusOfConvergence`, needing `hdense`, and
  `radiusOfConvergence_le_ofReal_exp`, which does not), each derived from a per-radius
  workhorse about restricted-ness (`isRestricted_of_lt_slope`, `not_isRestricted_of_slopes_le`
  — the polygon-analytic content).  Sharpness genuinely needs infinitely many nonzero
  coefficients: for a polynomial the radius is `∞` while the slopes are bounded.

The public statements phrase the polygon data in textbook form on the constructed polygon:
"`μ` is the `a`-th slope" is `(newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = μ`, and
"every slope is `≤ m`" quantifies that equation over all honest indices (slopes past the
support are the junk value `⊤`, so they impose nothing).  The private lemmas keep the raw
`Construction` form `newtonPolygon (coeffVal f) a = some s`.
-/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-! ### The radius of convergence, and convergence on closed balls -/

omit [IsUltrametricDist K] in
/-- Restricted-ness is monotone in the radius.  Blueprint §5.12 infrastructure;
[T] `test.lean:1973`. -/
theorem isRestricted_of_le (f : PowerSeries K) {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c ≤ c')
    (h : PowerSeries.IsRestricted c' f) : PowerSeries.IsRestricted c f := by
  rw [PowerSeries.isRestricted_iff] at h ⊢
  refine squeeze_zero (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg hc k))
    (fun k => ?_) h
  gcongr

omit [IsUltrametricDist K] in
/-- **A restricted power series converges on the closed ball**: for `f` restricted of
parameter `c`, the series `∑ aₖ xᵏ` genuinely converges at every point of norm `≤ c` of every
complete ultrametric extension of `K`.  Blueprint §5.12 infrastructure; [T] `test.lean:1985`. -/
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
`summable_of_isRestricted`, which handles the rest of the ball.)  Blueprint §5.12
infrastructure; [T] `test.lean:2003`. -/
theorem isRestricted_iff_summable {f : PowerSeries K} {c : ℝ}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ = c) :
    PowerSeries.IsRestricted c f ↔
      Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k) := by
  refine ⟨fun hf => summable_of_isRestricted hf hL hx.le, fun hs => ?_⟩
  rw [PowerSeries.isRestricted_iff]
  have h0 := hs.tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero] at h0
  refine h0.congr fun k => ?_
  rw [norm_mul, norm_pow, hL, hx]

omit [IsUltrametricDist K] in
/-- Genuine convergence at a point makes the series restricted at that point's norm.
Blueprint §5.12 infrastructure; [T] `test.lean:2018`. -/
theorem isRestricted_of_summable {f : PowerSeries K}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (h : Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k)) :
    PowerSeries.IsRestricted ‖x‖ f :=
  (isRestricted_iff_summable hL rfl).mpr h

omit [IsUltrametricDist K] in
/-- **The radius of convergence** of `f` over a complete ultrametric extension `L` of `K`:
the supremum of the norms of the points of `L` at which the series `∑ aₖ xᵏ` genuinely
converges.  Relative to `L` of necessity: over `L = ℚ_p` the attainable norms are only the
powers of `p`, so this supremum can undershoot the analytic radius; over a norm-dense
extension (`ℂ_p`) it is the blueprint's radius of convergence.  Blueprint §5.12;
[T] `test.lean:2031`. -/
noncomputable def radiusOfConvergence (L : Type*) [NontriviallyNormedField L]
    [IsUltrametricDist L] [CompleteSpace L] [Algebra K L] (f : PowerSeries K) : ENNReal :=
  ⨆ (x : L) (_ : Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k)),
    (‖x‖₊ : ENNReal)

omit [IsUltrametricDist K] in
/-- Points of convergence bound the radius of convergence from below.  Blueprint §5.12
infrastructure; [T] `test.lean:2038`. -/
theorem le_radiusOfConvergence_of_summable {f : PowerSeries K}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L]
    {x : L} (h : Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k)) :
    (‖x‖₊ : ENNReal) ≤ radiusOfConvergence L f :=
  le_iSup_of_le x (le_iSup_of_le h le_rfl)

omit [IsUltrametricDist K] in
/-- **Points strictly inside the radius of convergence converge.**  (At the boundary both
behaviours occur — `∑ xⁿ` diverges on its boundary sphere while `∑ pⁿ² xⁿ` converges on
its — so `<` cannot be improved to `≤`.)  Blueprint §5.12 infrastructure;
[T] `test.lean:2051`. -/
theorem summable_of_lt_radiusOfConvergence {f : PowerSeries K}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (h : (‖x‖₊ : ENNReal) < radiusOfConvergence L f) :
    Summable (fun k => algebraMap K L (PowerSeries.coeff k f) * x ^ k) := by
  simp only [radiusOfConvergence, lt_iSup_iff] at h
  obtain ⟨y, hy, hlt⟩ := h
  exact summable_of_isRestricted (isRestricted_of_summable hL hy) hL (by exact_mod_cast hlt.le)

omit [IsUltrametricDist K] in
/-- Radii strictly below the radius of convergence are restricted.  Blueprint §5.12
infrastructure; [T] `test.lean:2065`. -/
theorem isRestricted_of_lt_radiusOfConvergence {f : PowerSeries K} {c : ℝ} (hc : 0 ≤ c)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (h : ENNReal.ofReal c < radiusOfConvergence L f) :
    PowerSeries.IsRestricted c f := by
  simp only [radiusOfConvergence, lt_iSup_iff] at h
  obtain ⟨y, hy, hlt⟩ := h
  have hcy : c < ‖y‖ := by simpa using (ENNReal.ofReal_lt_coe_iff hc).mp hlt
  exact isRestricted_of_le f hc hcy.le (isRestricted_of_summable hL hy)

omit [IsUltrametricDist K] in
/-- Over an extension with **dense norms**, restricted radii bound the radius of convergence
from below.  Some density is necessary: over `L = ℚ_p` there are no points with norm strictly
between consecutive powers of `p`.  Blueprint §5.12 infrastructure; [T] `test.lean:2085`. -/
theorem le_radiusOfConvergence_of_isRestricted {f : PowerSeries K} {c : ℝ}
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (hdense : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a < b → ∃ x : L, a < ‖x‖ ∧ ‖x‖ < b)
    (h : PowerSeries.IsRestricted c f) :
    ENNReal.ofReal c ≤ radiusOfConvergence L f := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨x, hx1, hx2⟩ := hdense r.coe_nonneg (ENNReal.coe_lt_ofReal.mp hr)
  have hsx := summable_of_isRestricted h hL hx2.le
  calc (r : ENNReal) ≤ (‖x‖₊ : ENNReal) := by exact_mod_cast hx1.le
    _ ≤ _ := le_radiusOfConvergence_of_summable hsx

/-! ### 5.12: the radius of convergence off the polygon -/

/-! #### Bridging helpers: the algorithm, the valuation sequence and the packaged polygon -/

/-- With `Γ = ℝ` the algebra map is the identity, so `slopeReal` is the usual difference
quotient.  [T] `test.lean:142`. -/
private lemma slopeReal_real (x₀ x₁ : ℕ) (y₀ y₁ : ℝ) :
    slopeReal x₀ x₁ y₀ y₁ = (y₁ - y₀) / ((x₁ : ℝ) - x₀) := by
  simp [slopeReal, Algebra.algebraMap_self]

omit [IsUltrametricDist K] in
/-- Data of a finite point of the coefficient-valuation sequence.  [T] `test.lean:2538`. -/
private lemma coeffVal_eq_coe {f : PowerSeries K} {k : ℕ} {y : ℝ}
    (h : coeffVal f k = ((y : ℝ) : WithTop ℝ)) :
    PowerSeries.coeff k f ≠ 0 ∧ y = -Real.log ‖PowerSeries.coeff k f‖ := by
  have hak : PowerSeries.coeff k f ≠ 0 := fun h0 =>
    WithTop.coe_ne_top (h.symm.trans (coeffVal_eq_top_iff.mpr h0))
  exact ⟨hak, WithTop.coe_inj.mp (h.symm.trans (coeffVal_of_ne_zero hak))⟩

omit [IsUltrametricDist K] in
/-- The Gauss-norm term `‖a‖ cᵏ` at a positive radius `c`, in exponential form: the radius
form of `norm_mul_exp_pow_eq_exp`. -/
private lemma norm_mul_pow_eq_exp {a : K} (ha : a ≠ 0) {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ‖a‖ * c ^ k = Real.exp (Real.log ‖a‖ + k * Real.log c) := by
  rw [mul_comm (k : ℝ), ← norm_mul_exp_pow_eq_exp ha, Real.exp_log hc]

omit [IsUltrametricDist K] in
/-- Every nonzero coefficient to the right of a point contributes its slope to the slope set. -/
private lemma mem_slopeSet_coeffVal (f : PowerSeries K) {i₀ k : ℕ} {i₁ : ℝ} (hk : i₀ < k)
    (hak : PowerSeries.coeff k f ≠ 0) :
    (-Real.log ‖PowerSeries.coeff k f‖ - i₁) / ((k : ℝ) - i₀) ∈ slopeSet (coeffVal f) i₀ i₁ :=
  ⟨k, hk, fun h => hak (coeffVal_eq_top_iff.mp h), -Real.log ‖PowerSeries.coeff k f‖,
    coeffVal_of_ne_zero hak, (slopeReal_real i₀ k i₁ _).symm⟩

omit [IsUltrametricDist K] in
/-- The slope sequence of the packaged polygon is the slope sequence of the algorithm.  This is
the bridge between the textbook data form of the public statements and the raw `Construction`
form used by the proofs. -/
private lemma newtonPolygon₀OfPowerSeries_slopes (f : PowerSeries K) (a : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = slopes' (newtonPolygon (coeffVal f) a) :=
  rfl

omit [IsUltrametricDist K] in
/-- A real slope of the packaged polygon comes from an honest step of the algorithm. -/
private lemma exists_step_of_slopes_eq {f : PowerSeries K} {a : ℕ} {μ : ℝ}
    (hμ : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ)) :
    ∃ s : Step ℝ, newtonPolygon (coeffVal f) a = some s ∧ slopes s = (μ : WithBotTop ℝ) := by
  rw [newtonPolygon₀OfPowerSeries_slopes] at hμ
  cases h : newtonPolygon (coeffVal f) a with
  | none => exact absurd (h ▸ hμ).symm (by simp [slopes'])
  | some s => exact ⟨s, rfl, by rwa [h] at hμ⟩

omit [IsUltrametricDist K] in
/-- Feeding a step of the algorithm to a hypothesis phrased on the packaged polygon. -/
private lemma slopes_le_of_step {f : PowerSeries K} {m : ℝ}
    (hm : ∀ (a : ℕ) (μ : ℝ),
      (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ) → μ ≤ m)
    {a : ℕ} {s : Step ℝ} (hs : newtonPolygon (coeffVal f) a = some s) {μ : ℝ}
    (hμ : slopes s = (μ : WithBotTop ℝ)) : μ ≤ m :=
  hm a μ (by rwa [newtonPolygon₀OfPowerSeries_slopes, hs])

/-- Any vertex of the polygon at a successor index sits above the previous vertex.
[T] `test.lean:2209`. -/
private lemma newtonPolygon_succ_eq {w : ℕ → WithTop ℝ} {a j₀ l : ℕ} {j₁ m : ℝ}
    (h : newtonPolygon w a = some (.nextVertex j₀ j₁ l m)) :
    newtonPolygon w (a + 1) = some (nextStep w j₀ j₁) := by
  simp only [newtonPolygon, h]

/-- Any step at a successor index is produced by `nextStep` at the previous vertex.
[T] `test.lean:2103`; here a two-line consequence of `Construction`'s
`newtonPolygon_nextVertex_of_succ_ne_none`. -/
private lemma exists_nextStep_of_succ {w : ℕ → WithTop ℝ} {b : ℕ} {s : Step ℝ}
    (hs : newtonPolygon w (b + 1) = some s) :
    ∃ (p₀ : ℕ) (p₁ : ℝ), nextStep w p₀ p₁ = s := by
  obtain ⟨i₀, i₁, l, m, hb⟩ :=
    newtonPolygon_nextVertex_of_succ_ne_none w (hs ▸ Option.some_ne_none s)
  exact ⟨i₀, i₁, Option.some_inj.mp ((newtonPolygon_succ_eq hb).symm.trans hs)⟩

/-- If a step returns `.tail`, the slope set is empty.  (The `⊤` arm of the final match cannot
fire: the chosen vertex lies in the achieving set, so its value is finite.)
[T] `test.lean:227`. -/
private lemma slopeSet_eq_empty_of_nextStep_tail {w : ℕ → WithTop ℝ} {i₀ : ℕ} {i₁ : ℝ}
    (h : nextStep w i₀ i₁ = .tail) : slopeSet w i₀ i₁ = ∅ := by
  by_contra hne
  simp_rw [nextStep] at h
  rw [if_neg hne] at h
  split_ifs at h with h1 h2 h3
  split at h
  · rename_i heq
    have hfin := Set.not_infinite.mp h3
    have hmax := Finset.max'_mem hfin.toFinset
      (hfin.toFinset_nonempty.mpr h2.choose_spec.1)
    exact (hfin.mem_toFinset.mp hmax).2.1 heq
  · exact absurd h (by simp)

omit [IsUltrametricDist K] in
/-- With `a₀ = 1` the first finite point is the origin.  [T] `test.lean:156`. -/
private lemma findFirstFinite_zero {f : PowerSeries K} (hf0 : PowerSeries.coeff 0 f = 1) :
    findFirstFinite (coeffVal f) 0 = some (0, 0) := by
  classical
  have hv0 : coeffVal f 0 = ((0 : ℝ) : WithTop ℝ) := coeffVal_zero_of_coeff_zero_eq_one hf0
  have hfin : finite (coeffVal f) 0 := hv0.trans_ne WithTop.coe_ne_top
  have hex : ∃ i ≥ 0, finite (coeffVal f) i := ⟨0, le_rfl, hfin⟩
  have hzero : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr ⟨le_rfl, hfin⟩
  have hchoose : (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose = (0 : ℝ) :=
    WithTop.coe_inj.mp ((Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose_spec.trans
      (by rw [hzero, hv0]))
  rw [findFirstFinite, dif_pos hex, hchoose, hzero]

omit [IsUltrametricDist K] in
/-- With `a₀ = 1` the algorithm starts at the origin, so step `0` is `nextStep … 0 0`.
[T] `test.lean:176`. -/
private lemma newtonPolygon_zero_eq (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1) :
    newtonPolygon (coeffVal f) 0 = some (nextStep (coeffVal f) 0 0) := by
  simp only [newtonPolygon, findFirstFinite_zero hf0]

/-! #### The two workhorses -/

omit [IsUltrametricDist K] in
/-- Points beyond the base of a step lie on/above the line with slope `sInf slopeSet` — the
common core of the step-slope bounds and their ray analogues.  [T] `test.lean:2120`. -/
private lemma slope_le_of_sInf (f : PowerSeries K) {i₀ : ℕ} {i₁ m : ℝ}
    (hbdd : BddBelow (slopeSet (coeffVal f) i₀ i₁))
    (hm : m = sInf (slopeSet (coeffVal f) i₀ i₁))
    {k : ℕ} (hk : i₀ < k) (hak : PowerSeries.coeff k f ≠ 0) :
    m * ((k : ℝ) - i₀) ≤ -Real.log ‖PowerSeries.coeff k f‖ - i₁ := by
  have hle : m ≤ (-Real.log ‖PowerSeries.coeff k f‖ - i₁) / ((k : ℝ) - i₀) :=
    hm ▸ csInf_le hbdd (mem_slopeSet_coeffVal f hk hak)
  have hki : (0 : ℝ) < (k : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hk)
  rw [le_div_iff₀ hki] at hle
  linarith

omit [IsUltrametricDist K] in
/-- **Workhorse for 5.12, convergence half.**  If `μ` is any slope of the Newton polygon of
`f` (of a bounded segment or of a final infinite one), then `f` is restricted for — converges
on the closed ball of — every radius `c < exp μ`.  Blueprint Theorem 5.12;
[T] `test.lean:2145`. -/
theorem isRestricted_of_lt_slope (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1)
    {a : ℕ} {μ : ℝ}
    (hμ : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ))
    {c : ℝ} (hc0 : 0 < c) (hc : c < Real.exp μ) :
    PowerSeries.IsRestricted c f := by
  obtain ⟨s, hs, hsμ⟩ := exists_step_of_slopes_eq hμ
  -- a base point `(p₀, p₁)` producing the step
  obtain ⟨p₀, p₁, hst⟩ : ∃ (p₀ : ℕ) (p₁ : ℝ), nextStep (coeffVal f) p₀ p₁ = s := by
    rcases a with _ | b
    · exact ⟨0, 0, Option.some_inj.mp ((newtonPolygon_zero_eq f hf0).symm.trans hs)⟩
    · exact exists_nextStep_of_succ hs
  -- the slope `μ` bounds the slope set below
  obtain ⟨hbdd, hsInf⟩ : BddBelow (slopeSet (coeffVal f) p₀ p₁) ∧
      μ = sInf (slopeSet (coeffVal f) p₀ p₁) := by
    rcases s with _ | _ | m' | m' | ⟨j₀, j₁, l, m'⟩
    · exact absurd hsμ.symm (WithBotTop.coe_ne_top μ)
    · exact absurd hsμ.symm (WithBotTop.coe_ne_bot μ)
    · have hmμ : m' = μ := WithBotTop.coe_injective hsμ
      exact ⟨limitingRay_bddBelow _ hst, hmμ ▸ limitingRay_slope_eq_sInf _ hst⟩
    · have hmμ : m' = μ := WithBotTop.coe_injective hsμ
      exact ⟨infiniteRay_bddBelow _ hst, hmμ ▸ infiniteRay_slope_eq_sInf _ hst⟩
    · have hmμ : m' = μ := WithBotTop.coe_injective hsμ
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
  · have hline := slope_le_of_sInf f hbdd hsInf (by omega : p₀ < k) hak
    calc ‖PowerSeries.coeff k f‖ * c ^ k
        = Real.exp (Real.log ‖PowerSeries.coeff k f‖ + k * Real.log c) :=
          norm_mul_pow_eq_exp hak hc0 k
      _ ≤ Real.exp (μ * p₀ - p₁ + k * (Real.log c - μ)) := by
          rw [Real.exp_le_exp]
          nlinarith [hline]
      _ = Real.exp (μ * p₀ - p₁) * r ^ k := by
          rw [Real.exp_add, hrexp, ← Real.exp_nat_mul]

omit [IsUltrametricDist K] in
/-- **Workhorse for 5.12, sharpness half.**  If `f` has infinitely many nonzero coefficients
and every slope of its Newton polygon is `≤ m` (quantified over the honest indices: past the
support the slopes are the junk value `⊤`), then `f` is not restricted for any radius
`c > exp m`.  Blueprint Theorem 5.12; [T] `test.lean:2217`. -/
theorem not_isRestricted_of_slopes_le (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    (hinf : {k : ℕ | PowerSeries.coeff k f ≠ 0}.Infinite)
    {m : ℝ} (hm : ∀ (a : ℕ) (μ : ℝ),
      (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ) → μ ≤ m)
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
  -- terms through the coefficient valuation
  have hterm : ∀ (k : ℕ) (y : ℝ), coeffVal f k = ((y : ℝ) : WithTop ℝ) →
      ‖PowerSeries.coeff k f‖ * c ^ k = Real.exp (-y + k * Real.log c) := by
    intro k y hy
    obtain ⟨hak, hyval⟩ := coeffVal_eq_coe hy
    rw [norm_mul_pow_eq_exp hak hc0, hyval, neg_neg]
  -- every polygon vertex lies under the line of slope `m` through the origin
  have hchain : ∀ (a : ℕ) (j₀' l' : ℕ) (j₁' μ' : ℝ),
      newtonPolygon (coeffVal f) a = some (.nextVertex j₀' j₁' l' μ') →
      coeffVal f j₀' = ((j₁' : ℝ) : WithTop ℝ) ∧ j₁' ≤ m * j₀' := by
    intro a
    induction a with
    | zero =>
      intro j₀' l' j₁' μ' hstep0
      have hv : nextStep (coeffVal f) 0 0 = .nextVertex j₀' j₁' l' μ' :=
        Option.some_inj.mp ((newtonPolygon_zero_eq f hf0).symm.trans hstep0)
      refine ⟨nextVertex_j₁_eq _ hv, ?_⟩
      have hslope := nextVertex_slope_eq_sInf' _ hv
      rw [slopeReal_real] at hslope
      have hj₀pos : (0 : ℝ) < (j₀' : ℝ) := by exact_mod_cast nextVertex_lt _ hv
      have hj₁ : j₁' = μ' * j₀' := by
        rw [eq_div_iff (by simpa using hj₀pos.ne')] at hslope
        push_cast at hslope
        linarith
      have hμm : μ' ≤ m := slopes_le_of_step hm hstep0 rfl
      nlinarith [hj₀pos.le]
    | succ a ih =>
      intro j₀' l' j₁' μ' hstepa
      obtain ⟨i₀, i₁, li, mi, hprev⟩ := nextStep_nextVertex' _ hstepa
      have hv : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀' j₁' l' μ' :=
        nextStep_nextVertex'' _ hstepa hprev
      refine ⟨nextVertex_j₁_eq _ hv, ?_⟩
      have hih := (ih _ _ _ _ hprev).2
      have hslope := nextVertex_slope_eq_sInf' _ hv
      rw [slopeReal_real] at hslope
      have hlt : i₀ < j₀' := nextVertex_lt _ hv
      have hltR : (0 : ℝ) < (j₀' : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast hlt)
      have hline : j₁' = i₁ + μ' * ((j₀' : ℝ) - i₀) := by
        rw [eq_div_iff hltR.ne'] at hslope
        linarith
      have hμm : μ' ≤ m := slopes_le_of_step hm hstepa rfl
      nlinarith [hih, mul_nonneg (sub_nonneg.mpr hμm) hltR.le]
  by_cases hall : ∀ a : ℕ, ∃ (j₀ l : ℕ) (j₁ μ : ℝ),
      newtonPolygon (coeffVal f) a = some (.nextVertex j₀ j₁ l μ)
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
    have hex : ∃ a, ∀ (j₀ l : ℕ) (j₁ μ : ℝ),
        newtonPolygon (coeffVal f) a ≠ some (.nextVertex j₀ j₁ l μ) := by
      simpa using hall
    have hbspec := Nat.find_spec hex
    have hbmin : ∀ a < Nat.find hex, ∃ (j₀ l : ℕ) (j₁ μ : ℝ),
        newtonPolygon (coeffVal f) a = some (.nextVertex j₀ j₁ l μ) :=
      fun a ha => by simpa using Nat.find_min hex ha
    obtain ⟨p₀, p₁, hstb, hp₁⟩ : ∃ (p₀ : ℕ) (p₁ : ℝ),
        newtonPolygon (coeffVal f) (Nat.find hex)
          = some (nextStep (coeffVal f) p₀ p₁) ∧ p₁ ≤ m * p₀ := by
      cases hfind : Nat.find hex with
      | zero =>
        refine ⟨0, 0, ?_, by norm_num⟩
        exact newtonPolygon_zero_eq f hf0
      | succ a =>
        obtain ⟨i₀, li, i₁, μi, hveq⟩ := hbmin a (hfind.symm ▸ Nat.lt_succ_self a)
        exact ⟨i₀, i₁, newtonPolygon_succ_eq hveq, (hchain a i₀ li i₁ μi hveq).2⟩
    -- the slope of every finite point beyond `p₀`, as a total function
    set sl : ℕ → ℝ :=
      fun k => (-Real.log ‖PowerSeries.coeff k f‖ - p₁) / ((k : ℝ) - p₀) with hsl
    have hslopeSet : slopeSet (coeffVal f) p₀ p₁ =
        sl '' {k | p₀ < k ∧ PowerSeries.coeff k f ≠ 0} := by
      ext x
      constructor
      · rintro ⟨k, hk, hfin, y, hy, hx⟩
        obtain ⟨hak, hyval⟩ := coeffVal_eq_coe hy
        refine ⟨k, ⟨hk, hak⟩, ?_⟩
        simp only [hsl]
        rw [hx, slopeReal_real, hyval]
      · rintro ⟨k, ⟨hk, hak⟩, rfl⟩
        exact mem_slopeSet_coeffVal f hk hak
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
        exact hSinf.sdiff (Set.finite_Iio k₀)
      · rintro k ⟨⟨⟨hk, hak⟩, hslk⟩, hk₀'⟩
        rw [hterm k _ (coeffVal_of_ne_zero hak),
          show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_le_exp]
        have hkp : (0 : ℝ) < (k : ℝ) - p₀ := sub_pos.mpr (by exact_mod_cast hk)
        have h1 : -Real.log ‖PowerSeries.coeff k f‖ - p₁ ≤ t₀ * ((k : ℝ) - p₀) := by
          simp only [hsl] at hslk
          rwa [div_le_iff₀ hkp] at hslk
        have h2 : p₁ - t₀ * p₀ ≤ (k : ℝ) * (Real.log c - t₀) := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log c - t₀)] at hk₀
          have h4 : (k₀ : ℝ) ≤ k := by exact_mod_cast hk₀'
          nlinarith [hk₀, h4]
        nlinarith [h1, h2]
    -- case on the terminal step
    rcases hsb : nextStep (coeffVal f) p₀ p₁ with _ | _ | mr | mr | ⟨j₀', j₁', l', μ'⟩
    · -- tail: finite support, contradicting `hinf`
      refine absurd (Set.Finite.subset (Set.finite_Iic p₀) fun k hk => ?_) hinf
      by_contra hgt
      rw [Set.mem_Iic, not_le] at hgt
      have hmem := mem_slopeSet_coeffVal f (i₁ := p₁) hgt hk
      rw [slopeSet_eq_empty_of_nextStep_tail hsb] at hmem
      exact hmem
    · -- unbounded below: arbitrarily steep points give arbitrarily large terms
      have hnb := unboundedBelow _ hsb
      refine hkill (Real.log c - 1) (by linarith) ?_
      by_contra hfin
      rw [Set.not_infinite] at hfin
      apply hnb
      have hsub : slopeSet (coeffVal f) p₀ p₁ ⊆
          sl '' {k | (p₀ < k ∧ PowerSeries.coeff k f ≠ 0) ∧ sl k ≤ Real.log c - 1} ∪
          Set.Ici (Real.log c - 1) := by
        rw [hslopeSet]
        rintro x ⟨k, hkS, rfl⟩
        by_cases hlt : sl k ≤ Real.log c - 1
        · exact Or.inl ⟨k, ⟨hkS, hlt⟩, rfl⟩
        · exact Or.inr (not_le.mp hlt).le
      exact BddBelow.mono hsub ((hfin.image sl).bddBelow.union bddBelow_Ici)
    · -- limiting ray of slope `mr ≤ m`: slopes accumulate at `mr` from above
      have hμm : mr ≤ m := slopes_le_of_step hm (by rw [hstb, hsb]) rfl
      have hδ : (0 : ℝ) < (Real.log c - m) / 2 := by linarith
      refine hkill (mr + (Real.log c - m) / 2) (by linarith) ?_
      refine Set.infinite_of_forall_exists_gt fun N => ?_
      obtain ⟨k, hkN, y, hy, hslope⟩ := limitingRay_exists_slope_lt _ hsb hδ (max N p₀)
      obtain ⟨hak, hyval⟩ := coeffVal_eq_coe hy
      rw [slopeReal_real] at hslope
      refine ⟨k, ⟨⟨(le_max_right N p₀).trans_lt hkN, hak⟩, ?_⟩, (le_max_left N p₀).trans_lt hkN⟩
      simp only [hsl, ← hyval]
      exact hslope.le
    · -- infinite ray of slope `mr ≤ m`: infinitely many points on the ray
      have hμm : mr ≤ m := slopes_le_of_step hm (by rw [hstb, hsb]) rfl
      refine hkill m (by linarith) (Set.infinite_of_forall_exists_gt fun N => ?_)
      obtain ⟨k, hkN, hk, hfin, y, hy, hslope⟩ := infiniteRay_exists_achieving_gt _ hsb N
      obtain ⟨hak, hyval⟩ := coeffVal_eq_coe hy
      rw [slopeReal_real] at hslope
      refine ⟨k, ⟨⟨hk, hak⟩, ?_⟩, hkN⟩
      simp only [hsl, ← hyval, ← hslope]
      exact hμm
    · -- a vertex: contradicts minimality
      exact absurd (by rw [hstb, hsb]) (hbspec j₀' l' j₁' μ')

-- The `[IsUltrametricDist K]` binder of the two headline statements is kept deliberately: it is
-- the standing hypothesis of §5.12 and part of the blueprint-facing signature, even though the
-- proofs below only use ultrametricity of the extension `L`.
set_option linter.unusedSectionVars false in
/-- **Blueprint Theorem 5.12, lower half.**  Over an extension with dense norms (`ℂ_p`),
every slope `μ` of the polygon pushes the radius of convergence up to at least `exp μ`;
ranging over the slopes, the radius is at least `exp (sup of the slopes)`.
[T] `test.lean:2496`. -/
theorem ofReal_exp_le_radiusOfConvergence (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {a : ℕ} {μ : ℝ}
    (hμ : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ))
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (hdense : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a < b → ∃ x : L, a < ‖x‖ ∧ ‖x‖ < b) :
    ENNReal.ofReal (Real.exp μ) ≤ radiusOfConvergence L f := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨x, hx1, hx2⟩ := hdense r.coe_nonneg (ENNReal.coe_lt_ofReal.mp hr)
  have hres := isRestricted_of_lt_slope f hf0 hμ (r.coe_nonneg.trans_lt hx1) hx2
  have hsx := summable_of_isRestricted hres hL le_rfl
  calc (r : ENNReal) ≤ (‖x‖₊ : ENNReal) := by exact_mod_cast hx1.le
    _ ≤ _ := le_radiusOfConvergence_of_summable hsx

set_option linter.unusedSectionVars false in
/-- **Blueprint Theorem 5.12, upper half.**  If `f` has infinitely many nonzero coefficients
and every slope of its Newton polygon is `≤ m` (quantified over the honest indices: past the
support the slopes are the junk value `⊤`), then over *any* complete ultrametric extension the
radius of convergence is at most `exp m`; at `m = sup of the slopes` this is the sharp bound.
(No density is needed for this half.)  [T] `test.lean:2519`. -/
theorem radiusOfConvergence_le_ofReal_exp (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    (hinf : {k : ℕ | PowerSeries.coeff k f ≠ 0}.Infinite)
    {m : ℝ} (hm : ∀ (a : ℕ) (μ : ℝ),
      (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ) → μ ≤ m)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) :
    radiusOfConvergence L f ≤ ENNReal.ofReal (Real.exp m) := by
  rw [radiusOfConvergence]
  refine iSup₂_le fun x hx => ?_
  by_contra hgt
  rw [not_le, ENNReal.ofReal_lt_coe_iff (Real.exp_pos m).le, coe_nnnorm] at hgt
  exact not_isRestricted_of_slopes_le f hf0 hinf hm hgt (isRestricted_of_summable hL hx)
