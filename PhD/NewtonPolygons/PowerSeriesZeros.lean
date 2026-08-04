/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import PhD.NewtonPolygons.RadiusOfConvergence
import PhD.NewtonPolygons.PolynomialRoots
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulDistinguished
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassPrep
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Units
import Mathlib.RingTheory.Valuation.Basic

/-!
# Weierstrass factorisation along the polygon and zeros of power series (blueprint §5.13–§5.14)

Proved results, refactored from
`PhD/Test/test.lean` lines 2538–3553 onto the `negLogNorm`/`coeffVal` valuation bridge, the
`ForMathlib` restricted-power-series API and Martin's Weierstrass preparation
(`IsMulDistinguished` / `weierstrassPreparation_exists_of_isMulDistinguished`, which works at
**every** positive radius — all the divisible-value-group plumbing of the old proof route is
gone).

* **§5.13** (`exists_weierstrass_factorisation`): if the `k`-th segment of the polygon of `f`
  ends at `x = j₀` with slope `m` and `f` converges on the closed ball of radius `exp m`, then
  `f = g · h` with `g` a polynomial of degree `j₀` normalised by `g₀ = 1`, `h` converging on
  the ball with `|h − 1|_c < 1`, `|f − g|_c < |f|_c`, and the polygon of `g` is the part of
  the polygon of `f` over `[0, j₀]` (slopes and lengths agree at every index `≤ k`).
  Deviation from the blueprint: its bound `|f − g|_c < 1` is correct only on the *first*
  segment (`k = 0`, where `|f|_c = 1`); the scale-correct clause is
  `|f − g|_c < |f|_c`, with `|h − 1|_c < 1` carrying the blueprint's intent.  The
  factorisation is normalised by `g(0) = 1` instead of monicity of `g`.

* **§5.14** counts zeros of the *series*.  Evaluation of `f` at a point needs a complete
  valued extension (the blueprint's `ℂ_p`), so zeros are phrased via `HasSum` over a complete
  ultrametric normed field `L` extending `K` isometrically; `AlgebraicClosure K` is *not*
  complete, hence the change of setting relative to §5.7–§5.11.
  `hasSum_zero_iff_aeval_eq_zero` identifies the zeros of `f` in the ball with the roots of
  the polynomial factor `g` of §5.13 — through it, the blueprint's count "`i_j` zeros of
  absolute value `exp m_j`" *with* multiplicity is exactly the §5.11 root count applied to
  `g`, whose polygon agrees with that of `f` by §5.13(5).  The remaining half, "no other
  zeros in the ball" (`norm_eq_exp_slope_of_hasSum_zero`), says every zero in the ball lies
  on a sphere `exp μ_a` for one of the first `k + 1` slopes.
-/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-! ### Step-inversion helpers

`SpecConstruction.lean`, `FirstBreak.lean` and `PolynomialRoots.lean` keep their step-inversion
lemmas private, so the handful of pieces needed to drive the algorithm here are re-derived. -/

section StepInversion

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ] {w : ℕ → WithTop Γ} {i₀ : ℕ} {i₁ : Γ}

/-- If a step returns `.tail`, the slope set is empty.  (The `⊤` arm of the final match cannot
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

/-- The slope from `(x₀, y₀)` to `(x₁, y₁)` over `Γ = ℝ`. -/
private lemma slopeReal_real (x₀ x₁ : ℕ) (y₀ y₁ : ℝ) :
    slopeReal x₀ x₁ y₀ y₁ = (y₁ - y₀) / ((x₁ : ℝ) - (x₀ : ℝ)) := by
  simp [slopeReal, Algebra.algebraMap_self]

end StepInversion

/-! ### 5.13: Weierstrass factorisation along the polygon -/

omit [IsUltrametricDist K] in
/-- Data of a finite point of the valuation sequence.  [T] `test.lean:2538`. -/
private lemma coeffVal_eq_coe_iff {f : PowerSeries K} {t : ℕ} {y : ℝ}
    (h : coeffVal f t = ((y : ℝ) : WithTop ℝ)) :
    PowerSeries.coeff t f ≠ 0 ∧ y = - Real.log ‖PowerSeries.coeff t f‖ := by
  have hak : PowerSeries.coeff t f ≠ 0 := fun h0 =>
    WithTop.top_ne_coe ((coeffVal_eq_top_iff.mpr h0).symm.trans h)
  exact ⟨hak, WithTop.coe_inj.mp (h.symm.trans (coeffVal_of_ne_zero hak))⟩

omit [IsUltrametricDist K] in
/-- Points to the right of a vertex lie on/above its outgoing line (`nextStep_slope_le` read
through `coeffVal`). -/
private lemma coeffVal_slope_le {f : PowerSeries K} {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m) {k : ℕ} (hk : i₀ < k)
    (hak : PowerSeries.coeff k f ≠ 0) :
    m * ((k : ℝ) - (i₀ : ℝ)) ≤ -Real.log ‖PowerSeries.coeff k f‖ - i₁ := by
  have h1 := nextStep_slope_le (coeffVal f) h hk (coeffVal_of_ne_zero hak)
  rwa [Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply] at h1

omit [IsUltrametricDist K] in
/-- Points beyond a vertex lie strictly above its incoming line (`nextStep_slope_lt` read
through `coeffVal`). -/
private lemma coeffVal_slope_lt {f : PowerSeries K} {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m) {k : ℕ} (hk : j₀ < k)
    (hak : PowerSeries.coeff k f ≠ 0) :
    m * ((k : ℝ) - (i₀ : ℝ)) < -Real.log ‖PowerSeries.coeff k f‖ - i₁ := by
  have h1 := nextStep_slope_lt (coeffVal f) h hk (coeffVal_of_ne_zero hak)
  rwa [Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply] at h1

omit [IsUltrametricDist K] in
/-- The output vertex of a step lies on the line of the step's slope through its input vertex. -/
private lemma coeffVal_vertex_line {f : PowerSeries K} {i₀ j₀ l : ℕ} {i₁ j₁ m : ℝ}
    (h : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m) :
    j₁ = i₁ + m * ((j₀ : ℝ) - (i₀ : ℝ)) := by
  have hijR : (0 : ℝ) < (j₀ : ℝ) - (i₀ : ℝ) := by
    rw [sub_pos]; exact_mod_cast nextVertex_lt _ h
  have hslope := nextVertex_slope_eq_sInf' _ h
  rw [slopeReal_real, eq_div_iff hijR.ne'] at hslope
  linarith

omit [IsUltrametricDist K] in
/-- With `a₀ = 1` the algorithm starts at the origin. -/
private lemma findFirstFinite_coeffVal_zero {f : PowerSeries K}
    (hf0 : PowerSeries.coeff 0 f = 1) : findFirstFinite (coeffVal f) 0 = some (0, (0 : ℝ)) := by
  classical
  have hval : coeffVal f 0 = ((0 : ℝ) : WithTop ℝ) := coeffVal_zero_of_coeff_zero_eq_one hf0
  have hfin : finite (coeffVal f) 0 := by
    show coeffVal f 0 ≠ ⊤
    rw [hval]; exact WithTop.coe_ne_top
  have hex : ∃ i ≥ 0, finite (coeffVal f) i := ⟨0, le_refl _, hfin⟩
  have hzero : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr ⟨le_refl _, hfin⟩
  have h2 : coeffVal f (Nat.find hex) = ((0 : ℝ) : WithTop ℝ) := by rw [hzero]; exact hval
  unfold findFirstFinite
  rw [dif_pos hex]
  have hchoose : (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose = (0 : ℝ) :=
    WithTop.coe_inj.mp
      ((Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose_spec.trans h2)
  rw [hchoose, hzero]

omit [IsUltrametricDist K] in
/-- Step `0` of the algorithm is the step out of the origin. -/
private lemma newtonPolygon_coeffVal_zero {f : PowerSeries K} (hf0 : PowerSeries.coeff 0 f = 1) :
    newtonPolygon (coeffVal f) 0 = some (nextStep (coeffVal f) 0 (0 : ℝ)) := by
  simp only [newtonPolygon, findFirstFinite_coeffVal_zero hf0]

omit [IsUltrametricDist K] in
/-- Series form of the vertex-line bound: every finite point lies on/above the line through
the `a`-th vertex with the `a`-th slope.  [T] `test.lean:2588`. -/
private theorem vertex_line_le' (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1) :
    ∀ (a : ℕ) {j₀ l : ℕ} {j₁ m : ℝ},
      newtonPolygon (coeffVal f) a = some (.nextVertex j₀ j₁ l m) →
      ∀ t, PowerSeries.coeff t f ≠ 0 →
        m * ((t : ℝ) - (j₀ : ℝ)) ≤ - Real.log ‖PowerSeries.coeff t f‖ - j₁ := by
  intro a
  induction a with
  | zero =>
      intro j₀ l j₁ m hseg t ht
      have hv : nextStep (coeffVal f) 0 (0 : ℝ) = .nextVertex j₀ j₁ l m :=
        Option.some_inj.mp ((newtonPolygon_coeffVal_zero hf0).symm.trans hseg)
      have hj₁ : j₁ = m * (j₀ : ℝ) := by simpa using coeffVal_vertex_line hv
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · have hν0 : -Real.log ‖PowerSeries.coeff 0 f‖ = 0 := by
          rw [hf0, norm_one, Real.log_one, neg_zero]
        have hexp : m * (((0 : ℕ) : ℝ) - (j₀ : ℝ)) = -(m * (j₀ : ℝ)) := by push_cast; ring
        rw [hν0, hexp, hj₁]
        linarith
      · have hfb : m * (t : ℝ) ≤ -Real.log ‖PowerSeries.coeff t f‖ := by
          simpa using coeffVal_slope_le hv htpos ht
        have hexp : m * ((t : ℝ) - (j₀ : ℝ)) = m * (t : ℝ) - m * (j₀ : ℝ) := by ring
        rw [hexp, hj₁]
        linarith
  | succ a ih =>
      intro j₀ l j₁ m hseg t ht
      obtain ⟨i₀, i₁, l', m', hprev⟩ := nextStep_nextVertex' _ hseg
      have hstep : nextStep (coeffVal f) i₀ i₁ = .nextVertex j₀ j₁ l m :=
        nextStep_nextVertex'' _ hseg hprev
      have hline : j₁ = i₁ + m * ((j₀ : ℝ) - (i₀ : ℝ)) := coeffVal_vertex_line hstep
      have key : m * ((t : ℝ) - (i₀ : ℝ)) ≤ -Real.log ‖PowerSeries.coeff t f‖ - i₁ := by
        rcases Nat.lt_or_ge i₀ t with hti | hti
        · exact coeffVal_slope_le hstep hti ht
        · have h1 := ih hprev t ht
          have hts : ((t : ℝ) - (i₀ : ℝ)) ≤ 0 := by rw [sub_nonpos]; exact_mod_cast hti
          obtain ⟨p₀, p₁, hprevstep⟩ := nextStep_nextVertex _ hprev
          have hmm : m' < m := slopes_increasing_nextVertex _ hprevstep hstep
          nlinarith [h1, mul_nonneg (sub_nonneg.mpr hmm.le) (neg_nonneg.mpr hts)]
      have hexp : m * ((t : ℝ) - (j₀ : ℝ))
          = m * ((t : ℝ) - (i₀ : ℝ)) - m * ((j₀ : ℝ) - (i₀ : ℝ)) := by ring
      linarith [key, hline, hexp]

omit [IsUltrametricDist K] in
/-- Series form of the strict vertex-line bound: beyond the `a`-th vertex, finite points lie
strictly above the `a`-th slope line (through the next step of the algorithm).
[T] `test.lean:2646`. -/
private theorem vertex_line_lt' (f : PowerSeries K) {a j₀ l : ℕ} {j₁ m : ℝ}
    (hseg : newtonPolygon (coeffVal f) a = some (.nextVertex j₀ j₁ l m))
    {t : ℕ} (htj : j₀ < t) (hat : PowerSeries.coeff t f ≠ 0) :
    m * ((t : ℝ) - (j₀ : ℝ)) < - Real.log ‖PowerSeries.coeff t f‖ - j₁ := by
  obtain ⟨i₀, i₁, hstep⟩ := nextStep_nextVertex _ hseg
  have hlt := coeffVal_slope_lt hstep htj hat
  have hline : j₁ = i₁ + m * ((j₀ : ℝ) - (i₀ : ℝ)) := coeffVal_vertex_line hstep
  have hexp : m * ((t : ℝ) - (j₀ : ℝ))
      = m * ((t : ℝ) - (i₀ : ℝ)) - m * ((j₀ : ℝ) - (i₀ : ℝ)) := by ring
  linarith [hlt, hline, hexp]

omit [IsUltrametricDist K] in
/-- The Gauss norm is monotone in the radius (on series restricted at the larger radius).
[T] `test.lean:2703`. -/
private lemma gaussNorm_le_of_radius_le {x : PowerSeries K} {c c' : ℝ} (hc'0 : 0 ≤ c')
    (hcc : c' ≤ c) (hx : PowerSeries.IsRestricted c x) :
    PowerSeries.gaussNorm norm c' x ≤ PowerSeries.gaussNorm norm c x := by
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun t => ?_
  calc ‖PowerSeries.coeff t x‖ * c' ^ t ≤ ‖PowerSeries.coeff t x‖ * c ^ t := by gcongr
    _ ≤ _ := PowerSeries.le_gaussNorm norm c x hx.hasGaussNorm t

/-- **Congruence of the algorithm at one step.**  If the slope set of `w₁` from `(p₀, p₁)` is
bounded below by `m` and its achieving set at `m` coincides with that of `w₂`, then `w₁`'s
step from `(p₀, p₁)` outputs the same vertex as `w₂`'s.  [T] `test.lean:2715`. -/
private lemma nextStep_congr {w₁ w₂ : ℕ → WithTop ℝ} {p₀ j₀ l : ℕ} {p₁ j₁ m : ℝ}
    (h : nextStep w₂ p₀ p₁ = .nextVertex j₀ j₁ l m)
    (hlb : ∀ x ∈ slopeSet w₁ p₀ p₁, m ≤ x)
    (hach : achievingSet w₁ p₀ p₁ m = achievingSet w₂ p₀ p₁ m) :
    nextStep w₁ p₀ p₁ = .nextVertex j₀ j₁ l m := by
  have hsInf₂ : m = sInf (slopeSet w₂ p₀ p₁) := nextVertex_slope_eq_sInf'' _ h
  have hj₀mem₂ : j₀ ∈ achievingSet w₂ p₀ p₁ m := hsInf₂ ▸ nextVertex_j₀Mem _ h
  obtain ⟨hj₀gt, hj₀fin, y₁, hy₁, hsl₁⟩ : j₀ ∈ achievingSet w₁ p₀ p₁ m := hach ▸ hj₀mem₂
  have hm_mem : m ∈ slopeSet w₁ p₀ p₁ := ⟨j₀, hj₀gt, hj₀fin, y₁, hy₁, hsl₁⟩
  have hbdd₁ : BddBelow (slopeSet w₁ p₀ p₁) := ⟨m, hlb⟩
  have hsInf₁ : sInf (slopeSet w₁ p₀ p₁) = m :=
    le_antisymm (csInf_le hbdd₁ hm_mem) (le_csInf ⟨m, hm_mem⟩ hlb)
  have hfin₂ : (achievingSet w₂ p₀ p₁ m).Finite := hsInf₂ ▸ nextVertex_finite _ h
  have hfin₁ : (achievingSet w₁ p₀ p₁ m).Finite := hach ▸ hfin₂
  -- the value at `j₀` is the one on the line: `y₁ = j₁`
  have hy₁val : y₁ = j₁ := by
    obtain ⟨-, -, y₂, hy₂, hsl₂⟩ := hj₀mem₂
    have hj₂ : w₂ j₀ = ((j₁ : ℝ) : WithTop ℝ) := nextVertex_j₁_eq _ h
    have hy₂j : y₂ = j₁ := by
      rw [hy₂] at hj₂
      exact_mod_cast hj₂
    rw [slopeReal_real] at hsl₁ hsl₂
    have hgt : (0 : ℝ) < (j₀ : ℝ) - (p₀ : ℝ) := sub_pos.mpr (by exact_mod_cast hj₀gt)
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
      have hq₀mem : q₀ ∈ achievingSet w₁ p₀ p₁ m₁ := hsInf₁ ▸ nextVertex_j₀Mem _ hs₁
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
    obtain rfl : q₀ = j₀ := le_antisymm hq₀le hj₀le
    have hq₁ : q₁ = y₁ := by
      have h2 := nextVertex_j₁_eq _ hs₁
      rw [hy₁] at h2
      exact_mod_cast h2.symm
    have hl₁ : l₁ = l := by
      rw [nextVertex_l_eq _ hs₁, nextVertex_l_eq _ h]
    rw [hq₁, hy₁val, hl₁]

/-- Step `a + 1` of the algorithm is the step out of the vertex produced at step `a`.
[T] `test.lean:2209`. -/
private lemma newtonPolygon_succ_eq {w : ℕ → WithTop ℝ} {a j₀ l : ℕ} {j₁ m : ℝ}
    (h : newtonPolygon w a = some (.nextVertex j₀ j₁ l m)) :
    newtonPolygon w (a + 1) = some (nextStep w j₀ j₁) := by
  simp only [newtonPolygon, h]

omit [IsUltrametricDist K] in
/-- **From textbook segment data to algorithm data**: a finite slope together with a finite
right endpoint at index `a` forces the algorithm to output a `nextVertex` there, with that
endpoint and that slope.  (The two final rays carry infinite length, so no vertex follows
them.)  Series copy of the `PolynomialRoots.lean` private of the same name. -/
private lemma step_of_segment_data {f : PowerSeries K} {a j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (a + 1) = ((j₀ : ℤ) : WithTop ℤ)) :
    ∃ (j₁ : ℝ) (l : ℕ), newtonPolygon (coeffVal f) a = some (.nextVertex j₀ j₁ l m) := by
  have hslopes : slopes' (newtonPolygon (coeffVal f) a) = (m : WithBotTop ℝ) := hm
  have hray : ∀ m' : ℝ, newtonPolygon (coeffVal f) a = some (.limitingRay m') ∨
      newtonPolygon (coeffVal f) a = some (.infiniteRay m') → False := by
    intro m' h
    have hlen : (newtonPolygon₀OfPowerSeries negLogNorm f).lengths a = ⊤ := by
      show newtonPolygon_lengths (coeffVal f) a = ⊤
      rcases h with h | h <;> simp only [newtonPolygon_lengths, h]
    rw [NewtonPolygon₀.vertexX_succ, hlen, WithTop.map_top, add_top] at hj
    exact WithTop.coe_ne_top hj.symm
  cases hstep : newtonPolygon (coeffVal f) a with
  | none =>
      rw [hstep] at hslopes
      exact ((WithBotTop.coe_ne_top m) (show (m : WithBotTop ℝ) = ⊤ from hslopes.symm)).elim
  | some S =>
      rw [hstep] at hslopes
      cases S with
      | tail =>
          exact ((WithBotTop.coe_ne_top m) (show (m : WithBotTop ℝ) = ⊤ from hslopes.symm)).elim
      | unboundedBelow =>
          exact ((WithBotTop.coe_ne_bot m) (show (m : WithBotTop ℝ) = ⊥ from hslopes.symm)).elim
      | limitingRay m' => exact (hray m' (Or.inl hstep)).elim
      | infiniteRay m' => exact (hray m' (Or.inr hstep)).elim
      | nextVertex j₀' j₁ l m' =>
          obtain rfl : m' = m :=
            WithBotTop.coe_injective (show (m' : WithBotTop ℝ) = (m : WithBotTop ℝ) from hslopes)
          have hvx : ((j₀' : ℤ) : WithTop ℤ) = ((j₀ : ℤ) : WithTop ℤ) :=
            (newtonPolygon₀OfSeq_vertexX (coeffVal f) hstep).symm.trans hj
          obtain rfl : j₀' = j₀ := by exact_mod_cast hvx
          exact ⟨j₁, l, rfl⟩

omit [IsUltrametricDist K] in
/-- Two-position comparison of Gauss-norm terms at radius `c`: `‖a‖ cᵗ ≤ ‖b‖ cˢ` iff
`(t, -log ‖a‖)` lies on/above the line of slope `log c` through `(s, -log ‖b‖)`.
[T] `test.lean:1514`. -/
private lemma term_le_term_iff' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {c : ℝ} (hc : 0 < c)
    (t s : ℕ) :
    ‖a‖ * c ^ t ≤ ‖b‖ * c ^ s ↔
      Real.log c * ((t : ℝ) - s) ≤ -Real.log ‖a‖ - -Real.log ‖b‖ := by
  rw [show c = Real.exp (Real.log c) from (Real.exp_log hc).symm,
    norm_mul_exp_pow_eq_exp ha _ t, norm_mul_exp_pow_eq_exp hb _ s, Real.exp_le_exp,
    Real.log_exp, mul_sub]
  constructor <;> intro h <;> linarith

omit [IsUltrametricDist K] in
/-- Strict variant of `term_le_term_iff'`.  [T] `test.lean:1524`. -/
private lemma term_lt_term_iff' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {c : ℝ} (hc : 0 < c)
    (t s : ℕ) :
    ‖a‖ * c ^ t < ‖b‖ * c ^ s ↔
      Real.log c * ((t : ℝ) - s) < -Real.log ‖a‖ - -Real.log ‖b‖ := by
  rw [show c = Real.exp (Real.log c) from (Real.exp_log hc).symm,
    norm_mul_exp_pow_eq_exp ha _ t, norm_mul_exp_pow_eq_exp hb _ s, Real.exp_lt_exp,
    Real.log_exp, mul_sub]
  constructor <;> intro h <;> linarith

/-- The Gauss norm at radius `c` of the series underlying a restricted series is its norm in
`PowerSeries.Restricted K c`. -/
private lemma gaussNorm_val_eq_norm {c : ℝ} [Fact (0 < c)] (x : PowerSeries.Restricted K c) :
    PowerSeries.gaussNorm norm c x.1 = ‖x‖ :=
  (PowerSeries.Restricted.norm_def _ x).symm

/-- **Isosceles principle.**  If `a` and `b` are closer to each other than `a` is to `0`, then
they have the same norm; in particular `b ≠ 0`. -/
private lemma norm_eq_and_ne_zero_of_norm_sub_lt {a b : K} (h : ‖a - b‖ < ‖a‖) :
    ‖b‖ = ‖a‖ ∧ b ≠ 0 := by
  have hb : ‖b‖ = ‖a‖ := by
    rw [show b = a - (a - b) by ring, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact ne_of_gt h),
      norm_neg, max_eq_left h.le]
  exact ⟨hb, norm_pos_iff.mp (by rw [hb]; exact (norm_nonneg _).trans_lt h)⟩

/-- **The congruence certificate at a chain vertex.**  Let `f = g · h` with `h` a series of
Gauss distance `< 1` from `1` at radius `exp m`, and let `(v₀, v₁)` be a vertex from which the
algorithm on `f` steps to `(u₀, u₁)` with slope `μ' ≤ m`, the target being the `b`-th output
vertex of the polygon of `f`.  Then, at `(v₀, v₁)`, the slope set of `g` is bounded below by
`μ'` and the achieving sets of `g` and `f` at `μ'` coincide — the two inputs of
`nextStep_congr`.  [T] `test.lean:2971`. -/
private lemma slopeSet_lb_and_achievingSet_eq {f : PowerSeries K} {gp : Polynomial K}
    {hp : PowerSeries K} {m : ℝ} (hf0 : PowerSeries.coeff 0 f = 1)
    (hconv : PowerSeries.IsRestricted (Real.exp m) f)
    (hfgh : f = (gp : PowerSeries K) * hp)
    (hhres : PowerSeries.IsRestricted (Real.exp m) hp)
    (hh1norm : PowerSeries.gaussNorm norm (Real.exp m) (hp - 1) < 1)
    {b v₀ u₀ lu : ℕ} {v₁ u₁ μ' : ℝ}
    (hu : newtonPolygon (coeffVal f) b = some (.nextVertex u₀ u₁ lu μ')) (hμm : μ' ≤ m)
    (hq : nextStep (coeffVal f) v₀ v₁ = .nextVertex u₀ u₁ lu μ') :
    (∀ x ∈ slopeSet (coeffVal (gp : PowerSeries K)) v₀ v₁, μ' ≤ x) ∧
      achievingSet (coeffVal (gp : PowerSeries K)) v₀ v₁ μ'
        = achievingSet (coeffVal f) v₀ v₁ μ' := by
  obtain ⟨hu₀ne, hu₁val⟩ := coeffVal_eq_coe_iff (nextVertex_j₁_eq _ hq)
  have hc'0 : (0 : ℝ) < Real.exp μ' := Real.exp_pos μ'
  have hc'le : Real.exp μ' ≤ Real.exp m := Real.exp_le_exp.mpr hμm
  haveI : Fact (0 < Real.exp μ') := ⟨hc'0⟩
  -- geometry of the step: `(v₀, v₁)` sits on the `u₀`-line
  have hvu : v₀ < u₀ := nextVertex_lt _ hq
  have hvuR : (0 : ℝ) < (u₀ : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast hvu)
  have hslq := nextVertex_slope_eq_sInf' _ hq
  rw [slopeReal_real] at hslq
  have hv₁ : u₁ = v₁ + μ' * ((u₀ : ℝ) - v₀) := by
    rw [eq_div_iff hvuR.ne'] at hslq
    linarith
  -- `f`-terms at radius `exp μ'` are dominated by the `u₀`-term
  have hApos : 0 < ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ :=
    mul_pos (norm_pos_iff.mpr hu₀ne) (pow_pos hc'0 u₀)
  have hfle : ∀ t, ‖PowerSeries.coeff t f‖ * Real.exp μ' ^ t
      ≤ ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
    intro t
    by_cases hat : PowerSeries.coeff t f = 0
    · rw [hat, norm_zero, zero_mul]
      exact hApos.le
    · refine (term_le_term_iff' hat hu₀ne hc'0 t u₀).mpr ?_
      rw [Real.log_exp]
      have h1 := vertex_line_le' f hf0 b hu t hat
      rwa [hu₁val] at h1
  -- restrictedness at the smaller radius `exp μ'`
  have hfres : PowerSeries.IsRestricted (Real.exp μ') f := isRestricted_of_le f hc'0.le hc'le hconv
  have hhres' : PowerSeries.IsRestricted (Real.exp μ') hp :=
    isRestricted_of_le hp hc'0.le hc'le hhres
  have hsub_res : PowerSeries.IsRestricted (Real.exp m) (hp - 1) :=
    PowerSeries.isRestricted.sub _ hhres (PowerSeries.isRestricted_one _)
  set H' : PowerSeries.Restricted K (Real.exp μ') := ⟨hp, hhres'⟩ with hH'def
  set F' : PowerSeries.Restricted K (Real.exp μ') := ⟨f, hfres⟩ with hF'def
  set G' : PowerSeries.Restricted K (Real.exp μ') :=
    Polynomial.toRestricted (Real.exp μ') gp with hG'def
  have hH'1lt : ‖H' - 1‖ < 1 := by
    rw [← show PowerSeries.gaussNorm norm (Real.exp μ') (hp - 1) = ‖H' - 1‖ from
      gaussNorm_val_eq_norm (H' - 1)]
    exact lt_of_le_of_lt (gaussNorm_le_of_radius_le hc'0.le hc'le hsub_res) hh1norm
  have hF'norm : ‖F'‖ = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ :=
    le_antisymm ((PowerSeries.Restricted.norm_le_iff _ F').mpr hfle)
      (PowerSeries.Restricted.norm_coeff_mul_pow_le _ F' u₀)
  -- the global coefficient estimate at radius `exp μ'`
  have hE : ∀ t, ‖PowerSeries.coeff t f - PowerSeries.coeff t (gp : PowerSeries K)‖ *
      Real.exp μ' ^ t < ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
    have hFGH' : F' = G' * H' := Subtype.ext hfgh
    have hH'norm : ‖H'‖ = 1 := by
      have h8 : H' = 1 + (H' - 1) := by ring
      rw [h8, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [norm_one]; exact (ne_of_lt hH'1lt).symm), norm_one, max_eq_left hH'1lt.le]
    have hG'norm : ‖G'‖ = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
      rw [← hF'norm, hFGH', norm_mul, hH'norm, mul_one]
    have h7 : F' - G' = G' * (H' - 1) := by rw [hFGH']; ring
    have h5 : ‖F' - G'‖ < ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ :=
      calc ‖F' - G'‖ = ‖G'‖ * ‖H' - 1‖ := by rw [h7, norm_mul]
        _ < ‖G'‖ * 1 := by
            refine mul_lt_mul_of_pos_left hH'1lt ?_
            rw [hG'norm]
            exact hApos
        _ = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by rw [mul_one, hG'norm]
    intro t
    have h3 : PowerSeries.coeff t f - PowerSeries.coeff t (gp : PowerSeries K)
        = PowerSeries.coeff t (f - (gp : PowerSeries K)) := (_root_.map_sub _ _ _).symm
    rw [h3]
    exact lt_of_le_of_lt
      (PowerSeries.Restricted.norm_coeff_mul_pow_le _ (F' - G') t) h5
  -- (T1) nonzero `g`-coefficients lie on/above the line
  have hgle : ∀ t, ‖PowerSeries.coeff t (gp : PowerSeries K)‖ * Real.exp μ' ^ t
      ≤ ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
    intro t
    have h3 : ‖PowerSeries.coeff t (gp : PowerSeries K)‖
        ≤ max ‖PowerSeries.coeff t f‖
          ‖PowerSeries.coeff t f - PowerSeries.coeff t (gp : PowerSeries K)‖ := by
      have h4 := IsUltrametricDist.norm_add_le_max (PowerSeries.coeff t f)
        (PowerSeries.coeff t (gp : PowerSeries K) - PowerSeries.coeff t f)
      rw [add_sub_cancel] at h4
      rwa [norm_sub_rev] at h4
    calc ‖PowerSeries.coeff t (gp : PowerSeries K)‖ * Real.exp μ' ^ t
        ≤ max ‖PowerSeries.coeff t f‖
            ‖PowerSeries.coeff t f - PowerSeries.coeff t (gp : PowerSeries K)‖ *
          Real.exp μ' ^ t := mul_le_mul_of_nonneg_right h3 (pow_pos hc'0 t).le
      _ = max (‖PowerSeries.coeff t f‖ * Real.exp μ' ^ t)
          (‖PowerSeries.coeff t f - PowerSeries.coeff t (gp : PowerSeries K)‖ *
            Real.exp μ' ^ t) := by rw [max_mul_of_nonneg _ _ (pow_pos hc'0 t).le]
      _ ≤ ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := max_le (hfle t) (hE t).le
  constructor
  · -- lower bound on the `g`-slope set
    rintro x ⟨t, ht, htfin, y, hy, hx⟩
    obtain ⟨hgt_ne, hyval⟩ := coeffVal_eq_coe_iff hy
    have htR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast ht)
    rw [hx, slopeReal_real, le_div_iff₀ htR]
    have h3 := (term_le_term_iff' hgt_ne hu₀ne hc'0 t u₀).mp (hgle t)
    rw [Real.log_exp] at h3
    rw [hyval, hu₁val] at *
    linarith [h3, hv₁]
  · -- the achieving sets agree
    ext t
    simp only [achievingSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ht, htfin, y, hy, hslope⟩
      obtain ⟨hgt_ne, hyval⟩ := coeffVal_eq_coe_iff hy
      have htR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast ht)
      rw [slopeReal_real, eq_comm, div_eq_iff htR.ne'] at hslope
      -- `t` is on the line: the `g`-term equals the `u₀`-term
      have hgeq_term : ‖PowerSeries.coeff t (gp : PowerSeries K)‖ * Real.exp μ' ^ t
          = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
        rw [norm_mul_exp_pow_eq_exp hgt_ne μ' t, norm_mul_exp_pow_eq_exp hu₀ne μ' u₀,
          Real.exp_eq_exp]
        have h4 : Real.log ‖PowerSeries.coeff t (gp : PowerSeries K)‖ = -y := by
          rw [hyval]; ring
        have h5 : Real.log ‖PowerSeries.coeff u₀ f‖ = -u₁ := by rw [hu₁val]; ring
        rw [h4, h5]
        linarith [hslope, hv₁]
      -- the `f`-coefficient has the same norm (isosceles)
      have hdiff_lt : ‖PowerSeries.coeff t (gp : PowerSeries K) - PowerSeries.coeff t f‖ <
          ‖PowerSeries.coeff t (gp : PowerSeries K)‖ := by
        rw [norm_sub_rev]
        have h4 := hE t
        rw [← hgeq_term] at h4
        exact lt_of_mul_lt_mul_right h4 (pow_pos hc'0 t).le
      obtain ⟨hfnorm, hft_ne⟩ := norm_eq_and_ne_zero_of_norm_sub_lt hdiff_lt
      refine ⟨ht, ?_, -Real.log ‖PowerSeries.coeff t f‖, coeffVal_of_ne_zero hft_ne, ?_⟩
      · exact fun hc => hft_ne (coeffVal_eq_top_iff.mp hc)
      · rw [slopeReal_real, eq_comm, div_eq_iff htR.ne', hfnorm]
        rw [hyval] at hslope
        linarith [hslope]
    · rintro ⟨ht, htfin, y, hy, hslope⟩
      obtain ⟨hft_ne, hyval⟩ := coeffVal_eq_coe_iff hy
      have htR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast ht)
      rw [slopeReal_real, eq_comm, div_eq_iff htR.ne'] at hslope
      have hfeq_term : ‖PowerSeries.coeff t f‖ * Real.exp μ' ^ t
          = ‖PowerSeries.coeff u₀ f‖ * Real.exp μ' ^ u₀ := by
        rw [norm_mul_exp_pow_eq_exp hft_ne μ' t, norm_mul_exp_pow_eq_exp hu₀ne μ' u₀,
          Real.exp_eq_exp]
        have h4 : Real.log ‖PowerSeries.coeff t f‖ = -y := by rw [hyval]; ring
        have h5 : Real.log ‖PowerSeries.coeff u₀ f‖ = -u₁ := by rw [hu₁val]; ring
        rw [h4, h5]
        linarith [hslope, hv₁]
      have hdiff_lt : ‖PowerSeries.coeff t f - PowerSeries.coeff t (gp : PowerSeries K)‖ <
          ‖PowerSeries.coeff t f‖ := by
        have h4 := hE t
        rw [← hfeq_term] at h4
        exact lt_of_mul_lt_mul_right h4 (pow_pos hc'0 t).le
      obtain ⟨hgnorm, hgt_ne⟩ := norm_eq_and_ne_zero_of_norm_sub_lt hdiff_lt
      refine ⟨ht, ?_, -Real.log ‖PowerSeries.coeff t (gp : PowerSeries K)‖,
        coeffVal_of_ne_zero hgt_ne, ?_⟩
      · exact fun hc => hgt_ne (coeffVal_eq_top_iff.mp hc)
      · rw [slopeReal_real, eq_comm, div_eq_iff htR.ne', hgnorm]
        rw [hyval] at hslope
        linarith [hslope]

/-- **Blueprint Proposition 5.13** (power-series Weierstrass factorisation along the polygon).
If the `k`-th slope of the Newton polygon of `f` is `m`, the `k`-th segment ends at `x = j₀`,
and `f` converges on the closed ball of radius `c = exp m`, then `f = g · h` with `g` a
polynomial of degree `j₀` normalised by `g₀ = 1`, `h` a power series converging on the ball
with `|h - 1|_c < 1`, `|f - g|_c < |f|_c`, and the polygon of `g` is the portion of the
polygon of `f` over `[0, j₀]` (slopes and lengths agree at every index `≤ k`).

Deviation from the blueprint: its clause `|f - g|_c < 1` holds only for the *first* segment,
where `|f|_c = 1`; for `k ≥ 1` the Gauss norm of `f` exceeds `1` and the correct (and here
stated) bound is `|f - g|_c = |f|_c · |h - 1|_c < |f|_c`.

Proof route: `f` is Martin-distinguished of order `j₀` at radius `exp m`
(`PowerSeries.IsMulDistinguished`), so
`PowerSeries.Restricted.weierstrassPreparation_exists_of_isMulDistinguished` applies directly
— no divisible-value-group hypothesis.  [T] `test.lean:2795`. -/
theorem exists_weierstrass_factorisation [CompleteSpace K] (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (k + 1) = ((j₀ : ℤ) : WithTop ℤ))
    (hconv : PowerSeries.IsRestricted (Real.exp m) f) :
    ∃ (g : Polynomial K) (h : PowerSeries K),
      f = (g : PowerSeries K) * h ∧
      g.natDegree = j₀ ∧
      g.coeff 0 = 1 ∧
      PowerSeries.gaussNorm norm (Real.exp m) (f - (g : PowerSeries K))
        < PowerSeries.gaussNorm norm (Real.exp m) f ∧
      PowerSeries.IsRestricted (Real.exp m) h ∧
      PowerSeries.gaussNorm norm (Real.exp m) (h - 1) < 1 ∧
      ∀ a, a ≤ k →
        (newtonPolygon₀OfPowerSeries negLogNorm (g : PowerSeries K)).slopes a
            = (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a ∧
          (newtonPolygon₀OfPowerSeries negLogNorm (g : PowerSeries K)).lengths a
            = (newtonPolygon₀OfPowerSeries negLogNorm f).lengths a := by
  classical
  have hc0 : (0 : ℝ) < Real.exp m := Real.exp_pos m
  haveI : Fact (0 < Real.exp m) := ⟨hc0⟩
  obtain ⟨j₁, l, hseg⟩ := step_of_segment_data hm hj
  obtain ⟨p₀, p₁, hst⟩ := nextStep_nextVertex _ hseg
  obtain ⟨haj₀, hj₁val⟩ := coeffVal_eq_coe_iff (nextVertex_j₁_eq _ hst)
  -- the Gauss terms are dominated by the `j₀`-th, strictly beyond it
  have hterm_le : ∀ t, ‖PowerSeries.coeff t f‖ * Real.exp m ^ t
      ≤ ‖PowerSeries.coeff j₀ f‖ * Real.exp m ^ j₀ := by
    intro t
    by_cases hat : PowerSeries.coeff t f = 0
    · rw [hat, norm_zero, zero_mul]
      positivity
    · refine (term_le_term_iff' hat haj₀ hc0 t j₀).mpr ?_
      rw [Real.log_exp]
      have h1 := vertex_line_le' f hf0 k hseg t hat
      rwa [hj₁val] at h1
  have hterm_lt : ∀ t, j₀ < t → ‖PowerSeries.coeff t f‖ * Real.exp m ^ t
      < ‖PowerSeries.coeff j₀ f‖ * Real.exp m ^ j₀ := by
    intro t htj
    by_cases hat : PowerSeries.coeff t f = 0
    · rw [hat, norm_zero, zero_mul]
      exact mul_pos (norm_pos_iff.mpr haj₀) (pow_pos hc0 j₀)
    · refine (term_lt_term_iff' hat haj₀ hc0 t j₀).mpr ?_
      rw [Real.log_exp]
      have h1 := vertex_line_lt' f hseg htj hat
      rwa [hj₁val] at h1
  -- `f` is Martin-distinguished of order `j₀` at radius `exp m`
  have hdist : PowerSeries.IsMulDistinguished (Real.exp m) f j₀ :=
    ⟨(isUnit_iff_ne_zero.mpr haj₀).isNormMulUnit,
      le_antisymm (by rw [PowerSeries.gaussNorm_eq]; exact ciSup_le hterm_le)
        (PowerSeries.le_gaussNorm norm _ f hconv.hasGaussNorm j₀),
      hterm_lt⟩
  -- Weierstrass preparation at radius `exp m`
  obtain ⟨ω, e, ωm, ωd, ωn, he, hgeq⟩ :=
    PowerSeries.Restricted.weierstrassPreparation_exists_of_isMulDistinguished
      (g := (⟨f, hconv⟩ : PowerSeries.Restricted K (Real.exp m))) (s := j₀) hdist
  have hnat : ω.natDegree = j₀ := Polynomial.natDegree_eq_of_degree_eq_some ωd
  have hfeq : f = e.1 * (ω : PowerSeries K) := congrArg Subtype.val hgeq
  -- constant coefficients
  have hcoeff0 : PowerSeries.coeff 0 e.1 * ω.coeff 0 = 1 := by
    have h1 := congrArg (PowerSeries.coeff 0) hfeq
    rw [hf0, PowerSeries.coeff_mul] at h1
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Polynomial.coeff_coe] at h1
    exact h1.symm
  have hω₀ : ω.coeff 0 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hcoeff0
    exact zero_ne_one hcoeff0
  -- the normalised polynomial factor `g` and the unit part `h`
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
    linear_combination (-(e.1 * (ω : PowerSeries K))) * hCC
  have hh0 : PowerSeries.coeff 0 h = 1 := by
    rw [hhdef, PowerSeries.coeff_C_mul, mul_comm]
    exact hcoeff0
  have hhres : PowerSeries.IsRestricted (Real.exp m) h := by
    rw [hhdef]
    exact PowerSeries.isRestricted.mul _ (PowerSeries.isRestricted_C _ _) e.2
  -- `h` as a unit of the restricted ring, with strictly dominant constant coefficient
  set H : PowerSeries.Restricted K (Real.exp m) :=
    PowerSeries.Restricted.C (Real.exp m) (ω.coeff 0) * e with hHdef
  have hHunit : IsUnit H :=
    ((isUnit_iff_ne_zero.mpr hω₀).map (PowerSeries.Restricted.C (Real.exp m))).mul he.isUnit
  have hhdom : ∀ t, 1 ≤ t → ‖PowerSeries.coeff t h‖ * Real.exp m ^ t < 1 := by
    intro t ht
    have h1 := PowerSeries.Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit
      (Real.exp m) hHunit (Nat.one_le_iff_ne_zero.mp ht)
    rwa [PowerSeries.Restricted.constantCoeff_eq_coeff_zero,
      show PowerSeries.coeff 0 H.1 = PowerSeries.coeff 0 h from rfl,
      show ∀ t : ℕ, PowerSeries.coeff t H.1 = PowerSeries.coeff t h from fun _ => rfl,
      hh0, norm_one] at h1
  -- `|h − 1|_c < 1`
  have hH1lt : ‖(H - 1 : PowerSeries.Restricted K (Real.exp m))‖ < 1 := by
    rw [PowerSeries.Restricted.norm_lt_iff]
    intro i
    rw [show PowerSeries.coeff i (H - 1 : PowerSeries.Restricted K (Real.exp m)).1
      = PowerSeries.coeff i (h - 1) from rfl]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [_root_.map_sub, hh0, PowerSeries.coeff_one, if_pos rfl, sub_self, norm_zero, zero_mul]
      norm_num
    · rw [_root_.map_sub, PowerSeries.coeff_one, if_neg hipos.ne', sub_zero]
      exact hhdom i hipos
  have hh1norm : PowerSeries.gaussNorm norm (Real.exp m) (h - 1) < 1 := by
    rw [show PowerSeries.gaussNorm norm (Real.exp m) (h - 1)
      = ‖(H - 1 : PowerSeries.Restricted K (Real.exp m))‖ from gaussNorm_val_eq_norm (H - 1)]
    exact hH1lt
  -- `|f − g|_c < |f|_c`, by Gauss multiplicativity
  set G : PowerSeries.Restricted K (Real.exp m) :=
    Polynomial.toRestricted (Real.exp m) g with hGdef
  set F : PowerSeries.Restricted K (Real.exp m) := ⟨f, hconv⟩ with hFdef
  have hFGH : F = G * H := Subtype.ext hfgh
  have hHnorm : ‖H‖ = 1 := by
    have h2 : H = 1 + (H - 1) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_one]; exact (ne_of_lt hH1lt).symm), norm_one, max_eq_left hH1lt.le]
  have hFne : F ≠ 0 := by
    intro h0
    have h1 : PowerSeries.coeff 0 F.1 = PowerSeries.coeff 0 (0 : PowerSeries K) :=
      congrArg (fun z : PowerSeries.Restricted K (Real.exp m) => PowerSeries.coeff 0 z.1) h0
    rw [show PowerSeries.coeff 0 F.1 = PowerSeries.coeff 0 f from rfl, hf0, map_zero] at h1
    exact one_ne_zero h1
  have hFpos : (0 : ℝ) < ‖F‖ := norm_pos_iff.mpr hFne
  have hGnorm : ‖G‖ = ‖F‖ := by rw [hFGH, norm_mul, hHnorm, mul_one]
  have hfg_lt : PowerSeries.gaussNorm norm (Real.exp m) (f - (g : PowerSeries K))
      < PowerSeries.gaussNorm norm (Real.exp m) f := by
    have h1 : F - G = G * (H - 1) := by rw [hFGH]; ring
    have h2 : ‖F - G‖ < ‖F‖ := by
      rw [h1, norm_mul]
      calc ‖G‖ * ‖H - 1‖ < ‖G‖ * 1 :=
            mul_lt_mul_of_pos_left hH1lt (by rw [hGnorm]; exact hFpos)
        _ = ‖F‖ := by rw [mul_one, hGnorm]
    rw [show PowerSeries.gaussNorm norm (Real.exp m) (f - (g : PowerSeries K)) = ‖F - G‖ from
        gaussNorm_val_eq_norm (F - G),
      show PowerSeries.gaussNorm norm (Real.exp m) f = ‖F‖ from gaussNorm_val_eq_norm F]
    exact h2
  -- the polygons agree at every index `≤ k`
  have hpoly : ∀ a, a ≤ k → newtonPolygon (coeffVal (g : PowerSeries K)) a
      = newtonPolygon (coeffVal f) a := by
    -- the chain of `f`-vertices below the `k`-th, with slopes at most `m`
    have hfchain : ∀ b a, a + b = k → ∃ (v₀ lv : ℕ) (v₁ μ : ℝ),
        newtonPolygon (coeffVal f) a = some (.nextVertex v₀ v₁ lv μ) ∧ μ ≤ m := by
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
          exact ⟨i₀, li, i₁, mi, hprev, (slopes_increasing_nextVertex _ hq hstep).le.trans hμ⟩
    -- upward induction along the polygon
    intro a
    induction a with
    | zero =>
        intro _
        obtain ⟨v₀, lv, v₁, μ, hv, hμ⟩ := hfchain k 0 (by omega)
        have hg0' : PowerSeries.coeff 0 (g : PowerSeries K) = 1 :=
          (Polynomial.coeff_coe g 0).trans hg0
        have hstep0 : nextStep (coeffVal f) 0 0 = .nextVertex v₀ v₁ lv μ :=
          Option.some_inj.mp ((newtonPolygon_coeffVal_zero hf0).symm.trans hv)
        obtain ⟨hlb, hach⟩ :=
          slopeSet_lb_and_achievingSet_eq hf0 hconv hfgh hhres hh1norm hv hμ hstep0
        rw [newtonPolygon_coeffVal_zero hg0', newtonPolygon_coeffVal_zero hf0, hstep0]
        exact congrArg _ (nextStep_congr hstep0 hlb hach)
    | succ a ih =>
        intro ha
        have hprev_eq := ih (by omega)
        obtain ⟨v₀, lv, v₁, μ, hv, hμ⟩ := hfchain (k - a) a (by omega)
        obtain ⟨u₀, lu, u₁, μ', hu, hμ'⟩ := hfchain (k - (a + 1)) (a + 1) (by omega)
        have hstep : nextStep (coeffVal f) v₀ v₁ = .nextVertex u₀ u₁ lu μ' :=
          nextStep_nextVertex'' _ hu hv
        obtain ⟨hlb, hach⟩ :=
          slopeSet_lb_and_achievingSet_eq hf0 hconv hfgh hhres hh1norm hu hμ' hstep
        rw [newtonPolygon_succ_eq (hprev_eq.trans hv), newtonPolygon_succ_eq hv, hstep]
        exact congrArg _ (nextStep_congr hstep hlb hach)
  refine ⟨g, h, hfgh, hgdeg, hg0, hfg_lt, hhres, hh1norm, fun a ha => ⟨?_, ?_⟩⟩
  · show slopes' (newtonPolygon (coeffVal (g : PowerSeries K)) a)
      = slopes' (newtonPolygon (coeffVal f) a)
    rw [hpoly a ha]
  · show newtonPolygon_lengths (coeffVal (g : PowerSeries K)) a
      = newtonPolygon_lengths (coeffVal f) a
    simp only [newtonPolygon_lengths, hpoly a ha]

/-! ### 5.14: zeros of the series in the ball -/

omit [IsUltrametricDist K] in
/-- **A polynomial whose `s`-th term strictly dominates at the point's own radius is nonzero
there.**  Between consecutive slope spheres the polygon-vertex coefficient dominates strictly,
so a polynomial has no zeros strictly between the spheres of consecutive slope radii.
[T] `test.lean:3229`. -/
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
      · rw [h, sub_self]
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

-- The `hf0`/`hm`/`hj` hypotheses and the `IsUltrametricDist K` instance are part of the frozen
-- statement of this blueprint corollary, even though this proof route does not use them.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **Blueprint Corollary 5.14, counting half.**  In the closed ball of radius `exp m` the
zeros of `f` are exactly the roots of the polynomial factor `g` of 5.13 (any `g` with the
5.13 properties).  Zero counts *with multiplicity* then transfer to `g`: combined with the
§5.11 root count at each slope for `g` — whose polygon is that of `f` over `[0, j₀]` by
5.13(5) — this gives the blueprint's "`f` has exactly `i_j` zeros of absolute value `exp m_j`
for each slope `m_j`, and no others in the ball".  [T] `test.lean:3271`. -/
theorem hasSum_zero_iff_aeval_eq_zero (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (k + 1) = ((j₀ : ℤ) : WithTop ℤ))
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
    summable_of_isRestricted hhconv hL hx
  have hG : HasSum (fun i => algebraMap K L (g.coeff i) * x ^ i) (Polynomial.aeval x g) := by
    have h2 : HasSum (fun i => algebraMap K L (g.coeff i) * x ^ i)
        (∑ i ∈ Finset.range (g.natDegree + 1), algebraMap K L (g.coeff i) * x ^ i) :=
      hasSum_sum_of_ne_finset_zero fun i hi => by
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hi), map_zero, zero_mul]
    have h3 : ∑ i ∈ Finset.range (g.natDegree + 1), algebraMap K L (g.coeff i) * x ^ i
        = Polynomial.aeval x g := by
      rw [Polynomial.aeval_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm
    rwa [h3] at h2
  set H : L := ∑' j, algebraMap K L (PowerSeries.coeff j h) * x ^ j with hHdef
  -- `H` is a unit: `|H - 1| < 1` since every term of `h - 1` is small on the ball
  have hs1res : PowerSeries.IsRestricted (Real.exp m) (h - 1) :=
    PowerSeries.isRestricted.sub _ hhconv (PowerSeries.isRestricted_one _)
  have hone : HasSum
      (fun j => algebraMap K L (PowerSeries.coeff j (1 : PowerSeries K)) * x ^ j) 1 := by
    have h2 : HasSum
        (fun j : ℕ => algebraMap K L (PowerSeries.coeff j (1 : PowerSeries K)) * x ^ j)
        (algebraMap K L (PowerSeries.coeff 0 (1 : PowerSeries K)) * x ^ 0) :=
      hasSum_single 0 fun j hj => by rw [PowerSeries.coeff_one, if_neg hj, map_zero, zero_mul]
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
    · exact le_trans (by positivity)
        (PowerSeries.le_gaussNorm norm (Real.exp m) (h - 1) hs1res.hasGaussNorm 0)
    · rw [norm_mul, norm_pow, hL]
      calc ‖PowerSeries.coeff j (h - 1)‖ * ‖x‖ ^ j
          ≤ ‖PowerSeries.coeff j (h - 1)‖ * Real.exp m ^ j := by gcongr
        _ ≤ _ := PowerSeries.le_gaussNorm norm (Real.exp m) (h - 1) hs1res.hasGaussNorm j
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
  have hjoint := hG.summable.mul_of_nonarchimedean hsh
  have hsF : Summable (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) :=
    summable_of_isRestricted hconv hL hx
  have hprod : (∑' t, algebraMap K L (PowerSeries.coeff t f) * x ^ t)
      = Polynomial.aeval x g * H := by
    rw [hHdef, ← hG.tsum_eq,
      Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hG.summable hsh hjoint]
    exact tsum_congr hterm
  refine ⟨fun hzero => ?_, fun hzero => ?_⟩
  · have h0 : Polynomial.aeval x g * H = 0 := by rw [← hprod, hzero.tsum_eq]
    exact (mul_eq_zero.mp h0).resolve_right hHne
  · have h0 : (∑' t, algebraMap K L (PowerSeries.coeff t f) * x ^ t) = 0 := by
      rw [hprod, hzero, zero_mul]
    exact h0 ▸ hsF.hasSum

omit [IsUltrametricDist K] in
/-- Every nonzero coefficient to the right of a point contributes its slope to the slope set.
Series copy of the `RadiusOfConvergence.lean` private of the same name. -/
private lemma mem_slopeSet_coeffVal (f : PowerSeries K) {i₀ t : ℕ} {i₁ : ℝ} (ht : i₀ < t)
    (hat : PowerSeries.coeff t f ≠ 0) :
    (-Real.log ‖PowerSeries.coeff t f‖ - i₁) / ((t : ℝ) - i₀) ∈ slopeSet (coeffVal f) i₀ i₁ :=
  ⟨t, ht, fun h => hat (coeffVal_eq_top_iff.mp h), -Real.log ‖PowerSeries.coeff t f‖,
    coeffVal_of_ne_zero hat, (slopeReal_real i₀ t i₁ _).symm⟩

omit [IsUltrametricDist K] in
/-- Points beyond the base of a step lie on/above the line with slope `sInf slopeSet`.
Series copy of the `RadiusOfConvergence.lean` private of the same name. -/
private lemma slope_le_of_sInf' (f : PowerSeries K) {i₀ : ℕ} {i₁ m : ℝ}
    (hbdd : BddBelow (slopeSet (coeffVal f) i₀ i₁))
    (hm : m = sInf (slopeSet (coeffVal f) i₀ i₁))
    {t : ℕ} (ht : i₀ < t) (hat : PowerSeries.coeff t f ≠ 0) :
    m * ((t : ℝ) - i₀) ≤ -Real.log ‖PowerSeries.coeff t f‖ - i₁ := by
  have hle : m ≤ (-Real.log ‖PowerSeries.coeff t f‖ - i₁) / ((t : ℝ) - i₀) :=
    hm ▸ csInf_le hbdd (mem_slopeSet_coeffVal f ht hat)
  have hti : (0 : ℝ) < (t : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast ht)
  rw [le_div_iff₀ hti] at hle
  linarith

omit [IsUltrametricDist K] in
/-- The slope sequence of the packaged polygon at an output vertex of the algorithm. -/
private lemma slopes_eq_of_step {f : PowerSeries K} {a v₀ lv : ℕ} {v₁ μ : ℝ}
    (hv : newtonPolygon (coeffVal f) a = some (.nextVertex v₀ v₁ lv μ)) :
    (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ) := by
  show slopes' (newtonPolygon (coeffVal f) a) = _
  rw [hv]
  rfl

omit [IsUltrametricDist K] in
/-- A real slope of the packaged polygon comes from an honest step of the algorithm.  Series
copy of the `RadiusOfConvergence.lean` private `exists_step_of_slopes_eq`. -/
private lemma exists_step_of_slopes_eq' {f : PowerSeries K} {a : ℕ} {μ : ℝ}
    (hμ : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ)) :
    ∃ s : Step ℝ, newtonPolygon (coeffVal f) a = some s ∧ slopes s = (μ : WithBotTop ℝ) := by
  have hμ' : slopes' (newtonPolygon (coeffVal f) a) = (μ : WithBotTop ℝ) := hμ
  cases h : newtonPolygon (coeffVal f) a with
  | none => exact absurd ((h ▸ hμ').symm : (μ : WithBotTop ℝ) = ⊤) (WithBotTop.coe_ne_top μ)
  | some s => exact ⟨s, rfl, by rwa [h] at hμ'⟩

omit [IsUltrametricDist K] in
/-- **A strictly dominant term forbids a zero.**  If the `s`-th term of the series strictly
dominates every other one at the point `x`, the series does not sum to `0` there: the terms
tend to `0`, so the dominance is uniform, and the ultrametric inequality bounds every partial
sum containing `s` below by the `s`-th term.  (Series analogue of
`aeval_ne_zero_of_dominant_at`.) -/
private lemma not_hasSum_zero_of_dominant {f : PowerSeries K} {c : ℝ}
    (hconv : PowerSeries.IsRestricted c f)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ ≤ c) {s : ℕ}
    (hA : 0 < ‖PowerSeries.coeff s f‖ * ‖x‖ ^ s)
    (hdom : ∀ t, t ≠ s → ‖PowerSeries.coeff t f‖ * ‖x‖ ^ t
      < ‖PowerSeries.coeff s f‖ * ‖x‖ ^ s) :
    ¬ HasSum (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) 0 := by
  classical
  intro hzero
  set u : ℕ → ℝ := fun t => ‖PowerSeries.coeff t f‖ * ‖x‖ ^ t with hu
  set A : ℝ := u s with hAdef
  have hterm : ∀ t, ‖algebraMap K L (PowerSeries.coeff t f) * x ^ t‖ = u t :=
    fun t => by rw [norm_mul, norm_pow, hL]
  -- the terms tend to `0`, so the dominance is uniform
  have hres : PowerSeries.IsRestricted ‖x‖ f := isRestricted_of_le f (norm_nonneg x) hx hconv
  have htend : Filter.Tendsto u Filter.atTop (nhds 0) := by
    rw [PowerSeries.isRestricted_iff'] at hres
    exact hres
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const (by linarith : (0 : ℝ) < A / 2) htend)
  -- the finitely many early terms other than the `s`-th are bounded by some `B < A`
  obtain ⟨B, hB0, hBA, hBle⟩ : ∃ B : ℝ, 0 ≤ B ∧ B < A ∧ ∀ t, t ≠ s → u t ≤ B := by
    rcases ((Finset.range N).erase s).eq_empty_or_nonempty with hF | hF
    · refine ⟨A / 2, by linarith, by linarith, fun t ht => ?_⟩
      by_cases htN : t < N
      · exact absurd (Finset.mem_erase.mpr ⟨ht, Finset.mem_range.mpr htN⟩)
          (by rw [hF]; exact Finset.notMem_empty t)
      · exact (hN t (not_lt.mp htN)).le
    · obtain ⟨b, hbF, hbmax⟩ := Finset.exists_max_image _ u hF
      refine ⟨max (A / 2) (u b), le_max_of_le_left (by linarith),
        max_lt (by linarith) (hdom b (Finset.mem_erase.mp hbF).1), fun t ht => ?_⟩
      by_cases htN : t < N
      · exact le_max_of_le_right (hbmax t (Finset.mem_erase.mpr ⟨ht, Finset.mem_range.mpr htN⟩))
      · exact le_max_of_le_left (hN t (not_lt.mp htN)).le
  -- a partial sum containing `s` has norm at least `A`
  obtain ⟨S, hSball, hSs⟩ := ((hzero.eventually (Metric.ball_mem_nhds (0 : L) hA)).and
    (Filter.eventually_ge_atTop ({s} : Finset ℕ))).exists
  have hsS : s ∈ S := hSs (Finset.mem_singleton_self s)
  have hsplit : ∑ t ∈ S, algebraMap K L (PowerSeries.coeff t f) * x ^ t
      - ∑ t ∈ S.erase s, algebraMap K L (PowerSeries.coeff t f) * x ^ t
      = algebraMap K L (PowerSeries.coeff s f) * x ^ s := by
    rw [← Finset.add_sum_erase S _ hsS]
    ring
  have herase : ‖∑ t ∈ S.erase s, algebraMap K L (PowerSeries.coeff t f) * x ^ t‖ ≤ B :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun t ht => by
      rw [hterm]
      exact hBle t (Finset.mem_erase.mp ht).1
  have hlt : ‖∑ t ∈ S, algebraMap K L (PowerSeries.coeff t f) * x ^ t‖ < A := by
    simpa using mem_ball_zero_iff.mp hSball
  have hAle : A ≤ max ‖∑ t ∈ S, algebraMap K L (PowerSeries.coeff t f) * x ^ t‖
      ‖∑ t ∈ S.erase s, algebraMap K L (PowerSeries.coeff t f) * x ^ t‖ := by
    rw [← show ‖algebraMap K L (PowerSeries.coeff s f) * x ^ s‖ = A from (hterm s).trans hAdef.symm,
      ← hsplit, sub_eq_add_neg]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (by rw [norm_neg])
  exact absurd hAle (not_le.mpr (max_lt hlt (herase.trans_lt hBA)))

omit [IsUltrametricDist K] in
/-- With `a₀ = 1` the series does not vanish at a point of norm `0`. -/
private lemma not_hasSum_zero_of_norm_eq_zero {f : PowerSeries K} {c : ℝ}
    (hf0 : PowerSeries.coeff 0 f = 1) (hconv : PowerSeries.IsRestricted c f)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ ≤ c) (hx0 : ‖x‖ = 0) :
    ¬ HasSum (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) 0 := by
  refine not_hasSum_zero_of_dominant hconv hL hx (s := 0) (by simp [hf0]) fun t ht => ?_
  rw [hx0, zero_pow ht, mul_zero]
  simp [hf0]

omit [IsUltrametricDist K] in
/-- **No `infiniteRay` at a radius of convergence.**  Infinitely many points on the ray have
Gauss term `exp (m ⬝ i₀ - i₁) ≠ 0` at radius `exp m`, contradicting restricted-ness. -/
private lemma nextStep_ne_infiniteRay {f : PowerSeries K} {i₀ : ℕ} {i₁ m : ℝ}
    (hconv : PowerSeries.IsRestricted (Real.exp m) f) :
    nextStep (coeffVal f) i₀ i₁ ≠ .infiniteRay m := by
  intro h
  have hinf := achievingSet_infinite_of_nextStep_infiniteRay h
  have hval : ∀ t ∈ achievingSet (coeffVal f) i₀ i₁ m,
      ‖PowerSeries.coeff t f‖ * Real.exp m ^ t = Real.exp (m * (i₀ : ℝ) - i₁) := by
    rintro t ⟨htgt, -, j₁, hj₁, hsl⟩
    obtain ⟨hat, hj₁val⟩ := coeffVal_eq_coe_iff hj₁
    rw [slopeReal_real] at hsl
    have htR : (0 : ℝ) < (t : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast htgt)
    rw [eq_div_iff htR.ne'] at hsl
    rw [norm_mul_exp_pow_eq_exp hat m t]
    congr 1
    linarith [hsl, hj₁val]
  rw [PowerSeries.isRestricted_iff'] at hconv
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const (Real.exp_pos (m * (i₀ : ℝ) - i₁)) hconv)
  obtain ⟨t, htmem, htN⟩ := Set.Infinite.exists_gt hinf N
  exact absurd (hval t htmem) (ne_of_lt (hN t htN.le))

omit [IsUltrametricDist K] in
/-- On a `limitingRay` the points beyond the base lie **strictly** above the ray: the infimum
slope is not attained. -/
private lemma coeffVal_slope_lt_of_limitingRay {f : PowerSeries K} {i₀ : ℕ} {i₁ m : ℝ}
    (h : nextStep (coeffVal f) i₀ i₁ = .limitingRay m) {t : ℕ} (ht : i₀ < t)
    (hat : PowerSeries.coeff t f ≠ 0) :
    m * ((t : ℝ) - i₀) < -Real.log ‖PowerSeries.coeff t f‖ - i₁ := by
  have hsInf := limitingRay_slope_eq_sInf _ h
  have hle := slope_le_of_sInf' f (limitingRay_bddBelow _ h) hsInf ht hat
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · refine absurd ⟨m, ?_, hsInf⟩ (not_attained_of_nextStep_limitingRay h)
    have hti : (0 : ℝ) < (t : ℝ) - i₀ := sub_pos.mpr (by exact_mod_cast ht)
    have hm : m = (-Real.log ‖PowerSeries.coeff t f‖ - i₁) / ((t : ℝ) - i₀) := by
      rw [eq_div_iff hti.ne']
      linarith
    rw [hm]
    exact mem_slopeSet_coeffVal f ht hat

omit [IsUltrametricDist K] in
/-- **The ray window.**  At a `limitingRay` step out of `(v₀, v₁)` with slope `m`, every point
of the closed ball of radius `exp m` whose radius exceeds `exp μ` — `μ` a slope bounding the
points to the left of `v₀` — is a non-zero of `f`: the `v₀`-th term strictly dominates. -/
private lemma not_hasSum_zero_of_limitingRay {f : PowerSeries K} {v₀ : ℕ} {v₁ m μ : ℝ}
    (hconv : PowerSeries.IsRestricted (Real.exp m) f)
    (hstep : nextStep (coeffVal f) v₀ v₁ = .limitingRay m)
    (hv₀ : PowerSeries.coeff v₀ f ≠ 0) (hv₁ : v₁ = -Real.log ‖PowerSeries.coeff v₀ f‖)
    (hbelow : ∀ t, t < v₀ → PowerSeries.coeff t f ≠ 0 →
      μ * ((t : ℝ) - (v₀ : ℝ)) ≤ -Real.log ‖PowerSeries.coeff t f‖ - v₁)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ ≤ Real.exp m) (hxμ : Real.exp μ < ‖x‖) :
    ¬ HasSum (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) 0 := by
  have hr0 : (0 : ℝ) < ‖x‖ := lt_trans (Real.exp_pos μ) hxμ
  have hlogμ : μ < Real.log ‖x‖ := (Real.lt_log_iff_exp_lt hr0).mpr hxμ
  have hlogm : Real.log ‖x‖ ≤ m := by
    rw [show m = Real.log (Real.exp m) from (Real.log_exp m).symm]
    exact Real.log_le_log hr0 hx
  refine not_hasSum_zero_of_dominant hconv hL hx
    (s := v₀) (mul_pos (norm_pos_iff.mpr hv₀) (pow_pos hr0 v₀)) fun t ht => ?_
  by_cases hat : PowerSeries.coeff t f = 0
  · rw [hat, norm_zero, zero_mul]
    exact mul_pos (norm_pos_iff.mpr hv₀) (pow_pos hr0 v₀)
  · rw [show ‖x‖ = Real.exp (Real.log ‖x‖) from (Real.exp_log hr0).symm]
    refine (term_lt_term_iff' hat hv₀ (Real.exp_pos _) t v₀).mpr ?_
    rw [Real.log_exp, ← hv₁]
    rcases Nat.lt_or_ge t v₀ with htv | htv
    · have hline := hbelow t htv hat
      have htvR : ((t : ℝ) - v₀) < 0 := sub_neg.mpr (by exact_mod_cast htv)
      nlinarith [hline, mul_lt_mul_of_neg_right hlogμ htvR]
    · have htv' : v₀ < t := lt_of_le_of_ne htv (Ne.symm ht)
      have hline := coeffVal_slope_lt_of_limitingRay hstep htv' hat
      have htvR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast htv')
      nlinarith [hline, mul_le_mul_of_nonneg_right hlogm htvR.le]

omit [IsUltrametricDist K] in
/-- **Transfer of algorithm data along the 5.13 polygon agreement.**  If the packaged polygons
of `gp` and `f` agree in slopes and lengths up to index `k`, then each vertex of `f` at an
index `≤ k` is a vertex of `gp`, with the same abscissa and the same outgoing slope. -/
private lemma newtonPolygon_transfer {f gp : PowerSeries K}
    (hf0 : PowerSeries.coeff 0 f = 1) (hg0 : PowerSeries.coeff 0 gp = 1) {k : ℕ}
    (hagree : ∀ a, a ≤ k →
      (newtonPolygon₀OfPowerSeries negLogNorm gp).slopes a
          = (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a ∧
        (newtonPolygon₀OfPowerSeries negLogNorm gp).lengths a
          = (newtonPolygon₀OfPowerSeries negLogNorm f).lengths a)
    {a : ℕ} (ha : a ≤ k) {v₀ lv : ℕ} {v₁ μ : ℝ}
    (hv : newtonPolygon (coeffVal f) a = some (.nextVertex v₀ v₁ lv μ)) :
    ∃ (w₁ : ℝ) (lw : ℕ), newtonPolygon (coeffVal gp) a = some (.nextVertex v₀ w₁ lw μ) := by
  have hvx : ∀ b, b ≤ k + 1 → (newtonPolygon₀OfPowerSeries negLogNorm gp).vertexX b
      = (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX b := by
    intro b
    induction b with
    | zero =>
        intro _
        rw [NewtonPolygon₀.vertexX_zero, NewtonPolygon₀.vertexX_zero,
          newtonPolygon₀_starting_point_of_coeff_zero_eq_one hg0,
          newtonPolygon₀_starting_point_of_coeff_zero_eq_one hf0]
    | succ b ih =>
        intro hb
        rw [NewtonPolygon₀.vertexX_succ, NewtonPolygon₀.vertexX_succ, ih (by omega),
          (hagree b (by omega)).2]
  exact step_of_segment_data ((hagree a ha).1.trans (slopes_eq_of_step hv))
    ((hvx (a + 1) (by omega)).trans (newtonPolygon₀OfSeq_vertexX (coeffVal f) hv))

/-- **The `nextVertex` case of the "no other zeros" half.**  If the `k`-th segment of the
polygon of `f` genuinely ends at `x = j₀`, every zero of `f` in the closed ball of radius
`exp m` lies on a sphere `exp μ` for one of the first `k + 1` slopes: the zero is a root of
the polynomial factor `g` of 5.13, and strictly between two consecutive slope radii — or below
the first — the vertex term of `g` strictly dominates, so `g` has no root there.
[T] `test.lean:3387`. -/
private theorem norm_eq_exp_slope_aux [CompleteSpace K] (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1) {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (k + 1) = ((j₀ : ℤ) : WithTop ℤ))
    (hconv : PowerSeries.IsRestricted (Real.exp m) f)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ ≤ Real.exp m)
    (hzero : HasSum (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) 0) :
    ∃ (a : ℕ) (μ : ℝ), a ≤ k ∧
      (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ) ∧
      ‖x‖ = Real.exp μ := by
  classical
  obtain ⟨j₁, l, hseg⟩ := step_of_segment_data hm hj
  -- the Weierstrass factorisation along the polygon, and `x` as a root of its polynomial part
  obtain ⟨g, h, hfeq, hdeg, hg0, -, hhconv, hh1, hpoly⟩ :=
    exists_weierstrass_factorisation f hf0 hm hj hconv
  have hgzero : Polynomial.aeval x g = 0 :=
    (hasSum_zero_iff_aeval_eq_zero f hf0 hm hj hconv g h hfeq hdeg hhconv hh1 hL hx).mp hzero
  have hg0' : PowerSeries.coeff 0 (g : PowerSeries K) = 1 := (Polynomial.coeff_coe g 0).trans hg0
  -- the norm of `L` as a valuation
  set w : Valuation L NNReal :=
    { toFun := fun y => ‖y‖₊
      map_zero' := nnnorm_zero
      map_one' := nnnorm_one
      map_mul' := fun a b => nnnorm_mul a b
      map_add_le_max' := fun a b => IsUltrametricDist.nnnorm_add_le_max a b } with hwdef
  have hwapp : ∀ y : L, w y = ‖y‖₊ := fun _ => rfl
  have hw : ∀ a : K, w (algebraMap K L a) = ‖a‖₊ := fun a => by
    rw [hwapp]
    exact NNReal.coe_injective (by simpa using hL a)
  have hwx : (w x : ℝ) = ‖x‖ := rfl
  -- the middle-window contradiction: between two consecutive slope radii the vertex dominates
  have hmid : ∀ a, a + 1 ≤ k → ∀ {v₀ lv : ℕ} {v₁ μ : ℝ},
      newtonPolygon (coeffVal f) a = some (.nextVertex v₀ v₁ lv μ) → Real.exp μ < ‖x‖ →
      ∀ {u₀ lu : ℕ} {u₁ μ' : ℝ},
      newtonPolygon (coeffVal f) (a + 1) = some (.nextVertex u₀ u₁ lu μ') →
      ‖x‖ < Real.exp μ' → False := by
    intro a ha v₀ lv v₁ μ hv hxgt u₀ lu u₁ μ' hu hxlt
    -- transfer both vertices to the polygon of `g`
    obtain ⟨v₁', lv', hgv⟩ := newtonPolygon_transfer hf0 hg0' hpoly (by omega) hv
    obtain ⟨u₁', lu', hgu⟩ := newtonPolygon_transfer hf0 hg0' hpoly ha hu
    -- data of the vertex `(v₀, v₁')` on `g`
    obtain ⟨p₀, p₁, hpv⟩ := nextStep_nextVertex _ hgv
    obtain ⟨hgV, hyval⟩ := coeffVal_eq_coe_iff (nextVertex_j₁_eq _ hpv)
    rw [Polynomial.coeff_coe] at hgV hyval
    -- the step from `(v₀, v₁')` to `(u₀, u₁')` on `g`, and the line relation
    have hstep : nextStep (coeffVal (g : PowerSeries K)) v₀ v₁' = .nextVertex u₀ u₁' lu' μ' :=
      nextStep_nextVertex'' _ hgu hgv
    have hvu : v₀ < u₀ := nextVertex_lt _ hstep
    have hvuR : (0 : ℝ) < (u₀ : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast hvu)
    have hslope := nextVertex_slope_eq_sInf' _ hstep
    rw [slopeReal_real] at hslope
    have hu₁ : u₁' = v₁' + μ' * ((u₀ : ℝ) - v₀) := by
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
      · have hgt' : PowerSeries.coeff t (g : PowerSeries K) ≠ 0 := by rwa [Polynomial.coeff_coe]
        rw [show ‖x‖ = Real.exp (Real.log ‖x‖) from (Real.exp_log hr0).symm]
        refine (term_lt_term_iff' hgt hgV (Real.exp_pos _) t v₀).mpr ?_
        rw [Real.log_exp, ← hyval]
        rcases Nat.lt_or_ge t v₀ with htv | htv
        · -- below the vertex: the `a`-th line with slope `μ < log ‖x‖`
          have hline := vertex_line_le' (g : PowerSeries K) hg0' a hgv t hgt'
          rw [Polynomial.coeff_coe] at hline
          have htvR : ((t : ℝ) - v₀) < 0 := sub_neg.mpr (by exact_mod_cast htv)
          nlinarith [hline, mul_lt_mul_of_neg_right hlogl htvR]
        · -- above the vertex: the `(a + 1)`-th line with slope `μ' > log ‖x‖`
          have htv' : v₀ < t := lt_of_le_of_ne htv (Ne.symm ht)
          have hline := vertex_line_le' (g : PowerSeries K) hg0' (a + 1) hgu t hgt'
          rw [Polynomial.coeff_coe] at hline
          have htvR : (0 : ℝ) < (t : ℝ) - v₀ := sub_pos.mpr (by exact_mod_cast htv')
          have h2 : μ' * ((t : ℝ) - v₀) ≤ -Real.log ‖g.coeff t‖ - v₁' := by
            nlinarith [hline, hu₁]
          nlinarith [h2, mul_lt_mul_of_pos_right hlogr htvR]
    have hwx0 : w x ≠ 0 := nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp hr0)
    exact aeval_ne_zero_of_dominant_at w hw g hgV hwx0 hdom hgzero
  -- walk down the polygon from the `k`-th vertex to the window containing `‖x‖`
  have key : ∀ a, a ≤ k → ∀ {v₀ lv : ℕ} {v₁ μ : ℝ},
      newtonPolygon (coeffVal f) a = some (.nextVertex v₀ v₁ lv μ) → ‖x‖ ≤ Real.exp μ →
      ∃ (b : ℕ) (ν : ℝ), b ≤ k ∧
        (newtonPolygon₀OfPowerSeries negLogNorm f).slopes b = (ν : WithBotTop ℝ) ∧
        ‖x‖ = Real.exp ν := by
    intro a
    induction a with
    | zero =>
        intro _ v₀ lv v₁ μ hv hxle
        rcases eq_or_lt_of_le hxle with heq | hlt
        · exact ⟨0, μ, Nat.zero_le k, slopes_eq_of_step hv, heq⟩
        · -- the first window: below the first slope the constant term of `g` dominates
          exfalso
          obtain ⟨v₁', lv', hgv⟩ := newtonPolygon_transfer hf0 hg0' hpoly (Nat.zero_le k) hv
          have hv0g : nextStep (coeffVal (g : PowerSeries K)) 0 (0 : ℝ)
              = .nextVertex v₀ v₁' lv' μ :=
            Option.some_inj.mp ((newtonPolygon_coeffVal_zero hg0').symm.trans hgv)
          have hV₀pos : 0 < v₀ := nextVertex_lt _ hv0g
          have hV₀R : (0 : ℝ) < (v₀ : ℝ) := by exact_mod_cast hV₀pos
          have hslope := nextVertex_slope_eq_sInf' _ hv0g
          rw [slopeReal_real] at hslope
          have hy₀ : v₁' = μ * v₀ := by
            rw [eq_div_iff (by push_cast; simpa using hV₀R.ne')] at hslope
            push_cast at hslope
            linarith
          have hg0ne : g.coeff 0 ≠ 0 := hg0 ▸ one_ne_zero
          have hdom : ∀ t, 1 ≤ t → ‖g.coeff t‖ * Real.exp μ ^ t ≤ ‖g.coeff 0‖ := by
            intro t ht
            by_cases hgt : g.coeff t = 0
            · rw [hgt, norm_zero, zero_mul, hg0, norm_one]
              norm_num
            · have hgt' : PowerSeries.coeff t (g : PowerSeries K) ≠ 0 := by
                rwa [Polynomial.coeff_coe]
              have h1 := (term_le_term_iff' hgt hg0ne (Real.exp_pos μ) t 0).mpr ?_
              · simpa using h1
              · rw [Real.log_exp, hg0, norm_one, Real.log_one]
                have hline := vertex_line_le' (g : PowerSeries K) hg0' 0 hgv t hgt'
                rw [Polynomial.coeff_coe] at hline
                push_cast
                nlinarith [hline, hy₀]
          exact aeval_ne_zero_of_dominant_lt w hw g hg0ne hdom (by rw [hwx]; exact hlt) hgzero
    | succ a ih =>
        intro ha v₀ lv v₁ μ hv hxle
        rcases eq_or_lt_of_le hxle with heq | hlt
        · exact ⟨a + 1, μ, ha, slopes_eq_of_step hv, heq⟩
        · obtain ⟨u₀, u₁, lu, μ', hu⟩ := nextStep_nextVertex' _ hv
          rcases le_or_gt ‖x‖ (Real.exp μ') with hle' | hgt'
          · exact ih (by omega) hu hle'
          · exact (hmid a ha hu hgt' hv hlt).elim
  exact key k le_rfl hseg hx

/-- **Blueprint Corollary 5.14, "no other zeros" half.**  Let `L/K` be a *complete*
ultrametric extension (the blueprint's `ℂ_p`) and suppose `f` converges on the closed ball of
radius `exp m`, where `m` is the `k`-th slope of the Newton polygon of `f`.  Then every zero
of `f` in that ball lies on a sphere of radius `exp μ` for one of the first `k + 1` slopes
`μ`.  [T] `test.lean:3387`. -/
theorem norm_eq_exp_slope_of_hasSum_zero [CompleteSpace K] (f : PowerSeries K)
    (hf0 : PowerSeries.coeff 0 f = 1)
    {k : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hconv : PowerSeries.IsRestricted (Real.exp m) f)
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [Algebra K L] (hL : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {x : L} (hx : ‖x‖ ≤ Real.exp m)
    (hzero : HasSum (fun t => algebraMap K L (PowerSeries.coeff t f) * x ^ t) 0) :
    ∃ (a : ℕ) (μ : ℝ), a ≤ k ∧
      (newtonPolygon₀OfPowerSeries negLogNorm f).slopes a = (μ : WithBotTop ℝ) ∧
      ‖x‖ = Real.exp μ := by
  classical
  obtain ⟨s, hs, hsm⟩ := exists_step_of_slopes_eq' hm
  rcases s with _ | _ | m' | m' | ⟨q₀, q₁, lq, m'⟩
  · exact ((WithBotTop.coe_ne_top m) (show (m : WithBotTop ℝ) = ⊤ from hsm.symm)).elim
  · exact ((WithBotTop.coe_ne_bot m) (show (m : WithBotTop ℝ) = ⊥ from hsm.symm)).elim
  · -- a limiting ray: no zero of `f` has radius above the previous slope's
    rw [show m' = m from WithBotTop.coe_injective hsm] at hs
    rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
    · exact (not_hasSum_zero_of_norm_eq_zero hf0 hconv hL hx hx0.symm hzero).elim
    · rcases k with _ | b
      · -- the ray leaves the origin: the constant term dominates on the whole ball
        have hstep : nextStep (coeffVal f) 0 (0 : ℝ) = .limitingRay m :=
          Option.some_inj.mp ((newtonPolygon_coeffVal_zero hf0).symm.trans hs)
        refine (not_hasSum_zero_of_limitingRay (μ := Real.log ‖x‖ - 1) hconv hstep
          (by rw [hf0]; exact one_ne_zero) (by rw [hf0, norm_one, Real.log_one, neg_zero])
          (fun t ht _ => absurd ht (Nat.not_lt_zero t)) hL hx ?_ hzero).elim
        rw [Real.exp_sub, Real.exp_log hx0]
        exact div_lt_self hx0 (by linarith [Real.add_one_le_exp (1 : ℝ)])
      · -- the ray leaves the `b`-th vertex: below it, recurse on the `b`-th segment
        obtain ⟨v₀, v₁, lv, μ, hprev⟩ := nextStep_limitingRay' _ hs
        have hstep : nextStep (coeffVal f) v₀ v₁ = .limitingRay m :=
          nextStep_limitingRay'' _ hs hprev
        obtain ⟨p₀, p₁, hpv⟩ := nextStep_nextVertex _ hprev
        have hμm : μ ≤ m := slopes_increasing_limitingRay _ hpv hstep
        rcases le_or_gt ‖x‖ (Real.exp μ) with hle | hgt
        · obtain ⟨a, ν, ha, hν, hxν⟩ := norm_eq_exp_slope_aux f hf0 (slopes_eq_of_step hprev)
            (newtonPolygon₀OfSeq_vertexX (coeffVal f) hprev)
            (isRestricted_of_le f (Real.exp_pos μ).le (Real.exp_le_exp.mpr hμm) hconv) hL hle
            hzero
          exact ⟨a, ν, by omega, hν, hxν⟩
        · obtain ⟨hv₀ne, hv₁val⟩ := coeffVal_eq_coe_iff (nextVertex_j₁_eq _ hpv)
          exact (not_hasSum_zero_of_limitingRay hconv hstep hv₀ne hv₁val
            (fun t _ hat => vertex_line_le' f hf0 b hprev t hat) hL hx hgt hzero).elim
  · -- an infinite ray is impossible at a radius of convergence
    rw [show m' = m from WithBotTop.coe_injective hsm] at hs
    rcases k with _ | b
    · exact absurd (Option.some_inj.mp ((newtonPolygon_coeffVal_zero hf0).symm.trans hs))
        (nextStep_ne_infiniteRay hconv)
    · obtain ⟨v₀, v₁, lv, μ, hprev⟩ := nextStep_infiniteRay' _ hs
      exact absurd (nextStep_infiniteRay'' _ hs hprev) (nextStep_ne_infiniteRay hconv)
  · -- an honest segment: the Weierstrass factorisation applies
    rw [show m' = m from WithBotTop.coe_injective hsm] at hs
    exact norm_eq_exp_slope_aux f hf0 hm (newtonPolygon₀OfSeq_vertexX (coeffVal f) hs) hconv hL
      hx hzero
