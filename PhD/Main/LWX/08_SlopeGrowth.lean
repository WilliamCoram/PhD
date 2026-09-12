/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«07_SlopeRatios»

/-!
# The slope ratios increase to infinity

[LWX, Theorem 1.5] asks for the `T`-free ratios `α₀(ω), α₁(ω), …` to be "in increasing order
and tending to infinity".  `PhD/Main/LWX/07_SlopeRatios.lean` proves the identity
`slope_j(T) = v(T)·slopeRatio j` but says nothing about how the ratios themselves behave; this
file supplies the two missing clauses.

Both are unconditional: unlike the identity, they need neither the small-annulus hypothesis nor
the touching hypothesis, only the halo estimate that is already proved.

* increasing is convexity of the shape polygon (`NewtonPolygon₀.monotone_toReal_unitSlope`, with
  the finiteness of its heights from `height_shapePolygon_ne_top`);
* tending to infinity is the lower bound polygon.  Units of the integral matrix occur only at
  heights `≥ λ(n)` ([LWX, Cor 3.18]), so the shape sequence dominates `λ`, whose increments
  `⌊k/t⌋ − ⌊k/(pt)⌋` grow without bound.  For each `M` the line `y = M·x − M²pt` lies on or below
  every point of the shape, so it lies on or below the shape polygon
  (`IsNewtonPolygonOf.line_le_height`); comparing that with the height as the sum of the first `n`
  slopes and using monotonicity gives a slope `≥ M − 1`.

## Main declarations

* `LWX.monotone_slopeRatio` — the ratios are increasing.
* `LWX.tendsto_slopeRatio_atTop` — the ratios tend to infinity.
-/

open Filter Topology Finset TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The ratios are increasing** ([LWX, Thm 1.5]: "in increasing order"): the shape polygon is
convex and has finite heights. -/
theorem monotone_slopeRatio (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] : Monotone (slopeRatio D ω) :=
  (shapePolygon D ω).monotone_toReal_unitSlope (by rw [shapePolygon_starting_point])
    (fun k => height_shapePolygon_ne_top hp2 D ω k)

/-- The shape sequence dominates the lower bound sequence `λ` ([LWX, Cor 3.18]: a unit
coefficient forces the height to be at least `λ(n)`). -/
theorem lwxLambda_le_pointHeight_shapeVal (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    ((lwxLambda p (Fintype.card ι) n : ℝ) : WithBotTop ℝ) ≤ pointHeight (shapeVal D ω) n := by
  classical
  by_cases hb : IsBelowUpper D ω n
  · rw [pointHeight_coe (shapeVal_of_isBelowUpper D ω hb)]
    have hmem : IsUnit ((charCoeff (D.op ω) n) ((unitIndex D ω n : ℕ) : ℤ)) := by
      have hne : {m : ℕ | IsUnit ((charCoeff (D.op ω) n) (m : ℤ))}.Nonempty := hb.1
      exact Nat.sInf_mem hne
    have hle := lwxLambda_le_of_isUnit hp2 D ω hmem
    have : (lwxLambda p (Fintype.card ι) n : ℝ) ≤ ((unitIndex D ω n : ℕ) : ℝ) := by
      exact_mod_cast hle
    simpa using this
  · by_cases hd : p * Fintype.card ι ∣ n
    · have hval : shapeVal D ω n = ((lwxLambda p (Fintype.card ι) n : ℝ) : WithTop ℝ) := by
        rw [shapeVal, if_neg hb, if_pos hd]
      rw [pointHeight_coe hval]
      simp
    · have hval : shapeVal D ω n = ⊤ := by rw [shapeVal, if_neg hb, if_neg hd]
      rw [pointHeight_eq_top_iff.mpr hval]
      exact le_top

/-- The increments of `λ` pass every bound: `⌊k/t⌋ − ⌊k/(pt)⌋ ≥ M` once `k ≥ M·p·t`. -/
private theorem le_div_sub_div {t : ℕ} (ht : 0 < t) (M k : ℕ) (hk : M * (p * t) ≤ k) :
    M ≤ k / t - k / (p * t) := by
  have hpt : 0 < p * t := Nat.mul_pos hp.out.pos ht
  have hMd : M ≤ k / (p * t) := (Nat.le_div_iff_mul_le hpt).mpr hk
  have hdd : k / (p * t) = k / t / p := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm t p]
  have h1 : p * (k / (p * t)) ≤ k / t := by
    rw [hdd, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have h2 : 2 * (k / (p * t)) ≤ p * (k / (p * t)) :=
    Nat.mul_le_mul_right _ hp.out.two_le
  omega

/-- **The lower bound line**: `M·n ≤ λ(n) + M²pt` for every `M` and `n`. -/
private theorem mul_le_lwxLambda_add {t : ℕ} (ht : 0 < t) (M n : ℕ) :
    M * n ≤ lwxLambda p t n + M * (M * (p * t)) := by
  rcases Nat.le_total n (M * (p * t)) with hn | hn
  · exact le_trans (Nat.mul_le_mul_left M hn) (Nat.le_add_left _ _)
  · have hsub : Finset.Ico (M * (p * t)) n ⊆ Finset.range n := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      exact Finset.mem_range.mpr hx.2
    have hcard : M * (n - M * (p * t)) = ∑ _k ∈ Finset.Ico (M * (p * t)) n, M := by
      rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.mul_comm]
    have hstep : ∑ _k ∈ Finset.Ico (M * (p * t)) n, M
        ≤ ∑ k ∈ Finset.Ico (M * (p * t)) n, (k / t - k / (p * t)) :=
      Finset.sum_le_sum fun k hk => le_div_sub_div ht M k (Finset.mem_Ico.mp hk).1
    have hall : ∑ k ∈ Finset.Ico (M * (p * t)) n, (k / t - k / (p * t))
        ≤ lwxLambda p t n :=
      Finset.sum_le_sum_of_subset hsub
    have hkey : M * (n - M * (p * t)) ≤ lwxLambda p t n := by
      rw [hcard]
      exact hstep.trans hall
    rw [Nat.mul_sub] at hkey
    have hle : M * (M * (p * t)) ≤ M * n := Nat.mul_le_mul_left M hn
    omega

/-- **The lower bound line lies on or below the shape polygon.** -/
theorem line_le_height_shapePolygon (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (M n : ℕ) :
    (((-((M * (M * (p * Fintype.card ι)) : ℕ) : ℝ) + (M : ℝ) * n : ℝ)) : WithBotTop ℝ)
      ≤ (shapePolygon D ω).height n := by
  refine (isNewtonPolygonOf_shapePolygon D ω).line_le_height
    (by rw [shapePolygon_starting_point]) (fun k => ?_) n
  refine le_trans ?_ (lwxLambda_le_pointHeight_shapeVal hp2 D ω k)
  rw [WithBotTop.coe_le_coe]
  have h := mul_le_lwxLambda_add (p := p) (t := Fintype.card ι)
    (Fintype.card_pos (α := ι)) M k
  have h' : (M : ℝ) * k ≤ (lwxLambda p (Fintype.card ι) k : ℝ)
      + ((M * (M * (p * Fintype.card ι)) : ℕ) : ℝ) := by exact_mod_cast h
  linarith

/-- Every bound is passed by some ratio. -/
theorem exists_le_slopeRatio (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (M : ℕ) : ∃ j, ((M : ℝ) - 1) ≤ slopeRatio D ω j := by
  refine ⟨M * (M * (p * Fintype.card ι)), ?_⟩
  have hN0 : 0 < M * (M * (p * Fintype.card ι)) + 1 := Nat.succ_pos _
  have hsr : ∀ i : ℕ,
      NewtonPolygon.toReal ((shapePolygon D ω).unitSlope i) = slopeRatio D ω i := fun _ => rfl
  have hline := line_le_height_shapePolygon hp2 D ω M (M * (M * (p * Fintype.card ι)) + 1)
  rw [height_shapePolygon_eq_toReal hp2 D ω _, WithBotTop.coe_le_coe,
    toReal_height_shapePolygon hp2 D ω _] at hline
  simp only [hsr] at hline
  have hbnd : ∑ i ∈ Finset.range (M * (M * (p * Fintype.card ι)) + 1), slopeRatio D ω i
      ≤ ((M * (M * (p * Fintype.card ι)) + 1 : ℕ) : ℝ)
        * slopeRatio D ω (M * (M * (p * Fintype.card ι))) := by
    have hsum := Finset.sum_le_card_nsmul (Finset.range (M * (M * (p * Fintype.card ι)) + 1))
      (slopeRatio D ω) (slopeRatio D ω (M * (M * (p * Fintype.card ι))))
      (fun i hi => monotone_slopeRatio hp2 D ω
        (by rw [Finset.mem_range] at hi; omega))
    simpa [nsmul_eq_mul] using hsum
  have hNR : (0 : ℝ) < ((M * (M * (p * Fintype.card ι)) + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hMN : ((M * (M * (p * Fintype.card ι)) : ℕ) : ℝ)
      ≤ ((M * (M * (p * Fintype.card ι)) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ _
  have hfinal : ((M * (M * (p * Fintype.card ι)) + 1 : ℕ) : ℝ) * ((M : ℝ) - 1)
      ≤ ((M * (M * (p * Fintype.card ι)) + 1 : ℕ) : ℝ)
        * slopeRatio D ω (M * (M * (p * Fintype.card ι))) := by
    have hrw : ((M * (M * (p * Fintype.card ι)) + 1 : ℕ) : ℝ) * ((M : ℝ) - 1)
        = (M : ℝ) * ((M * (M * (p * Fintype.card ι)) + 1 : ℕ) : ℝ)
          - ((M * (M * (p * Fintype.card ι)) + 1 : ℕ) : ℝ) := by ring
    rw [hrw]
    linarith
  exact le_of_mul_le_mul_left hfinal hNR

/-- **The ratios tend to infinity** ([LWX, Thm 1.5]: "tending to infinity"). -/
theorem tendsto_slopeRatio_atTop (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] : Tendsto (slopeRatio D ω) atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone (monotone_slopeRatio hp2 D ω) fun b => ?_
  obtain ⟨j, hj⟩ := exists_le_slopeRatio hp2 D ω (⌈b⌉₊ + 1)
  refine ⟨j, le_trans ?_ hj⟩
  have : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  push_cast
  linarith

end LWX

end
