/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.Vertices
import PhD.LWX.Claim

/-!
# Slope ratios near the boundary: [LWX, Theorem 1.5], first half

Granting the Claim of [LWX, §4.2] (`Claim.lean`) and the touching hypothesis at every `n_k`
(`HasUnitBand`, `Vertices.lean`), [LWX] concludes that for `T` in the small annulus
`0 < v(T) < 8/((p²−1)t+8)` the Newton polygon of `∑ c_n(T)Xⁿ` is the convex hull of the
`T`-free point set `{(n_k, λ(n_k))} ∐ {(l, m(l)) : l strictly below the upper polygon}`,
scaled by `v(T)`; "it is then clear that the ratios to `v(T)` of the slopes of this polygon
are independent of `T`".

* `shapeVal D ω` — the `T`-free point set as a valuation sequence, `shapePolygon` its Newton
  polygon (unconditionally well defined), `slopeRatio D ω j` its `j`-th unit slope: the
  sequence `φ(q)·α̃_j(ω)` of [LWX, Thm 1.5] (slopes counted with multiplicity);
* `height_specCharSeries_eq_smul_shape` — the two hulls agree (`v(T)`-scaled);
* **`unitSlope_specCharSeries_eq_slopeRatio`** — [LWX, (1.5.1)] at the polygon level:
  `slope_j(T) = v(T)·slopeRatio j` for every `T` in the small annulus.
-/

open Filter Topology Finset TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `T`-free shape: `m(l)` at indices strictly below the upper polygon, `λ(n_k)` at the
touching vertices `n_k = k·p·t`, and no point (`⊤`) elsewhere. -/
def shapeVal (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) : WithTop ℝ :=
  open Classical in
  if IsBelowUpper D ω n then ((unitIndex D ω n : ℝ) : WithTop ℝ)
  else if p * Fintype.card ι ∣ n then ((lwxLambda p (Fintype.card ι) n : ℝ) : WithTop ℝ)
  else ⊤

/-- The Newton polygon of the `T`-free shape. -/
def shapePolygon (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : NewtonPolygon₀ (Γ := ℝ) :=
  newtonPolygon₀OfSeq (shapeVal D ω)

/-- The `T`-free slope ratios: `slopeRatio D ω j = φ(q)·α̃_j(ω)` in the notation of
[LWX, Thm 1.5]. -/
def slopeRatio (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (j : ℕ) : ℝ :=
  NewtonPolygon.toReal ((shapePolygon D ω).unitSlope j)

/-- `0` is never strictly below the upper polygon (`lwxUpperTwice 0 = 0`). -/
theorem not_isBelowUpper_zero (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ¬ IsBelowUpper D ω 0 := by
  rintro ⟨-, hlt⟩
  simp [lwxUpperTwice] at hlt

/-- The shape at `0`: the vertex value `λ(0) = 0`. -/
theorem shapeVal_zero (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    shapeVal D ω 0 = ((0 : ℝ) : WithTop ℝ) := by
  rw [shapeVal, if_neg (not_isBelowUpper_zero D ω), if_pos (dvd_zero _)]
  simp [lwxLambda]

/-- A touching vertex is never strictly below the upper polygon (`m(n_k) ≥ λ(n_k) = upper(n_k)`). -/
theorem not_isBelowUpper_touchX (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (k : ℕ) : ¬ IsBelowUpper D ω (touchX p (Fintype.card ι) k) := by
  rintro ⟨hex, hlt⟩
  have := lwxLambda_le_unitIndex hp2 D ω hex
  rw [lwxUpperTwice_touchX] at hlt
  omega

/-- The shape at a touching vertex is `λ(n_k)`. -/
theorem shapeVal_touchX (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    shapeVal D ω (touchX p (Fintype.card ι) k) =
      ((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) : ℝ) : WithTop ℝ) := by
  rw [shapeVal, if_neg (not_isBelowUpper_touchX hp2 D ω k),
    if_pos (show p * Fintype.card ι ∣ touchX p (Fintype.card ι) k from ⟨k, by rw [touchX,
        mul_comm]⟩)]

/-- The shape at an index strictly below the upper polygon is `m(l)`. -/
theorem shapeVal_of_isBelowUpper (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {n : ℕ}
    (h : IsBelowUpper D ω n) : shapeVal D ω n = ((unitIndex D ω n : ℝ) : WithTop ℝ) := by
  rw [shapeVal, if_pos h]

/-- The shape has a point at `0`. -/
theorem exists_shapeVal_ne_top (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ∃ i, shapeVal D ω i ≠ ⊤ :=
  ⟨0, by rw [shapeVal_zero]; exact WithTop.coe_ne_top⟩

/-- The shape is admissible (all its values are `≥ 0`). -/
theorem isAdmissible_shapeVal (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    IsAdmissible (shapeVal D ω) := by
  classical
  refine isAdmissible_of_affine_bound (shapeVal D ω) (m := 0) (b := 0) fun k a hva ↦ ?_
  simp only [Algebra.algebraMap_self, RingHom.id_apply, zero_mul, zero_add]
  unfold shapeVal at hva
  split_ifs at hva with h h'
  · rw [WithTop.coe_inj.mp hva.symm]
    exact Nat.cast_nonneg _
  · rw [WithTop.coe_inj.mp hva.symm]
    exact Nat.cast_nonneg _
  · exact absurd hva WithTop.top_ne_coe

/-- The shape polygon has no `⊥` unit slope. -/
theorem unitSlope_shapePolygon_ne_bot (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (j : ℕ) :
    (shapePolygon D ω).unitSlope j ≠ ⊥ :=
  newtonPolygon₀OfSeq_unitSlope_ne_bot _ (exists_shapeVal_ne_top D ω) (isAdmissible_shapeVal D ω) j

/-- The shape has a point at `0` (`λ(0) = 0` at the vertex `n₀ = 0`) and is admissible, so its
Newton polygon exists. -/
theorem isNewtonPolygonOf_shapePolygon (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    IsNewtonPolygonOf (shapeVal D ω) (shapePolygon D ω) :=
  isNewtonPolygonOf_newtonPolygon₀OfSeq _ (exists_shapeVal_ne_top D ω) (isAdmissible_shapeVal D ω)

/-- The shape polygon is anchored at the origin. -/
theorem shapePolygon_starting_point (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    (shapePolygon D ω).starting_point = (0, 0) := by
  have hP := isNewtonPolygonOf_shapePolygon D ω
  have hv0 := shapeVal_zero D ω
  have hle : (shapePolygon D ω).starting_point.1 ≤ ((0 : ℕ) : ℤ) :=
    hP.starting_point_fst_le (by rw [hv0]; exact WithTop.coe_ne_top)
  obtain ⟨k, hk, hvk⟩ := hP.start_mem
  have hk0 : k = 0 := by omega
  subst hk0
  rw [hv0] at hvk
  have h2 : (shapePolygon D ω).starting_point.2 = 0 := (WithTop.coe_inj.mp hvk).symm
  refine Prod.ext ?_ h2
  simpa using hk.symm

/-- The shape polygon lies on/below the upper bound polygon (it passes below every touching
vertex and is convex). -/
theorem height_shapePolygon_le (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (n : ℕ) :
    (shapePolygon D ω).height n ≤
      (((lwxUpperTwice p (Fintype.card ι) n : ℝ) / 2 : ℝ) : WithBotTop ℝ) := by
  have hP := isNewtonPolygonOf_shapePolygon D ω
  have hst := shapePolygon_starting_point D ω
  have hpt : 0 < p * Fintype.card ι := Nat.mul_pos hp.out.pos Fintype.card_pos
  have hvert : ∀ k, (shapePolygon D ω).height (touchX p (Fintype.card ι) k) ≤
      ((lwxLambda
          p (Fintype.card ι) (touchX p (Fintype.card ι) k) : ℝ) : WithBotTop ℝ) := fun k ↦ by
    refine (hP.height_le _).trans (le_of_eq ?_)
    rw [pointHeight_coe (shapeVal_touchX hp2 D ω k), Algebra.algebraMap_self_apply]
  obtain ⟨k, x, hx, rfl⟩ : ∃ k x : ℕ,
      x ≤ p * Fintype.card ι ∧ n = touchX p (Fintype.card ι) k + x :=
    ⟨n / (p * Fintype.card ι), n % (p * Fintype.card ι), (Nat.mod_lt n hpt).le, by
      rw [touchX, Nat.mul_comm (n / (p * Fintype.card ι)) (p * Fintype.card ι), Nat.div_add_mod]⟩
  have hk1 : touchX p (Fintype.card
      ι) (k + 1) = touchX p (Fintype.card ι) k + p * Fintype.card ι := by
    rw [touchX, touchX, Nat.succ_mul]
  have hchord := (shapePolygon D ω).height_le_chord (x := touchX p (Fintype.card ι) k)
    (y := ((touchX p (Fintype.card ι) k + x : ℕ) : ℤ)) (z := touchX p (Fintype.card ι) (k + 1))
    (by simp [hst]) (by omega) (by omega) (hvert k) (hvert (k + 1))
  refine hchord.trans (le_of_eq ?_)
  congr 1
  have hU := lwxUpperTwice_touchX_add p (Fintype.card ι) k x hx
  have hA := lwxUpperTwice_touchX p (Fintype.card ι) k
  have hB := lwxUpperTwice_touchX p (Fintype.card ι) (k + 1)
  have hB' := lwxUpperTwice_touchX_add p (Fintype.card ι) k (p * Fintype.card ι) le_rfl
  rw [← hk1] at hB'
  have hpt' : ((touchX
      p (Fintype.card ι) (k + 1) : ℤ) : ℝ) - ((touchX p (Fintype.card ι) k : ℤ) : ℝ) =
      (p : ℝ) * Fintype.card ι := by
    rw [hk1]
    push_cast
    ring
  have hnx : (((touchX p (Fintype.card ι) k + x : ℕ) : ℤ) : ℝ) -
      ((touchX p (Fintype.card ι) k : ℤ) : ℝ) = x := by
    push_cast
    ring
  rw [hpt', hnx]
  have hpt0 : (p : ℝ) * Fintype.card ι ≠ 0 := by
    have : ((p * Fintype.card ι : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpt.ne'
    push_cast at this
    exact this
  have hUr : (lwxUpperTwice p (Fintype.card ι) (touchX p (Fintype.card ι) k + x) : ℝ) =
      2 * lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) +
        (x : ℝ) * ((2 * (k : ℝ) + 1) * ((p - 1 : ℕ) : ℝ)) := by
    rw [hU, hA]
    push_cast
    ring
  have hBr : (lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) (k + 1)) : ℝ) * 2 =
      2 * lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) +
        ((p : ℝ) * Fintype.card ι) * ((2 * (k : ℝ) + 1) * ((p - 1 : ℕ) : ℝ)) := by
    have h2 : 2 * lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) (k + 1)) =
        2 * lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) +
          p * Fintype.card ι * ((2 * k + 1) * (p - 1)) := by rw [← hB, ← hA, hB']
    have h3 := congrArg (fun m : ℕ ↦ (m : ℝ)) h2
    push_cast at h3
    linarith
  have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  have ht0' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hBeq : (lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) (k + 1)) : ℝ) =
      lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) +
        ((p : ℝ) * Fintype.card ι) * ((2 * (k : ℝ) + 1) * ((p - 1 : ℕ) : ℝ)) / 2 := by
    linarith
  rw [hUr, hBeq]
  field_simp
  ring

/-- The shape polygon has finite height everywhere. -/
theorem height_shapePolygon_ne_top (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (n : ℕ) : (shapePolygon D ω).height n ≠ ⊤ :=
  ne_top_of_le_ne_top (WithBotTop.coe_ne_top _) (height_shapePolygon_le hp2 D ω n)

/-- The shape polygon's heights are reals. -/
theorem height_shapePolygon_eq_toReal (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (n : ℕ) :
    (shapePolygon D ω).height n =
      (NewtonPolygon.toReal ((shapePolygon D ω).height n) : WithBotTop ℝ) := by
  have hbot : (shapePolygon D ω).height n ≠ ⊥ := by
    rw [Ne, NewtonPolygon₀.height_eq_bot_iff, shapePolygon_starting_point]
    exact not_lt.2 (Int.natCast_nonneg _)
  obtain ⟨r, hr⟩ := exists_coe_of_ne_bot_of_ne_top hbot (height_shapePolygon_ne_top hp2 D ω n)
  rw [hr, NewtonPolygon.toReal_coe]

/-- The shape polygon's height is the partial sum of its unit slopes. -/
theorem toReal_height_shapePolygon (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] (n : ℕ) :
    NewtonPolygon.toReal ((shapePolygon D ω).height n) =
      ∑ i ∈ Finset.range n, NewtonPolygon.toReal ((shapePolygon D ω).unitSlope i) := by
  have hst := shapePolygon_starting_point D ω
  have hst1 : (shapePolygon D ω).starting_point.1 = 0 := by rw [hst]
  have e := (shapePolygon D ω).height_eq_heightFun n
    (by rw [hst1, zero_add]; exact height_shapePolygon_ne_top hp2 D ω n)
  rw [hst1, zero_add, height_shapePolygon_eq_toReal hp2 D ω n] at e
  have e' : NewtonPolygon.toReal ((shapePolygon D ω).height n) = (shapePolygon D ω).heightFun n :=
    le_antisymm (WithBotTop.coe_le_coe.1 e.le) (WithBotTop.coe_le_coe.1 e.ge)
  rw [e', NewtonPolygon₀.heightFun, hst]
  simp

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The two hulls agree**: under the touching hypothesis at every `n_k`, for `T` in the small
annulus the Newton polygon of the specialized series is the shape polygon scaled by `v(T)`
([LWX, §4.2]: "the Newton polygon of `∑ c_n(T)Xⁿ` is the convex hull of the points
`{(n_k, λ(n_k)v(T))}_k ∐ {(l_i, m(l_i)v(T))}_i`"). -/
theorem height_specCharSeries_eq_smul_shape (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8))
    (hband : ∀ k, HasUnitBand D ω k) (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height n =
      (((-Real.log ‖T₀‖) * NewtonPolygon.toReal ((shapePolygon D ω).height n) : ℝ) :
        WithBotTop ℝ) := by
  classical
  have hNP := isNewtonPolygonOf_specCharSeries hp2 D ω ψ hψ h0 h1
  have hst := specCharSeries_starting_point_fst D ω ψ T₀
  have hP := isNewtonPolygonOf_shapePolygon D ω
  have hstS := shapePolygon_starting_point D ω
  have hstS1 : (shapePolygon D ω).starting_point.1 = 0 := by rw [hstS]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : (0 : ℝ) < ‖T₀‖ := (inv_pos.2 hp0).trans h0
  have hvT : 0 < -Real.log ‖T₀‖ := by
    have := Real.log_neg hr0 h1
    linarith
  have hpt : 0 < p * Fintype.card ι := Nat.mul_pos hp.out.pos Fintype.card_pos
  -- the specialized polygon has finite real heights (it passes through every touching vertex)
  have hTfin : ∀ m : ℕ,
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height m ≠ ⊤ := fun m ↦ by
    intro htop
    have hle : (m : ℤ) ≤ touchX p (Fintype.card ι) m := by
      have : m ≤ m * (p * Fintype.card ι) := Nat.le_mul_of_pos_right m hpt
      rw [touchX]
      exact_mod_cast this
    have := (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height_eq_top_mono
      htop hle
    rw [height_specCharSeries_touchX hp2 D ω ψ hψ h0 h1 (hband m)] at this
    exact WithBotTop.coe_ne_top _ this
  have hTbot : ∀ m : ℕ,
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height m ≠ ⊥ := fun m ↦ by
    rw [Ne, NewtonPolygon₀.height_eq_bot_iff, hst]
    exact not_lt.2 (Int.natCast_nonneg _)
  have hT : ∀ m : ℕ, (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height m =
      (NewtonPolygon.toReal
        ((newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height m) :
        WithBotTop ℝ) := fun m ↦ by
    obtain ⟨r, hr⟩ := exists_coe_of_ne_bot_of_ne_top (hTbot m) (hTfin m)
    rw [hr, NewtonPolygon.toReal_coe]
  have hTsum : ∀ m : ℕ, NewtonPolygon.toReal
      ((newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height m) =
      ∑ i ∈ Finset.range m, NewtonPolygon.toReal
        ((newtonPolygon₀OfPowerSeries
            negLogNorm (specCharSeries D ω ψ T₀)).unitSlope i) := fun m ↦ by
    have e := (newtonPolygon₀OfPowerSeries
        negLogNorm (specCharSeries D ω ψ T₀)).height_eq_heightFun m
      (by rw [hst, zero_add]; exact hTfin m)
    rw [hst, zero_add, hT m] at e
    have e' : NewtonPolygon.toReal
        ((newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height m) =
        (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).heightFun m :=
      le_antisymm (WithBotTop.coe_le_coe.1 e.le) (WithBotTop.coe_le_coe.1 e.ge)
    rw [e', NewtonPolygon₀.heightFun,
      newtonPolygon₀_starting_point_of_coeff_zero_eq_one (specCharSeries_coeff_zero D ω ψ T₀)]
    simp
  have hS := height_shapePolygon_eq_toReal hp2 D ω
  have hSsum := toReal_height_shapePolygon hp2 D ω
  have hσ := (shapePolygon D ω).monotone_toReal_unitSlope hstS1 (height_shapePolygon_ne_top hp2 D ω)
  have hτ := (newtonPolygon₀OfPowerSeries
      negLogNorm (specCharSeries D ω ψ T₀)).monotone_toReal_unitSlope
    hst hTfin
  -- (≥): the scaled shape hull is a competitor below every point of the specialized series
  set Q : NewtonPolygon₀ (Γ := ℝ) := NewtonPolygon₀.ofSlopes
    (fun j ↦ (-Real.log ‖T₀‖) * NewtonPolygon.toReal ((shapePolygon D ω).unitSlope j))
    (hσ.const_mul hvT.le) 0 with hQdef
  have hQh : ∀ m : ℕ, Q.height m =
      (((-Real.log ‖T₀‖) * NewtonPolygon.toReal ((shapePolygon D ω).height m) : ℝ) :
        WithBotTop ℝ) := fun m ↦ by
    rw [hQdef, NewtonPolygon₀.height_ofSlopes, hSsum, Finset.mul_sum, zero_add]
  have hQle : ∀ m : ℕ, Q.height m ≤ pointHeight (coeffVal (specCharSeries D ω ψ T₀)) m := fun m ↦ by
    rw [hQh]
    by_cases hm : IsBelowUpper D ω m
    · have h1' := hP.height_le m
      rw [pointHeight_eq_of_coeffVal_eq (shapeVal_of_isBelowUpper D ω hm), hS m,
        WithBotTop.coe_le_coe] at h1'
      rw [pointHeight_eq_of_coeffVal_eq
        (coeffVal_specCharSeries_eq_unitIndex_mul hp2 D ω ψ hψ h0 h1 hκ hm), WithBotTop.coe_le_coe]
      nlinarith
    · refine le_trans ?_ (le_pointHeight_of_le_coeffVal
        (le_coeffVal_specCharSeries_of_not_isBelowUpper hp2 D ω ψ hψ h0 h1 hκ hm))
      rw [WithBotTop.coe_le_coe]
      have h2' := height_shapePolygon_le hp2 D ω m
      rw [hS m, WithBotTop.coe_le_coe] at h2'
      nlinarith
  have hQ := hNP.isGreatest Q (by rw [hQdef, NewtonPolygon₀.ofSlopes_starting_point, hst]) hQle
  have hge : (((-Real.log ‖T₀‖) * NewtonPolygon.toReal ((shapePolygon D ω).height n) : ℝ) :
      WithBotTop ℝ) ≤ (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries
          D ω ψ T₀)).height n := by
    rw [← hQh n]
    exact NewtonPolygon₀.isBelow_iff_height.1 hQ n
  -- (≤): the rescaled specialized polygon is a competitor below every point of the shape
  set Q' : NewtonPolygon₀ (Γ := ℝ) := NewtonPolygon₀.ofSlopes
    (fun j ↦ NewtonPolygon.toReal
      ((newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j) /
        (-Real.log ‖T₀‖))
    (hτ.div_const hvT.le) 0 with hQ'def
  have hQ'h : ∀ m : ℕ, Q'.height m =
      ((NewtonPolygon.toReal
        ((newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height m) /
          (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) := fun m ↦ by
    rw [hQ'def, NewtonPolygon₀.height_ofSlopes, hTsum, Finset.sum_div, zero_add]
  have hQ'le : ∀ m : ℕ, Q'.height m ≤ pointHeight (shapeVal D ω) m := fun m ↦ by
    rw [hQ'h]
    by_cases hm : IsBelowUpper D ω m
    · rw [pointHeight_eq_of_coeffVal_eq (shapeVal_of_isBelowUpper D ω hm), WithBotTop.coe_le_coe,
        div_le_iff₀ hvT]
      have h1' := hNP.height_le m
      rw [pointHeight_eq_of_coeffVal_eq
        (coeffVal_specCharSeries_eq_unitIndex_mul hp2 D ω ψ hψ h0 h1 hκ hm), hT m,
        WithBotTop.coe_le_coe] at h1'
      exact h1'
    · by_cases hdvd : p * Fintype.card ι ∣ m
      · obtain ⟨k', hk'⟩ := hdvd
        have hm' : m = touchX p (Fintype.card ι) k' := by rw [touchX, hk', mul_comm]
        rw [pointHeight_eq_of_coeffVal_eq (show shapeVal D ω m =
            ((lwxLambda p (Fintype.card ι) m : ℝ) : WithTop ℝ) by
              rw [shapeVal, if_neg hm, if_pos ⟨k', hk'⟩]),
          WithBotTop.coe_le_coe, div_le_iff₀ hvT]
        have := height_specCharSeries_touchX hp2 D ω ψ hψ h0 h1 (hband k')
        rw [← hm', hT m] at this
        exact le_of_eq (le_antisymm
            (WithBotTop.coe_le_coe.1 this.le) (WithBotTop.coe_le_coe.1 this.ge))
      · rw [pointHeight_eq_top_iff.2 (by rw [shapeVal, if_neg hm, if_neg hdvd])]
        exact le_top
  have hQ' := hP.isGreatest Q' (by rw [hQ'def, NewtonPolygon₀.ofSlopes_starting_point, hstS1]) hQ'le
  have hle : NewtonPolygon.toReal
      ((newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).height n) /
        (-Real.log ‖T₀‖) ≤ NewtonPolygon.toReal ((shapePolygon D ω).height n) := by
    have := NewtonPolygon₀.isBelow_iff_height.1 hQ' n
    rw [hQ'h n, hS n, WithBotTop.coe_le_coe] at this
    exact this
  rw [hT n]
  refine le_antisymm ?_ (by rw [← hT n]; exact hge)
  rw [WithBotTop.coe_le_coe]
  rw [div_le_iff₀ hvT] at hle
  linarith

/-- **[LWX, Theorem 1.5, first half] at the polygon level** ((1.5.1)): under the touching
hypothesis at every `n_k`, for every `T` in the small annulus the `j`-th slope of the Newton
polygon of `∑ c_n(T)Xⁿ` is `v(T)·slopeRatio j`, with `slopeRatio` independent of `T`. -/
theorem unitSlope_specCharSeries_eq_slopeRatio (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8))
    (hband : ∀ k, HasUnitBand D ω k) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope j =
      (((-Real.log ‖T₀‖) * slopeRatio D ω j : ℝ) : WithBotTop ℝ) := by
  have hst := specCharSeries_starting_point_fst D ω ψ T₀
  have hstS1 : (shapePolygon D ω).starting_point.1 = 0 := by rw [shapePolygon_starting_point]
  have hj := height_specCharSeries_eq_smul_shape hp2 D ω ψ hψ h0 h1 hκ hband j
  have hj1 := height_specCharSeries_eq_smul_shape hp2 D ω ψ hψ h0 h1 hκ hband (j + 1)
  rw [(newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ T₀)).unitSlope_eq_of_height_eq
    hst (unitSlope_specCharSeries_ne_bot hp2 D ω ψ hψ h0 h1 j) hj hj1]
  rw [slopeRatio, (shapePolygon D ω).unitSlope_eq_of_height_eq hstS1
    (unitSlope_shapePolygon_ne_bot D ω j) (height_shapePolygon_eq_toReal hp2 D ω j)
    (height_shapePolygon_eq_toReal hp2 D ω (j + 1)), NewtonPolygon.toReal_coe]
  congr 1
  ring

end LWX

end
