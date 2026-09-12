/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«14_Touching»

/-!
# Step I of [LWX, Theorem 1.3] at conductor `p^{h+1}`

[LWX, §4.2] (`lwx.txt:2322–2336`) runs the Step I / Prop 3.22 argument again at a nebentypus
`ψ` of conductor `p^M`, `M = h + 1`: "Let `ψ` be a character of conductor `p^M`. We look at
weights of the form `(k, ψ)` for all `k ≥ 0`. First, note that `v(T_{(k,ψ)}) = q/ϕ(p^M) =
q/((p−1)p^{M−1})` by the assumption on `M`".  With `q = p` (odd `p`): `v(T) = 1/(p^{h−1}(p−1))`,
and the classical space `S^D_{k+2}(K^p Iw_{p^{h+1}}; ψ)` has dimension `(k+1)p^h t` by (3.21.1)
(`lwx.txt:1757–1760`: "`dim S^D_{k+2}(K^pIw_{p^m};ψ) = (k+1)q^{−1}p^m t`").

This file is `14_Touching.lean` at analyticity level `h` in place of `1`:

* `ClassicalDataH` — a halo point at level `h` whose norm is that of a classical point of
  conductor `p^{h+1}` (`‖T₀‖^{p^{h−1}(p−1)} = ‖p‖`) and whose level-`h` halo weight has the
  classical shape of exponent `k`;
* the arithmetic of [LWX, (3.23.1)] at the vertex `n = (k+1)p^h t = touchX p t ((k+1)p^{h−1})`;
* the touching `isStepOneTouching_of_atkinLehnerHypothesisH` and its hand-off
  `hasUnitBand_of_atkinLehnerHypothesisH`, granted H1 at level `h`
  (`AtkinLehnerHypothesis ψ h k`, stated at every level in `13_AtkinLehnerInst.lean`).

The level-`h` vertex `(k+1)p^h t` is the level-`1` vertex `n_{(k+1)p^{h−1}}`, so the touching
here adds nothing to `HasUnitBand` beyond what level `1` supplies; it is the faithful analogue
of Step I and a consistency check.  What [LWX, Thm 1.5]'s second half needs from level `h` is
H1 itself (`21_AtkinLehnerIdentityH.lean`) and the slope reflection of `23_ConductorSlopes.lean`.

Every level is `h ≥ 1` (conductor `p^{h+1}` with `h = 0` is the tame case, which is not in the
halo); the hypothesis `0 < h` is explicit wherever `p^{h−1}` occurs.  Nothing here depends on
Jacquet–Langlands (`.mathlib-quality/lwx-stepone/JL-AUDIT.md`).
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash
open scoped Nat TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The vertex `n = (k+1)p^h t` and [LWX, (3.23.1)] at level `h` -/

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The level-`h` vertex `(k+1)·p^h·t` is the level-`1` vertex `n_{(k+1)p^{h−1}}`
([LWX, §4.2]: "`(k+1)q^{−1}p^M t`" with `q = p`, `M = h + 1`). -/
theorem touchX_mul_prime_pow (h : ℕ) (hh : 0 < h) (t k : ℕ) :
    touchX p t ((k + 1) * p ^ (h - 1)) = t * ((k + 1) * p ^ h) := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [touchX, Nat.add_sub_cancel, pow_succ]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **[LWX, (3.23.1)] at conductor `p^{h+1}`**: at a point with
`v(T₀) = v(p)/(p^{h−1}(p−1))` ([LWX, §4.2]: "`v(T_{(k,ψ)}) = q/((p−1)p^{M−1})`"),
`2·λ(n)·v(T₀) = n·(k+1)·v(p)` for the vertex `n = t·(k+1)·p^h`. -/
theorem two_mul_lwxLambda_touchX_mul_eq_prime_pow (h : ℕ) (hh : 0 < h) (t k : ℕ) {T₀ c : K}
    (hT : ‖T₀‖ ^ (p ^ (h - 1) * (p - 1)) = ‖c‖) :
    2 * ((lwxLambda p t (touchX p t ((k + 1) * p ^ (h - 1))) : ℝ) * (-Real.log ‖T₀‖))
      = ((t * ((k + 1) * p ^ h) : ℕ) : ℝ) * ((k + 1) * (-Real.log ‖c‖)) := by
  have hp1 : 1 ≤ p := hp.out.one_le
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hT ⊢
  have hcast : (2 : ℝ) * ((lwxLambda p t (touchX p t ((k + 1) * p ^ h')) : ℕ) : ℝ)
      = (((k : ℝ) + 1) * (p : ℝ) ^ h') ^ 2 * p * ((p : ℝ) - 1) * t := by
    have hnat := congrArg (fun n : ℕ => (n : ℝ))
      (two_mul_lwxLambda_touchX p t ((k + 1) * p ^ h'))
    push_cast [Nat.cast_sub hp1] at hnat
    linarith
  have hlog : -Real.log ‖c‖ = ((p : ℝ) ^ h' * ((p : ℝ) - 1)) * (-Real.log ‖T₀‖) := by
    rw [← hT, Real.log_pow]
    push_cast [Nat.cast_sub hp1]
    ring
  rw [hlog]
  push_cast
  linear_combination (-Real.log ‖T₀‖) * hcast

/-! ### The classical data at a halo point of level `h` -/

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : ℕ) (ψ : ℚ_[p] →+* K)
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
  (uu : ι → Fin p → U)

/-- **A classical weight of conductor `p^{h+1}`, seen from the halo**: a halo point `T₀` at
analyticity level `h` whose norm is that of a classical point of conductor `p^{h+1}`
(`‖T₀‖^{p^{h−1}(p−1)} = ‖p‖`, i.e. `v(T₀) = v(p)/(p^{h−1}(p−1))`, [LWX, §2.1]:
"`v(T_{(k,ψ)}) = 1/p^{m−2}(p−1)` if `m ≥ 2`"), and whose level-`h` halo weight has the classical
shape of exponent `k`.  `ClassicalData` is the case `h = 1`. -/
structure ClassicalDataH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (T₀ : K) (k : ℕ) where
  /-- The halo annulus, lower bound. -/
  h0 : (p : ℝ)⁻¹ < ‖T₀‖
  /-- The halo annulus, upper bound. -/
  h1 : ‖T₀‖ < 1
  /-- The level-`h` analyticity condition. -/
  hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹
  /-- The norm of a classical point of conductor `p^{h+1}`. -/
  hnorm : ‖T₀‖ ^ (p ^ (h - 1) * (p - 1)) = ‖ψ p‖
  /-- The nebentypus constants. -/
  u : ι → Fin p → ZMod (p ^ h) → K
  /-- The classical shape of exponent `k`. -/
  shape : IsClassicalShape θG h ψ U hU vRep hvΔ uu (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) k u

namespace ClassicalDataH

variable {θG h ψ U hU vRep hvΔ uu} {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}
  {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K} {k : ℕ}

/-- The level-`h` halo weight of the datum. -/
def weight (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    AnalyticWeight (haloUnitsH h ψ) (M1Kh h ψ) (haloRhoH p h T₀) :=
  haloWeightH h ψ T₀ ω hp2 hψ c.h0 c.h1 c.hT

/-- The matrix of `U_p` on the classical subspace (of dimension `t(k+1)p^h`, [LWX, (3.21.1)])
at the datum. -/
def matrix [Nonempty ι] (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K :=
  classicalMatrix θG h ψ U hU vRep hvΔ idx uu c.weight c.shape

omit [Fintype ι] [DecidableEq ι] in
/-- `v(T₀)·p^{h−1}(p−1) = v(p)` at a classical datum. -/
theorem mul_neg_log_norm_eq (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) = -Real.log ‖ψ p‖ := by
  rw [← c.hnorm, Real.log_pow]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Two classical data at the same level have points of the same norm (`hnorm` at both, with
the exponent `p^{h−1}(p−1) ≥ 1`). -/
theorem norm_eq (_hh : 0 < h) {ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀' : K} {k' : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k') : ‖T₀‖ = ‖T₀'‖ := by
  have he : p ^ (h - 1) * (p - 1) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (by have := hp.out.two_le; omega)
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) he).1 (c.hnorm.trans c'.hnorm.symm)

end ClassicalDataH

section Bridge

variable {θG ψ U hU vRep hvΔ uu}

/-- Level `1` is the case `h = 1`: a `ClassicalData` is a `ClassicalDataH 1`
(`p^{1−1}(p−1) = p − 1`). -/
def _root_.LWX.ClassicalData.toH {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    ClassicalDataH θG 1 ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k where
  h0 := c.h0
  h1 := c.h1
  hT := c.hT
  hnorm := by rw [Nat.sub_self, pow_zero, one_mul]; exact c.hnorm
  u := c.u
  shape := c.shape

/-- The bridge preserves the classical matrix. -/
theorem _root_.LWX.ClassicalData.toH_matrix [Nonempty ι] {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    c.toH.matrix idx = c.matrix idx :=
  rfl

end Bridge

/-! ### Step I at level `h` -/

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The two ways of landing in `WithBotTop ℝ` agree (`WithBotTop.coe` is `WithBot.some ∘
WithTop.some`); the level-`h` copy of `14_Touching.lean`'s private `coe_withTop_coe`. -/
private theorem coe_withTop_coeH (x : ℝ) :
    ((x : WithTop ℝ) : WithBotTop ℝ) = (x : WithBotTop ℝ) :=
  rfl

/-- **[LWX, §3.23 Step I] at conductor `p^{h+1}`: the touching**, granted H1 at level `h`.  At
a classical point `T₀` of weight `k` and conductor `p^{h+1}` whose Atkin–Lehner partner is the
classical point `T₀'` (of the conjugate nebentypus), the Newton polygon of `∑ c_n(T₀) Xⁿ`
passes through `(n, λ(n)·v(T₀))` at `n = (k+1)p^h t = n_{(k+1)p^{h−1}}` — the squeeze of
`14_Touching.lean` with [LWX, (3.23.1)] replaced by `two_mul_lwxLambda_touchX_mul_eq_prime_pow`. -/
theorem isStepOneTouching_of_atkinLehnerHypothesisH (hp2 : p ≠ 2) [Nonempty ι] (hh : 0 < h)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx)) :
    IsStepOneTouching (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀
      ((k + 1) * p ^ (h - 1)) := by
  obtain ⟨B, hAB, P, Q, hQP, hA'⟩ := hAL
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun hcon =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [hcon, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hA0 : (c.matrix idx).det ≠ 0 := det_ne_zero_of_mul_eq_smul' hcne hAB
  have hA'0 : (c'.matrix idx).det ≠ 0 := det_ne_zero_of_mul_eq_smul_conj hcne hAB hQP hA'
  -- The index `n = t·(k+1)·p^h`, in the two spellings.
  have hidx : ((Fintype.card ι : ℤ) * (((k : ℤ) + 1) * (p : ℤ) ^ h))
      = ((touchX p (Fintype.card ι) ((k + 1) * p ^ (h - 1)) : ℕ) : ℤ) := by
    rw [touchX_mul_prime_pow h hh]; push_cast; ring
  -- The Minkowski upper bound at both points, through the seam.
  have hup : ∀ {ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₁ : K}
      (c₁ : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω₁ T₁ k),
      (newtonPolygon₀OfPowerSeries negLogNorm
          (specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ (intHom ψ) T₁)).height
            ((touchX p (Fintype.card ι) ((k + 1) * p ^ (h - 1)) : ℕ) : ℤ)
        ≤ ((negLogNorm (c₁.matrix idx).det : WithTop ℝ) : WithBotTop ℝ) := by
    intro ω₁ T₁ c₁
    rw [specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₁ ω₁ h θG U hU vRep hvΔ idx uu
        hp2 c₁.h0 c₁.h1 c₁.hT hshape, ← hidx]
    exact height_le_negLogNorm_det θG h ψ U hU vRep hvΔ idx uu c₁.weight c₁.shape
      (haloRhoH_nonneg h T₁) (max_lt (haloRhoH_lt_one h T₁ c₁.hT) inv_lt_one_p) hshape
  -- The [LWX, Cor 3.18] lower bound at both points.
  have hlow : ∀ {ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₁ : K}
      (c₁ : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω₁ T₁ k),
      (((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) ((k + 1) * p ^ (h - 1))) : ℝ)
            * (-Real.log ‖T₁‖) : ℝ) : WithBotTop ℝ)
        ≤ (newtonPolygon₀OfPowerSeries negLogNorm
            (specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ (intHom ψ)
              T₁)).height ((touchX p (Fintype.card ι) ((k + 1) * p ^ (h - 1)) : ℕ) : ℤ) :=
    fun c₁ =>
      lwxLambda_mul_le_height_specCharSeries hp2 _ _ (intHom ψ) (norm_intHom ψ hψ) c₁.h0 c₁.h1 _
  -- Squeezing the two bounds against each other, in `ℝ`.
  have hsq : ∀ {ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₁ : K}
      (c₁ : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω₁ T₁ k), (c₁.matrix idx).det ≠ 0 →
      (lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) ((k + 1) * p ^ (h - 1))) : ℝ)
          * (-Real.log ‖T₁‖)
        ≤ -Real.log ‖(c₁.matrix idx).det‖ := by
    intro ω₁ T₁ c₁ h₁
    have hchain := (hlow c₁).trans (hup c₁)
    rwa [negLogNorm_of_ne_zero h₁, coe_withTop_coeH, WithBotTop.coe_le_coe] at hchain
  -- [LWX, (3.23.1)] at level `h` at both points, and H1 on the determinants.
  have har : ∀ {T₁ : K}, ‖T₁‖ ^ (p ^ (h - 1) * (p - 1)) = ‖ψ (p : ℚ_[p])‖ →
      2 * ((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) ((k + 1) * p ^ (h - 1))) : ℝ)
          * (-Real.log ‖T₁‖))
        = ((Fintype.card ι * ((k + 1) * p ^ h) : ℕ) : ℝ)
            * (((k : ℝ) + 1) * (-Real.log ‖ψ (p : ℚ_[p])‖)) :=
    fun h₂ => two_mul_lwxLambda_touchX_mul_eq_prime_pow h hh (Fintype.card ι) k h₂
  have hsum : -Real.log ‖(c.matrix idx).det‖ + -Real.log ‖(c'.matrix idx).det‖
      = ((Fintype.card ι * ((k + 1) * p ^ h) : ℕ) : ℝ)
          * (((k : ℝ) + 1) * (-Real.log ‖ψ (p : ℚ_[p])‖)) := by
    have hAL := neg_log_norm_det_add_of_mul_eq_smul hcne hAB hQP hA'
    rw [Fintype.card_fin, norm_pow, Real.log_pow] at hAL
    rw [hAL]
    push_cast
    ring
  -- The touching.
  have key : -Real.log ‖(c.matrix idx).det‖
      = (lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) ((k + 1) * p ^ (h - 1))) : ℝ)
          * (-Real.log ‖T₀‖) := by
    have h1 := hsq c hA0
    have h2 := hsq c' hA'0
    have h3 := har c.hnorm
    have h4 := har c'.hnorm
    linarith
  refine le_antisymm ((hup c).trans (le_of_eq ?_)) (hlow c)
  rw [negLogNorm_of_ne_zero hA0, coe_withTop_coeH, key]

/-- **The hand-off to Step II at level `h`**: the touching hypothesis at the vertex
`n_{(k+1)p^{h−1}}`. -/
theorem hasUnitBand_of_atkinLehnerHypothesisH (hp2 : p ≠ 2) [Nonempty ι] (hh : 0 < h)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx)) :
    HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω ((k + 1) * p ^ (h - 1)) :=
  hasUnitBand_of_isStepOneTouching hp2 _ ω (intHom ψ) (norm_intHom ψ hψ) c.h0 c.h1
    (isStepOneTouching_of_atkinLehnerHypothesisH θG h ψ U hU vRep hvΔ idx uu hp2 hh hψ hshape c
      c' hAL)

end LWX

end
