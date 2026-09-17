/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«14_Touching»
import PhD.Main.LWX.«07_Degrees»
import PhD.Main.TateFredholm.«10_NewtonSlopes»
import PhD.Main.LWX.«05_TateRiesz»
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import PhD.Main.NewtonPolygons.RootFaces

/-!
# Step III of [LWX, Theorem 1.3]: the degrees — SKELETON (tranche 7 of `lwx-theta`)

[LWX, §3.23 Step III] (`lwx.txt:2014–2088`) computes the degrees `deg X_{I,ω}` from the two
gaps `n_{k+1} − n⁻_{k+1}` and `n⁺_{k+1} − n_{k+1}` at the touching points of Step I.  At the
coefficient level the degrees are differences of the unit indices of `PhD/Main/LWX/06_Vertices.lean`,
and the two gaps are:

* **the left gap** `n_{k+1} − n⁻_{k+1}` — "the dimension of the slope `k+1` subspace in
  `S^D_{k+2}(K^pIw_{q²}; ψ)`.  By Atkin–Lehner theory (Proposition 3.22) and Proposition 2.15,
  the multiplicity is the same as the dimension of the slope zero subspace in
  `S^{D,†}_{(k,ψ⁻¹)}`.  Using Corollary 3.21 again … `= r_ord(ω⁻¹ω₀^{2k})`";
* **the right gap** `n⁺_{k+1} − n_{k+1}` — "the codimension of `S^D_{k+2}(K^pIw_{q²}, ψ)` in the
  slope `≤ k+1` subspace in `S^{D,†}_{(k,ψ)}`.  The latter in turn is equal to the dimension of
  slope zero subspace of `S^{D,†}_{(−k−2,ψ)}` by the exact sequence.  Using Corollary 3.21, …
  `= r_ord(ωω₀^{−2k−2})`".

Here `r_ord` is `LWX.ordDim` (`07_Degrees.lean`), the slope-zero count at the coefficient level:
[LWX, Cor 3.21] is `faceRight_zero_specCharSeries_eq_ordDim`, proved from Step II's band
structure at `k = 0`.  The multiplicities are face lengths of Newton polygons
(`NewtonPolygon₀.faceLeft`/`faceRight`, `PhD/Main/NewtonPolygons/Face.lean`), the polygon of the
overconvergent series splits as the polygon of the classical factor plus that of the complement
(`faceRight_mul`, `faceLeft_mul`, `PhD/Main/NewtonPolygons/Product.lean`), and the classical factor's
faces are counted by its roots (`card_roots_slope`, `PhD/Main/NewtonPolygons/PolynomialRoots.lean`).

**Hypotheses.**  H1 (`AtkinLehnerHypothesis`) as in Step I; the theta intertwining in the
classical-shape form with the nebentypus constants (`IsClassicalShape'`, the target weight
`(−k−2, ψ)`); and **H2**, the right-exactness of the theta sequence, taken in the only form Step
III consumes: the Fredholm determinant of `U_p` on the complement of the classical subspace is
that of `p^{k+1}·U_p` on the target space (`IsThetaExact`).  [LWX] cite H2 to
[Jo11] O. Jones, *An analogue of the BGG resolution for locally analytic principal series*; it
is not Jacquet–Langlands (`.mathlib-quality/lwx-stepone/JL-AUDIT.md`).

## Main declarations

* `LWX.rightIndex_zero_eq_ordDim`, `LWX.faceRight_zero_specCharSeries_eq_ordDim` —
  [LWX, Cor 3.21] at the coefficient level.
* `LWX.faceRight_specCharSeries_eq_rightIndex`, `LWX.faceLeft_specCharSeries_eq_leftIndex` —
  Step II's bands as faces.
* `LWX.IsClassicalShape'`, `LWX.thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape`,
  `LWX.norm_le_of_eigen_compl` — the intertwining with the nebentypus constants and
  [Bu04, Prop 4]'s small-slope argument on the complement.
* `LWX.IsThetaExact` — hypothesis H2.
* `LWX.touchX_sub_leftIndex_eq_ordDim`, `LWX.rightIndex_sub_touchX_eq_ordDim` — the two gaps.
* `LWX.degX`, `LWX.degXint`, `LWX.degX_succ`, `LWX.degXint_succ` — [LWX, Thm 1.3]'s degree
  formulas.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash
open scoped Nat TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### Zeros of entire series along the polygon (API gap AG-Z) -/

omit [CharZero K] in
/-- **A slope of an entire series carries a zero of the matching norm** (the converse of
`norm_eq_exp_slope_of_hasSum_zero`): if the `j`-th unit slope is `m`, some `a` with
`‖a‖ = exp m` is a zero.  Via the slope factorisation `f = P·G` at radius `exp m`
(`exists_isDominantFactorization`) and the root count of the polynomial factor
(`card_roots_slope`). -/
theorem exists_evalT_eq_zero_of_unitSlope_eq [IsAlgClosed K] {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f = 1)
    {j : ℕ} {m : ℝ}
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j = (m : WithBotTop ℝ)) :
    ∃ a : K, PowerSeries.evalT a f = 0 ∧ ‖a‖ = Real.exp m :=
  TateFredholm.exists_evalT_zero_of_unitSlope f hf0 hf hj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### [LWX, Cor 3.21] at the coefficient level -/

/-- `n⁺_0 = ordDim`: below `t` the halo exponent `λ` vanishes, so a unit `T^0`-coefficient is a
unit of the halo ring; above `t` no coefficient is a unit.

`_hp2` is **slack**: `le_card_of_isUnit_charCoeff` covers `p = 2` on its own (there `UpDatum.op`
is the junk `0`).  It is kept because the ticketed statement carries it and because every other
statement of this file needs it.  `[Nonempty ι]` is slack for the same reason and is kept for the
same reason (hence the `nolint`). -/
@[nolint unusedArguments]
theorem rightIndex_zero_eq_ordDim (_hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] : rightIndex D ω 0 = ordDim D ω := by
  have h0 : touchX p (Fintype.card ι) 0 = 0 := by simp [touchX]
  have hset : {n : ℕ | touchX p (Fintype.card ι) 0 ≤ n ∧
      n ≤ touchX p (Fintype.card ι) 0 + Fintype.card ι ∧ IsUnitCoeff D ω n}
      = {n : ℕ | IsUnit (charCoeff (D.op ω) n)} := by
    ext n
    simp only [Set.mem_ofPred_eq, h0, Nat.zero_le, true_and, zero_add, IsUnitCoeff]
    constructor
    · rintro ⟨hle, hu⟩
      rw [lwxLambda_eq_zero_of_le hle, Nat.cast_zero] at hu
      exact HaloInt.isUnit_of_isUnit_coeff_zero _ hu
    · intro hu
      have hle := le_card_of_isUnit_charCoeff D ω hu
      refine ⟨hle, ?_⟩
      rw [lwxLambda_eq_zero_of_le hle, Nat.cast_zero]
      exact HaloInt.isUnit_coeff_zero_of_isUnit hu
  rw [rightIndex, ordDim, hset]

/-! ### Step II's bands as faces -/

omit [CharZero K] in
/-- `n⁺_k` is the right endpoint of the face of slope `kϕ(q)v(T₀)`
(`unitSlope_specCharSeries_eq_of_mem_band`, `lt_unitSlope_specCharSeries_of_rightIndex_le`). -/
theorem faceRight_specCharSeries_eq_rightIndex (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ₀ : ℤ_[p] →+* K) (hψ₀ : ∀ x, ‖ψ₀ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).faceRight
        (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖))
      = rightIndex D ω k := by
  have hset : {j : ℕ | ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) <
        (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).unitSlope j}
      = {j : ℕ | rightIndex D ω k ≤ j} := by
    ext j
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun hj => ?_, lt_unitSlope_specCharSeries_of_rightIndex_le hp2 D ω ψ₀ hψ₀ h0 h1 hb⟩
    by_contra hlt
    rw [not_le] at hlt
    rcases lt_or_ge j (leftIndex D ω k) with hj' | hj'
    · exact absurd hj
        (not_lt.2 (unitSlope_specCharSeries_lt_of_lt_leftIndex hp2 D ω ψ₀ hψ₀ h0 h1 hb hj').le)
    · exact absurd hj (not_lt.2
        (unitSlope_specCharSeries_eq_of_mem_band hp2 D ω ψ₀ hψ₀ h0 h1 hb hj' hlt).le)
  rw [NewtonPolygon₀.faceRight, hset]
  have hmem : rightIndex D ω k ∈ {j : ℕ | rightIndex D ω k ≤ j} := by simp
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨_, hmem⟩)

omit [CharZero K] in
/-- `n⁻_k` is the left endpoint of the face of slope `kϕ(q)v(T₀)`. -/
theorem faceLeft_specCharSeries_eq_leftIndex (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ₀ : ℤ_[p] →+* K) (hψ₀ : ∀ x, ‖ψ₀ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).faceLeft
        (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖))
      = leftIndex D ω k := by
  have hset : {j : ℕ | ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) ≤
        (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).unitSlope j}
      = {j : ℕ | leftIndex D ω k ≤ j} := by
    ext j
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hj
      by_contra hlt
      rw [not_le] at hlt
      exact absurd hj
        (not_le.2 (unitSlope_specCharSeries_lt_of_lt_leftIndex hp2 D ω ψ₀ hψ₀ h0 h1 hb hlt))
    · intro hj
      rcases lt_or_ge j (rightIndex D ω k) with hj' | hj'
      · exact (unitSlope_specCharSeries_eq_of_mem_band hp2 D ω ψ₀ hψ₀ h0 h1 hb hj hj').ge
      · exact (lt_unitSlope_specCharSeries_of_rightIndex_le hp2 D ω ψ₀ hψ₀ h0 h1 hb hj').le
  rw [NewtonPolygon₀.faceLeft, hset]
  have hmem : leftIndex D ω k ∈ {j : ℕ | leftIndex D ω k ≤ j} := by simp
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨_, hmem⟩)

omit [CharZero K] in
/-- **[LWX, Cor 3.21] (Hida) at the coefficient level**: at every halo point the number of slope
`0` unit slopes of `∑ c_n(T₀) Xⁿ` is `ordDim`.  Step II's band at `k = 0` is unconditional
(`hasUnitBand_zero`). -/
theorem faceRight_zero_specCharSeries_eq_ordDim (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ₀ : ℤ_[p] →+* K) (hψ₀ : ∀ x, ‖ψ₀ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).faceRight 0
      = ordDim D ω := by
  have h := faceRight_specCharSeries_eq_rightIndex hp2 D ω ψ₀ hψ₀ h0 h1 (hasUnitBand_zero D ω)
  rw [show (((0 * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖)) = 0 by norm_num] at h
  rw [h, rightIndex_zero_eq_ordDim hp2 D ω]

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable (h : ℕ) (ψ : ℚ_[p] →+* K) {UK UK' : Subgroup Kˣ} {ρ ρ' : ℝ}
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
  (uu : ι → Fin p → U)

/-! ### The intertwining with the nebentypus constants -/

/-- **The classical shape of the theta target** `(−k−2, ψ)`: `autFactor · L^{k+2} = C u`, with the
*same* constants `u` as the source weight `(k, ψ)`. -/
def IsClassicalShape' (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') (k : ℕ)
    (u : ι → Fin p → ZMod (p ^ h) → K) : Prop :=
  ∀ i t a, κ'.toWeightSeries.autFactor (certConj θG h ψ U hU vRep hvΔ uu i t a)
      * linX (certConj θG h ψ U hU vRep hvΔ uu i t a) ^ (k + 2)
    = PowerSeries.C (u i t a)

omit [CharZero K] in
/-- `θ^{k+1} ∘ U_p = p^{(k+1)} • U_p' ∘ θ^{k+1}` at a classical-shape pair with common constants:
`thetaBlock_comp_discHeckeBlockOp_of_autFactor` generalised by the constant (ticket G1). -/
theorem thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') {k : ℕ}
    {u : ι → Fin p → ZMod (p ^ h) → K} (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hcl' : IsClassicalShape' θG h ψ U hU vRep hvΔ uu κ' k u)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p) :
    (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp
        (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu)
      = (ψ p ^ (k + 1)) • ((discHeckeBlockOp θG h ψ κ' U hU vRep hvΔ idx uu).comp
          (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1))) :=
  thetaBlock_comp_discHeckeBlockOp_of_autFactor (p := p) (K := K) (ι := ι) ψ θG h (k + 1)
    κ κ' U hU vRep hvΔ idx uu (ψ (p : ℚ_[p])) hcl hcl' fun i t => by rw [hdet i t]

omit [CharZero K] in
/-- **`U_p` has operator norm at most one** ([Bu04, Prop 4]: "`U_p` is an operator with norm at
most 1"): every matrix coefficient is a coefficient of the weight's generating function
(`norm_coeff_genFun_le_one`), and `‖u‖ = sup‖a_{ij}‖` (`norm_eq_iSup_matrixCoeff`). -/
theorem norm_discHeckeBlockOp_le_one (κ : AnalyticWeight UK (M1Kh h ψ) ρ) :
    ‖discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu‖ ≤ 1 := by
  rw [norm_eq_iSup_matrixCoeff]
  refine Real.iSup_le (fun x => Real.iSup_le (fun y => ?_) zero_le_one) zero_le_one
  obtain ⟨i, a, m⟩ := x
  obtain ⟨j, b, n⟩ := y
  rw [discHeckeBlockOp, matrixCoeff_blockOp, discHeckeBlock, matrixCoeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => ?_
  rw [matrixCoeff_discSlash]
  split_ifs with hb
  · rw [AnalyticWeight.matrixCoeff_kappaSlash]
    exact κ.toWeightSeries.norm_coeff_genFun_le_one
      (discConjK h (certM1 θG U hU vRep hvΔ uu i t) a ψ).2 m n
  · rw [norm_zero]
    exact zero_le_one

/-- **[Bu04, Prop 4]'s small-slope argument on the complement of the classical subspace**: an
eigenvalue `μ` of `U_p ∘ (1 − pr)` satisfies `‖μ‖ ≤ ‖p‖^{k+1}`.  Since `θ^{k+1}` kills `range pr`,
`θ^{k+1} ∘ U_p(1 − pr) = p^{k+1} • U_p' ∘ θ^{k+1}`, so `eq_zero_of_intertwine_of_norm_lt` gives
`θ^{k+1} f = 0`, i.e. `f` classical, i.e. `(1 − pr) f = 0`, i.e. `μ f = 0`. -/
theorem norm_le_of_eigen_compl (κ : AnalyticWeight UK (M1Kh h ψ) ρ)
    (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') {k : ℕ} {u : ι → Fin p → ZMod (p ^ h) → K}
    (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hcl' : IsClassicalShape' θG h ψ U hU vRep hvΔ uu κ' k u)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {f : c(ι × (ZMod (p ^ h) × ℕ), K)} (hf : f ≠ 0) {μ : K}
    (hμ : (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu).comp
        (1 - truncation (classicalSupport p ι h k)) f = μ • f) :
    ‖μ‖ ≤ ‖ψ p‖ ^ (k + 1) := by
  by_contra hcon
  rw [not_le] at hcon
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  -- `θ^{k+1}` kills the classical part, so the intertwining survives the projection.
  have hint : (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp
        ((discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu).comp
          (1 - truncation (R := K) (classicalSupport p ι h k)))
      = (ψ (p : ℚ_[p]) ^ (k + 1)) •
        (discHeckeBlockOp θG h ψ κ' U hU vRep hvΔ idx uu).comp
          (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)) := by
    refine ContinuousLinearMap.ext fun g => ?_
    have hS := congrArg
      (fun T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K) =>
        T ((1 - truncation (R := K) (classicalSupport p ι h k)) g))
      (thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape θG h ψ U hU vRep hvΔ idx uu κ κ'
        hcl hcl' hdet)
    have hkill : thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)
        ((1 - truncation (R := K) (classicalSupport p ι h k)) g)
        = thetaBlock (p := p) (K := K) (ι := ι) h (k + 1) g := by
      rw [sub_apply, one_apply_eq_self, map_sub,
        (thetaBlock_eq_zero_iff h k _).2 (truncation_classicalSupport_mem h k g), sub_zero]
    simpa only [ContinuousLinearMap.comp_apply, _root_.smul_apply, hkill] using hS
  -- Buzzard's small-slope argument: the eigenvector is classical, so `μ • f = 0`.
  have hP1 : ‖discHeckeBlockOp θG h ψ κ' U hU vRep hvΔ idx uu‖ ≤ 1 :=
    norm_discHeckeBlockOp_le_one θG h ψ U hU vRep hvΔ idx uu κ'
  have hcmp : ‖ψ (p : ℚ_[p]) ^ (k + 1)‖ < ‖μ‖ := by rwa [norm_pow]
  have hθf : thetaBlock (p := p) (K := K) (ι := ι) h (k + 1) f = 0 :=
    eq_zero_of_intertwine_of_norm_lt hP1 (pow_ne_zero (k + 1) hψp) hint hμ hcmp
  have hmem : f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k :=
    (thetaBlock_eq_zero_iff h k f).1 hθf
  have hzero : (1 - truncation (R := K) (classicalSupport p ι h k)) f = 0 := by
    rw [sub_apply, one_apply_eq_self,
      truncation_classicalSupport_of_mem h k hmem, sub_self]
  rw [ContinuousLinearMap.comp_apply, hzero, map_zero] at hμ
  rw [(smul_eq_zero.1 hμ.symm).resolve_right hf, norm_zero] at hcon
  exact absurd hcon (not_lt.2 (pow_nonneg (norm_nonneg _) _))

/-- **Every slope of the complement factor is at least `(k+1)·v(p)`**: a smaller slope would
carry a zero (`exists_evalT_eq_zero_of_unitSlope_eq`), i.e. an eigenvalue of `U_p ∘ (1 − pr)` of
norm `> ‖p‖^{k+1}`, against `norm_le_of_eigen_compl`. -/
theorem le_unitSlope_compl [IsAlgClosed K] (κ : AnalyticWeight UK (M1Kh h ψ) ρ)
    (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') {k : ℕ} {u : ι → Fin p → ZMod (p ^ h) → K}
    (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hcl' : IsClassicalShape' θG h ψ U hU vRep hvΔ uu κ' k u)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    (hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape) (j : ℕ) :
    ((((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖) : ℝ) : WithBotTop ℝ) ≤
      (newtonPolygon₀OfPowerSeries negLogNorm (charPowerSeries
        ((discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu).comp
          (1 - truncation (classicalSupport p ι h k))))).unitSlope j := by
  by_contra hcon
  rw [not_le] at hcon
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  set P := (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu).comp
    (1 - truncation (R := K) (classicalSupport p ι h k)) with hPdef
  have hcomp : IsCompactoid P :=
    (isCompactoid_discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu hρ hσ hshape).comp_right _
  have hent : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c (charPowerSeries P) :=
    fun c hc => charPowerSeries_isEntire _ hcomp c hc
  have hR0 : PowerSeries.coeff 0 (charPowerSeries P) = 1 := by
    rw [charPowerSeries_coeff, charCoeff_zero]
  -- the offending unit slope is a real number
  obtain ⟨m, hm⟩ := exists_coe_of_ne_bot_of_ne_top
    ((isEntireNewtonPolygonOf_coeffVal hent (by rw [hR0]; exact one_ne_zero)).unitSlope_ne_bot j)
    (ne_top_of_lt hcon)
  rw [hm, WithBotTop.coe_lt_coe] at hcon
  -- it carries a zero of the Fredholm determinant, hence an eigenvalue of `U_p ∘ (1 − pr)`
  obtain ⟨a, ha, hanorm⟩ := exists_evalT_eq_zero_of_unitSlope_eq hent hR0 hm
  obtain ⟨ha0, x, hx0, hx⟩ := exists_eigenvector_of_evalT_charPowerSeries_eq_zero P hcomp ha
  have hle : ‖a‖⁻¹ ≤ ‖ψ (p : ℚ_[p])‖ ^ (k + 1) := by
    rw [← norm_inv]
    exact norm_le_of_eigen_compl θG h ψ U hU vRep hvΔ idx uu κ κ' hcl hcl' hdet hx0 hx
  -- reading it off in logarithms contradicts `m < (k+1)·v(p)`
  have hpos : (0 : ℝ) < ‖ψ (p : ℚ_[p])‖ := norm_pos_iff.2 hψp
  have hexp : Real.exp (-m) ≤ ‖ψ (p : ℚ_[p])‖ ^ (k + 1) := by
    rwa [hanorm, ← Real.exp_neg] at hle
  have hlog := Real.log_le_log (Real.exp_pos (-m)) hexp
  rw [Real.log_exp, Real.log_pow] at hlog
  push_cast at hcon hlog
  nlinarith [hcon, hlog]

/-! ### Hypothesis H2 -/

/-- **Hypothesis H2, the right-exactness of the theta sequence, in determinant form**: the
Fredholm determinant of `U_p` on the complement of the classical subspace is that of
`p^{k+1}·U_p` on the target space `(−k−2, ψ)` ([LWX, §3.23 Step III]: "0 → S^D_{k+2} →
S^{D,†}_{(k,ψ)} → S^{D,†}_{(−k−2,ψ)} → 0 … equivariant for the `U_p`-action on the first two
spaces, and the `p^{k+1}U_p`-action on the third"). -/
def IsThetaExact (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ')
    (k : ℕ) : Prop :=
  charPowerSeries ((discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu).comp
      (1 - truncation (classicalSupport p ι h k)))
    = PowerSeries.rescale (ψ p ^ (k + 1))
        (discHeckeCharPowerSeries θG h ψ κ' U hU vRep hvΔ idx uu)

/-! ### The classical data of the theta target -/

variable {θG h ψ U hU vRep hvΔ uu}

/-- **The theta target of a classical datum**: a halo point `T₁` of the weight `(−k−2, ψ)` whose
halo weight has the target shape with the datum's nebentypus constants. -/
structure TargetData {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K}
    {k : ℕ} (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) (ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (T₁ : K) where
  /-- The halo annulus, lower bound. -/
  h0 : (p : ℝ)⁻¹ < ‖T₁‖
  /-- The halo annulus, upper bound. -/
  h1 : ‖T₁‖ < 1
  /-- The level-`1` analyticity condition. -/
  hT : ‖TH p 1 T₁‖ ^ 2 < (p : ℝ)⁻¹
  /-- The target shape, with the source's constants. -/
  shape : IsClassicalShape' θG 1 ψ U hU vRep hvΔ uu (haloWeightH 1 ψ T₁ ω₁ hp2 hψ h0 h1 hT) k c.u

namespace TargetData

variable {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₁ : K} {k : ℕ}
  {c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k}

/-- The halo weight of the target. -/
def weight (d : TargetData c ω₁ T₁) :
    AnalyticWeight (haloUnitsH 1 ψ) (M1Kh 1 ψ) (haloRhoH p 1 T₁) :=
  haloWeightH 1 ψ T₁ ω₁ hp2 hψ d.h0 d.h1 d.hT

end TargetData

/-! ### The two gaps -/

omit [CharZero K] in
/-- **[S7.10a] Every classical eigenvalue has norm at most one.**  A root of the characteristic
polynomial of `U_p` on the classical subspace is an eigenvalue of the restriction
(`Module.End.hasEigenvalue_iff_isRoot_charpoly`), hence of `U_p` itself, and `‖U_p‖ ≤ 1`
([Bu04, Prop 4], `norm_discHeckeBlockOp_le_one`).  No compactoidness is needed. -/
theorem norm_le_one_of_isRoot_charpoly_upMatrix [Nonempty ι]
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (k : ℕ)
    (hst : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu f
        ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k)
    {y : K} (hy : (upMatrix (p := p) (K := K) (ι := ι) h k
      (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu) hst).charpoly.IsRoot y) :
    ‖y‖ ≤ 1 := by
  haveI := finite_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k
  rw [upMatrix, LinearMap.charpoly_toMatrix] at hy
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ y).2 hy).exists_hasEigenvector
  have hveq := congrArg (fun w : ↥(locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) =>
    (w : c(ι × (ZMod (p ^ h) × ℕ), K))) (Module.End.mem_eigenspace_iff.1 hv.1)
  simp only [LinearMap.restrict_apply, Submodule.coe_smul] at hveq
  exact norm_le_one_of_eigen (norm_discHeckeBlockOp_le_one θG h ψ U hU vRep hvΔ idx uu κ)
    (fun hc => hv.2 (Submodule.coe_eq_zero.1 hc)) hveq

/-- **[S7.10b] The classical eigenvalues at `ψ` have norm at least `‖p‖^{k+1}`**: their
Atkin–Lehner partners are eigenvalues of `U_p` at the conjugate nebentypus, hence of norm at most
one (`norm_le_one_of_isRoot_charpoly_upMatrix`). -/
theorem norm_pow_le_of_mem_roots_charpoly_matrix [Nonempty ι] [IsAlgClosed K] {hp2 : p ≠ 2}
    {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx))
    {x : K} (hx : x ∈ (c.matrix idx).charpoly.roots) :
    ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ ≤ ‖x‖ := by
  classical
  obtain ⟨B, ⟨Zm, Nm, hNm, hAB, hZmA, hZmN⟩, P, Q, hQP, hA'⟩ := hAL
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hA0 : (c.matrix idx).det ≠ 0 := Matrix.det_ne_zero_of_mul_eq_smul_mul hcne hAB hNm hZmN
  have hone : ∀ y ∈ (c'.matrix idx).charpoly.roots, ‖y‖ ≤ 1 := fun y hy =>
    norm_le_one_of_isRoot_charpoly_upMatrix idx c'.weight k _ (Polynomial.mem_roots'.1 hy).2
  have hxne : x ≠ 0 := by
    intro h0
    exact hA0 (by rw [Matrix.det_eq_prod_roots_charpoly]; exact Multiset.prod_eq_zero (h0 ▸ hx))
  have hmem : ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ / ‖x‖
      ∈ (c'.matrix idx).charpoly.roots.map (fun y => ‖y‖) := by
    rw [norm_roots_charpoly_atkinLehnerZ hcne hAB hZmA hNm hZmN hQP hA']
    exact Multiset.mem_map_of_mem _ hx
  obtain ⟨y, hy, hyeq⟩ := Multiset.mem_map.1 hmem
  have hy1 := hone y hy
  rw [hyeq, div_le_one (norm_pos_iff.2 hxne)] at hy1
  exact hy1

/-- **The classical slopes are at most `k+1`** ([LWX, Step I]: "the set of all `U_p`-slopes on
`S^D_{k+2}(ψ) ⊕ S^D_{k+2}(ψ⁻¹)` …"; derived from H1 and `‖U_p‖ ≤ 1`, never from
[Bu04, Prop 4]'s converse — `JL-AUDIT.md` §2): every root of the classical factor at `ψ` has
norm `≥ ‖p‖^{k+1}`, because its Atkin–Lehner partner is an eigenvalue of `U_p` at `ψ⁻¹`. -/
theorem unitSlope_charpolyRev_matrix_le [Nonempty ι] [IsAlgClosed K] {hp2 : p ≠ 2}
    {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) {j : ℕ} (hj : j < Fintype.card ι * ((k + 1) * p ^ 1)) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        ((c.matrix idx).charpolyRev : PowerSeries K)).unitSlope j
      ≤ ((((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖) : ℝ) : WithBotTop ℝ) := by
  obtain ⟨B, ⟨Zm, Nm, hNm, hAB, hZmA, hZmN⟩, P, Q, hQP, hA'⟩ := hAL
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hccpos : (0 : ℝ) < ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ := norm_pos_iff.2 hcne
  have hA0 : (c.matrix idx).det ≠ 0 := Matrix.det_ne_zero_of_mul_eq_smul_mul hcne hAB hNm hZmN
  have hlow : ∀ x ∈ (c.matrix idx).charpoly.roots, ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ ≤ ‖x‖ :=
    fun x hx => norm_pow_le_of_mem_roots_charpoly_matrix idx c c'
      ⟨B, ⟨Zm, Nm, hNm, hAB, hZmA, hZmN⟩, P, Q, hQP, hA'⟩ hx
  -- the `j`-th unit slope of the classical factor is a real number
  have hGres : ∀ cst : ℝ, 0 < cst →
      PowerSeries.IsRestricted cst ((c.matrix idx).charpolyRev : PowerSeries K) :=
    fun cst _ => Polynomial.isRestricted_toPowerSeries _ _
  have hG0 : PowerSeries.coeff 0 ((c.matrix idx).charpolyRev : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hG0' : PowerSeries.coeff 0 ((c.matrix idx).charpolyRev : PowerSeries K) ≠ 0 := by
    rw [hG0]; exact one_ne_zero
  have hent := isEntireNewtonPolygonOf_coeffVal hGres hG0'
  have hcoeffN : PowerSeries.coeff (Fintype.card ι * ((k + 1) * p ^ 1))
      ((c.matrix idx).charpolyRev : PowerSeries K) ≠ 0 := by
    have hcc := coeff_charpolyRev_card (c.matrix idx)
    rw [Fintype.card_fin] at hcc
    rw [Polynomial.coeff_coe, hcc]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hA0
  have hNtop : (newtonPolygon₀OfPowerSeries negLogNorm
      ((c.matrix idx).charpolyRev : PowerSeries K)).height
      ((Fintype.card ι * ((k + 1) * p ^ 1) : ℕ) : ℤ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (height_le_coeffVal hGres hG0 _)
    rw [coeffVal_apply, negLogNorm_of_ne_zero hcoeffN]
    simp
  obtain ⟨m, hm⟩ := exists_coe_of_ne_bot_of_ne_top (hent.unitSlope_ne_bot j)
    ((newtonPolygon₀OfPowerSeries negLogNorm
      ((c.matrix idx).charpolyRev : PowerSeries K)).unitSlope_ne_top_of_height_natCast
      hent.starting_point_fst hNtop hj)
  rw [hm, WithBotTop.coe_le_coe]
  -- it carries a zero of `charpolyRev`, i.e. the inverse of an eigenvalue
  obtain ⟨a, ha, hanorm⟩ := exists_evalT_eq_zero_of_unitSlope_eq hGres hG0 hm
  rw [PowerSeries.evalT_coe] at ha
  have hrne : (c.matrix idx).charpolyRev ≠ 0 := by
    intro h0
    rw [h0] at hG0
    simp at hG0
  obtain ⟨x, hx, hxa⟩ := Multiset.mem_map.1
    (by rw [← Matrix.roots_charpolyRev hA0]; exact Polynomial.mem_roots'.2 ⟨hrne, ha⟩ :
      a ∈ (c.matrix idx).charpoly.roots.map fun x => x⁻¹)
  have hxne : x ≠ 0 := by
    intro h0
    exact hA0 (by rw [Matrix.det_eq_prod_roots_charpoly]; exact Multiset.prod_eq_zero (h0 ▸ hx))
  have hexp : Real.exp m ≤ ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖⁻¹ := by
    rw [← hanorm, ← hxa, norm_inv, inv_le_inv₀ (norm_pos_iff.2 hxne) hccpos]
    exact hlow x hx
  have hlog := Real.log_le_log (Real.exp_pos m) hexp
  rw [Real.log_exp, Real.log_inv, norm_pow, Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

/-- **The Atkin–Lehner reflection of the classical polygon**: the number of classical slopes at `ψ`
strictly below `k+1` is `n_{k+1}` minus the number of slope-`0` classical slopes at `ψ⁻¹`
(`norm_roots_charpoly_atkinLehner`, `card_roots_slope`). -/
theorem faceLeft_charpolyRev_matrix_eq [Nonempty ι] [IsAlgClosed K] {hp2 : p ≠ 2}
    {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    (newtonPolygon₀OfPowerSeries negLogNorm ((c.matrix idx).charpolyRev : PowerSeries K)).faceLeft
        (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖))
      = Fintype.card ι * ((k + 1) * p ^ 1)
        - (newtonPolygon₀OfPowerSeries negLogNorm
            ((c'.matrix idx).charpolyRev : PowerSeries K)).faceRight 0 := by
  classical
  obtain ⟨B, ⟨Zm, Nm, hNm, hAB, hZmA, hZmN⟩, P, Q, hQP, hA'⟩ := hAL
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hccpos : (0 : ℝ) < ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ := norm_pos_iff.2 hcne
  have hA0 : (c.matrix idx).det ≠ 0 := Matrix.det_ne_zero_of_mul_eq_smul_mul hcne hAB hNm hZmN
  have hA'0 : (c'.matrix idx).det ≠ 0 :=
    det_ne_zero_of_mul_eq_smul_mul_conj hcne hAB hNm hZmN hQP hA'
  have hcf0 : ((c.matrix idx).charpolyRev).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hcf0' : ((c'.matrix idx).charpolyRev).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hexpσ : Real.exp (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖))
      = ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖⁻¹ := by
    have hp0 : (0 : ℝ) < ‖ψ (p : ℚ_[p])‖ := norm_pos_iff.2 hψp
    rw [norm_pow, show ((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖)
        = -Real.log (‖ψ (p : ℚ_[p])‖ ^ (k + 1)) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_neg, Real.exp_log (by positivity)]
  -- the two faces, as root counts over the eigenvalues
  rw [faceLeft_eq_card_roots_lt_self _ hcf0, faceRight_eq_card_roots_le_self _ hcf0',
    Matrix.roots_charpolyRev hA0, Matrix.roots_charpolyRev hA'0,
    ← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter,
    Multiset.countP_map, Multiset.countP_map, ← Multiset.countP_eq_card_filter,
    ← Multiset.countP_eq_card_filter]
  -- the Atkin–Lehner reflection turns the `ψ⁻¹`-count into a `ψ`-count
  have hnormOnly : ∀ s : Multiset K,
      Multiset.countP (fun y : K => ‖y⁻¹‖ ≤ Real.exp 0) s
        = Multiset.countP (fun r : ℝ => r⁻¹ ≤ Real.exp 0) (s.map fun y => ‖y‖) := by
    intro s
    rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter]
    exact Multiset.countP_congr rfl fun y _ => by rw [norm_inv]
  rw [hnormOnly, norm_roots_charpoly_atkinLehnerZ hcne hAB hZmA hNm hZmN hQP hA',
    Multiset.countP_map, ← Multiset.countP_eq_card_filter]
  -- the two predicates on the `ψ`-eigenvalues are complementary
  have hcompl : ∀ x ∈ (c.matrix idx).charpoly.roots,
      ((‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ / ‖x‖)⁻¹ ≤ Real.exp 0)
        = ¬ (‖x⁻¹‖ < Real.exp (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖))) := by
    intro x hx
    have hxne : x ≠ 0 := by
      intro h0
      exact hA0 (by rw [Matrix.det_eq_prod_roots_charpoly]; exact Multiset.prod_eq_zero (h0 ▸ hx))
    have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hxne
    rw [hexpσ, norm_inv, Real.exp_zero]
    refine propext ?_
    rw [inv_div, div_le_one hccpos, not_lt, inv_le_inv₀ hccpos hxpos]
  have hsum := congrArg Multiset.card
    (Multiset.filter_add_not
      (fun x : K => ‖x⁻¹‖ < Real.exp (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖)))
      ((c.matrix idx).charpoly.roots))
  rw [Multiset.card_add, ← Multiset.countP_eq_card_filter,
    ← Multiset.countP_eq_card_filter] at hsum
  have hcard : ((c.matrix idx).charpoly.roots).card = Fintype.card ι * ((k + 1) * p ^ 1) := by
    rw [← (IsAlgClosed.splits ((c.matrix idx).charpoly)).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [Multiset.countP_congr rfl hcompl]
  omega

/-- **The Fredholm determinant at a classical datum splits** as the complement factor times the
characteristic polynomial of `U_p` on the classical subspace: the seam of `11_SeamH.lean` followed by
`charPowerSeries_eq_mul_of_stable`, with `14_Touching.lean`'s coordinate-vs-basis bridge. -/
private theorem specCharSeries_eq_mul_charpolyRev {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}
    [Nonempty ι] (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀
      = charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
          (1 - truncation (R := K) (classicalSupport p ι 1 k)))
        * (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) := by
  have hst : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) 1 k,
      discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu f
        ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) 1 k := fun f hf =>
    mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG 1 ψ U hU
      vRep hvΔ idx uu c.weight c.shape hf
  have hcomp : IsCompactoid (discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu) :=
    isCompactoid_discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu (haloRhoH_nonneg 1 T₀)
      (max_lt (haloRhoH_lt_one 1 T₀ c.hT) inv_lt_one_p) hshape
  calc specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀
      = charPowerSeries (discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu) :=
        specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω 1 θG U hU vRep hvΔ idx uu
          hp2 c.h0 c.h1 c.hT hshape
    _ = charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
          (1 - truncation (R := K) (classicalSupport p ι 1 k)))
        * (((classicalCoordMatrix 1 k
            (discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu)).charpolyRev :
              Polynomial K) : PowerSeries K) :=
        charPowerSeries_eq_mul_of_stable 1 k hcomp hst
    _ = _ := by
        rw [charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix 1 k _ hst]
        rfl

/-- **The left gap** ([LWX, Step III]: `n_{k+1} − n⁻_{k+1} = r_ord(ω⁻¹ω₀^{2k})`), with the
conjugate character `ω'` of the datum `c'` in place of `ω⁻¹ω₀^{2k}`. -/
theorem touchX_sub_leftIndex_eq_ordDim (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetData c ω₁ T₁) (d' : TargetData c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    touchX p (Fintype.card ι) (k + 1)
        - leftIndex (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω' := by
  have hψpK : ‖ψ (p : ℚ_[p])‖ = (p : ℝ)⁻¹ := by rw [map_natCast]; exact norm_natCast_p ψ hψ
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hσpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖) := by
    rw [hψpK, Real.log_inv, neg_neg]
    exact mul_pos (by exact_mod_cast Nat.succ_pos k) (Real.log_pos hp1R)
  have hbandσ : ∀ {T : K}, ‖T‖ ^ (p - 1) = ‖ψ (p : ℚ_[p])‖ →
      (((k + 1) * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T‖)
        = ((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖) := by
    intro T hT
    have h1 : ((p - 1 : ℕ) : ℝ) * Real.log ‖T‖ = Real.log ‖ψ (p : ℚ_[p])‖ := by
      rw [← Real.log_pow, hT]
    rw [← h1]
    push_cast [Nat.cast_sub hp.out.one_le]
    ring
  -- the two Fredholm splittings
  have hsplit := specCharSeries_eq_mul_charpolyRev idx hshape c
  have hsplit' := specCharSeries_eq_mul_charpolyRev idx hshape c'
  have hcompc : IsCompactoid (discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu) :=
    isCompactoid_discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu (haloRhoH_nonneg 1 T₀)
      (max_lt (haloRhoH_lt_one 1 T₀ c.hT) inv_lt_one_p) hshape
  have hcompc' : IsCompactoid (discHeckeBlockOp θG 1 ψ c'.weight U hU vRep hvΔ idx uu) :=
    isCompactoid_discHeckeBlockOp θG 1 ψ c'.weight U hU vRep hvΔ idx uu (haloRhoH_nonneg 1 T₀')
      (max_lt (haloRhoH_lt_one 1 T₀' c'.hT) inv_lt_one_p) hshape
  have hRres : ∀ cst : ℝ, 0 < cst → PowerSeries.IsRestricted cst
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k)))) :=
    fun cst hcst => charPowerSeries_isEntire _ (hcompc.comp_right _) cst hcst
  have hRres' : ∀ cst : ℝ, 0 < cst → PowerSeries.IsRestricted cst
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c'.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k)))) :=
    fun cst hcst => charPowerSeries_isEntire _ (hcompc'.comp_right _) cst hcst
  have hR0 : PowerSeries.coeff 0
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k)))) ≠ 0 := by
    rw [charPowerSeries_coeff, charCoeff_zero]
    exact one_ne_zero
  have hR0' : PowerSeries.coeff 0
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c'.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k)))) ≠ 0 := by
    rw [charPowerSeries_coeff, charCoeff_zero]
    exact one_ne_zero
  have hGres : ∀ cst : ℝ, 0 < cst →
      PowerSeries.IsRestricted cst (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) :=
    fun cst _ => Polynomial.isRestricted_toPowerSeries _ _
  have hGres' : ∀ cst : ℝ, 0 < cst →
      PowerSeries.IsRestricted cst (((c'.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) :=
    fun cst _ => Polynomial.isRestricted_toPowerSeries _ _
  have hG0 : PowerSeries.coeff 0
      (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) ≠ 0 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    exact one_ne_zero
  have hG0' : PowerSeries.coeff 0
      (((c'.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) ≠ 0 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    exact one_ne_zero
  -- (1) the left face of the overconvergent polygon is `leftIndex`, and it splits
  have hleft := faceLeft_specCharSeries_eq_leftIndex hp2
    (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) (norm_intHom ψ hψ) c.h0 c.h1
    (hasUnitBand_of_atkinLehnerHypothesis θG ψ U hU vRep hvΔ idx uu hp2 hψ hshape c c' hAL)
  rw [hbandσ c.hnorm, hsplit, faceLeft_newtonPolygon₀OfPowerSeries_mul hRres hGres hR0 hG0] at hleft
  -- (2) the right face at `0` is `ordDim ω'`, and it splits
  have hright := faceRight_zero_specCharSeries_eq_ordDim hp2
    (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω' (intHom ψ) (norm_intHom ψ hψ) c'.h0 c'.h1
  rw [hsplit', faceRight_newtonPolygon₀OfPowerSeries_mul hRres' hGres' hR0' hG0'] at hright
  -- (3) the complement factors contribute nothing to either face
  have hcomplLeft : (newtonPolygon₀OfPowerSeries negLogNorm
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k))))).faceLeft
      (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖)) = 0 :=
    Nat.le_zero.1 (Nat.sInf_le (le_unitSlope_compl θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight
      c.shape d.shape hdet (haloRhoH_nonneg 1 T₀)
      (max_lt (haloRhoH_lt_one 1 T₀ c.hT) inv_lt_one_p) hshape 0))
  have hcomplRight : (newtonPolygon₀OfPowerSeries negLogNorm
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c'.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k))))).faceRight 0 = 0 :=
    Nat.le_zero.1 (Nat.sInf_le (lt_of_lt_of_le (WithBotTop.coe_lt_coe.2 hσpos)
      (le_unitSlope_compl θG 1 ψ U hU vRep hvΔ idx uu c'.weight d'.weight c'.shape d'.shape hdet
        (haloRhoH_nonneg 1 T₀') (max_lt (haloRhoH_lt_one 1 T₀' c'.hT) inv_lt_one_p) hshape 0)))
  rw [hcomplLeft, zero_add] at hleft
  rw [hcomplRight, zero_add] at hright
  -- (4) the Atkin–Lehner reflection, and the arithmetic
  have hAL11 := faceLeft_charpolyRev_matrix_eq idx c c' hAL
  have hord : ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
      ≤ Fintype.card ι * ((k + 1) * p ^ 1) := by
    refine le_trans (ordDim_le_card _ ω') ?_
    have h1 : 1 ≤ (k + 1) * p ^ 1 := Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (Nat.succ_ne_zero k) (pow_ne_zero 1 hp.out.ne_zero))
    nlinarith [Fintype.card_pos (α := ι)]
  rw [touchX_succ_eq]
  omega

omit hp [Fintype ι] [DecidableEq ι] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Cancelling a real summand in `WithTop ℝ`. -/
private theorem withTop_add_coe_self {a : WithTop ℝ} {c : ℝ}
    (h : a + (c : WithTop ℝ) = (c : WithTop ℝ)) : a = ((0 : ℝ) : WithTop ℝ) := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe r =>
    rw [← WithTop.coe_add, WithTop.coe_inj] at h
    rw [WithTop.coe_inj]
    linarith

/-- **The right gap** ([LWX, Step III]: `n⁺_{k+1} − n_{k+1} = r_ord(ωω₀^{−2k−2})`), with the
target character `ω₁` of the datum `d` in place of `ωω₀^{−2k−2}`, granted **H2**. -/
theorem rightIndex_sub_touchX_eq_ordDim (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetData c ω₁ T₁)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx))
    (hH2 : IsThetaExact θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight k) :
    rightIndex (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
        - touchX p (Fintype.card ι) (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ := by
  classical
  have hψpK : ‖ψ (p : ℚ_[p])‖ = (p : ℝ)⁻¹ := by rw [map_natCast]; exact norm_natCast_p ψ hψ
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hccpos : (0 : ℝ) < ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ := norm_pos_iff.2 hcne
  have hA0 : (c.matrix idx).det ≠ 0 := by
    obtain ⟨B, ⟨Zm, Nm, hNm, hAB, -, hZmN⟩, -⟩ := hAL
    exact Matrix.det_ne_zero_of_mul_eq_smul_mul hcne hAB hNm hZmN
  have hexpσ : Real.exp (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖))
      = ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖⁻¹ := by
    have hp0 : (0 : ℝ) < ‖ψ (p : ℚ_[p])‖ := norm_pos_iff.2 hψp
    rw [norm_pow, show ((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖)
        = -Real.log (‖ψ (p : ℚ_[p])‖ ^ (k + 1)) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_neg, Real.exp_log (by positivity)]
  have hbandσ : (((k + 1) * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖)
      = ((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖) := by
    have h1 : ((p - 1 : ℕ) : ℝ) * Real.log ‖T₀‖ = Real.log ‖ψ (p : ℚ_[p])‖ := by
      rw [← Real.log_pow, c.hnorm]
    rw [← h1]
    push_cast [Nat.cast_sub hp.out.one_le]
    ring
  -- the factors of the splitting, and their standing hypotheses
  have hcompc : IsCompactoid (discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu) :=
    isCompactoid_discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu (haloRhoH_nonneg 1 T₀)
      (max_lt (haloRhoH_lt_one 1 T₀ c.hT) inv_lt_one_p) hshape
  have hRres : ∀ cst : ℝ, 0 < cst → PowerSeries.IsRestricted cst
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k)))) :=
    fun cst hcst => charPowerSeries_isEntire _ (hcompc.comp_right _) cst hcst
  have hR1 : PowerSeries.coeff 0
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k)))) = 1 := by
    rw [charPowerSeries_coeff, charCoeff_zero]
  have hR0 : PowerSeries.coeff 0
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k)))) ≠ 0 := by
    rw [hR1]; exact one_ne_zero
  have hGres : ∀ cst : ℝ, 0 < cst →
      PowerSeries.IsRestricted cst (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) :=
    fun cst _ => Polynomial.isRestricted_toPowerSeries _ _
  have hcf0 : ((c.matrix idx).charpolyRev).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hG0 : PowerSeries.coeff 0
      (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) ≠ 0 := by
    rw [Polynomial.coeff_coe, hcf0]; exact one_ne_zero
  -- (1) the right face of the overconvergent polygon is `rightIndex`, and it splits
  have hrt := faceRight_specCharSeries_eq_rightIndex hp2
    (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) (norm_intHom ψ hψ) c.h0 c.h1
    (hasUnitBand_of_atkinLehnerHypothesis θG ψ U hU vRep hvΔ idx uu hp2 hψ hshape c c' hAL)
  rw [hbandσ, specCharSeries_eq_mul_charpolyRev idx hshape c,
    faceRight_newtonPolygon₀OfPowerSeries_mul hRres hGres hR0 hG0] at hrt
  -- (2) every classical slope is at most `σ`, so the classical factor contributes all of `N`
  have hGface : (newtonPolygon₀OfPowerSeries negLogNorm
      (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K)).faceRight
      (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖))
      = Fintype.card ι * ((k + 1) * p ^ 1) := by
    have hall : ∀ x ∈ (c.matrix idx).charpoly.roots,
        ‖x⁻¹‖ ≤ Real.exp (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖)) := by
      intro x hx
      have hxne : x ≠ 0 := by
        intro h0
        exact hA0 (by
          rw [Matrix.det_eq_prod_roots_charpoly]
          exact Multiset.prod_eq_zero (h0 ▸ hx))
      rw [hexpσ, norm_inv, inv_le_inv₀ (norm_pos_iff.2 hxne) hccpos]
      exact norm_pow_le_of_mem_roots_charpoly_matrix idx c c' hAL hx
    rw [faceRight_eq_card_roots_le_self _ hcf0, Matrix.roots_charpolyRev hA0,
      ← Multiset.countP_eq_card_filter, Multiset.countP_map, ← Multiset.countP_eq_card_filter,
      Multiset.countP_eq_card.2 hall,
      ← (IsAlgClosed.splits ((c.matrix idx).charpoly)).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- (3) the complement factor's face is the target's ordinary face
  have hseamd : specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ (intHom ψ) T₁
      = discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu :=
    specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₁ ω₁ 1 θG U hU vRep hvΔ idx uu
      hp2 d.h0 d.h1 d.hT hshape
  have hFres : ∀ cst : ℝ, 0 < cst → PowerSeries.IsRestricted cst
      (discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu) := fun cst hcst =>
    charPowerSeries_isEntire _ (isCompactoid_discHeckeBlockOp θG 1 ψ d.weight U hU vRep hvΔ idx uu
      (haloRhoH_nonneg 1 T₁) (max_lt (haloRhoH_lt_one 1 T₁ d.hT) inv_lt_one_p) hshape) cst hcst
  have hF1 : PowerSeries.coeff 0
      (discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu) = 1 := by
    rw [discHeckeCharPowerSeries, charPowerSeries_coeff, charCoeff_zero]
  have hlowF : ∀ j : ℕ, (((0 : ℝ) : ℝ) : WithBotTop ℝ) ≤ (newtonPolygon₀OfPowerSeries negLogNorm
      (discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu)).unitSlope j := by
    intro j
    rw [← hseamd]
    have hleft0 : leftIndex (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ 0 = 0 := by
      refine Nat.le_zero.1 (Nat.sInf_le ?_)
      have h0 : touchX p (Fintype.card ι) 0 = 0 := by simp [touchX]
      exact ⟨by rw [h0]; omega, by rw [h0], isUnitCoeff_zero _ ω₁⟩
    rcases lt_or_ge j (rightIndex (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ 0) with
      hj | hj
    · rw [unitSlope_specCharSeries_eq_of_mem_band hp2 _ ω₁ (intHom ψ) (norm_intHom ψ hψ)
        d.h0 d.h1 (hasUnitBand_zero _ ω₁) (by omega) hj]
      norm_num
    · refine le_of_lt ?_
      have hgt := lt_unitSlope_specCharSeries_of_rightIndex_le hp2 _ ω₁ (intHom ψ)
        (norm_intHom ψ hψ) d.h0 d.h1 (hasUnitBand_zero _ ω₁) hj
      simpa using hgt
  have hlowR : ∀ j : ℕ, ((((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖) : ℝ) : WithBotTop ℝ)
      ≤ (newtonPolygon₀OfPowerSeries negLogNorm
          (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
            (1 - truncation (R := K) (classicalSupport p ι 1 k))))).unitSlope j :=
    fun j => le_unitSlope_compl θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight c.shape d.shape hdet
      (haloRhoH_nonneg 1 T₀) (max_lt (haloRhoH_lt_one 1 T₀ c.hT) inv_lt_one_p) hshape j
  have hcoeff : ∀ n : ℕ,
      coeffVal (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k)))) n
      = coeffVal (discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu) n
        + (((((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖)) * (n : ℝ) : ℝ) : WithTop ℝ) := by
    intro n
    rw [coeffVal_apply, coeffVal_apply, hH2, PowerSeries.coeff_rescale, negLogNorm_mul,
      negLogNorm_of_ne_zero (pow_ne_zero n hcne), add_comm]
    congr 1
    rw [norm_pow, norm_pow, Real.log_pow, Real.log_pow]
    congr 1
    push_cast
    ring
  have hRface : (newtonPolygon₀OfPowerSeries negLogNorm
      (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι 1 k))))).faceRight
        (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ (p : ℚ_[p])‖))
      = (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu)).faceRight 0 := by
    have hRpt := pointHeight_eq_coe_iff.1 (pointHeight_faceRight_eq hRres hR1 hlowR)
    have hFpt := pointHeight_eq_coe_iff.1 (pointHeight_faceRight_eq hFres hF1 hlowF)
    rw [hcoeff] at hRpt
    have hFzero : coeffVal (discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu)
        ((newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu)).faceRight 0)
        = ((0 : ℝ) : WithTop ℝ) := by rw [hFpt]; norm_num
    refine le_antisymm ?_ ?_
    · by_contra hlt
      rw [not_le] at hlt
      have h3 := lt_pointHeight_of_faceRight_lt hFres hF1 hlowF hlt
      rw [pointHeight_eq_coe_iff.2 (withTop_add_coe_self hRpt)] at h3
      exact absurd (WithBotTop.coe_lt_coe.1 h3) (by norm_num)
    · by_contra hlt
      rw [not_le] at hlt
      have h3 := lt_pointHeight_of_faceRight_lt hRres hR1 hlowR hlt
      rw [pointHeight_eq_coe_iff.2 (show coeffVal
          (charPowerSeries ((discHeckeBlockOp θG 1 ψ c.weight U hU vRep hvΔ idx uu).comp
            (1 - truncation (R := K) (classicalSupport p ι 1 k))))
          ((newtonPolygon₀OfPowerSeries negLogNorm
            (discHeckeCharPowerSeries θG 1 ψ d.weight U hU vRep hvΔ idx uu)).faceRight 0)
          = _ from by rw [hcoeff, hFzero, ← WithTop.coe_add, zero_add])] at h3
      exact absurd (WithBotTop.coe_lt_coe.1 h3) (lt_irrefl _)
  -- (4) the target's ordinary face is `ordDim ω₁`
  have hord := faceRight_zero_specCharSeries_eq_ordDim hp2
    (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ (intHom ψ) (norm_intHom ψ hψ) d.h0 d.h1
  rw [hseamd] at hord
  rw [hGface, hRface, hord] at hrt
  rw [touchX_succ_eq]
  omega

/-! ### The degrees -/

variable {idx}

/-- **`deg X_{k,ω}`** at the coefficient level: `n⁺_k − n⁻_k` ([LWX, (3.23.3)–(3.23.4)]). -/
def degX (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) : ℕ :=
  rightIndex D ω k - leftIndex D ω k

/-- **`deg X_{(k,k+1),ω}`** at the coefficient level: `n⁻_{k+1} − n⁺_k`. -/
def degXint (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) : ℕ :=
  leftIndex D ω (k + 1) - rightIndex D ω k

/-- **[LWX, Thm 1.3]: `deg X_{0,ω} = r_ord(ω)`** — unconditional at the coefficient level. -/
theorem degX_zero (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] :
    degX D ω 0 = ordDim D ω := by
  have h0 : touchX p (Fintype.card ι) 0 = 0 := by simp [touchX]
  have hleft : leftIndex D ω 0 = 0 := by
    refine Nat.le_zero.1 (Nat.sInf_le ?_)
    have hmem : touchX p (Fintype.card ι) 0 ≤ 0 + Fintype.card ι ∧
        0 ≤ touchX p (Fintype.card ι) 0 ∧ IsUnitCoeff D ω 0 :=
      ⟨by rw [h0]; omega, by rw [h0], isUnitCoeff_zero D ω⟩
    exact hmem
  rw [degX, hleft, Nat.sub_zero, rightIndex_zero_eq_ordDim hp2 D ω]

variable (idx)

/-- **[LWX, Thm 1.3]: `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})`**, the two gaps
added, with the conjugate and target characters of the data in place of the twists. -/
theorem degX_succ (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K] (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetData c ω₁ T₁) (d' : TargetData c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx))
    (hH2 : IsThetaExact θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight k) :
    degX (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
        + ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ := by
  have hleftGap := touchX_sub_leftIndex_eq_ordDim idx hp2 hψ hshape hdet c c' d d' hAL
  have hrightGap := rightIndex_sub_touchX_eq_ordDim idx hp2 hψ hshape hdet c c' d hAL hH2
  have hband : HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1) :=
    hasUnitBand_of_atkinLehnerHypothesis θG ψ U hU vRep hvΔ idx uu hp2 hψ hshape c c' hAL
  have hL := (leftIndex_mem (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω hband).2.1
  have hR := (rightIndex_mem (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω hband).1
  have hord : ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
      ≤ touchX p (Fintype.card ι) (k + 1) := by
    rw [touchX_succ_eq]
    refine le_trans (ordDim_le_card _ ω') ?_
    have h1 : 1 ≤ (k + 1) * p ^ 1 := Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (Nat.succ_ne_zero k) (pow_ne_zero 1 hp.out.ne_zero))
    nlinarith [Fintype.card_pos (α := ι)]
  rw [degX]
  omega

/-- **[LWX, Thm 1.3]: `deg X_{(0,1),ω} = qt − r_ord(ω⁻¹) − r_ord(ω)`**. -/
theorem degXint_zero (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K] (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ 0)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' 0)
    (d : TargetData c ω₁ T₁) (d' : TargetData c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 0 (c.matrix idx) B
      (c'.matrix idx)) :
    degXint (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω 0
      = p * Fintype.card ι - ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
        - ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω := by
  have hgap := touchX_sub_leftIndex_eq_ordDim idx hp2 hψ hshape hdet c c' d d' hAL
  have hband : HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (0 + 1) :=
    hasUnitBand_of_atkinLehnerHypothesis θG ψ U hU vRep hvΔ idx uu hp2 hψ hshape c c' hAL
  have hle := (leftIndex_mem (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω hband).2.1
  have hright := rightIndex_zero_eq_ordDim hp2
    (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω
  have htouch : touchX p (Fintype.card ι) (0 + 1) = p * Fintype.card ι := by
    rw [touchX]
    ring
  rw [htouch] at hgap hle
  rw [degXint, hright]
  omega

end LWX

end
