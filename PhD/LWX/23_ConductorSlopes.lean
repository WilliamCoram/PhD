/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«22_AtkinLehnerFamily»
import PhD.LWX.«13_SlopesSeam»
import PhD.NewtonPolygons.RootFaces

/-!
# The slope reflection at conductor `p^{h+1}`

The input to [LWX, Thm 1.5]'s second half ((1.5.2), `lwx.txt:2322–2366`), at the polygon level.
[LWX, §4.2]: "Let `ψ` be a character of conductor `p^M`. … `v(T_{(k,ψ)}) = q/((p−1)p^{M−1})`
by the assumption on `M`; thus `(k,ψ) ∈ W^{>λ}`. … it then follows that the `U_p`-slopes of
`S^D_{k+2}(K^pIw_{p^M}, ψ)` are `q²p^{−M}α̃_0, …, q²p^{−M}α̃_{(k+1)q^{−1}p^Mt−1}`. Hence, by
Atkin–Lehner theory (Proposition 3.22), … `α̃_{(k+1)q^{−1}p^Mt−1−i}(ψ⁻¹|_Δ·ω₀^k) =
(k+1)q^{−2}p^M − α̃_i(ψ|_Δ·ω₀^k)` for `0 ≤ i ≤ q^{−1}p^Mt − 1`."

With `M = h + 1`, `q = p`, `N = t(k+1)p^h` and `slopeRatio D ω j = ϕ(q)·α̃_j(ω)`
(`07_SlopeRatios.lean`), the displayed relation reads

  `slopeRatio D ω' (N − 1 − i) + slopeRatio D ω i = (k+1)·p^{h−1}(p−1)`,

`ω' = ω⁻¹ω₀^{2k}` the partner nebentypus.  Its proof here:

* **the region** ("the assumption on `M`"): `v(T) < 8/((p²−1)t+8)` at
  `v(T) = 1/(p^{h−1}(p−1))` is `(p²−1)t + 8 < 8p^{h−1}(p−1)` (`inv_pow_lt_norm_pow_of_norm_pow_eq`),
  which puts the classical point in the domain of `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio`;
* **the classical slopes are the first `N` slopes**: the Fredholm determinant splits off the
  classical factor `det(1 − X·A)` (`specCharSeries_eq_mul_charpolyRevH`), whose slopes are
  `≤ k+1` by H1 (`unitSlope_charpolyRev_matrix_leH`), while the complement's are `≥ k+1`
  (`le_unitSlope_compl` through the theta target of `18_TargetPointH.lean`); the product polygon
  then starts with the classical factor's slopes
  (`unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le`).  This replaces [LWX]'s appeal
  to classicality (Prop 2.15), exactly as in `14_Touching.lean`;
* **the reflection**: H1 (`roots_charpoly_of_atkinLehnerHypothesis`) gives the roots of the
  partner's classical factor as `p^{k+1}/x`, and counting roots in balls
  (`faceRight_eq_card_roots_le_self`, `faceLeft_eq_card_roots_lt_self`) turns that into the
  reflection `s'_{N−1−i} = (k+1)v(p) − s_i` of the sorted slopes
  (`toReal_unitSlope_charpolyRev_reflect`);
* dividing by `v(T) = v(p)/(p^{h−1}(p−1))` gives the identity of ratios.

The abstract form (`slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH`) still carries the
unit-band hypotheses `hband`, `hband'` of the slope reading.  They are discharged by the
**family** of Atkin–Lehner data (`22_AtkinLehnerFamily.lean`: one section, a Hecke character at
every classical weight `(ω, k)` of conductor `p²`): `hasUnitBand_of_atkinLehnerFamily` gives
`HasUnitBand D ω n` for every disc and every vertex (row 1 of the dependency ledger in
`.mathlib-quality/lwx-stepone/FINDINGS.md`, closed), hence [LWX, Thm 1.5 (1.5.1)] for the genuine
`U_p` unconditionally, the slope reflection with no hypothesis left
(`slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH`), and the ψ-varying bookkeeping
of [LWX, §4.2]: (4.2.5) `slopeRatio_partnerChar_succ`, (4.2.6) = **(1.5.2)**
`slopeRatio_mul_teichChar_sq`, and the arithmetic progressions `slopeRatio_add_period`
("since ω₀^{ϕ(q)} = 1", `lwx.txt:2361–2366`).  No Jacquet–Langlands input anywhere.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash
open scoped Nat TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The region `v(T) < 8/((p²−1)t + 8)` at conductor `p^{h+1}` -/

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **"The assumption on `M`"** ([LWX, Thm 1.5]: "`p^{−q/p^{M−1}(p−1)} > λ`" with
`λ = p^{−8/((p²−1)t+8)}`): at a point with `v(T₀) = v(p)/(p^{h−1}(p−1))`, the radius
condition `v(T₀) < 8/((p²−1)t+8)` of the slope reading is `(p²−1)t + 8 < 8p^{h−1}(p−1)`. -/
theorem inv_pow_lt_norm_pow_of_norm_pow_eq (h : ℕ) (_hh : 0 < h) {t : ℕ}
    (hM : (p ^ 2 - 1) * t + 8 < 8 * (p ^ (h - 1) * (p - 1))) {T₀ : K} (h1 : ‖T₀‖ < 1)
    (hnorm : ‖T₀‖ ^ (p ^ (h - 1) * (p - 1)) = (p : ℝ)⁻¹) :
    (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * t + 8) := by
  have he : p ^ (h - 1) * (p - 1) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (by have := hp.out.two_le; omega)
  have hT0 : 0 < ‖T₀‖ := by
    rcases (norm_nonneg T₀).lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq, zero_pow he] at hnorm
      exact absurd hnorm.symm (inv_ne_zero (Nat.cast_ne_zero.2 hp.out.ne_zero))
  calc (p : ℝ)⁻¹ ^ 8 = ‖T₀‖ ^ (8 * (p ^ (h - 1) * (p - 1))) := by
        rw [← hnorm, ← pow_mul, mul_comm (p ^ (h - 1) * (p - 1)) 8]
    _ < ‖T₀‖ ^ ((p ^ 2 - 1) * t + 8) := pow_lt_pow_right_of_lt_one₀ hT0 h1 hM

/-! ### The slopes of the classical factor at a level-`h` datum -/

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : ℕ) (ψ : ℚ_[p] →+* K)
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
  (uu : ι → Fin p → U)

section Datum

variable {θG h ψ U hU vRep hvΔ uu} {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}

omit [DecidableEq ι] in
/-- The region condition at a level-`h` classical datum. -/
theorem ClassicalDataH.inv_pow_lt_norm_pow (hh : 0 < h) {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K}
    {k : ℕ} (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1))) :
    (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8) :=
  inv_pow_lt_norm_pow_of_norm_pow_eq h hh hM c.h1 (by rw [c.hnorm, hψ, Padic.norm_p])

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq ι] in
/-- **Hypothesis H1 is symmetric in the two points**: `B' := P A Q` (the roles of `A` and
`A'` exchanged, `mul_eq_one_comm`). -/
theorem atkinLehnerHypothesis_symm {k : ℕ}
    {A B A' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K}
    (hAL : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A B A') :
    ∃ B', AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A' B' A := by
  obtain ⟨hAB, P, Q, hQP, hA'⟩ := hAL
  have hc0 : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero ψ).2 (Nat.cast_ne_zero.2 hp.out.ne_zero))
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hAinv : A * (((ψ (p : ℚ_[p])) ^ (k + 1))⁻¹ • B) = 1 := by
    rw [Matrix.mul_smul, hAB, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hBA : B * A = (ψ (p : ℚ_[p])) ^ (k + 1) • (1 : Matrix _ _ K) := by
    have h1 : (((ψ (p : ℚ_[p])) ^ (k + 1))⁻¹ • B) * A = 1 := mul_eq_one_comm.mp hAinv
    rw [Matrix.smul_mul] at h1
    calc B * A = (ψ (p : ℚ_[p])) ^ (k + 1) • (((ψ (p : ℚ_[p])) ^ (k + 1))⁻¹ • (B * A)) := by
          rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      _ = (ψ (p : ℚ_[p])) ^ (k + 1) • (1 : Matrix _ _ K) := by rw [h1]
  refine ⟨P * A * Q, ?_, Q, P, hPQ, ?_⟩
  · calc A' * (P * A * Q) = P * B * Q * (P * A * Q) := by rw [hA']
      _ = P * (B * (Q * P) * A) * Q := by simp only [Matrix.mul_assoc]
      _ = P * (B * A) * Q := by rw [hQP, Matrix.mul_one]
      _ = (ψ (p : ℚ_[p])) ^ (k + 1) • (P * Q) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = (ψ (p : ℚ_[p])) ^ (k + 1) • (1 : Matrix _ _ K) := by rw [hPQ]
  · calc A = Q * P * A * (Q * P) := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (P * A * Q) * P := by simp only [Matrix.mul_assoc]

/-- **The classical eigenvalues at `ψ` have norm at least `‖p‖^{k+1}`** at level `h`: their
Atkin–Lehner partners are eigenvalues of `U_p` at the partner point, hence of norm at most
one (`norm_le_one_of_isRoot_charpoly_upMatrix`, general in `h`). -/
theorem norm_pow_le_of_mem_roots_charpoly_matrixH [Nonempty ι] [IsAlgClosed K]
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx))
    {x : K} (hx : x ∈ (c.matrix idx).charpoly.roots) :
    ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ ≤ ‖x‖ := by
  classical
  obtain ⟨B, hAB, P, Q, hQP, hA'⟩ := hAL
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hA0 : (c.matrix idx).det ≠ 0 := det_ne_zero_of_mul_eq_smul' hcne hAB
  have hone : ∀ y ∈ (c'.matrix idx).charpoly.roots, ‖y‖ ≤ 1 := fun y hy =>
    norm_le_one_of_isRoot_charpoly_upMatrix idx c'.weight k _ (Polynomial.mem_roots'.1 hy).2
  have hxne : x ≠ 0 := by
    intro h0
    exact hA0 (by rw [Matrix.det_eq_prod_roots_charpoly]; exact Multiset.prod_eq_zero (h0 ▸ hx))
  have hmem : ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ / ‖x‖
      ∈ (c'.matrix idx).charpoly.roots.map (fun y => ‖y‖) := by
    rw [norm_roots_charpoly_atkinLehner hcne hAB hQP hA']
    exact Multiset.mem_map_of_mem _ hx
  obtain ⟨y, hy, hyeq⟩ := Multiset.mem_map.1 hmem
  have hy1 := hone y hy
  rw [hyeq, div_le_one (norm_pos_iff.2 hxne)] at hy1
  exact hy1

/-- **The classical slopes are at most `k+1`** at level `h` ([LWX, §4.2]: the `U_p`-slopes of
`S^D_{k+2}(K^pIw_{p^M}, ψ)`; derived from H1 and `‖U_p‖ ≤ 1`, never from classicality). -/
theorem unitSlope_charpolyRev_matrix_leH [Nonempty ι] [IsAlgClosed K]
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx)) {j : ℕ} (hj : j < Fintype.card ι * ((k + 1) * p ^ h)) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K)).unitSlope j
      ≤ ((((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖) : ℝ) : WithBotTop ℝ) := by
  obtain ⟨B, hAB, P, Q, hQP, hA'⟩ := hAL
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hccpos : (0 : ℝ) < ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ := norm_pos_iff.2 hcne
  have hA0 : (c.matrix idx).det ≠ 0 := det_ne_zero_of_mul_eq_smul' hcne hAB
  have hlow : ∀ x ∈ (c.matrix idx).charpoly.roots, ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ ≤ ‖x‖ :=
    fun x hx => norm_pow_le_of_mem_roots_charpoly_matrixH idx c c' ⟨B, hAB, P, Q, hQP, hA'⟩ hx
  have hGres : ∀ cst : ℝ, 0 < cst →
      PowerSeries.IsRestricted cst ((c.matrix idx).charpolyRev : PowerSeries K) :=
    fun cst _ => Polynomial.isRestricted_toPowerSeries _ _
  have hG0 : PowerSeries.coeff 0 ((c.matrix idx).charpolyRev : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hG0' : PowerSeries.coeff 0 ((c.matrix idx).charpolyRev : PowerSeries K) ≠ 0 := by
    rw [hG0]; exact one_ne_zero
  have hent := isEntireNewtonPolygonOf_coeffVal hGres hG0'
  have hcoeffN : PowerSeries.coeff (Fintype.card ι * ((k + 1) * p ^ h))
      ((c.matrix idx).charpolyRev : PowerSeries K) ≠ 0 := by
    have hcc := coeff_charpolyRev_card (c.matrix idx)
    rw [Fintype.card_fin] at hcc
    rw [Polynomial.coeff_coe, hcc]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hA0
  have hNtop : (newtonPolygon₀OfPowerSeries negLogNorm
      ((c.matrix idx).charpolyRev : PowerSeries K)).height
      ((Fintype.card ι * ((k + 1) * p ^ h) : ℕ) : ℤ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (height_le_coeffVal hGres hG0 _)
    rw [coeffVal_apply, negLogNorm_of_ne_zero hcoeffN]
    simp
  obtain ⟨m, hm⟩ := exists_coe_of_ne_bot_of_ne_top (hent.unitSlope_ne_bot j)
    ((newtonPolygon₀OfPowerSeries negLogNorm
      ((c.matrix idx).charpolyRev : PowerSeries K)).unitSlope_ne_top_of_height_natCast
      hent.starting_point_fst hNtop hj)
  rw [hm, WithBotTop.coe_le_coe]
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

/-- **The Fredholm determinant at a level-`h` classical datum splits** as the complement factor
times the characteristic polynomial of the classical matrix
(`charPowerSeries_eq_mul_of_stable`, `charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix`,
and the seam `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`). -/
theorem specCharSeries_eq_mul_charpolyRevH [Nonempty ι]
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀
      = charPowerSeries ((discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu).comp
          (1 - truncation (R := K) (classicalSupport p ι h k)))
        * (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) := by
  have hst : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu f
        ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := fun f hf =>
    mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG h ψ U hU
      vRep hvΔ idx uu c.weight c.shape hf
  have hcomp : IsCompactoid (discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu) :=
    isCompactoid_discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu (haloRhoH_nonneg h T₀)
      (max_lt (haloRhoH_lt_one h T₀ c.hT) inv_lt_one_p) hshape
  calc specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀
      = charPowerSeries (discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu) :=
        specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θG U hU vRep hvΔ idx uu
          hp2 c.h0 c.h1 c.hT hshape
    _ = charPowerSeries ((discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu).comp
          (1 - truncation (R := K) (classicalSupport p ι h k)))
        * (((classicalCoordMatrix h k
            (discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu)).charpolyRev :
              Polynomial K) : PowerSeries K) :=
        charPowerSeries_eq_mul_of_stable h k hcomp hst
    _ = _ := by
        rw [charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix h k _ hst]
        rfl

/-- **The first `N = t(k+1)p^h` slopes of the Fredholm determinant at a level-`h` classical
datum are the slopes of the classical factor** ([LWX, §4.2]: "the `U_p`-slopes of
`S^D_{k+2}(K^pIw_{p^M}, ψ)` are `q²p^{−M}α̃_0, …, q²p^{−M}α̃_{(k+1)q^{−1}p^Mt−1}`"): the
classical slopes are `≤ k+1`, the complement's are `≥ k+1`
(`le_unitSlope_compl` at the theta target `d`), and the product polygon starts with the
smaller factor (`unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le`). -/
theorem unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH [Nonempty ι] [IsAlgClosed K]
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetDataH c ω₁ T₁)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx)) {j : ℕ} (hj : j < Fintype.card ι * ((k + 1) * p ^ h)) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ)
          T₀)).unitSlope j
      = (newtonPolygon₀OfPowerSeries negLogNorm
          (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K)).unitSlope j := by
  rw [specCharSeries_eq_mul_charpolyRevH idx hshape c]
  have hcomp : IsCompactoid ((discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu).comp
      (1 - truncation (R := K) (classicalSupport p ι h k))) :=
    (isCompactoid_discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu (haloRhoH_nonneg h T₀)
      (max_lt (haloRhoH_lt_one h T₀ c.hT) inv_lt_one_p) hshape).comp_right _
  have hRres : ∀ cst : ℝ, 0 < cst → PowerSeries.IsRestricted cst
      (charPowerSeries ((discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι h k)))) :=
    fun cst hcst => charPowerSeries_isEntire _ hcomp cst hcst
  have hGres : ∀ cst : ℝ, 0 < cst →
      PowerSeries.IsRestricted cst (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) :=
    fun cst _ => Polynomial.isRestricted_toPowerSeries _ _
  have hR0 : PowerSeries.coeff 0
      (charPowerSeries ((discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu).comp
        (1 - truncation (R := K) (classicalSupport p ι h k)))) ≠ 0 := by
    rw [charPowerSeries_coeff, charCoeff_zero]; exact one_ne_zero
  have hG0 : PowerSeries.coeff 0 (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K)
      ≠ 0 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    exact one_ne_zero
  refine unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le hRres hGres hR0 hG0
    (fun i hi j' => ?_) hj
  exact (unitSlope_charpolyRev_matrix_leH idx c c' hAL hi).trans
    (le_unitSlope_compl θG h ψ U hU vRep hvΔ idx uu c.weight d.weight c.shape d.shape hdet
      (haloRhoH_nonneg h T₀) (max_lt (haloRhoH_lt_one h T₀ c.hT) inv_lt_one_p) hshape j')

end Datum

/-! ### The reflection of the sorted slopes -/

/-- **[LWX, Prop 3.22] in sorted-slope form**: if the characteristic roots of `A'` are
`c/x` for the roots `x` of `A` (with multiplicity), then the `(n−1−i)`-th unit slope of
`det(1 − X·A')` is `v(c)` minus the `i`-th unit slope of `det(1 − X·A)`.  Counting roots in
balls (`faceRight_eq_card_roots_le_self`, `faceLeft_eq_card_roots_lt_self`, `roots_charpolyRev`):
`faceRight_{A'} σ = n − faceLeft_A (v(c) − σ)`, and the face API of `Face.lean` turns that into
the reflection of the unit slopes. -/
theorem toReal_unitSlope_charpolyRev_reflect [IsAlgClosed K] {n : Type*} [Fintype n]
    [DecidableEq n] {A A' : Matrix n n K} {c : K} (hc : c ≠ 0) (hA : A.det ≠ 0)
    (hroots : A'.charpoly.roots = A.charpoly.roots.map (fun x => c / x)) {i : ℕ}
    (hi : i < Fintype.card n) :
    NewtonPolygon.toReal ((newtonPolygon₀OfPowerSeries negLogNorm
        ((A'.charpolyRev : Polynomial K) : PowerSeries K)).unitSlope (Fintype.card n - 1 - i))
      = -Real.log ‖c‖ - NewtonPolygon.toReal ((newtonPolygon₀OfPowerSeries negLogNorm
          ((A.charpolyRev : Polynomial K) : PowerSeries K)).unitSlope i) := by
  classical
  have hf0 : (A.charpolyRev).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hf'0 : (A'.charpolyRev).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hroot0 : ∀ x ∈ A.charpoly.roots, x ≠ 0 := fun x hx h0 =>
    hA (by rw [Matrix.det_eq_prod_roots_charpoly]; exact Multiset.prod_eq_zero (h0 ▸ hx))
  have hA' : A'.det ≠ 0 := by
    rw [Matrix.det_eq_prod_roots_charpoly, hroots]
    refine Multiset.prod_ne_zero fun h0 => ?_
    obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.1 h0
    exact div_ne_zero hc (hroot0 x hx) hx0
  have hcard : A.charpoly.roots.card = Fintype.card n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim]
  have hdeg : ∀ B : Matrix n n K, B.det ≠ 0 → B.charpolyRev.natDegree = Fintype.card n := by
    intro B hB
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [← Matrix.reverse_charpoly]
      exact (Polynomial.reverse_natDegree_le _).trans (Matrix.charpoly_natDegree_eq_dim B).le
    · rw [coeff_charpolyRev_card]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hB
  have hres : ∀ f : Polynomial K, ∀ cst : ℝ, 0 < cst →
      PowerSeries.IsRestricted cst (f : PowerSeries K) :=
    fun _ _ _ => Polynomial.isRestricted_toPowerSeries _ _
  have hc0 : ∀ f : Polynomial K, f.coeff 0 = 1 → PowerSeries.coeff 0 (f : PowerSeries K) ≠ 0 :=
    fun f hf => by rw [Polynomial.coeff_coe, hf]; exact one_ne_zero
  have hsu := slopesUnbounded_newtonPolygon₀OfPowerSeries (hres A.charpolyRev) (hc0 _ hf0)
  have hsu' := slopesUnbounded_newtonPolygon₀OfPowerSeries (hres A'.charpolyRev) (hc0 _ hf'0)
  have hfl_le : ∀ τ : ℝ, (newtonPolygon₀OfPowerSeries negLogNorm
      ((A.charpolyRev : Polynomial K) : PowerSeries K)).faceLeft τ ≤ Fintype.card n := by
    intro τ
    rw [faceLeft_eq_card_roots_lt_self _ hf0, Matrix.roots_charpolyRev hA]
    calc _ ≤ (A.charpoly.roots.map fun x => x⁻¹).card :=
          Multiset.card_le_card (Multiset.filter_le ..)
      _ = Fintype.card n := by rw [Multiset.card_map, hcard]
  have hcount : ∀ σ : ℝ, (newtonPolygon₀OfPowerSeries negLogNorm
      ((A'.charpolyRev : Polynomial K) : PowerSeries K)).faceRight σ
        = Fintype.card n - (newtonPolygon₀OfPowerSeries negLogNorm
          ((A.charpolyRev : Polynomial K) : PowerSeries K)).faceLeft (-Real.log ‖c‖ - σ) := by
    intro σ
    rw [faceRight_eq_card_roots_le_self _ hf'0, faceLeft_eq_card_roots_lt_self _ hf0,
      Matrix.roots_charpolyRev hA', Matrix.roots_charpolyRev hA,
      ← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter,
      Multiset.countP_map, Multiset.countP_map, ← Multiset.countP_eq_card_filter,
      ← Multiset.countP_eq_card_filter, hroots, Multiset.countP_map,
      ← Multiset.countP_eq_card_filter]
    have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
    have hcompl : ∀ x ∈ A.charpoly.roots,
        (‖(c / x)⁻¹‖ ≤ Real.exp σ) = ¬ (‖x⁻¹‖ < Real.exp (-Real.log ‖c‖ - σ)) := by
      intro x hx
      have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 (hroot0 x hx)
      refine propext ?_
      rw [inv_div, norm_div, norm_inv, not_lt,
        show Real.exp (-Real.log ‖c‖ - σ) = (‖c‖ * Real.exp σ)⁻¹ by
          rw [Real.exp_sub, Real.exp_neg, Real.exp_log hcpos, mul_inv, div_eq_mul_inv],
        inv_le_inv₀ (mul_pos hcpos (Real.exp_pos σ)) hxpos, div_le_iff₀ hcpos,
        mul_comm (Real.exp σ)]
    have hsum := congrArg Multiset.card (Multiset.filter_add_not
      (fun x : K => ‖x⁻¹‖ < Real.exp (-Real.log ‖c‖ - σ)) A.charpoly.roots)
    rw [Multiset.card_add, ← Multiset.countP_eq_card_filter,
      ← Multiset.countP_eq_card_filter] at hsum
    rw [Multiset.countP_congr rfl hcompl]
    omega
  have hi' : Fintype.card n - 1 - i < Fintype.card n := by omega
  have hent := isEntireNewtonPolygonOf_coeffVal (hres A.charpolyRev) (hc0 _ hf0)
  have hent' := isEntireNewtonPolygonOf_coeffVal (hres A'.charpolyRev) (hc0 _ hf'0)
  obtain ⟨m, hm⟩ := exists_coe_of_ne_bot_of_ne_top (hent.unitSlope_ne_bot i)
    (unitSlope_ne_top_of_lt_natDegree hf0 (by rw [hdeg A hA]; exact hi))
  obtain ⟨m', hm'⟩ := exists_coe_of_ne_bot_of_ne_top (hent'.unitSlope_ne_bot _)
    (unitSlope_ne_top_of_lt_natDegree hf'0 (by rw [hdeg A' hA']; exact hi'))
  have key : ∀ σ : ℝ, m' ≤ σ ↔ -Real.log ‖c‖ - σ ≤ m := by
    intro σ
    have h1 : (newtonPolygon₀OfPowerSeries negLogNorm
        ((A'.charpolyRev : Polynomial K) : PowerSeries K)).unitSlope (Fintype.card n - 1 - i)
          ≤ (σ : WithBotTop ℝ) ↔ Fintype.card n - 1 - i < (newtonPolygon₀OfPowerSeries negLogNorm
            ((A'.charpolyRev : Polynomial K) : PowerSeries K)).faceRight σ := by
      refine ⟨fun hle => ?_, fun hlt => NewtonPolygon₀.unitSlope_le_of_lt_faceRight (hj := hlt)⟩
      by_contra hcon
      exact absurd hle (not_le.2
        (NewtonPolygon₀.lt_unitSlope_of_faceRight_le (hP := hsu') (hj := not_lt.1 hcon)))
    have h2 : (newtonPolygon₀OfPowerSeries negLogNorm
        ((A.charpolyRev : Polynomial K) : PowerSeries K)).faceLeft (-Real.log ‖c‖ - σ) ≤ i
          ↔ ((-Real.log ‖c‖ - σ : ℝ) : WithBotTop ℝ) ≤ (newtonPolygon₀OfPowerSeries negLogNorm
            ((A.charpolyRev : Polynomial K) : PowerSeries K)).unitSlope i :=
      ⟨fun hle => NewtonPolygon₀.le_unitSlope_of_faceLeft_le (hP := hsu) (hj := hle),
        fun hle => NewtonPolygon₀.faceLeft_le_of_le_unitSlope (hj := hle)⟩
    rw [hm', WithBotTop.coe_le_coe, hcount σ] at h1
    rw [hm, WithBotTop.coe_le_coe] at h2
    rw [h1, ← h2]
    have hle := hfl_le (-Real.log ‖c‖ - σ)
    constructor <;> intro hlt <;> omega
  rw [hm, hm', NewtonPolygon.toReal_coe, NewtonPolygon.toReal_coe]
  have hle1 : m' ≤ -Real.log ‖c‖ - m := (key _).2 (by linarith)
  have hle2 := (key m').1 le_rfl
  linarith

/-! ### The slope reflection, abstractly -/

section Reflection

variable {θG h ψ U hU vRep hvΔ uu} {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}

/-- **[LWX, (4.2.5)'s input] at a pair of level-`h` classical data with targets**: for
`i < N = t(k+1)p^h`,
`slopeRatio ω' (N − 1 − i) + slopeRatio ω i = (k+1)·p^{h−1}(p−1)`.
The unit-band hypotheses are the level-`1` output at every vertex
(`hasUnitBand_of_atkinLehnerData`, one `k` at a time). -/
theorem slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH [Nonempty ι] [IsAlgClosed K]
    (hh : 0 < h)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetDataH c ω₁ T₁) (d' : TargetDataH c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx))
    (hband : ∀ n, HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω n)
    (hband' : ∀ n, HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω' n)
    {i : ℕ} (hi : i < Fintype.card ι * ((k + 1) * p ^ h)) :
    slopeRatio (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
          (Fintype.card ι * ((k + 1) * p ^ h) - 1 - i)
        + slopeRatio (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω i
      = ((k + 1 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  obtain ⟨B, hB⟩ := hAL
  have hAL' := atkinLehnerHypothesis_symm hB
  have hi' : Fintype.card ι * ((k + 1) * p ^ h) - 1 - i < Fintype.card ι * ((k + 1) * p ^ h) := by
    omega
  have hread := unitSlope_discHeckeCharPowerSeries_eq_slopeRatio ψ hψ T₀ ω θG U hU vRep hvΔ idx
    uu h hp2 c.h0 c.h1 c.hT (c.inv_pow_lt_norm_pow hh hM) hshape hband i
  rw [← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θG U hU vRep hvΔ idx uu
    hp2 c.h0 c.h1 c.hT hshape, unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH idx
    hshape hdet c c' d ⟨B, hB⟩ hi] at hread
  have hread' := unitSlope_discHeckeCharPowerSeries_eq_slopeRatio ψ hψ T₀' ω' θG U hU vRep hvΔ
    idx uu h hp2 c'.h0 c'.h1 c'.hT (c'.inv_pow_lt_norm_pow hh hM) hshape hband'
    (Fintype.card ι * ((k + 1) * p ^ h) - 1 - i)
  rw [← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀' ω' h θG U hU vRep hvΔ idx uu
    hp2 c'.h0 c'.h1 c'.hT hshape, unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH idx
    hshape hdet c' c d' hAL' hi'] at hread'
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun h0 =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [h0, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hA0 : (c.matrix idx).det ≠ 0 := by
    obtain ⟨hAB, -⟩ := hB
    exact det_ne_zero_of_mul_eq_smul' hcne hAB
  have hrefl := toReal_unitSlope_charpolyRev_reflect hcne hA0
    (roots_charpoly_of_atkinLehnerHypothesis (hAL := hB)) (i := i)
    (by rw [Fintype.card_fin]; exact hi)
  rw [Fintype.card_fin] at hrefl
  have hr := congrArg NewtonPolygon.toReal hread
  have hr' := congrArg NewtonPolygon.toReal hread'
  rw [NewtonPolygon.toReal_coe] at hr hr'
  have hvpos : 0 < -Real.log ‖T₀‖ := by
    have hT0pos : 0 < ‖T₀‖ := lt_trans (inv_pos.2 (Nat.cast_pos.2 hp.out.pos)) c.h0
    linarith [Real.log_neg hT0pos c.h1]
  have hv : -Real.log ‖T₀'‖ = -Real.log ‖T₀‖ := by rw [c.norm_eq hh c']
  rw [hr', hr, hv, norm_pow, Real.log_pow] at hrefl
  have he := c.mul_neg_log_norm_eq
  refine mul_left_cancel₀ hvpos.ne' ?_
  linear_combination hrefl - (((k + 1 : ℕ) : ℝ)) * he

end Reflection

/-! ### At the classical points, from the Atkin–Lehner data -/

section Data

variable {vRep hvΔ idx uu}

/-- **Row 1 of the dependency ledger closed at level `1`**: the touching hypothesis at
`n_{k+1}` with no hypothesis left, granted the adelic data
(`hasUnitBand_of_atkinLehnerHypothesis` at `classicalData` and its partner, with H1 from
`atkinLehnerHypothesis_of_atkinLehnerData`). -/
theorem hasUnitBand_of_atkinLehnerData [Nonempty ι] (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (k : ℕ)
    (D : AtkinLehnerData θG ψ U Γ (nebCharK ψ ω k ζ))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (idx : ι → Fin p → ι) (uu : ι → Fin p → U) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRepD θG ψ U D t)⁻¹ = d i t * c (idx i t) * (uu i t : G))
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU (vRepD θG ψ U D)
      (vRepD_mem_levelM1 θG ψ U D) uu i t)).IsUpShape) :
    HasUnitBand (UpDatum.ofCerts θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu
      hshape) ω (k + 1) :=
  hasUnitBand_of_atkinLehnerHypothesis (hp2 := hp2) (hψ := hψ) (hshape := hshape)
    (c := classicalData ψ ω θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ
      (norm_natCast_p ψ hψ) k)
    (c' := classicalData ψ (partnerChar p ω k) θG U hU (vRepD θG ψ U D)
      (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ.inv (norm_natCast_p ψ hψ) k)
    (hAL := atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ
      (norm_natCast_p ψ hψ) D hfin hv hvinj c hc hstab idx uu d hd hfact)

end Data

/-! ### The unit band at every vertex, and the slope reflection without hypotheses -/

section Family

variable {ζ₁ : K} (F : AtkinLehnerFamily θG ψ U Γ ζ₁)
variable (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltF θG ψ U F} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
  (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepF θG ψ U F))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltF θG ψ U F} : Set G) * (U : Set G))) : Set (RightCosets U)))
  (hvinj : Function.Injective (vRepF θG ψ U F))
  (c : ι → G)
  (hc : Function.Bijective
    (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
  (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
  (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
  (hfact : ∀ i t, c i * (vRepF θG ψ U F t)⁻¹ = d i t * c (idx i t) * (uu i t : G))
  (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F)
    uu i t)).IsUpShape)

include hfin hv hvinj c hc hstab d hd hfact in
/-- **Row 1 of the dependency ledger closed**: the unit-band hypothesis at **every** vertex and
**every** disc, granted the adelic data at every classical weight of conductor `p²`
(`hasUnitBand_zero` at `n = 0`, `hasUnitBand_of_atkinLehnerData` at `F.toData ω k` for
`n = k + 1`; the `UpDatum` is the same for every `(ω, k)` by `vRepD_toData`). -/
theorem hasUnitBand_of_atkinLehnerFamily [Nonempty ι] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ₁ : IsPrimitiveRoot ζ₁ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    HasUnitBand (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
      hshape) ω n := by
  rcases n with _ | k
  · exact hasUnitBand_zero _ ω
  · exact hasUnitBand_of_atkinLehnerData θG ψ U hU ω hp2 hψ hζ₁ k
      (AtkinLehnerFamily.toData θG ψ U F ω k) hfin hv hvinj c hc hstab idx uu d hd hfact hshape

include hfin hv hvinj c hc hstab d hd hfact in
/-- **[LWX, Thm 1.5 (1.5.1)] for the genuine `U_p`, with no hypothesis left**: at every halo
point of the slope-reading region and every analyticity level, every slope of `det(1 − X·U_p)`
is `v(T₀)` times a `T`-free ratio (`unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` with the
unit band supplied by `hasUnitBand_of_atkinLehnerFamily`). -/
theorem unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily [Nonempty ι]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : K} (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries θG h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU
            (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu)).unitSlope j
      = (((-Real.log ‖T₀‖)
          * slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F)
              idx uu hshape) ω j : ℝ) : WithBotTop ℝ) :=
  unitSlope_discHeckeCharPowerSeries_eq_slopeRatio ψ hψ T₀ ω θG U hU (vRepF θG ψ U F)
    (vRepF_mem_levelM1 θG ψ U F) idx uu h hp2 h0 h1 hT hκ hshape
    (fun n => hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd
      hfact hshape hp2 hψ hζ₁ ω n) j

variable {ζ : K} (X : AtkinLehnerFamilyH θG ψ U F h ζ)
variable (hdet : ∀ i t, (certM1 θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu i t :
    Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)

include hfin hv hvinj c hc hstab d hd hfact X hdet in
/-- **[LWX, §4.2]'s displayed relation, with no hypothesis left**
("α̃_{(k+1)q^{−1}p^Mt−1−i}(ψ⁻¹|_Δ·ω₀^k) = (k+1)q^{−2}p^M − α̃_i(ψ|_Δ·ω₀^k)", `lwx.txt:2345–2350`):
at conductor `p^{h+1}`, for `i < N = t(k+1)p^h`,
`slopeRatio (ω⁻¹ω₀^{2k}) (N − 1 − i) + slopeRatio ω i = (k+1)·p^{h−1}(p−1)`
(`slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH` at the classical points of the level-`h`
family, with the unit bands from the level-`1` family). -/
theorem slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) {i : ℕ} (hi : i < Fintype.card ι * ((k + 1) * p ^ h)) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω k) (Fintype.card ι * ((k + 1) * p ^ h) - 1 - i)
        + slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) ω i
      = ((k + 1 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) :=
  slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH idx hh hshape hdet hM
    (classicalDataH ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hh hζ
      (norm_natCast_p ψ hψ) k)
    (classicalDataH ψ (partnerChar p ω k) θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F)
      uu hp2 hψ hh hζ.inv (norm_natCast_p ψ hψ) k)
    (targetData_classicalPointH ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2
      hψ hh hζ (norm_natCast_p ψ hψ) k)
    (targetData_classicalPointH ψ (partnerChar p ω k) θG U hU (vRepF θG ψ U F)
      (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hh hζ.inv (norm_natCast_p ψ hψ) k)
    (atkinLehnerHypothesis_of_atkinLehnerDataH θG ψ U hU h k ω hp2 hψ hh hζ (norm_natCast_p ψ hψ)
      (AtkinLehnerFamilyH.toDataH θG ψ U F X ω k) hfin hv hvinj c hc hstab idx uu d hd hfact)
    (hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact
      hshape hp2 hψ hζ₁ ω)
    (hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact
      hshape hp2 hψ hζ₁ (partnerChar p ω k))
    hi

include hfin hv hvinj c hc hstab d hd hfact X hdet in
/-- **[LWX, (4.2.5)]**: "α̃_{(k+2)q^{−1}p^Mt−1−i}(ψ⁻¹|_Δ·ω₀^{k+2}) = α̃_{(k+1)q^{−1}p^Mt−1−i}(ψ⁻¹|_Δ·ω₀^k)
+ q^{−2}p^M" (`lwx.txt:2353–2355`) — the displayed relation at `(ω, k)` and at `(ω, k+1)`,
subtracted. -/
theorem slopeRatio_partnerChar_succ [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) {i : ℕ} (hi : i < Fintype.card ι * ((k + 1) * p ^ h)) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω (k + 1)) (Fintype.card ι * ((k + 2) * p ^ h) - 1 - i)
      = slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) (partnerChar p ω k) (Fintype.card ι * ((k + 1) * p ^ h) - 1 - i)
        + ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  have hi' : i < Fintype.card ι * ((k + 1 + 1) * p ^ h) := by
    have hle : Fintype.card ι * ((k + 1) * p ^ h) ≤ Fintype.card ι * ((k + 1 + 1) * p ^ h) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
    omega
  have h1 := slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH θG h ψ U hU idx uu F hfin
    hv hvinj c hc hstab d hd hfact hshape X hdet hp2 hψ hh hζ₁ hζ hM ω k hi
  have h2 : slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
        uu hshape) (partnerChar p ω (k + 1)) (Fintype.card ι * ((k + 2) * p ^ h) - 1 - i)
      + slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
        uu hshape) ω i
      = ((k + 2 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) :=
    slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH θG h ψ U hU idx uu F hfin hv hvinj
      c hc hstab d hd hfact hshape X hdet hp2 hψ hh hζ₁ hζ hM ω (k + 1) hi'
  push_cast at h1 h2 ⊢
  linarith

include hfin hv hvinj c hc hstab d hd hfact X hdet in
/-- **[LWX, Thm 1.5, (1.5.2)] at the polygon level** — (4.2.6), `lwx.txt:2356–2360`:
"α̃_{j+q^{−1}p^Mt}(ωω₀²) = α̃_j(ω) + q^{−2}p^M for any j ≥ 0".  With `slopeRatio = ϕ(q)·α̃`,
`M = h + 1`, `q = p`: `slopeRatio (ωω₀²) (j + p^h t) = slopeRatio ω j + p^{h−1}(p−1)`
(`slopeRatio_partnerChar_succ` at the disc `ω⁻¹ω₀^{2k}` with `k = j / (p^h t)`,
`partnerChar_invChar_mul_teichChar_pow`, `partnerChar_succ`). -/
theorem slopeRatio_mul_teichChar_sq [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (j : ℕ) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * teichChar p ^ 2) (j + p ^ h * Fintype.card ι)
      = slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) ω j + ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  have hT : 0 < p ^ h * Fintype.card ι := Nat.mul_pos (pow_pos hp.out.pos h) Fintype.card_pos
  obtain ⟨k, hk⟩ : ∃ k, k = j / (p ^ h * Fintype.card ι) := ⟨_, rfl⟩
  have hdiv := Nat.lt_div_mul_add (a := j) hT
  have hle := Nat.div_mul_le_self j (p ^ h * Fintype.card ι)
  rw [← hk] at hdiv hle
  have hN : Fintype.card ι * ((k + 1) * p ^ h)
      = k * (p ^ h * Fintype.card ι) + p ^ h * Fintype.card ι := by ring
  have hN2 : Fintype.card ι * ((k + 2) * p ^ h)
      = Fintype.card ι * ((k + 1) * p ^ h) + p ^ h * Fintype.card ι := by ring
  have hi : Fintype.card ι * ((k + 1) * p ^ h) - 1 - j < Fintype.card ι * ((k + 1) * p ^ h) := by
    omega
  have h45 := slopeRatio_partnerChar_succ θG h ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact
    hshape X hdet hp2 hψ hh hζ₁ hζ hM (invChar ω * teichChar p ^ (2 * k)) k hi
  rw [partnerChar_succ, partnerChar_invChar_mul_teichChar_pow,
    show Fintype.card ι * ((k + 1) * p ^ h) - 1 - (Fintype.card ι * ((k + 1) * p ^ h) - 1 - j)
      = j by omega,
    show Fintype.card ι * ((k + 2) * p ^ h) - 1 - (Fintype.card ι * ((k + 1) * p ^ h) - 1 - j)
      = j + p ^ h * Fintype.card ι by omega] at h45
  exact h45

include hfin hv hvinj c hc hstab d hd hfact X hdet in
/-- (1.5.2) iterated `m` times. -/
theorem slopeRatio_mul_teichChar_pow [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m j : ℕ) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * teichChar p ^ (2 * m)) (j + m * (p ^ h * Fintype.card ι))
      = slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) ω j + (m : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  induction m generalizing j with
  | zero =>
    rw [mul_teichChar_pow_zero ω, zero_mul, add_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ m ih =>
    rw [mul_teichChar_pow_succ ω m, show j + (m + 1) * (p ^ h * Fintype.card ι)
        = j + m * (p ^ h * Fintype.card ι) + p ^ h * Fintype.card ι by ring,
      slopeRatio_mul_teichChar_sq θG h ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape
        X hdet hp2 hψ hh hζ₁ hζ hM (ω * teichChar p ^ (2 * m)), ih]
    push_cast
    ring

include hfin hv hvinj c hc hstab d hd hfact X hdet in
/-- **[LWX, Thm 1.5, second half] at the polygon level** (`lwx.txt:2361–2366`): "since
ω₀^{ϕ(q)} = 1, we have α̃_{j+(p−1)p^{M−1}t/2}(ω) = α̃_j(ω) + ϕ(q)p^M/(2q²). Therefore the sequence
α̃_0(ω), α̃_1(ω), … is the disjoint union of arithmetic progressions … which have common
difference ϕ(q)p^M/(2q²)."  Here: the slope ratios of every disc `ω` are periodic of period
`(p−1)/2·p^h t` up to the constant `(p−1)/2·p^{h−1}(p−1)` (`slopeRatio_mul_teichChar_pow` at
`m = (p−1)/2` and `mul_teichChar_pow_two_mul_sub_one_div_two`). -/
theorem slopeRatio_add_period [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (j : ℕ) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω (j + (p - 1) / 2 * (p ^ h * Fintype.card ι))
      = slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) ω j + (((p - 1) / 2 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  have hres := slopeRatio_mul_teichChar_pow θG h ψ U hU idx uu F hfin hv hvinj c hc hstab d hd
    hfact hshape X hdet hp2 hψ hh hζ₁ hζ hM ω ((p - 1) / 2) j
  rwa [mul_teichChar_pow_two_mul_sub_one_div_two hp2] at hres

end Family


end LWX

end
