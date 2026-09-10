/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.SlopeRatios
import PhD.LWX.QuaternionicH

/-!
# The halo estimates and slope theorems, read on the genuine `U_p`

`PhD/LWX/{Halo,Sharpness,UpperPolygon,Vertices,Claim,SlopeRatios}.lean` prove [LWX]'s halo
estimate ([LWX, Thm 3.16], [LWX, Cor 3.18]) and slope theorems ([LWX, Thm 1.3], [LWX, Thm 1.5])
about `LWX.specCharSeries`, the specialisation at `T₀` of the characteristic series of the
**integral matrix** of a certificate datum.  `PhD/LWX/SeamH.lean` identifies that series with
the Fredholm determinant `det(1 − X·U_p)` of the genuine Hecke operator on `S^{D,†,m}` at every
analyticity level `m = h + 1` ([LWX, Prop 2.17]).

This file composes the two.  Each statement below is the corresponding polygon-level theorem
with `specCharSeries` replaced by `discHeckeCharPowerSeries`, at every point of the boundary
annulus `p⁻¹ < ‖T₀‖ < 1`.  Nothing new is proved: each proof is the seam identity followed by
the corresponding polygon-level theorem.

`discHeckeCharPowerSeries` is the Fredholm determinant computed in the block model at
certificate data.  It is the determinant of `U_p` acting on `S^{D,†,m}` itself at a neat level,
through `discEvalAtReps_discHeckeOperator` and `bijective_discEvalAtReps_of_stabilizer_eq_bot`;
`evalT_discHeckeCharPowerSeries_eq_zero_iff` is that reading in eigenvalue form.  The
statements below carry no neatness hypothesis because they do not need one.

The definite-quaternion case of [LWX, §2.4] is the instantiation `θ = LWX.thetaInt p D`,
`ψ = LWX.padicComparison p` (as in `PhD/LWX/QuaternionicH.lean`); no separate statement is
given for it here.

The two remaining clauses of [LWX, Thm 1.5]'s first half, that the ratios are increasing and
tend to infinity, are `T`-free statements about `LWX.slopeRatio` and live in
`PhD/LWX/SlopeGrowth.lean`; they apply verbatim to the ratios appearing below.

## Main declarations

* `LWX.isBelow_newtonPolygon_discHeckeCharPowerSeries` — [LWX, Cor 3.18] for `det(1 − X·U_p)`.
* `LWX.hasUnitBand_of_height_discHeckeCharPowerSeries_eq` — **the interface [LWX, Step I] has to
  hit**: if the Newton polygon of `det(1 − X·U_p)` touches the lower bound polygon at `n_k` at
  one halo point, the touching hypothesis `HasUnitBand` holds.
* `LWX.unitSlope_discHeckeCharPowerSeries_eq_iff`,
  `LWX.unitSlope_discHeckeCharPowerSeries_mem_Ioo` — [LWX, Thm 1.3]'s slope reading for
  `U_p` (the `X_k` and `X_{(k,k+1)}` clauses).
* `LWX.unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` — [LWX, Thm 1.5 (1.5.1)] for `U_p`.
* `LWX.exists_level_unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` — the same at *every*
  halo point, at a level supplied by `exists_sq_norm_pow_prime_pow_sub_one_lt`.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash

open scoped Nat TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : Type*} [Group G] (θ : G →* Matrix (Fin 2) (Fin 2) ℚ_[p]) (U : Subgroup G)
  (hU : (U : Set G) ⊆ levelM1 (p := p) θ)
variable (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θ) (idx : ι → Fin p → ι)
  (u : ι → Fin p → U)

section AtOneLevel

variable (h : ℕ)

/-- **[LWX, Corollary 3.18] for the genuine `U_p`**: at every halo point and every analyticity
level, the Newton polygon of `det(1 − X·U_p)` on `S^{D,†,m}` lies on or above the polygon with
vertices `(n, λ(n)·v(T₀))`. -/
theorem isBelow_newtonPolygon_discHeckeCharPowerSeries (hp2 : p ≠ 2) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    (NewtonPolygon₀.ofSlopes (lwxSlopes p (Fintype.card ι) T₀)
        (monotone_lwxSlopes _ _ h1
          ((inv_pos.2 (by exact_mod_cast hp.out.pos)).trans h0)) 0).IsBelow
      (newtonPolygon₀OfPowerSeries negLogNorm
        (discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
          idx u)) := by
  rw [← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
    hp2 h0 h1 hT hshape]
  exact isBelow_newtonPolygon_specCharSeries hp2 _ ω (intHom ψ) (norm_intHom ψ hψ) h0 h1

/-- **The interface [LWX, Step I] has to hit.**  [LWX, Step I] shows that at the classical weight
`T_{χ_k}` the Newton polygon of `det(1 − X·U_p)` touches the lower bound polygon at `n_k`.  This
says that such a touching, at any single halo point and any analyticity level, gives the `T`-free
touching hypothesis `HasUnitBand` that [LWX, Step II] runs on. -/
theorem hasUnitBand_of_height_discHeckeCharPowerSeries_eq (hp2 : p ≠ 2) [Nonempty ι]
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) {k : ℕ}
    (htouch : (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
            idx u)).height (touchX p (Fintype.card ι) k)
        = (((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) k) : ℝ)
            * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ)) :
    HasUnitBand (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω k := by
  refine hasUnitBand_of_height_eq hp2 _ ω (intHom ψ) (norm_intHom ψ hψ) h0 h1 ?_
  rwa [specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
    hp2 h0 h1 hT hshape]

/-- **[LWX, Theorem 1.3]'s `X_k` clause for the genuine `U_p`**: the `j`-th slope of
`det(1 − X·U_p)` is `kφ(q)v(T₀)` exactly for `j ∈ [n_k^−, n_k^+)`. -/
theorem unitSlope_discHeckeCharPowerSeries_eq_iff (hp2 : p ≠ 2) [Nonempty ι]
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) {k : ℕ}
    (hb : HasUnitBand (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω k) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
            idx u)).unitSlope j
        = ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) ↔
      leftIndex (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω k ≤ j ∧
        j < rightIndex (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω k := by
  rw [← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
    hp2 h0 h1 hT hshape]
  exact unitSlope_specCharSeries_eq_iff hp2 _ ω (intHom ψ) (norm_intHom ψ hψ) h0 h1 hb j

/-- **[LWX, Theorem 1.3]'s `X_{(k,k+1)}` clause for the genuine `U_p`**: for
`j ∈ [n_k^+, n_{k+1}^−)` the `j`-th slope of `det(1 − X·U_p)` lies strictly between
`kφ(q)v(T₀)` and `(k+1)φ(q)v(T₀)`. -/
theorem unitSlope_discHeckeCharPowerSeries_mem_Ioo (hp2 : p ≠ 2) [Nonempty ι]
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) {k : ℕ}
    (hb : HasUnitBand (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω k)
    (hb' : HasUnitBand (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω (k + 1)) {j : ℕ}
    (hj1 : rightIndex (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω k ≤ j)
    (hj2 : j < leftIndex (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω (k + 1)) :
    (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
            idx u)).unitSlope j ∈
      Set.Ioo ((((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ)
        (((((k + 1) * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) := by
  rw [← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
    hp2 h0 h1 hT hshape]
  exact unitSlope_specCharSeries_mem_Ioo hp2 _ ω (intHom ψ) (norm_intHom ψ hψ) h0 h1 hb hb'
    hj1 hj2

/-- **[LWX, Theorem 1.5 (1.5.1)] for the genuine `U_p`**: every slope of `det(1 − X·U_p)` is
`v(T₀)` times a `T`-free ratio. -/
theorem unitSlope_discHeckeCharPowerSeries_eq_slopeRatio (hp2 : p ≠ 2) [Nonempty ι]
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8))
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape)
    (hband : ∀ k, HasUnitBand (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω k) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
            idx u)).unitSlope j
      = (((-Real.log ‖T₀‖)
          * slopeRatio (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω j : ℝ) : WithBotTop ℝ) := by
  rw [← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
    hp2 h0 h1 hT hshape]
  exact unitSlope_specCharSeries_eq_slopeRatio hp2 _ ω (intHom ψ) (norm_intHom ψ hψ) h0 h1 hκ
    hband j

end AtOneLevel

section EveryPoint

/-- **[LWX, Theorem 1.5 (1.5.1)] at every halo point.**  For every `T₀` in the boundary annulus
there is an analyticity level `m = h + 1` at which the slopes of `U_p` on `S^{D,†,m}` are
`v(T₀)` times the `T`-free ratios.  (The level is the one produced by
`exists_sq_norm_pow_prime_pow_sub_one_lt`; by `discHeckeCharPowerSeries_eq_of_levels` the
determinant, hence the conclusion, does not depend on which one is taken.) -/
theorem exists_level_unitSlope_discHeckeCharPowerSeries_eq_slopeRatio (hp2 : p ≠ 2) [Nonempty ι]
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8))
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape)
    (hband : ∀ k, HasUnitBand (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω k) (j : ℕ) :
    ∃ (h : ℕ) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹),
      (newtonPolygon₀OfPowerSeries negLogNorm
            (discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
              idx u)).unitSlope j
        = (((-Real.log ‖T₀‖)
            * slopeRatio (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω j : ℝ) :
          WithBotTop ℝ) := by
  have hpK : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  obtain ⟨h, hT⟩ := exists_sq_norm_pow_prime_pow_sub_one_lt (K := K) hpK h1
  exact ⟨h, hT, unitSlope_discHeckeCharPowerSeries_eq_slopeRatio ψ hψ T₀ ω θ U hU vRep hvΔ idx u
    h hp2 h0 h1 hT hκ hshape hband j⟩

end EveryPoint

end LWX

end
