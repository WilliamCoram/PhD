/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«16_ThetaExact»
import PhD.LWX.«16_TargetPoint»

/-!
# The degree formula granted H1 alone

[LWX, Theorem 1.3]'s `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})`, with hypothesis
H2 discharged (`isThetaExact_classicalData`) and the target datum constructed at the classical
points (`targetData`).  The only remaining hypothesis is H1, the Atkin–Lehner symmetry
[LWX, Prop 3.22], stated on the classical subspaces at the classical points `T_{χ_k}` of
nebentypus `ω` and its Atkin–Lehner partner of nebentypus `ω'`; identifying `ω'` with
`ω⁻¹ω₀^{2k}` is the other half of the gap `AG-ω₀`, outside this board.
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable {G : Type*} [Group G] {Γ : Subgroup G} {θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p]}
variable {ψ : ℚ_[p] →+* K}
variable {U : Subgroup G} {hU : (U : Set G) ⊆ levelM1 (p := p) θG}
  {vRep : Fin p → G} {hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG} (idx : ι → Fin p → ι)
  {uu : ι → Fin p → U}

/-- **[LWX, Thm 1.3], the degree formula at a classical datum with a target, granted H1**:
`degX_succ` with H2 supplied by `isThetaExact_classicalData`. -/
theorem degX_succ_of_targetData (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetData c ω₁ T₁) (d' : TargetData c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    degX (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
        + ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ :=
  degX_succ idx hp2 hψ hshape hdet c c' d d' hAL (isThetaExact_classicalData idx hshape hdet c d)

/-- **[LWX, Thm 1.3] at the classical points, granted H1**:
`deg X_{k+1,ω} = r_ord(ω') + r_ord(ω·ω₀^{−2k−2})`, where `ω'` is the nebentypus of the
Atkin–Lehner partner point at which H1 is asserted. -/
theorem degX_succ_classicalPoint (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p)
    (ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k
      ((classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ (norm_natCast_p ψ hψ) k).matrix idx) B
      ((classicalData ψ ω' θG U hU vRep hvΔ uu hp2 hψ hζ' (norm_natCast_p ψ hψ) k).matrix idx)) :
    degX (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
        + ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) (targetChar p ω k) :=
  degX_succ_of_targetData idx hp2 hψ hshape hdet
    (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ (norm_natCast_p ψ hψ) k)
    (classicalData ψ ω' θG U hU vRep hvΔ uu hp2 hψ hζ' (norm_natCast_p ψ hψ) k)
    (targetData_classicalPoint ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ (norm_natCast_p ψ hψ) k)
    (targetData_classicalPoint ψ ω' θG U hU vRep hvΔ uu hp2 hψ hζ' (norm_natCast_p ψ hψ) k)
    hAL

end LWX

end
