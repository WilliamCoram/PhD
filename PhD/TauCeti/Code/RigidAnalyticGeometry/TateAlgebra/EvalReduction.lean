/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Eval
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Reduction

/-!
# Reduction commutes with evaluation

Evaluating a series of the unit ball of the Tate algebra at a point of the unit ball and then
reducing is the same as reducing the series and evaluating the resulting polynomial at the reduced
point. This is the commutative square of BGR 5.1.4, for points with coordinates in a complete
extension field `L` of `K`, and its analogue for the substitution homomorphisms between Tate
algebras (BGR 5.1.3/7).

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.1.3 (BGR 5.1.4, 5.1.3/7).
Tau Ceti home: `TauCeti/RingTheory/TateAlgebra/Reduction.lean`.

## Main definitions

* `NormedField.unitClosedBallMap K L` — the map `K⁰ →+* L⁰` of unit balls of a normed extension.
* `NormedField.residueFieldMap K L` — the induced map of residue fields.

## Main results

* `MvPowerSeries.Restricted.residue_aeval` — reduction commutes with evaluation at a point.
* `MvPowerSeries.Restricted.reduction_aeval` — reduction commutes with substitution.
-/

open Subring NormedRing IsLocalRing

namespace NormedField

variable (K : Type*) [NormedField K] [IsUltrametricDist K]
  (L : Type*) [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]

/-- The map of unit balls `K⁰ → L⁰` induced by a normed field extension. -/
def unitClosedBallMap : unitClosedBall K →+* unitClosedBall L :=
  (algebraMap K L).restrict _ _ fun a ha ↦ by
    rw [mem_unitClosedBall] at ha ⊢
    rwa [norm_algebraMap']

@[simp]
theorem coe_unitClosedBallMap (a : unitClosedBall K) :
    (unitClosedBallMap K L a : L) = algebraMap K L a := rfl

instance isLocalHom_unitClosedBallMap : IsLocalHom (unitClosedBallMap K L) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [isUnit_iff_norm_eq_one] at ha ⊢
  rwa [coe_unitClosedBallMap, norm_algebraMap'] at ha

/-- The map of residue fields induced by a normed field extension. -/
noncomputable def residueFieldMap :
    ResidueField (unitClosedBall K) →+* ResidueField (unitClosedBall L) :=
  ResidueField.map (unitClosedBallMap K L)

end NormedField

namespace MvPowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}

/-- Evaluation at a tuple of the unit ball maps the unit ball of the Tate algebra to the unit
ball. Source: BGR 5.1.4/2. -/
theorem norm_aeval_le_one {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [NormOneClass B]
    [IsUltrametricDist B] [CompleteSpace B] {x : σ → B} (hx : ∀ i, ‖x i‖ ≤ 1)
    (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    ‖aeval (1 : σ → ℝ) x hx (f : Restricted K (1 : σ → ℝ))‖ ≤ 1 :=
  (norm_aeval_le hx _).trans (Subring.norm_le_one f)

/-- Two ring homomorphisms out of the unit ball of the Tate algebra that vanish on the open unit
ball and agree on the polynomials over the unit ball of `K` are equal. -/
private lemma ringHom_ext_of_openUnitBall {S : Type*} [Ring S]
    {ψ₁ ψ₂ : unitClosedBall (Restricted K (1 : σ → ℝ)) →+* S}
    (h₁ : ∀ f ∈ openUnitBallIdeal (Restricted K (1 : σ → ℝ)), ψ₁ f = 0)
    (h₂ : ∀ f ∈ openUnitBallIdeal (Restricted K (1 : σ → ℝ)), ψ₂ f = 0)
    (h : ∀ p, ψ₁ (ofUnitBallPolynomial p) = ψ₂ (ofUnitBallPolynomial p)) : ψ₁ = ψ₂ := by
  ext f
  obtain ⟨p, hp⟩ := exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal f
  have hf : f = ofUnitBallPolynomial p + (f - ofUnitBallPolynomial p) := by abel
  rw [hf, map_add, map_add, h p, h₁ _ hp, h₂ _ hp]

section Point

variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L] [CompleteSpace L]

/-- **Reduction commutes with evaluation at a point**: for a point `x` of the unit ball of a
complete extension field `L`, the residue class of `f(x)` is the value of the reduced polynomial
`f̃` at the reduced point `x̃`. Source: BGR 5.1.4 (the commutative diagram before Proposition 3);
Bosch 1.2/5. -/
theorem residue_aeval {x : σ → L} (hx : ∀ i, ‖x i‖ ≤ 1)
    (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    residue (unitClosedBall L)
        ⟨aeval (1 : σ → ℝ) x hx (f : Restricted K (1 : σ → ℝ)),
          mem_unitClosedBall.2 (norm_aeval_le_one hx f)⟩ =
      MvPolynomial.eval₂ (NormedField.residueFieldMap K L)
        (fun i ↦ residue (unitClosedBall L) ⟨x i, mem_unitClosedBall.2 (hx i)⟩) (reduction f) := by
  let ev : unitClosedBall (Restricted K (1 : σ → ℝ)) →+* unitClosedBall L :=
    ((aeval (1 : σ → ℝ) x hx).toRingHom.comp
      (unitClosedBall (Restricted K (1 : σ → ℝ))).subtype).codRestrict (unitClosedBall L)
        fun f ↦ mem_unitClosedBall.2 (norm_aeval_le_one hx f)
  let ψ₁ := (residue (unitClosedBall L)).comp ev
  let ψ₂ := (MvPolynomial.eval₂Hom (NormedField.residueFieldMap K L)
    fun i ↦ residue (unitClosedBall L) ⟨x i, mem_unitClosedBall.2 (hx i)⟩).comp reduction
  have hC (a : unitClosedBall K) : ψ₁ (ofUnitBallPolynomial (MvPolynomial.C a)) =
      ψ₂ (ofUnitBallPolynomial (MvPolynomial.C a)) := by
    have hev : ev (ofUnitBallPolynomial (MvPolynomial.C a)) =
        NormedField.unitClosedBallMap K L a :=
      Subtype.ext (show aeval (1 : σ → ℝ) x hx
          (↑(ofUnitBallPolynomial (σ := σ) (MvPolynomial.C a)) : Restricted K (1 : σ → ℝ)) =
            algebraMap K L a by
        rw [coe_ofUnitBallPolynomial, MvPolynomial.map_C, MvPolynomial.toRestricted_C,
          ← algebraMap_apply, AlgHom.commutes]
        rfl)
    simp only [ψ₁, ψ₂, RingHom.comp_apply, hev, reduction_ofUnitBallPolynomial,
      MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, NormedField.residueFieldMap,
      ResidueField.map_residue]
  have hX (i : σ) : ψ₁ (ofUnitBallPolynomial (MvPolynomial.X i)) =
      ψ₂ (ofUnitBallPolynomial (MvPolynomial.X i)) := by
    have hev : ev (ofUnitBallPolynomial (MvPolynomial.X i)) =
        ⟨x i, mem_unitClosedBall.2 (hx i)⟩ :=
      Subtype.ext (show aeval (1 : σ → ℝ) x hx
          (↑(ofUnitBallPolynomial (K := K) (σ := σ) (MvPolynomial.X i)) :
            Restricted K (1 : σ → ℝ)) = x i by
        rw [coe_ofUnitBallPolynomial, MvPolynomial.map_X, MvPolynomial.toRestricted_X, aeval_X])
    simp only [ψ₁, ψ₂, RingHom.comp_apply, hev, reduction_ofUnitBallPolynomial,
      MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
  have hp : ψ₁.comp ofUnitBallPolynomial = ψ₂.comp ofUnitBallPolynomial :=
    MvPolynomial.ringHom_ext hC hX
  have key : ψ₁ = ψ₂ := by
    refine ringHom_ext_of_openUnitBall (fun g hg ↦ ?_) (fun g hg ↦ ?_)
      fun p ↦ RingHom.congr_fun hp p
    · rw [RingHom.comp_apply, residue_eq_zero_iff, maximalIdeal_unitClosedBall,
        mem_openUnitBallIdeal]
      exact (norm_aeval_le hx _).trans_lt (mem_openUnitBallIdeal.1 hg)
    · rw [RingHom.comp_apply, (reduction_eq_zero_iff g).2 (mem_openUnitBallIdeal.1 hg),
        map_zero]
  exact RingHom.congr_fun key f

end Point

section Substitution

variable [CompleteSpace K] {τ : Type*}

/-- **Reduction commutes with substitution**: for a tuple `x` of the unit ball of a Tate algebra,
the reduction of `f(x)` is the reduced polynomial `f̃` evaluated at the reductions of the `x i`.
Source: BGR 5.1.3/7 (the induced `k̃`-algebra homomorphism `φ̃`), 5.2.4/1 ("`(σ(f))~ = σ̃(f̃)`"). -/
theorem reduction_aeval {x : σ → Restricted K (1 : τ → ℝ)} (hx : ∀ i, ‖x i‖ ≤ 1)
    (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reduction ⟨aeval (1 : σ → ℝ) x hx (f : Restricted K (1 : σ → ℝ)),
        mem_unitClosedBall.2 (norm_aeval_le_one hx f)⟩ =
      MvPolynomial.aeval (fun i ↦ reduction ⟨x i, mem_unitClosedBall.2 (hx i)⟩) (reduction f) := by
  let ev : unitClosedBall (Restricted K (1 : σ → ℝ)) →+*
      unitClosedBall (Restricted K (1 : τ → ℝ)) :=
    ((aeval (1 : σ → ℝ) x hx).toRingHom.comp
      (unitClosedBall (Restricted K (1 : σ → ℝ))).subtype).codRestrict _
        fun f ↦ mem_unitClosedBall.2 (norm_aeval_le_one hx f)
  let ψ₁ := reduction.comp ev
  let ψ₂ := (MvPolynomial.aeval fun i ↦ reduction ⟨x i, mem_unitClosedBall.2 (hx i)⟩).toRingHom.comp
    (reduction (K := K) (σ := σ))
  have hC (a : unitClosedBall K) : ψ₁ (ofUnitBallPolynomial (MvPolynomial.C a)) =
      ψ₂ (ofUnitBallPolynomial (MvPolynomial.C a)) := by
    have hmem : C (1 : τ → ℝ) (a : K) ∈ unitClosedBall (Restricted K (1 : τ → ℝ)) := by
      rw [mem_unitClosedBall, norm_C]
      exact Subring.norm_le_one a
    have hev : ev (ofUnitBallPolynomial (MvPolynomial.C a)) = ⟨C (1 : τ → ℝ) (a : K), hmem⟩ :=
      Subtype.ext (show aeval (1 : σ → ℝ) x hx
          (↑(ofUnitBallPolynomial (σ := σ) (MvPolynomial.C a)) : Restricted K (1 : σ → ℝ)) =
            C (1 : τ → ℝ) (a : K) by
        rw [coe_ofUnitBallPolynomial, MvPolynomial.map_C, MvPolynomial.toRestricted_C,
          ← algebraMap_apply, AlgHom.commutes, algebraMap_apply]
        rfl)
    simp only [ψ₁, ψ₂, RingHom.comp_apply, hev, reduction_C, reduction_ofUnitBallPolynomial,
      MvPolynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
  have hX (i : σ) : ψ₁ (ofUnitBallPolynomial (MvPolynomial.X i)) =
      ψ₂ (ofUnitBallPolynomial (MvPolynomial.X i)) := by
    have hev : ev (ofUnitBallPolynomial (MvPolynomial.X i)) =
        ⟨x i, mem_unitClosedBall.2 (hx i)⟩ :=
      Subtype.ext (show aeval (1 : σ → ℝ) x hx
          (↑(ofUnitBallPolynomial (K := K) (σ := σ) (MvPolynomial.X i)) :
            Restricted K (1 : σ → ℝ)) = x i by
        rw [coe_ofUnitBallPolynomial, MvPolynomial.map_X, MvPolynomial.toRestricted_X, aeval_X])
    simp only [ψ₁, ψ₂, RingHom.comp_apply, hev, reduction_ofUnitBallPolynomial,
      MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
  have hp : ψ₁.comp ofUnitBallPolynomial = ψ₂.comp ofUnitBallPolynomial :=
    MvPolynomial.ringHom_ext hC hX
  have key : ψ₁ = ψ₂ := by
    refine ringHom_ext_of_openUnitBall (fun g hg ↦ ?_) (fun g hg ↦ ?_)
      fun p ↦ RingHom.congr_fun hp p
    · rw [RingHom.comp_apply, reduction_eq_zero_iff]
      exact (norm_aeval_le hx _).trans_lt (mem_openUnitBallIdeal.1 hg)
    · rw [RingHom.comp_apply, (reduction_eq_zero_iff g).2 (mem_openUnitBallIdeal.1 hg),
        map_zero]
  exact RingHom.congr_fun key f

end Substitution

end MvPowerSeries.Restricted
