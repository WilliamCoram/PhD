/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.Weight.«06_Compact»
import PhD.Main.QMF.Slash.«05_Quaternionic»
import PhD.Main.QMF.«04_Finiteness»
import PhD.Main.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Overconvergent quaternionic modular forms `S^D_κ(U)`

The headline `QMF.Weight.Forms` instantiated at a quaternion algebra `D/F` and a finite place
`v`: `G = (D ⊗ 𝔸_F^∞)ˣ`, `Γ = Dˣ`, `θ = toMatrix F D v` (the `v`-component, through the
rigidification), `K = F_v = v.adicCompletion F`.  This is Buzzard's `S^D_κ(U)`
[*Eigenvarieties*, §10 p. 72: "define the space of `r`-overconvergent automorphic forms of
weight `κ` and level `U` to be `S^D_κ(U; r) := L(U, A_{κ,r})`"], with `U_ϖ = [UηU]` at
`η = (ϖ 0; 0 1)` [§12, Lemma 12.2].

## Main declarations

* `QMF.FormsQ` — `S^D_κ(U)` (an `abbrev` of `Forms`).
* `QMF.heckeUpiQ` — `U_ϖ` on `S^D_κ(U)`.
* `QMF.isCompactoid_heckeBlockOp_etaAdelic'` — **`U_ϖ` is compact** at every analytic weight
  (Buzzard Lemma 12.2): the general compactness theorem at `‖det (η)_v‖ = ‖ϖ‖`.
* `QMF.finite_image_etaAdelic'_of_isOpen_of_isCompact` — the Hecke finiteness hypothesis
  holds for compact open `U`.
-/

open scoped TensorProduct TensorProduct.RightActions Pointwise QMF TateFredholm
open IsDedekindDomain NumberField RightSlashAction AbstractHeckeOperatorSlash TateFredholm

namespace QMF

variable (F : Type*) [Field F] [NumberField F]

section General

variable (D : Type*) [Ring D] [Algebra F D]
variable (v : HeightOneSpectrum (RingOfIntegers F)) [RigidificationAt F D v]
variable {S : Submonoid (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))} {ρ : ℝ}
  {UK : Subgroup (v.adicCompletion F)ˣ}

/-- **Buzzard's `S^D_κ(U)`**: overconvergent automorphic forms of (analytic) weight `κ` and
level `U` for the quaternion algebra `D/F` at the place `v` [Buzzard, *Eigenvarieties*, §10
p. 72; Jacobs, Def 1.30] — the headline `QMF.Weight.Forms` at `Γ = Dˣ`, `θ = toMatrix F D v`. -/
noncomputable abbrev FormsQ (κ : AnalyticWeight UK S ρ) (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ Weight.levelMonoidOf (toMatrix F D v) S)
    (χ : S →* (v.adicCompletion F)ˣ := 1) :=
  Weight.Forms (globalUnits F D) (toMatrix F D v) κ U hU χ

/-- `η = (ϖ 0; 0 1)` lies in the wild-level monoid `Δ = θ⁻¹(Σ₀'(γ))` for `ϖ` integral and
nonzero (`etaAdelic'_mem_levelMonoid'`, read through `levelMonoidOf`). -/
theorem etaAdelic'_mem_levelMonoidOf_sigma0' (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1)
    (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) :
    etaAdelic' F D v ϖ hϖ0
      ∈ Weight.levelMonoidOf (toMatrix F D v) (Sigma0' (v.adicCompletion F) γ hγ) :=
  etaAdelic'_mem_levelMonoid' F D v γ hγ ϖ hϖ hϖ0

/-- **The `U_ϖ` operator on `S^D_κ(U)`** ([Buzzard, Lemma 12.2]: "`U_π` is the Hecke operator
`[UηU]` associated to the matrix `η`"; [Jacobs, Def 1.33]): the headline `heckeOperator` at
`η = etaAdelic' ϖ`. -/
noncomputable def heckeUpiQ (κ : AnalyticWeight UK S ρ) (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ Weight.levelMonoidOf (toMatrix F D v) S)
    (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0)
    (hη : etaAdelic' F D v ϖ hϖ0 ∈ Weight.levelMonoidOf (toMatrix F D v) S)
    (h : (((Quotient.mk'' : Dfx F D → RightCosets U) ''
          (({etaAdelic' F D v ϖ hϖ0} : Set (Dfx F D)) * (U : Set (Dfx F D)))) :
        Set (RightCosets U)).Finite) {χ : S →* (v.adicCompletion F)ˣ} :
    FormsQ F D v κ U hU χ →ₗ[v.adicCompletion F] FormsQ F D v κ U hU χ :=
  Weight.heckeOperator (toMatrix F D v) κ U hU hη h

/-- `‖det (η)_v‖ = ‖ϖ‖` for `η = (ϖ 0; 0 1)`: the determinant certificate of the compactness
theorem at `U_ϖ`. -/
theorem norm_det_toMatrix_etaAdelic' (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1)
    (hϖ0 : ϖ ≠ 0) :
    ‖(toMatrix F D v (etaAdelic' F D v ϖ hϖ0)).det‖ = ‖ϖ‖ := by
  rw [toMatrix_etaAdelic' F D v
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    (by decide) ϖ hϖ hϖ0, Sigma0'.eta, Matrix.det_fin_two_of]
  simp

/-- **`U_ϖ` is compact on `S^D_κ(U)` at every analytic weight** ([Buzzard, *Eigenvarieties*,
Lemma 12.2 p. 78]: "`U_π`, considered as an endomorphism of `S^D_κ(U;r)`, is also
norm-decreasing and compact"; [Jacobs, Lemma 2.7]): the block operator of `U_ϖ` in the model
is compactoid whenever `ρ ≤ ‖ϖ‖ < 1` — the general `isCompactoid_heckeBlockOp` at the
determinant certificate `‖det (η)_v‖ = ‖ϖ‖`. -/
theorem isCompactoid_heckeBlockOp_etaAdelic' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Type*} [Fintype T] (κ : AnalyticWeight UK S ρ) (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ Weight.levelMonoidOf (toMatrix F D v) S)
    (χ : S →* (v.adicCompletion F)ˣ)
    (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) (hρ : ρ ≤ ‖ϖ‖)
    (hϖ1 : ‖ϖ‖ < 1)
    {vRep : T → Dfx F D} (hvΔ : ∀ t, vRep t ∈ Weight.levelMonoidOf (toMatrix F D v) S)
    (hv : Set.BijOn (Quotient.mk'' : Dfx F D → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : Dfx F D → RightCosets U) ''
        (({etaAdelic' F D v ϖ hϖ0} : Set (Dfx F D)) * (U : Set (Dfx F D)))) :
        Set (RightCosets U)))
    (idx : ι → T → ι) (u : ι → T → U) :
    IsCompactoid (Weight.heckeBlockOp (toMatrix F D v) κ U hU χ vRep hvΔ idx u) :=
  Weight.isCompactoid_heckeBlockOp (toMatrix F D v) κ U hU χ hρ hϖ1
    (norm_det_toMatrix_etaAdelic' F D v ϖ hϖ hϖ0).le hvΔ hv idx u

end General

section Topology

variable (D : Type*) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
variable (v : HeightOneSpectrum (RingOfIntegers F)) [RigidificationAt F D v]

/-- At a compact open level the Hecke finiteness hypothesis of `heckeUpiQ` is automatic
(`finite_image_doubleCoset_of_isOpen_of_isCompact`; [Buzzard, §9 p. 69]: "decompose
`UηU = ∐ᵢ U xᵢ` (a finite union)"). -/
theorem finite_image_etaAdelic'_of_isOpen_of_isCompact (U : Subgroup (Dfx F D))
    (hUo : IsOpen (U : Set (Dfx F D))) (hUc : IsCompact (U : Set (Dfx F D)))
    (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0) :
    (((Quotient.mk'' : Dfx F D → RightCosets U) ''
        (({etaAdelic' F D v ϖ hϖ0} : Set (Dfx F D)) * (U : Set (Dfx F D)))) :
      Set (RightCosets U)).Finite :=
  finite_image_doubleCoset_of_isOpen_of_isCompact hUo hUc _

variable [Algebra.IsCentral F D]

/-- **Fujisaki's finiteness as a `Fintype` on the class set** (`QMF.finite_classSet`): the index
type of the block model `S^D_κ(U) ↪ ⊕_{Dˣ\D_f^×/U} A_κ` ([Buzzard, *Eigenvarieties*, §10 p. 73]:
"if `f ∈ S^D_κ(U;r)` then `f` is determined by `f(τ_λ)` for `λ = 1, …, µ`").  With this instance
in scope, `QMF.Weight.evalAtReps_out_injective` is that statement, and
`QMF.Weight.bijective_evalAtReps_out` upgrades it to an isomorphism at a neat level. -/
noncomputable def classSetFintype (U : Subgroup (Dfx F D)) (hUo : IsOpen (U : Set (Dfx F D))) :
    Fintype (DoubleCoset.Quotient ((globalUnits F D : Subgroup (Dfx F D)) : Set (Dfx F D))
      (U : Set (Dfx F D))) :=
  @Fintype.ofFinite _ (finite_classSet F D hUo)

end Topology

end QMF
