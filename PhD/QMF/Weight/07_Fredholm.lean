/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Weight.«06_Compact»

/-!
# The Fredholm determinant of a Hecke operator on `S_κ(U)`

At a neat level (`bijective_evalAtReps`), `S_κ(U) ≅ ⊕_λ A_κ` and the Hecke operator `[UηU]`
is the block operator `heckeBlockOp` of the certificate data (`evalAtReps_heckeOperator`).
For `η` of `U_ϖ` type the block operator is compactoid (`isCompactoid_heckeBlockOp`), so it
has a Fredholm determinant `det(1 − T·[UηU])` — [Jacobs, p. 21: "we obtain the matrix of
`U_p` with respect to the topological basis"; Buzzard, *Eigenvarieties*, §13] — and Serre's
Riesz theory reads its zeros as the reciprocal eigenvalues of `[UηU]` on `S_κ(U)`.

## Main declarations

* `QMF.Weight.heckeCharPowerSeries` — `det(1 − T·[UηU])`, computed in the block model at
  certificates.
* `QMF.Weight.evalT_heckeCharPowerSeries_eq_zero_iff` — **eigenforms ⇔ reciprocal roots**:
  `a` is a zero of `det(1 − T·[UηU])` iff `a⁻¹` is an eigenvalue of `[UηU]` on `S_κ(U)`.
* `QMF.Weight.transitionOp`, `evalAtReps_eq_transitionOp`,
  `heckeCharPowerSeries_eq_of_reps` — the determinant does not depend on the choice of
  representatives/certificates ([Buzzard, Cor 2.6]: basis independence of `det(1 − Xφ)`).
-/

open TateFredholm
open scoped TateFredholm QMF Pointwise

namespace QMF.Weight

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) K)
variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ} {UK : Subgroup Kˣ}

section Determinant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (κ : AnalyticWeight UK S ρ) (U : Subgroup G) (hU : (U : Set G) ⊆ levelMonoidOf θ S)
  (χ : S →* Kˣ)
variable {T : Type*} [Fintype T]

/-- **The Fredholm determinant `det(1 − T·[UηU])`** of the Hecke operator on `S_κ(U)`,
computed in the block model at certificate data ([Jacobs, p. 21]: the matrix of `U_p` with
respect to the topological basis of `⊕ᵢ A`; [Buzzard, §13]). -/
noncomputable def heckeCharPowerSeries (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (idx : ι → T → ι) (u : ι → T → U) : PowerSeries K :=
  charPowerSeries (heckeBlockOp θ κ U hU χ vRep hvΔ idx u)

/-- **Eigenforms are the reciprocal roots of the Fredholm determinant** ([Serre1962, §7,
Props. 11–12] through the model isomorphism `bijective_evalAtReps` and the transport
`evalAtReps_heckeOperator`): at a neat level and for `η` of `U_ϖ` type, `a ≠ 0` is a zero of
`det(1 − T·[UηU])` iff `a⁻¹` is an eigenvalue of `[UηU]` on `S_κ(U)`. -/
theorem evalT_heckeCharPowerSeries_eq_zero_iff (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c i))
      (a : c(ℕ, K)), χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ a = a)
    {η : G} (hη : η ∈ levelMonoidOf θ S)
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
          (({η} : Set G) * (U : Set G))) :
        Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → T → ι) (d : ι → T → G) (hd : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) (hdet : ‖(θ η).det‖ ≤ σ) {a : K} (ha0 : a ≠ 0) :
    PowerSeries.evalT a (heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u) = 0 ↔
      ∃ φ : Forms Γ θ κ U hU χ, φ ≠ 0 ∧ heckeOperator θ κ U hU hη h φ = a⁻¹ • φ := by
  have hcomp := isCompactoid_heckeBlockOp θ κ U hU χ hρσ hσ hdet hvΔ hv idx u
  have hbij := bijective_evalAtReps θ κ U hU χ c hc hstab
  have htr : ∀ φ : Forms Γ θ κ U hU χ,
      evalAtReps θ κ U hU χ c (heckeOperator θ κ U hU hη h φ)
        = heckeBlockOp θ κ U hU χ vRep hvΔ idx u (evalAtReps θ κ U hU χ c φ) :=
    fun φ => evalAtReps_heckeOperator θ κ U hU χ hη h c vRep hvΔ hv hvinj idx d hd u hfact φ
  rw [heckeCharPowerSeries, evalT_charPowerSeries_eq_zero_iff _ hcomp ha0]
  constructor
  · rintro ⟨x, hx0, hx⟩
    obtain ⟨φ, rfl⟩ := hbij.2 x
    refine ⟨φ, fun h0 => hx0 (by rw [h0, map_zero]), hbij.1 ?_⟩
    rw [htr, hx, map_smul]
  · rintro ⟨φ, hφ0, hφ⟩
    refine ⟨evalAtReps θ κ U hU χ c φ, fun h0 => hφ0 (hbij.1 (by rw [h0, map_zero])), ?_⟩
    rw [← htr, hφ, map_smul]

/-- **Serre's Riesz decomposition on `S_κ(U)`** ([Serre1962, §7 Prop. 12]; [Buzzard,
*Eigenvarieties*, Prop 3.2 p. 23]: "There is a unique decomposition `M = N ⊕ F` into closed
`φ`-stable submodules such that `1 − aφ` is invertible on `F` and `(1 − aφ)^h = 0` on `N` …
`N` is projective of rank `h`"), transported from the block model
(`TateFredholm.exists_riesz_decomposition`) along the neat-level model isomorphism: at a zero
`a` of `det(1 − T·[UηU])` over a discretely valued `K`, `S_κ(U) = N ⊕ F` with `N` the
`h`-dimensional generalised `a⁻¹`-eigenspace of `[UηU]` and `1 − a·[UηU]` bijective on `F`.
(Bundled as in the source: a shared-witness existential in `h`, `N`, `F`.) -/
theorem exists_riesz_decomposition_forms
    (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c i))
      (a : c(ℕ, K)), χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ a = a)
    {η : G} (hη : η ∈ levelMonoidOf θ S)
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
          (({η} : Set G) * (U : Set G))) :
        Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → T → ι) (d : ι → T → G) (hd' : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) (hdet : ‖(θ η).det‖ ≤ σ) {a : K}
    (ha : PowerSeries.evalT a (heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u) = 0) :
    ∃ (n : ℕ) (N F : Submodule K (Forms Γ θ κ U hU χ)), 1 ≤ n ∧ IsCompl N F ∧
      (∀ φ ∈ N, heckeOperator θ κ U hU hη h φ ∈ N) ∧
      (∀ φ ∈ F, heckeOperator θ κ U hU hη h φ ∈ F) ∧
      (∀ φ ∈ N, ((1 - a • heckeOperator θ κ U hU hη h) ^ n) φ = 0) ∧
      (∀ ψ ∈ F, ∃ φ ∈ F, (1 - a • heckeOperator θ κ U hU hη h) φ = ψ) ∧
      (∀ φ ∈ F, (1 - a • heckeOperator θ κ U hU hη h) φ = 0 → φ = 0) ∧
      Module.finrank K N = n := by
  classical
  set T := heckeOperator θ κ U hU hη h with hT
  set B := heckeBlockOp θ κ U hU χ vRep hvΔ idx u with hB
  have hcomp : IsCompactoid B := isCompactoid_heckeBlockOp θ κ U hU χ hρσ hσ hdet hvΔ hv idx u
  set E := formsModelEquiv θ κ U hU χ c hc hstab with hE
  have htr : ∀ φ, E (T φ) = B (E φ) := fun φ =>
    evalAtReps_heckeOperator θ κ U hU χ hη h c vRep hvΔ hv hvinj idx d hd' u hfact φ
  have hstep : ∀ φ, E ((1 - a • T) φ) = (1 - a • B) (E φ) := fun φ => by
    show E (φ - a • T φ) = E φ - a • B (E φ)
    rw [map_sub, map_smul, htr]
  have hpow : ∀ (k : ℕ) (φ : Forms Γ θ κ U hU χ),
      E (((1 - a • T) ^ k) φ) = ((1 - a • B) ^ k) (E φ) := by
    intro k
    induction k with
    | zero => intro φ; simp
    | succ k ih =>
      intro φ
      show E (((1 - a • T) ^ k) ((1 - a • T) φ)) = ((1 - a • B) ^ k) ((1 - a • B) (E φ))
      rw [ih, hstep]
  have hsymm : ∀ x : c(ι × ℕ, K),
      E ((E.symm : c(ι × ℕ, K) →ₗ[K] Forms Γ θ κ U hU χ) x) = x := fun x => E.apply_symm_apply x
  obtain ⟨n, N', F', hn, hcompl, hN', hF', hnil, hsurj, hinj, hrank⟩ :=
    exists_riesz_decomposition hd hcomp ha
  refine ⟨n, N'.map (E.symm : c(ι × ℕ, K) →ₗ[K] Forms Γ θ κ U hU χ),
    F'.map (E.symm : c(ι × ℕ, K) →ₗ[K] Forms Γ θ κ U hU χ), hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Submodule.orderIsoMapComap (E.symm : c(ι × ℕ, K) ≃ₗ[K] Forms Γ θ κ U hU χ)).isCompl
      hcompl.isCompl
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨B x, hN' x hx, E.injective (by rw [hsymm, htr, hsymm])⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨B x, hF' x hx, E.injective (by rw [hsymm, htr, hsymm])⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine E.injective ?_
    rw [hpow, hsymm, hnil x hx, map_zero]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hsurj y hy
    refine ⟨E.symm x, ⟨x, hx, rfl⟩, E.injective ?_⟩
    rw [hstep, E.apply_symm_apply, hsymm]
    exact hxy
  · rintro _ ⟨x, hx, rfl⟩ h0
    have hx0 : (1 - a • B) x = 0 := by
      have := congrArg E h0
      rwa [hstep, hsymm, map_zero] at this
    rw [hinj x hx hx0, map_zero]
  · rw [← hrank]
    exact (E.symm.submoduleMap N').finrank_eq.symm

end Determinant

section Independence

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
variable (κ : AnalyticWeight UK S ρ) (U : Subgroup G) (hU : (U : Set G) ⊆ levelMonoidOf θ S)
  (χ : S →* Kˣ)

/-- **The transition operator** between two families of representatives: from certificates
`c' i' = d i' · c (idx i') · u i'` (`d i' ∈ Γ`, `u i' ∈ U`), the operator
`c(ι × ℕ, K) → c(ι' × ℕ, K)` whose `i'`-th block reads the `idx i'`-th block and slashes it by
`u i'` — so that `evalAtReps c' = transitionOp ∘ evalAtReps c` (`evalAtReps_eq_transitionOp`). -/
noncomputable def transitionOp (idx : ι' → ι) (u : ι' → U) :
    c(ι × ℕ, K) →L[K] c(ι' × ℕ, K) :=
  ∑ i' : ι', (cSpace.blockIncl i').comp
    ((((χ (levelMonoidOfToS θ S ⟨(u i' : G), hU (u i').2⟩) : Kˣ) : K)
        • κ.kappaSlash (levelMonoidOfToS θ S ⟨(u i' : G), hU (u i').2⟩)).comp
      (cSpace.blockProj (idx i')))

/-- Evaluation at a second family of representatives factors through the transition
operator: `φ(c' i') = φ(d · c (idx i') · u) = φ(c (idx i')) ∣ u`. -/
theorem evalAtReps_eq_transitionOp (c : ι → G) (c' : ι' → G) (idx : ι' → ι) (d : ι' → G)
    (hd : ∀ i', d i' ∈ Γ) (u : ι' → U)
    (hfact : ∀ i', c' i' = d i' * c (idx i') * (u i' : G)) (φ : Forms Γ θ κ U hU χ) :
    evalAtReps θ κ U hU χ c' φ = transitionOp θ κ U hU χ idx u (evalAtReps θ κ U hU χ c φ) := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨i', n⟩ := x
  have hval : (φ : AutomorphicFunction G Γ c(ℕ, K)) (c' i')
      = ((χ (levelMonoidOfToS θ S ⟨(u i' : G), hU (u i').2⟩) : Kˣ) : K)
          • κ.kappaSlash (levelMonoidOfToS θ S ⟨(u i' : G), hU (u i').2⟩)
            ((φ : AutomorphicFunction G Γ c(ℕ, K)) (c (idx i'))) := by
    rw [hfact i', mul_assoc, (φ : AutomorphicFunction G Γ c(ℕ, K)).left_invt' (hd i'),
      (mem_forms_iff θ κ hU χ).mp φ.2 (u i') (c (idx i'))]
    rfl
  have hL := congrArg (fun g : c(ℕ, K) => g n) (blockProj_evalAtReps θ κ U hU χ c' φ i')
  simp only [cSpace.blockProj_apply] at hL
  rw [hL, hval, transitionOp]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    smul_apply, cSpace.sum_apply, cSpace.blockIncl_apply,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, blockProj_evalAtReps]

variable {T T' : Type*} [Fintype T] [Fintype T']

/-- **Independence of the Fredholm determinant from the representatives and certificates**
([Buzzard, *Eigenvarieties*, Cor 2.6 p. 14]: "the definitions of `det(1 − Xφ)` with respect
to these bases coincide"): at two neat families of representatives `c`, `c'` with certificate
data for the same `η`, the two block operators are conjugate by the transition operator
(a continuous linear equivalence), hence have the same characteristic power series
(`TateFredholm.charPowerSeries_conj`). -/
theorem heckeCharPowerSeries_eq_of_reps (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c i))
      (a : c(ℕ, K)), χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ a = a)
    (c' : ι' → G)
    (hc' : Function.Bijective
      (fun i' => (Quotient.mk'' (c' i') : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab' : ∀ i' (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c' i'))
      (a : c(ℕ, K)), χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ a = a)
    {η : G} (hη : η ∈ levelMonoidOf θ S)
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
          (({η} : Set G) * (U : Set G))) :
        Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hv : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep)
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → T → ι) (d : ι → T → G) (hd : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    (vRep' : T' → G) (hvΔ' : ∀ t, vRep' t ∈ levelMonoidOf θ S)
    (hv' : Set.BijOn (Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U)
      (Set.range vRep')
      (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)))
    (hvinj' : Function.Injective vRep')
    (idx' : ι' → T' → ι') (d' : ι' → T' → G) (hd' : ∀ i t, d' i t ∈ Γ) (u' : ι' → T' → U)
    (hfact' : ∀ i t, c' i * (vRep' t)⁻¹ = d' i t * c' (idx' i t) * (u' i t : G))
    (hcomp : IsCompactoid (heckeBlockOp θ κ U hU χ vRep hvΔ idx u)) :
    heckeCharPowerSeries θ κ U hU χ vRep' hvΔ' idx' u'
      = heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u := by
  classical
  -- transition certificates in both directions, from completeness of the two families
  have hrel : ∀ i' : ι', ∃ (i : ι) (a : G) (_ : a ∈ Γ) (b : U), c' i' = a * c i * (b : G) := by
    intro i'
    obtain ⟨i, hi⟩ := hc.2 (Quotient.mk'' (c' i'))
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi)
    exact ⟨i, a, ha, ⟨b, hb⟩, hab⟩
  have hrel' : ∀ i : ι, ∃ (i' : ι') (a : G) (_ : a ∈ Γ) (b : U), c i = a * c' i' * (b : G) := by
    intro i
    obtain ⟨i', hi'⟩ := hc'.2 (Quotient.mk'' (c i))
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi')
    exact ⟨i', a, ha, ⟨b, hb⟩, hab⟩
  choose idx₁ d₁ hd₁ u₁ hfact₁ using hrel
  choose idx₂ d₂ hd₂ u₂ hfact₂ using hrel'
  set T₁ := transitionOp θ κ U hU χ idx₁ u₁ with hT₁
  set T₂ := transitionOp θ κ U hU χ idx₂ u₂ with hT₂
  have h₁ : ∀ φ : Forms Γ θ κ U hU χ,
      evalAtReps θ κ U hU χ c' φ = T₁ (evalAtReps θ κ U hU χ c φ) :=
    fun φ => evalAtReps_eq_transitionOp θ κ U hU χ c c' idx₁ d₁ hd₁ u₁ hfact₁ φ
  have h₂ : ∀ φ : Forms Γ θ κ U hU χ,
      evalAtReps θ κ U hU χ c φ = T₂ (evalAtReps θ κ U hU χ c' φ) :=
    fun φ => evalAtReps_eq_transitionOp θ κ U hU χ c' c idx₂ d₂ hd₂ u₂ hfact₂ φ
  have hbij := bijective_evalAtReps θ κ U hU χ c hc hstab
  have hbij' := bijective_evalAtReps θ κ U hU χ c' hc' hstab'
  have hT₂T₁ : ∀ x, T₂ (T₁ x) = x := fun x => by
    obtain ⟨φ, rfl⟩ := hbij.2 x
    rw [← h₁, ← h₂]
  have hT₁T₂ : ∀ y, T₁ (T₂ y) = y := fun y => by
    obtain ⟨φ, rfl⟩ := hbij'.2 y
    rw [← h₂, ← h₁]
  -- the transition operator is a continuous linear equivalence
  let E : c(ι × ℕ, K) ≃L[K] c(ι' × ℕ, K) :=
    { toLinearEquiv := LinearEquiv.ofLinear (T₁ : c(ι × ℕ, K) →ₗ[K] c(ι' × ℕ, K))
        (T₂ : c(ι' × ℕ, K) →ₗ[K] c(ι × ℕ, K)) (LinearMap.ext hT₁T₂) (LinearMap.ext hT₂T₁)
      continuous_toFun := T₁.continuous
      continuous_invFun := T₂.continuous }
  -- the two block operators are conjugate by it
  have hconj : heckeBlockOp θ κ U hU χ vRep' hvΔ' idx' u'
      = ((E : c(ι × ℕ, K) →L[K] c(ι' × ℕ, K)).comp (heckeBlockOp θ κ U hU χ vRep hvΔ idx u)).comp
          (E.symm : c(ι' × ℕ, K) →L[K] c(ι × ℕ, K)) := by
    refine ContinuousLinearMap.ext fun y => ?_
    obtain ⟨φ, rfl⟩ := hbij'.2 y
    show heckeBlockOp θ κ U hU χ vRep' hvΔ' idx' u' (evalAtReps θ κ U hU χ c' φ)
      = T₁ (heckeBlockOp θ κ U hU χ vRep hvΔ idx u (T₂ (evalAtReps θ κ U hU χ c' φ)))
    rw [← evalAtReps_heckeOperator θ κ U hU χ hη h c' vRep' hvΔ' hv' hvinj' idx' d' hd' u' hfact' φ,
      ← h₂, ← evalAtReps_heckeOperator θ κ U hU χ hη h c vRep hvΔ hv hvinj idx d hd u hfact φ,
      ← h₁]
  rw [heckeCharPowerSeries, heckeCharPowerSeries, hconj]
  exact charPowerSeries_conj E _ hcomp

end Independence

end QMF.Weight
