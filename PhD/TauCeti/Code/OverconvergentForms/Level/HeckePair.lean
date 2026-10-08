/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Level.Standard
import PhD.TauCeti.Code.OverconvergentForms.Level.ClassSet
import Mathlib.NumberTheory.HeckeRing.Defs

/-!
# Double cosets, the Hecke pair `(Δ_t, U)` and the element `η_𝔭`

For a compact open subgroup `U` of a topological group, every double coset `U η U` is compact and
open, a finite union of right cosets and of left cosets, and the commensurator of `U` is the whole
group; hence `(Δ, U)` is a Hecke triple for every submonoid `Δ ⊇ U`. In `D_f^×`: the element
`η_v = ι_v(diag(ϖ, 1))`, the wild-level monoid `Δ_t = θ⁻¹(M_t)`, the decomposition
`U η_v U = ∐_α U · ι_v(x_α)` lifted from the local one, the determinants of the elements of
`U η_v U`, and the diamond elements `ι_v(diag(1, d))`.

[Buz07, §9, p. 69]: "If `η ∈ D_f^×` and `η_p ∈ M_t` then one can define an endomorphism `[UηU]` of
`L(U, A)` as follows: decompose `UηU = ∐_i U x_i` (a finite union)." [Buz07, §9, p. 68]: "we say
that a compact open subgroup `U ⊂ D_f^×` has wild level `≥ π^t` if the projection `U → D_p^×` is
contained within `M_t`."

## Main definitions

* `AdelicAlgebra.etaAdelic`, `AdelicAlgebra.etaAdelicRep`, `AdelicAlgebra.diamond`.
* `AdelicAlgebra.wildMonoid`, `AdelicAlgebra.wildMonoidOf`, `AdelicAlgebra.HasWildLevel`.
* `AdelicAlgebra.heckeElement`: the class of `η ∈ Δ` in `HeckeRing Δ U ℤ`.

## Main results

* `Subgroup.isCompact_doubleCoset`, `Subgroup.isOpen_doubleCoset`,
  `Subgroup.ncard_rightCosets_doubleCoset` (`[U : U ∩ η⁻¹ U η]` right cosets),
  `Subgroup.finite_rightCosets_doubleCoset`, `Subgroup.finite_leftCosets_doubleCoset`.
* `Subgroup.commensurator_eq_top_of_isCompact_of_isOpen`,
  `Subgroup.isHeckeTriple_of_isCompact_of_isOpen`.
* `AdelicAlgebra.toMatrix_etaAdelic`, `AdelicAlgebra.toMatrix_etaAdelicRep`,
  `AdelicAlgebra.det_toMatrix_etaAdelicRep`, `AdelicAlgebra.etaAdelic_mem_wildMonoid`,
  `AdelicAlgebra.etaAdelic_mem_wildMonoid_of_ne`,
  `AdelicAlgebra.unitAt_smul_one_mem_wildMonoid_iff`, `AdelicAlgebra.diamond_commute_etaAdelic`,
  `AdelicAlgebra.diamond_mem_wildMonoid`.
* `AdelicAlgebra.etaAdelic_mem_wildMonoidOf`, `AdelicAlgebra.hasWildLevel_U0Level`,
  `AdelicAlgebra.isHeckeTriple_wildMonoidOf`: the Hecke pair `(Δ_t, U)`.
* `AdelicAlgebra.existsUnique_etaAdelicRep`, `AdelicAlgebra.bijOn_etaAdelicRep`,
  `AdelicAlgebra.unitAt_iwahoriPrincipal_le_U1Level`.
* `AdelicAlgebra.valued_det_toMatrix_of_mem_doubleCoset` and its companion away from `v`,
  `AdelicAlgebra.valued_det_toMatrix_of_mem_doubleCoset_of_ne`.
* `AdelicAlgebra.heckeElement_eq_of_mem_doubleCoset`.

Roadmap: §0.3.4, §0.4.3, §0.4.4, §0.4.5. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/HeckePair.lean`.
-/

open scoped TensorProduct Classical Pointwise WithZero
open IsDedekindDomain NumberField LocalLevel

noncomputable section

section TopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **A double coset of a compact subgroup is compact.** -/
theorem Subgroup.isCompact_doubleCoset {U : Subgroup G} (hU : IsCompact (U : Set G)) (η : G) :
    IsCompact ((U : Set G) * {η} * (U : Set G)) :=
  (hU.mul isCompact_singleton).mul hU

/-- **A double coset of an open subgroup is open.** -/
theorem Subgroup.isOpen_doubleCoset {U : Subgroup G} (hU : IsOpen (U : Set G)) (η : G) :
    IsOpen ((U : Set G) * {η} * (U : Set G)) :=
  hU.mul_left

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem mem_conj_inv_smul_iff {U : Subgroup G} {η x : G} :
    x ∈ MulAut.conj η⁻¹ • U ↔ η * x * η⁻¹ ∈ U := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv MulAut.conj, inv_inv,
    MulAut.smul_def, MulAut.conj_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- **The number of right cosets `U x` in `U η U` is `[U : U ∩ η⁻¹ U η]`.** -/
theorem Subgroup.ncard_rightCosets_doubleCoset (U : Subgroup G) (η : G) :
    ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel U)) ''
      (({η} : Set G) * (U : Set G))).ncard = (MulAut.conj η⁻¹ • U).relIndex U := by
  have key : ∀ a b : U, b * a⁻¹ ∈ (MulAut.conj η⁻¹ • U).subgroupOf U ↔
      η * (b : G) * (η * a)⁻¹ ∈ U := fun a b => by
    rw [Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff, Subgroup.coe_mul, Subgroup.coe_inv,
      show η * ((b : G) * (a : G)⁻¹) * η⁻¹ = η * b * (η * a)⁻¹ by group]
  -- `W u ↦ U η u` is a bijection from `W \ U` onto the right cosets in `U η U`
  let f : Quotient (QuotientGroup.rightRel ((MulAut.conj η⁻¹ • U).subgroupOf U)) →
      Quotient (QuotientGroup.rightRel U) :=
    Quotient.map' (fun u : U => η * u) fun a b h =>
      QuotientGroup.rightRel_apply.mpr ((key a b).mp (QuotientGroup.rightRel_apply.mp h))
  have hf : Function.Injective f := by
    rintro ⟨a⟩ ⟨b⟩ h
    exact Quotient.sound' (QuotientGroup.rightRel_apply.mpr ((key a b).mpr
      (QuotientGroup.rightRel_apply.mp (Quotient.exact' h))))
  have hrange : Set.range f =
      (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel U)) '' ({η} * (U : Set G)) := by
    rw [Set.singleton_mul, Set.image_image]
    ext q
    constructor
    · rintro ⟨⟨a⟩, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Quotient.mk'' ⟨u, hu⟩, rfl⟩
  rw [← hrange, Set.ncard_range_of_injective hf]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)

/-- **`U η U` is a finite union of right cosets `U x`**, for `U` compact open. -/
theorem Subgroup.finite_rightCosets_doubleCoset {U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hUo : IsOpen (U : Set G)) (η : G) :
    ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel U)) ''
      (({η} : Set G) * (U : Set G))).Finite := by
  refine Set.finite_of_ncard_ne_zero ?_
  rw [Subgroup.ncard_rightCosets_doubleCoset]
  refine Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen hUc ?_
  have h : ((MulAut.conj η⁻¹ • U : Subgroup G) : Set G) = (fun x => η * x * η⁻¹) ⁻¹' U :=
    Set.ext fun _ => mem_conj_inv_smul_iff
  rw [h]
  exact hUo.preimage (IsTopologicalGroup.continuous_conj η)

/-- **`U η U` is a finite union of left cosets `x U`**, for `U` compact open. -/
theorem Subgroup.finite_leftCosets_doubleCoset {U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hUo : IsOpen (U : Set G)) (η : G) :
    ((QuotientGroup.mk : G → G ⧸ U) '' ((U : Set G) * ({η} : Set G))).Finite := by
  haveI := QuotientGroup.discreteTopology hUo
  exact ((hUc.mul isCompact_singleton).image QuotientGroup.continuous_mk).finite_of_discrete

/-- **The commensurator of a compact open subgroup is the whole group.** -/
theorem Subgroup.commensurator_eq_top_of_isCompact_of_isOpen {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    Subgroup.Commensurable.commensurator U = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  refine Subgroup.commensurable_of_isCompact_of_isOpen ?_ ?_ hUc hUo
  · rw [Subgroup.coe_pointwise_smul]
    exact hUc.smul _
  · rw [Subgroup.coe_pointwise_smul]
    exact hUo.smul _

/-- **`(Δ, U)` is a Hecke triple** for every compact open `U` and every submonoid `Δ ⊇ U`. -/
theorem Subgroup.isHeckeTriple_of_isCompact_of_isOpen {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) {Δ : Submonoid G}
    (hle : U.toSubmonoid ≤ Δ) : IsHeckeTriple Δ U U :=
  IsHeckeTriple.of_diagonal hle fun g _ => by
    rw [Subgroup.mem_toSubmonoid, Subgroup.commensurator_eq_top_of_isCompact_of_isOpen hUc hUo]
    exact Subgroup.mem_top g

end TopologicalGroup

namespace AdelicAlgebra

open scoped RightAlgebra

variable {F : Type*} [Field F] [NumberField F] {D : Type*} [Ring D] [Algebra F D]

section Wild

variable (F D) (v : HeightOneSpectrum (𝓞 F)) [RigidificationAt F D v]

/-- **The wild-level monoid at `v`**: `Δ = θ_v⁻¹(M(γ))`. -/
def wildMonoid (γ : ℤᵐ⁰) (hγ : γ < 1) : Submonoid (Dfx F D) :=
  (monoidM (v.adicCompletion F) γ hγ).comap (toMatrix F D v)

/-- **`η_v = ι_v(diag(ϖ, 1))`**, the unit with `v`-component `diag(ϖ, 1)` and trivial components
elsewhere. -/
def etaAdelic (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) : Dfx F D :=
  unitAt F D v (etaGL ϖ hϖ)

/-- The representatives `ι_v(x_α)`, `x_α = ((ϖ 0), (α ϖ^t 1))`. -/
def etaAdelicRep (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) (t : ℕ) (α : v.adicCompletion F) :
    Dfx F D :=
  unitAt F D v (etaRep ϖ hϖ t α)

/-- **The diamond element** `δ_d = ι_v(diag(1, d))`. -/
def diamond (d : (v.adicCompletion F)ˣ) : Dfx F D :=
  unitAt F D v (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, (d : _)])
    (by simp [Matrix.det_diagonal, Fin.prod_univ_two]))

variable {F D v}

private theorem coe_mkOfDetNeZero {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (h : A.det ≠ 0) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero A h : Matrix (Fin 2) (Fin 2) K) = A :=
  rfl

/-- Membership in `Δ` is a condition on the `v`-component. -/
theorem mem_wildMonoid_iff {γ : ℤᵐ⁰} {hγ : γ < 1} {g : Dfx F D} :
    g ∈ wildMonoid F D v γ hγ ↔ toMatrix F D v g ∈ monoidM (v.adicCompletion F) γ hγ :=
  Iff.rfl

/-- `θ_v(η_v) = diag(ϖ, 1)`. -/
theorem toMatrix_etaAdelic (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) :
    toMatrix F D v (etaAdelic F D v ϖ hϖ) = Matrix.diagonal ![ϖ, 1] := by
  rw [etaAdelic, ← coe_toGL, toGL_unitAt]
  rfl

/-- `θ_v(ι_v(x_α)) = ((ϖ 0), (α ϖ^t 1))`. -/
theorem toMatrix_etaAdelicRep (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) (t : ℕ)
    (α : v.adicCompletion F) :
    toMatrix F D v (etaAdelicRep F D v ϖ hϖ t α) = !![ϖ, 0; α * ϖ ^ t, 1] := by
  rw [etaAdelicRep, ← coe_toGL, toGL_unitAt, coe_etaRep]

/-- **`det θ_v(ι_v(x_α)) = ϖ`.** -/
theorem det_toMatrix_etaAdelicRep (ϖ : v.adicCompletion F) (hϖ : ϖ ≠ 0) (t : ℕ)
    (α : v.adicCompletion F) :
    (toMatrix F D v (etaAdelicRep F D v ϖ hϖ t α)).det = ϖ := by
  rw [etaAdelicRep, ← coe_toGL, toGL_unitAt, det_etaRep]

/-- **`η_v ∈ Δ`.** -/
theorem etaAdelic_mem_wildMonoid {γ : ℤᵐ⁰} (hγ : γ < 1) {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0)
    (hϖ1 : Valued.v ϖ ≤ 1) : etaAdelic F D v ϖ hϖ ∈ wildMonoid F D v γ hγ := by
  rw [mem_wildMonoid_iff, etaAdelic, ← coe_toGL, toGL_unitAt]
  exact coe_etaGL_mem_monoidM hγ hϖ hϖ1

/-- `η_v` has trivial components away from `v`, so it lies in every wild-level monoid there. -/
theorem etaAdelic_mem_wildMonoid_of_ne {w : HeightOneSpectrum (𝓞 F)} [RigidificationAt F D w]
    (hw : w ≠ v) {γ : ℤᵐ⁰} (hγ : γ < 1) (ϖ : w.adicCompletion F) (hϖ : ϖ ≠ 0) :
    etaAdelic F D w ϖ hϖ ∈ wildMonoid F D v γ hγ := by
  rw [mem_wildMonoid_iff, etaAdelic, ← coe_toGL, toGL_unitAt_of_ne w hw.symm, Units.val_one]
  exact one_mem _

/-- The scalars `ι_v(u · 1)` lie in `Δ` exactly when `u` is a unit of `𝒪_v`; in particular
`ι_v(ϖ · 1) ∉ Δ`. -/
theorem unitAt_smul_one_mem_wildMonoid_iff {γ : ℤᵐ⁰} (hγ : γ < 1) (u : (v.adicCompletion F)ˣ) :
    unitAt F D v (Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((u : v.adicCompletion F) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))
        (by rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact pow_ne_zero _ u.ne_zero)) ∈
        wildMonoid F D v γ hγ ↔ Valued.v (u : v.adicCompletion F) = 1 := by
  rw [mem_wildMonoid_iff, ← coe_toGL, toGL_unitAt, coe_mkOfDetNeZero]
  exact smul_one_mem_monoidM_iff hγ

/-- The diamond elements commute with `η_v`. -/
theorem diamond_commute_etaAdelic (d : (v.adicCompletion F)ˣ) (ϖ : v.adicCompletion F)
    (hϖ : ϖ ≠ 0) : Commute (diamond F D v d) (etaAdelic F D v ϖ hϖ) := by
  refine Commute.map (Units.ext ?_) (unitAt F D v)
  change Matrix.diagonal ![1, (d : v.adicCompletion F)] * Matrix.diagonal ![ϖ, 1] =
    Matrix.diagonal ![ϖ, 1] * Matrix.diagonal ![1, (d : v.adicCompletion F)]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ => mul_comm _ _)

/-- The diamond elements of units lie in `Δ`. -/
theorem diamond_mem_wildMonoid {γ : ℤᵐ⁰} (hγ : γ < 1) {d : (v.adicCompletion F)ˣ}
    (hd : Valued.v (d : v.adicCompletion F) = 1) : diamond F D v d ∈ wildMonoid F D v γ hγ := by
  rw [mem_wildMonoid_iff, diamond, ← coe_toGL, toGL_unitAt, coe_mkOfDetNeZero]
  exact diagonal_mem_monoidM hγ (map_one _).le one_ne_zero hd

end Wild

section Several

variable (F D) {κ : Type*} (w : κ → HeightOneSpectrum (𝓞 F)) [∀ k, RigidificationAt F D (w k)]

/-- **The wild-level monoid `Δ_t = θ_p⁻¹(∏_𝔭 M_{t_𝔭})`** at several places. -/
def wildMonoidOf (γ : κ → ℤᵐ⁰) (hγ : ∀ k, γ k < 1) : Submonoid (Dfx F D) :=
  ⨅ k, wildMonoid F D (w k) (γ k) (hγ k)

/-- **`U` has wild level `≥ 𝔭^t`**: `θ_p(U) ⊆ M_t`. -/
def HasWildLevel (U : Subgroup (Dfx F D)) (γ : κ → ℤᵐ⁰) (hγ : ∀ k, γ k < 1) : Prop :=
  U.toSubmonoid ≤ wildMonoidOf F D w γ hγ

variable {F D w}

/-- **`η_𝔭 ∈ Δ_t` for every `t`.** -/
theorem etaAdelic_mem_wildMonoidOf (hw : Function.Injective w) {γ : κ → ℤᵐ⁰}
    (hγ : ∀ k, γ k < 1) (k : κ) {ϖ : (w k).adicCompletion F} (hϖ : ϖ ≠ 0)
    (hϖ1 : Valued.v ϖ ≤ 1) : etaAdelic F D (w k) ϖ hϖ ∈ wildMonoidOf F D w γ hγ := by
  refine Submonoid.mem_iInf.mpr fun k' => ?_
  by_cases hk : k' = k
  · subst hk
    exact etaAdelic_mem_wildMonoid (hγ k') hϖ hϖ1
  · exact etaAdelic_mem_wildMonoid_of_ne (fun h => hk (hw h).symm) (hγ k') ϖ hϖ

/-- The standard levels `U₀(𝔫)` have wild level `≥ 𝔭^t`. -/
theorem hasWildLevel_U0Level {ι : Type*} {b : Module.Basis ι F D}
    {hb : IsOrderBasis b} {t : κ → ℕ} (ht : ∀ k, 1 ≤ t k) :
    HasWildLevel F D w (U0Level b hb w t) (fun k ↦ levelThreshold (t k))
      (fun k ↦ levelThreshold_lt_one (ht k)) := by
  intro g hg
  refine Submonoid.mem_iInf.mpr fun k => ?_
  have hg' : g ∈ U0Level b hb w t := hg
  rw [U0Level, standardLevel, Subgroup.mem_inf, Subgroup.mem_iInf] at hg'
  have hgk := mem_levelAt_iff.mp (hg'.2 k)
  rw [mem_wildMonoid_iff, ← coe_toGL]
  exact coe_mem_monoidM _ hgk

/-- **The Hecke pair `(Δ_t, U)`** for every compact open `U` of wild level `≥ 𝔭^t`. -/
theorem isHeckeTriple_wildMonoidOf [Module.Finite F D] {U : Subgroup (Dfx F D)}
    (hUc : IsCompact (U : Set (Dfx F D))) (hUo : IsOpen (U : Set (Dfx F D))) {γ : κ → ℤᵐ⁰}
    {hγ : ∀ k, γ k < 1} (hU : HasWildLevel F D w U γ hγ) :
    IsHeckeTriple (wildMonoidOf F D w γ hγ) U U :=
  Subgroup.isHeckeTriple_of_isCompact_of_isOpen hUc hUo hU

end Several

section Decomposition

variable (v : HeightOneSpectrum (𝓞 F)) [RigidificationAt F D v] {ι : Type*}

-- moving `ι_v(g)` past `u` conjugates it by `θ_v(u)`: the rest of `u` commutes with `ι_v(g)`
private theorem unitAt_mul_eq (u : Dfx F D) (g : GL (Fin 2) (v.adicCompletion F)) :
    unitAt F D v g * u = u * unitAt F D v ((toGL F D v u)⁻¹ * g * toGL F D v u) := by
  obtain ⟨u', hu'⟩ : ∃ u', u = unitAt F D v (toGL F D v u) * u' :=
    ⟨_, (mul_inv_cancel_left _ u).symm⟩
  have h1 : toGL F D v u' = 1 := by
    have h := congrArg (toGL F D v) hu'
    rw [map_mul, toGL_unitAt, left_eq_mul] at h
    exact h
  generalize toGL F D v u = m at hu' ⊢
  subst hu'
  have hc := fun h => unitAt_commute v h (toLocalUnits_eq_one_of_toGL_eq_one v h1)
  rw [mul_assoc (unitAt F D v m), ← (hc _).eq, ← mul_assoc, ← mul_assoc,
    ← map_mul (unitAt F D v), ← map_mul (unitAt F D v),
    show g * m = m * (m⁻¹ * g * m) by group]

/-- **The decomposition `U η_v U = ∐_α U · ι_v(x_α)` in `D_f^×`**: for a subgroup `U` whose
`v`-component lies in `Iw(v(ϖ)^t)` and which contains `ι_v(Iw₁₁(v(ϖ)^t))`. -/
theorem existsUnique_etaAdelicRep {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : v.adicCompletion F, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ}
    (ht : 1 ≤ t) {U : Subgroup (Dfx F D)}
    (hup : U ≤ levelAt F D v (iwahori (v.adicCompletion F) (Valued.v ϖ ^ t)))
    (hlow : (iwahoriPrincipal (v.adicCompletion F) (Valued.v ϖ ^ t)).map (unitAt F D v) ≤ U)
    (r : ι → v.adicCompletion F)
    (hr : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1)
    {u : Dfx F D} (hu : u ∈ U) :
    ∃! i, etaAdelic F D v ϖ hϖ * u * (etaAdelicRep F D v ϖ hϖ t (r i))⁻¹ ∈ U := by
  have hm : toGL F D v u ∈ iwahori (v.adicCompletion F) (Valued.v ϖ ^ t) := hup hu
  have hθ : ∀ i, toGL F D v (etaAdelic F D v ϖ hϖ * u * (etaAdelicRep F D v ϖ hϖ t (r i))⁻¹) =
      etaGL ϖ hϖ * toGL F D v u * (etaRep ϖ hϖ t (r i))⁻¹ := fun i => by
    rw [etaAdelic, etaAdelicRep, map_mul, map_mul, map_inv, toGL_unitAt, toGL_unitAt]
  obtain ⟨i, hi, huniq⟩ := existsUnique_etaRep hϖ hϖ1 hunif ht
    ((iwahoriPrincipal_le_iwahoriOne _).trans (iwahoriOne_le_iwahori _)) le_rfl r hr hm
  refine ⟨i, ?_, fun j hj => huniq j (by beta_reduce at hj ⊢; rw [← hθ j]; exact hup hj)⟩
  have hcorr := inv_mul_etaGL_mul_mem_iwahoriPrincipal hϖ hm
    (valued_le_one_of_etaConj_mem hϖ hϖ1 ht hm hi) hi
  beta_reduce
  rw [etaAdelic, etaAdelicRep, unitAt_mul_eq, mul_assoc u,
    ← map_inv (unitAt F D v) (etaRep ϖ hϖ t (r i)), ← map_mul (unitAt F D v)]
  refine U.mul_mem hu (hlow ⟨_, hcorr, ?_⟩)
  simp only [mul_assoc]

/-- **The adelic decomposition in bijective form**, as consumed by the Hecke operator `U_𝔭`. -/
theorem bijOn_etaAdelicRep {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : v.adicCompletion F, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ}
    (ht : 1 ≤ t) {U : Subgroup (Dfx F D)}
    (hup : U ≤ levelAt F D v (iwahori (v.adicCompletion F) (Valued.v ϖ ^ t)))
    (hlow : (iwahoriPrincipal (v.adicCompletion F) (Valued.v ϖ ^ t)).map (unitAt F D v) ≤ U)
    (r : ι → v.adicCompletion F) (hr1 : ∀ i, Valued.v (r i) ≤ 1)
    (hr : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1) :
    Set.BijOn (Quotient.mk'' : Dfx F D → Quotient (QuotientGroup.rightRel U))
      (Set.range fun i ↦ etaAdelicRep F D v ϖ hϖ t (r i))
      ((Quotient.mk'' : Dfx F D → Quotient (QuotientGroup.rightRel U)) ''
        (({etaAdelic F D v ϖ hϖ} : Set (Dfx F D)) * (U : Set (Dfx F D)))) := by
  have hmk : ∀ a b : Dfx F D,
      (Quotient.mk'' a : Quotient (QuotientGroup.rightRel U)) = Quotient.mk'' b ↔ b * a⁻¹ ∈ U :=
    fun _ _ => Quotient.eq''.trans QuotientGroup.rightRel_apply
  have hlow' : iwahoriPrincipal (v.adicCompletion F) (Valued.v ϖ ^ t) ≤ U.comap (unitAt F D v) :=
    Subgroup.map_le_iff_le_comap.mp hlow
  have hrep : ∀ i, etaAdelicRep F D v ϖ hϖ t (r i) ∈
      ({etaAdelic F D v ϖ hϖ} : Set (Dfx F D)) * (U : Set (Dfx F D)) := fun i => by
    obtain ⟨x, hx, y, hy, hxy⟩ := etaRep_mem_doubleCoset hϖ hϖ1 hlow' r hr1 i
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [etaAdelicRep, etaAdelic, ← hxy, map_mul]
    exact Set.mul_mem_mul (Set.mem_singleton _) hy
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · obtain ⟨i, rfl⟩ := hx
    exact Set.mem_image_of_mem _ (hrep i)
  · obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨e, he, u, hu, hηu⟩ := hrep i
    rw [Set.mem_singleton_iff] at he
    subst he
    beta_reduce at hηu
    obtain ⟨k, -, huniq⟩ := existsUnique_etaAdelicRep v hϖ hϖ1 hunif ht hup hlow r hr hu
    have hi : etaAdelic F D v ϖ hϖ * u * (etaAdelicRep F D v ϖ hϖ t (r i))⁻¹ ∈ U := by
      rw [hηu, mul_inv_cancel]
      exact one_mem U
    have hj : etaAdelic F D v ϖ hϖ * u * (etaAdelicRep F D v ϖ hϖ t (r j))⁻¹ ∈ U := by
      rw [hηu]
      simpa using U.inv_mem ((hmk _ _).mp hxy)
    obtain rfl := (huniq i hi).trans (huniq j hj).symm
    rfl
  · obtain ⟨x, ⟨e, he, u, hu, rfl⟩, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at he
    subst he
    obtain ⟨i, hi, -⟩ := existsUnique_etaAdelicRep v hϖ hϖ1 hunif ht hup hlow r hr hu
    exact ⟨etaAdelicRep F D v ϖ hϖ t (r i), ⟨i, rfl⟩, (hmk _ _).mpr hi⟩

/-- The standard levels satisfy the two hypotheses of the decomposition at an integral place. -/
theorem unitAt_iwahoriPrincipal_le_U1Level {κ : Type*}
    {w : κ → HeightOneSpectrum (𝓞 F)} [∀ k, RigidificationAt F D (w k)]
    (hw : Function.Injective w) {ι' : Type*} {b : Module.Basis ι' F D}
    {hb : IsOrderBasis b} (hint : ∀ k, RigidificationAt.IsIntegral b hb (w k)) (t : κ → ℕ)
    (k : κ) :
    (iwahoriPrincipal ((w k).adicCompletion F) (levelThreshold (t k))).map
      (unitAt F D (w k)) ≤ U1Level b hb w t := by
  rintro _ ⟨m, hm, rfl⟩
  rw [U1Level, standardLevel, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨(unitAt_mem_U0_iff (w k) (hint k)).mpr
    ((mem_integralGL_iff (w k)).mpr ⟨fun i j => hm.1.1 i j, hm.1.2.1⟩), fun k' => ?_⟩
  by_cases hk : k' = k
  · subst hk
    exact unitAt_mem_levelAt_iff.mpr (iwahoriPrincipal_le_iwahoriOne _ hm)
  · exact unitAt_mem_levelAt_of_ne (fun h => hk (hw h).symm) _ m

-- on a compact subgroup `v(det θ_w)` is trivial: some power of each element lies in the open
-- subgroup `θ_w⁻¹ GL₂(𝒪_w)`, and the value group is torsion-free
private theorem valued_det_toMatrix_eq_one_of_isCompact {w : HeightOneSpectrum (𝓞 F)}
    [RigidificationAt F D w] {U : Subgroup (Dfx F D)} (hU : IsCompact (U : Set (Dfx F D)))
    {u : Dfx F D} (hu : u ∈ U) : Valued.v (toMatrix F D w u).det = 1 := by
  haveI : Module.Finite F D := RigidificationAt.moduleFinite F D w
  have hopen : IsOpen (levelAt F D w (iwahori (w.adicCompletion F) 1) : Set (Dfx F D)) :=
    isOpen_levelAt (isOpen_iwahori ⟨1, one_ne_zero, (map_one _).le⟩)
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.relIndex_ne_zero_of_isCompact_of_isOpen hU hopen) (⟨u, hu⟩ : U)
  have h1 : Valued.v (toMatrix F D w (u ^ n)).det = 1 := by
    rw [← coe_toGL]
    exact (mem_levelAt_iff.mp (Subgroup.mem_subgroupOf.mp hmem)).2.1
  rw [map_pow, Matrix.det_pow, map_pow] at h1
  rcases lt_trichotomy (Valued.v (toMatrix F D w u).det) 1 with h | h | h
  · exact absurd h1 (pow_lt_one₀ zero_le h hn.ne').ne
  · exact h
  · exact absurd h1 (one_lt_pow₀ h hn.ne').ne'

/-- **Every `x ∈ U η_v U` has `v(det θ_v(x)) = v(ϖ)`.** -/
theorem valued_det_toMatrix_of_mem_doubleCoset {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) {γ : ℤᵐ⁰}
    {U : Subgroup (Dfx F D)} (hup : U ≤ levelAt F D v (iwahori (v.adicCompletion F) γ))
    {x : Dfx F D}
    (hx : x ∈ (U : Set (Dfx F D)) * ({etaAdelic F D v ϖ hϖ} : Set (Dfx F D)) *
      (U : Set (Dfx F D))) :
    Valued.v (toMatrix F D v x).det = Valued.v ϖ := by
  obtain ⟨y, ⟨u₁, hu₁, e, he, rfl⟩, u₂, hu₂, rfl⟩ := hx
  rw [Set.mem_singleton_iff] at he
  subst he
  have h₁ : Valued.v (toMatrix F D v u₁).det = 1 := by
    rw [← coe_toGL]
    exact (hup hu₁).2.1
  have h₂ : Valued.v (toMatrix F D v u₂).det = 1 := by
    rw [← coe_toGL]
    exact (hup hu₂).2.1
  rw [map_mul, map_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, h₁, h₂,
    toMatrix_etaAdelic, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

/-- **Every `x ∈ U η_v U` has `det θ_w(x) ∈ 𝒪_w^×` for `w ≠ v`**, for `U` compact. -/
theorem valued_det_toMatrix_of_mem_doubleCoset_of_ne {w : HeightOneSpectrum (𝓞 F)}
    [RigidificationAt F D w] (hw : w ≠ v)
    {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) {U : Subgroup (Dfx F D)}
    (hU : IsCompact (U : Set (Dfx F D))) {x : Dfx F D}
    (hx : x ∈ (U : Set (Dfx F D)) * ({etaAdelic F D v ϖ hϖ} : Set (Dfx F D)) *
      (U : Set (Dfx F D))) :
    Valued.v (toMatrix F D w x).det = 1 := by
  obtain ⟨y, ⟨u₁, hu₁, e, he, rfl⟩, u₂, hu₂, rfl⟩ := hx
  rw [Set.mem_singleton_iff] at he
  subst he
  have hη : toMatrix F D w (etaAdelic F D v ϖ hϖ) = 1 := by
    rw [etaAdelic, ← coe_toGL, toGL_unitAt_of_ne v hw, Units.val_one]
  rw [map_mul, map_mul, Matrix.det_mul, Matrix.det_mul, hη, Matrix.det_one, mul_one, map_mul,
    valued_det_toMatrix_eq_one_of_isCompact hU hu₁,
    valued_det_toMatrix_eq_one_of_isCompact hU hu₂, one_mul]

end Decomposition

section HeckeRing

variable {Δ : Submonoid (Dfx F D)} {U : Subgroup (Dfx F D)}

/-- **The element of `HeckeRing Δ U ℤ` defined by `η ∈ Δ`**: the class of the double coset
`U η U`. -/
def heckeElement (η : Dfx F D) (hη : η ∈ Δ) : HeckeRing Δ U ℤ :=
  HeckeCosetModule.of (Finsupp.single (HeckeCoset.mk U U ⟨η, hη⟩) 1)

/-- The class only depends on the double coset. -/
theorem heckeElement_eq_of_mem_doubleCoset {η η' : Dfx F D} (hη : η ∈ Δ) (hη' : η' ∈ Δ)
    (h : η' ∈ (U : Set (Dfx F D)) * ({η} : Set (Dfx F D)) * (U : Set (Dfx F D))) :
    (heckeElement η' hη' : HeckeRing Δ U ℤ) = heckeElement η hη := by
  obtain ⟨y, ⟨u₁, hu₁, e, he, rfl⟩, u₂, hu₂, rfl⟩ := h
  rw [Set.mem_singleton_iff] at he
  subst he
  have hmk : (HeckeCoset.mk U U ⟨u₁ * e * u₂, hη'⟩ : HeckeCoset Δ U U) =
      HeckeCoset.mk U U ⟨e, hη⟩ :=
    Quotient.sound (DoubleCoset.rel_iff.mpr ⟨u₁⁻¹, inv_mem hu₁, u₂⁻¹, inv_mem hu₂, by group⟩)
  rw [heckeElement, heckeElement, hmk]

end HeckeRing

end AdelicAlgebra
