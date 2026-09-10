/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.DiscModel
import PhD.LWX.Certificates
import PhD.QMF.Weight.Fredholm

/-!
# `S^{D,†,m}` in the disc model, and `U_p` on it — SKELETON

[LWX, §2.4–2.5] at analyticity level `m = h + 1`: the space of `m`-locally analytic automorphic
forms `S^{D,†,m}_κ(U)` is the space of functions `φ : (D ⊗ 𝔸_f)ˣ → OB_{qp^{-m}}`, left-invariant
under the global units and satisfying `φ(gu) = φ(g) ∣ u_p` for `u ∈ U`; and `U_p = [UηU]` acts by
the same formula (2.5.1).  In the disc model of `OB_{qp^{-m}}` (`DiscModel.lean`) this is the
`slashFixedPointsOfLE` of the disc action pulled back along the component map, and — at a family
of class representatives with trivial stabilisers — the Hecke operator becomes the block operator
of the certificate matrices of [LWX, Prop 3.1], now acting on `c(ι × (ℤ/pʰ × ℕ), K)`.

This file is `PhD/QMF/Weight/{Forms,Compact,Fredholm}.lean` transcribed for the disc model: the
same statements with `c(ℕ, K)` replaced by `c(ℤ/pʰ × ℕ, K)` and `kappaSlash` by `discSlash`.

## Main declarations

* `LWX.discLevelSlashAction`, `LWX.DiscForms` — the forms.
* `LWX.discEvalAtReps`, `LWX.bijective_discEvalAtReps_of_stabilizer_eq_bot` — the block model.
* `LWX.discHeckeOperator`, `LWX.discHeckeBlockOp`, `LWX.discEvalAtReps_discHeckeOperator` — `U_p`.
* `LWX.isCompactoid_discHeckeBlockOp`, `LWX.discHeckeCharPowerSeries`,
  `LWX.evalT_discHeckeCharPowerSeries_eq_zero_iff` — the Fredholm determinant and its zeros.
-/

open AbstractHeckeOperatorSlash RightSlashAction TateFredholm QMF QMF.Weight

open scoped Pointwise QMF TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) ℚ_[p]) (h : ℕ) (ψ : ℚ_[p] →+* K) {UK : Subgroup Kˣ}
  {ρ : ℝ} (κ : AnalyticWeight UK (M1Kh h ψ) ρ)

section Forms

set_option warn.classDefReducibility false in
/-- The disc action of the level monoid, pulled back along the component map
(`RightSlashAction.comap`). -/
@[instance_reducible]
def discLevelSlashAction : RightSlashAction (levelM1 (p := p) θ) c(ZMod (p ^ h) × ℕ, K) :=
  RightSlashAction.comap (levelM1ToM1 (p := p) θ) (discSlashAction h ψ κ)

set_option warn.classDefReducibility false in
set_option linter.defProp false in
/-- The pulled-back disc action commutes with scalars. -/
def discLevelSMulSlashClass :
    letI := discLevelSlashAction θ h ψ κ
    RightSlashAction.SMulSlashClass K (levelM1 (p := p) θ) c(ZMod (p ^ h) × ℕ, K) := by
  letI := discLevelSlashAction θ h ψ κ
  refine { smul_slash := ?_ }
  intro r a v
  exact (discSMulSlashClass h ψ κ).smul_slash r a (levelM1ToM1 (p := p) θ v)

variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ)

/-- **`S^{D,†,m}_κ(U)` in the disc model** ([LWX, §2.4], `m = h + 1`): the automorphic functions
valued in the disc model which are `U`-equivariant for the disc action. -/
def DiscForms : Submodule K (AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :=
  letI := discLevelSlashAction θ h ψ κ
  letI := discLevelSMulSlashClass θ h ψ κ
  AbstractHeckeOperatorSlash.slashFixedPointsOfLE K
    (AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) hU

omit [CharZero K] in
theorem mem_discForms_iff (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :
    φ ∈ DiscForms (Γ := Γ) θ h ψ κ U hU ↔
      ∀ (u : U) (g : G), φ.toFun (g * u) = discSlash h ψ κ ⟨θ u, hU u.2⟩ (φ.toFun g) := by
  letI := discLevelSlashAction θ h ψ κ
  letI := discLevelSMulSlashClass θ h ψ κ
  exact AutomorphicFunction.mem_levelSubmoduleSlash_iff' K hU

end Forms

section BlockModel

variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of a disc-model form at the representatives `c : ι → G`, assembled into the block
model `c(ι × (ℤ/pʰ × ℕ), K)` ([Buzzard, §9 p. 69]). -/
def discEvalAtReps (c : ι → G) :
    DiscForms (Γ := Γ) θ h ψ κ U hU →ₗ[K] c(ι × (ZMod (p ^ h) × ℕ), K) where
  toFun φ := ∑ i : ι, cSpace.blockIncl i
    ((φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i))
  map_add' φ ψ' := by simp [Finset.sum_add_distrib]
  map_smul' r φ := by simp [Finset.smul_sum]

omit [CharZero K] in
theorem blockProj_discEvalAtReps (c : ι → G) (φ : DiscForms (Γ := Γ) θ h ψ κ U hU) (i : ι) :
    cSpace.blockProj i (discEvalAtReps θ h ψ κ U hU c φ)
      = (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i) := by
  simp only [discEvalAtReps, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    cSpace.blockProj_blockIncl, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [CharZero K] in
/-- Coordinates of the evaluation: `(discEvalAtReps c φ) (i, x) = φ(cᵢ) x`. -/
theorem discEvalAtReps_apply (c : ι → G) (φ : DiscForms (Γ := Γ) θ h ψ κ U hU)
    (i : ι) (x : ZMod (p ^ h) × ℕ) :
    discEvalAtReps θ h ψ κ U hU c φ (i, x)
      = (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i) x :=
  DFunLike.congr_fun (blockProj_discEvalAtReps θ h ψ κ U hU c φ i) x

omit [CharZero K] in
/-- **Buzzard's decomposition at a neat level** ([Buzzard, §9 p. 69]; [LWX, (2.11.1)]):
evaluation at a complete family of representatives with trivial stabilisers is a bijection
`S^{D,†,m}_κ(U) ≅ ⊕ᵢ OB_{qp^{-m}}`. -/
theorem bijective_discEvalAtReps_of_stabilizer_eq_bot (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    Function.Bijective (discEvalAtReps (Γ := Γ) θ h ψ κ U hU c) := by
  letI := discLevelSlashAction θ h ψ κ
  letI := discLevelSMulSlashClass θ h ψ κ
  refine ⟨fun φ φ' hφφ' => ?_, fun F => ?_⟩
  · have hval : ∀ i, (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i)
        = (φ' : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i) := fun i => by
      simpa only [blockProj_discEvalAtReps] using congrArg (cSpace.blockProj i) hφφ'
    refine Subtype.ext (AutomorphicFunction.ext fun g => ?_)
    obtain ⟨i, hi⟩ := hc.2 (Quotient.mk'' g)
    obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi)
    calc (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x * c i * y)
        = (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i * y) := by
          rw [mul_assoc]
          exact AutomorphicFunction.left_invt' _ hx _
      _ = (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i)
            ∣ₛ (⟨y, hU hy⟩ : levelM1 (p := p) θ) :=
          AutomorphicFunction.slash_apply_mul K hU φ.2 ⟨y, hy⟩ (c i)
      _ = (φ' : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i)
            ∣ₛ (⟨y, hU hy⟩ : levelM1 (p := p) θ) := by
          rw [hval i]
      _ = (φ' : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i * y) :=
          (AutomorphicFunction.slash_apply_mul K hU φ'.2 ⟨y, hy⟩ (c i)).symm
      _ = (φ' : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x * c i * y) := by
          rw [mul_assoc]
          exact (AutomorphicFunction.left_invt' _ hx _).symm
  · let e : ι ≃ DoubleCoset.Quotient (Γ : Set G) (U : Set G) := Equiv.ofBijective _ hc
    have hσ : ∀ q, (Quotient.mk'' (c (e.symm q)) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))
        = q := fun q => e.apply_symm_apply q
    obtain ⟨φ, hφ⟩ := (AutomorphicFunction.bijective_evalAtRepsSlash
      (A := c(ZMod (p ^ h) × ℕ, K)) K hU (fun q => c (e.symm q)) hσ).2
      (fun q => ⟨cSpace.blockProj (e.symm q) F, fun w => by
        have hw1 : (w : G) = 1 := Subgroup.mem_bot.mp (hstab (e.symm q) ▸ w.2)
        have hw' : (⟨(w : G), hU w.2.1⟩ : levelM1 (p := p) θ) = 1 := Subtype.ext hw1
        exact (congrArg (fun v : levelM1 (p := p) θ =>
          cSpace.blockProj (e.symm q) F ∣ₛ v) hw').trans (RightSlashAction.slash_one _)⟩)
    refine ⟨⟨φ.1, φ.2⟩, DFunLike.ext _ _ fun z => ?_⟩
    obtain ⟨i, x⟩ := z
    have h3 : (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c (e.symm (e i)))
        = cSpace.blockProj (e.symm (e i)) F :=
      congrArg Subtype.val (congrFun hφ (e i))
    rw [Equiv.symm_apply_apply] at h3
    rw [discEvalAtReps_apply]
    exact (congrArg (fun a => a x) h3).trans (cSpace.blockProj_apply _ _ _)

end BlockModel

section Hecke

variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θ) (idx : ι → Fin p → ι)
  (u : ι → Fin p → U)

/-- **`U_p = [UηU]` on `S^{D,†,m}_κ(U)`** ([LWX, (2.5.1)]). -/
def discHeckeOperator {η : G} (hη : η ∈ levelM1 (p := p) θ)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    DiscForms (Γ := Γ) θ h ψ κ U hU →ₗ[K] DiscForms (Γ := Γ) θ h ψ κ U hU :=
  letI := discLevelSlashAction θ h ψ κ
  letI := discLevelSMulSlashClass θ h ψ κ
  AbstractHeckeOperatorSlash.heckeOperatorSlash K hU hU hη hfin

/-- The `(i, j)` block of `U_p` in the disc block model: the sum of the disc actions of the
certificate matrices `u_{i,t}·v_t` with target `j` ([Jacobs, pp. 20–21]; [LWX, Prop 3.1]). -/
def discHeckeBlock (i j : ι) :
    c(ZMod (p ^ h) × ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K) :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin p => idx i t = j),
    discSlash h ψ κ (certM1 θ U hU vRep hvΔ u i t)

/-- **The block operator of `U_p`** on `c(ι × (ℤ/pʰ × ℕ), K)`. -/
def discHeckeBlockOp : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K) :=
  blockOp (discHeckeBlock θ h ψ κ U hU vRep hvΔ idx u)

omit [CharZero K] in
/-- **The transport**: under evaluation at the representatives, `U_p` is the block operator of the
certificate matrices (`heckeOperatorSlash_apply_rep`, exactly as in
`QMF.Weight.evalAtReps_heckeOperator`). -/
theorem discEvalAtReps_discHeckeOperator {η : G} (hη : η ∈ levelM1 (p := p) θ)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite)
    (c : ι → G)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
        Set (RightCosets U)))
    (hvinj : Function.Injective vRep) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    (φ : DiscForms (Γ := Γ) θ h ψ κ U hU) :
    discEvalAtReps θ h ψ κ U hU c (discHeckeOperator θ h ψ κ U hU hη hfin φ)
      = discHeckeBlockOp θ h ψ κ U hU vRep hvΔ idx u
          (discEvalAtReps θ h ψ κ U hU c φ) := by
  letI := discLevelSlashAction θ h ψ κ
  letI := discLevelSMulSlashClass θ h ψ κ
  have key : ∀ i : ι,
      (discHeckeOperator θ h ψ κ U hU hη hfin φ :
          AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i)
        = ∑ j : ι, discHeckeBlock θ h ψ κ U hU vRep hvΔ idx u i j
            ((φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c j)) := by
    intro i
    have hrep := AutomorphicFunction.heckeOperatorSlash_apply_rep (Γ := Γ) K hU hη hfin φ
      vRep hvΔ hv hvinj (c i) (fun t => c (idx i t)) (d i) (hd i) (u i) (hfact i)
      (fun t => mul_mem (hU (u i t).2) (hvΔ t))
    refine hrep.trans ?_
    rw [← Finset.sum_fiberwise Finset.univ (idx i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [discHeckeBlock, sum_apply]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [show idx i t = j from by simpa using ht]
    rfl
  simp only [discEvalAtReps, LinearMap.coe_mk, AddHom.coe_mk, key, map_sum, discHeckeBlockOp,
    blockOp_blockIncl]
  exact Finset.sum_comm

omit [CharZero K] in
/-- **`U_p` is compactoid** ([Buzzard, Lemma 12.2]): every certificate matrix has the `U_p`-shape
`‖a‖ ≤ p⁻¹`, so every disc block is compactoid (`isCompactoid_discSlash`). -/
theorem isCompactoid_discHeckeBlockOp (hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    IsCompactoid (discHeckeBlockOp θ h ψ κ U hU vRep hvΔ idx u) := by
  refine isCompactoid_blockOp fun i j => ?_
  refine IsCompactoid.finset_sum _ fun t _ => ?_
  refine isCompactoid_discSlash h ψ κ hρ hσ ?_
  have hs := hshape i t
  rwa [LocalMat.IsUpShape, PadicInt.norm_def, M1.coe_toLocalMat_a] at hs

/-- **The Fredholm determinant `det(1 − X·U_p)` on `S^{D,†,m}_κ(U)`** ([LWX, Def 2.13] at a
point). -/
def discHeckeCharPowerSeries : PowerSeries K :=
  charPowerSeries (discHeckeBlockOp θ h ψ κ U hU vRep hvΔ idx u)

omit [CharZero K] in
/-- **Eigenforms are the reciprocal roots** ([Serre1962, §7, Props. 11–12]) in the disc model. -/
theorem evalT_discHeckeCharPowerSeries_eq_zero_iff (hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape)
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    {η : G} (hη : η ∈ levelM1 (p := p) θ)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
        Set (RightCosets U)))
    (hvinj : Function.Injective vRep) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    {a : K} (ha0 : a ≠ 0) :
    PowerSeries.evalT a (discHeckeCharPowerSeries θ h ψ κ U hU vRep hvΔ idx u) = 0 ↔
      ∃ φ : DiscForms (Γ := Γ) θ h ψ κ U hU, φ ≠ 0 ∧
        discHeckeOperator θ h ψ κ U hU hη hfin φ = a⁻¹ • φ := by
  have hcomp := isCompactoid_discHeckeBlockOp θ h ψ κ U hU vRep hvΔ idx u hρ hσ hshape
  have hbij := bijective_discEvalAtReps_of_stabilizer_eq_bot θ h ψ κ U hU c hc hstab
  have htr : ∀ φ : DiscForms (Γ := Γ) θ h ψ κ U hU,
      discEvalAtReps θ h ψ κ U hU c (discHeckeOperator θ h ψ κ U hU hη hfin φ)
        = discHeckeBlockOp θ h ψ κ U hU vRep hvΔ idx u
            (discEvalAtReps θ h ψ κ U hU c φ) := fun φ =>
    discEvalAtReps_discHeckeOperator θ h ψ κ U hU vRep hvΔ idx u hη hfin c hv hvinj d hd
      hfact φ
  rw [discHeckeCharPowerSeries, evalT_charPowerSeries_eq_zero_iff _ hcomp ha0]
  constructor
  · rintro ⟨x, hx0, hx⟩
    obtain ⟨φ, rfl⟩ := hbij.2 x
    refine ⟨φ, fun h0 => hx0 (by rw [h0, map_zero]), hbij.1 ?_⟩
    rw [htr, hx, map_smul]
  · rintro ⟨φ, hφ0, hφ⟩
    refine ⟨discEvalAtReps θ h ψ κ U hU c φ,
      fun h0 => hφ0 (hbij.1 (by rw [h0, map_zero])), ?_⟩
    rw [← htr, hφ, map_smul]

end Hecke

end LWX

end
