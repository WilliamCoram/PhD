/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.Halo
import PhD.LWX.IntegralModel
import PhD.QMF.Weight.Compact

/-!
# `U_p` on `S^D_int` from coset certificates: [LWX, Prop 3.1] in full

[LWX, Prop 3.1]: "In terms of the isomorphism (2.11.1), the `U_p`-operator on `S^D_int` can be
described by the following commutative diagram … the right vertical arrow `U_p` is given by a
`t × t` matrix … (1) each entry is a sum of operators `‖_{δ_p}` … (2) exactly `p` such operators
in each row and each column … (3) each `δ_p` belongs to `(pℤ_p ℤ_p; qℤ_p ℤ_p^×)`."  Its proof
writes `γ_i v_j⁻¹ = δ_{i,j}⁻¹ γ_{λ_{i,j}} u_{i,j}` and finds
`(U_pφ)(γ_i) = ∑_j φ(γ_{λ_{i,j}})‖_{u_{i,j,p} v_j}` with
`δ_{i,j,p} = u_{i,j,p} v_j ∈ Iw_q (p 0; 0 1) Iw_q ⊆ (pℤ_p ℤ_p; qℤ_p ℤ_p^×)`.

The repo's ring-generic Hecke layer already proves the display
(`AutomorphicFunction.heckeOperatorSlash_apply_rep`, [Jacobs, pp. 20–21] verbatim) and the seam
`intEvalAtReps_comm` (`PhD/LWX/IntegralModel.lean`: any operator satisfying the display at the
representatives intertwines `intEvalAtReps` with `UpDatum.op`).  This file closes the loop for
the **genuine** integral Hecke operator `[UηU]` on `S^D_int`:

* the `UpDatum` assembled from right-coset certificates `(vRep, idx, u)` of `UηU`
  (`UpDatum.ofCerts`), with the shape clause (3) derived from `Iw·η·Iw` (`isUpShape_certM1`);
* the integral `U_p = [UηU]` on `S^D_int` (`intHeckeOperator`, the ring-generic
  `heckeOperatorSlash` at the `(2.3.2)`-action);
* **[LWX, Prop 3.1]**: `intEvalAtReps ∘ [UηU] = (ofCerts).op ω ∘ intEvalAtReps`;
* **[LWX, (2.11.1)]** at a neat level: `intEvalAtReps` is bijective.

## Main declarations

* `LWX.certM1`, `LWX.UpDatum.ofCerts`, `LWX.isUpShape_certM1`.
* `LWX.intHeckeOperator`, `LWX.intEvalAtReps_intHeckeOperator`.
* `LWX.bijective_intEvalAtReps_of_stabilizer_eq_bot`.
-/

open AbstractHeckeOperatorSlash RightSlashAction TateFredholm

open scoped Pointwise QMF TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) ℚ_[p]) (U : Subgroup G)
  (hU : (U : Set G) ⊆ levelM1 (p := p) θ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θ) (idx : ι → Fin p → ι)
  (u : ι → Fin p → U)

/-- The certificate matrix `δ_{i,j,p} = u_{i,j,p}·v_j` of [LWX, Prop 3.1], as an element of
`M₁`. -/
def certM1 (i : ι) (t : Fin p) : M1 p :=
  ⟨θ ((u i t : G) * vRep t), mul_mem (hU (u i t).2) (hvΔ t)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coe_certM1 (i : ι) (t : Fin p) :
    (certM1 θ U hU vRep hvΔ u i t : Matrix (Fin 2) (Fin 2) ℚ_[p]) = θ ((u i t : G) * vRep t) :=
  rfl

/-- **The `UpDatum` of a system of certificates** ([LWX, Prop 3.1]): targets `idx`, local
matrices `δ_{i,j,p} = u_{i,j,p}·v_j`, shapes as hypotheses. -/
def UpDatum.ofCerts
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    UpDatum p ι where
  tgt := idx
  mat i t := M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)
  hshape := hshape

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem UpDatum.ofCerts_tgt
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape).tgt = idx := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem UpDatum.ofCerts_mat
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) (i : ι)
    (t : Fin p) :
    (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape).mat i t
      = M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t) := rfl

/-- Members of `M₁` have determinant of norm `≤ 1` (integral entries). -/
theorem norm_det_le_one_of_mem_M1 {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ M1 p) :
    ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_one₀ (hg.1 _ _) (norm_nonneg _) (hg.1 _ _)
  · rw [norm_neg, norm_mul]
    exact mul_le_one₀ (hg.1 _ _) (norm_nonneg _) (hg.1 _ _)

include hU in
/-- Elements of the level group have unit determinant (`θ x` and `θ x⁻¹` both lie in `M₁`). -/
theorem norm_det_theta_eq_one (x : U) : ‖(θ x).det‖ = 1 := by
  have h1 : ‖(θ x).det‖ ≤ 1 := norm_det_le_one_of_mem_M1 (hU x.2)
  have h2 : ‖(θ (x⁻¹ : U)).det‖ ≤ 1 := norm_det_le_one_of_mem_M1 (hU (x⁻¹).2)
  have hmul : (θ x).det * (θ (x⁻¹ : U)).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      map_one, Matrix.det_one]
  have hnorm := congrArg norm hmul
  rw [norm_mul, norm_one] at hnorm
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖(θ x).det‖ * ‖(θ (x⁻¹ : U)).det‖ := hnorm.symm
    _ ≤ ‖(θ x).det‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖(θ x).det‖ := mul_one _

include hU in
/-- Elements of the level group are Iwahori-shaped: `a` is a unit (`ad − bc = det` a unit and
`‖bc‖ < 1`). -/
theorem norm_theta_apply_zero_zero_eq_one (x : U) : ‖θ x 0 0‖ = 1 := by
  have hg : θ x ∈ M1 p := hU x.2
  have hd : ‖θ x 1 1‖ = 1 := hg.2.2.1
  have hdet : ‖(θ x).det‖ = 1 := norm_det_theta_eq_one θ U hU x
  have hkey : θ x 0 0 * θ x 1 1 = (θ x).det + θ x 0 1 * θ x 1 0 := by
    rw [Matrix.det_fin_two]
    ring
  have hbc : ‖θ x 0 1 * θ x 1 0‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hg.1 0 1)).trans_lt
      (hg.2.1.trans_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)))
  calc ‖θ x 0 0‖ = ‖θ x 0 0 * θ x 1 1‖ := by rw [norm_mul, hd, mul_one]
    _ = ‖(θ x).det + θ x 0 1 * θ x 1 0‖ := by rw [hkey]
    _ = max ‖(θ x).det‖ ‖θ x 0 1 * θ x 1 0‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdet]; exact hbc.ne')
    _ = 1 := by rw [hdet, max_eq_left hbc.le]

/-- **`Iw_q (p 0; 0 1) Iw_q ⊆ (pℤ_p ℤ_p; qℤ_p ℤ_p^×)`** ([LWX, Prop 3.1, proof]): for
`x, y ∈ U` and `η ∈ M₁` with `‖η₀₀‖ ≤ p⁻¹`, the local matrix of `x·η·y` has the `U_p`-shape
(`(xηy)₀₀ = x₀₀η₀₀y₀₀ + x₀₀η₀₁y₁₀ + x₀₁η₁₀y₀₀ + x₀₁η₁₁y₁₀`, every term in `pℤ_p`). -/
theorem isUpShape_toLocalMat_mul_mul (x y : U) {η : G} (hη : η ∈ levelM1 (p := p) θ)
    (hηa : ‖θ η 0 0‖ ≤ (p : ℝ)⁻¹) :
    (M1.toLocalMat (⟨θ ((x : G) * η * y),
      mul_mem (mul_mem (hU x.2) hη) (hU y.2)⟩ : M1 p)).IsUpShape := by
  have hA : ∀ i j, ‖θ x i j‖ ≤ 1 := (hU x.2).1
  have hB : ∀ i j, ‖θ η i j‖ ≤ 1 := hη.1
  have hB10 : ‖θ η 1 0‖ ≤ (p : ℝ)⁻¹ := hη.2.1
  have hC : ∀ i j, ‖θ y i j‖ ≤ 1 := (hU y.2).1
  have hC10 : ‖θ y 1 0‖ ≤ (p : ℝ)⁻¹ := (hU y.2).2.1
  have hle : ∀ {a b : ℚ_[p]}, ‖a‖ ≤ 1 → ‖b‖ ≤ (p : ℝ)⁻¹ → ‖a * b‖ ≤ (p : ℝ)⁻¹ :=
    fun ha hb => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hb
  have hle' : ∀ {a b : ℚ_[p]}, ‖a‖ ≤ (p : ℝ)⁻¹ → ‖b‖ ≤ 1 → ‖a * b‖ ≤ (p : ℝ)⁻¹ :=
    fun ha hb => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hb).trans ha
  unfold LocalMat.IsUpShape
  rw [PadicInt.norm_def, M1.coe_toLocalMat_a]
  change ‖θ ((x : G) * η * y) 0 0‖ ≤ (p : ℝ)⁻¹
  simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact hle' ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hle (hA 0 0) hηa) (hle (hA 0 1) hB10))) (hC 0 0)
  · refine hle ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) hC10
    · rw [norm_mul]
      exact mul_le_one₀ (hA 0 0) (norm_nonneg _) (hB 0 1)
    · rw [norm_mul]
      exact mul_le_one₀ (hA 0 1) (norm_nonneg _) (hB 1 1)

omit [Fintype ι] [DecidableEq ι] in
/-- **[LWX, Prop 3.1(3)]**: every certificate matrix of `UηU` has the `U_p`-shape
(`v_j ∈ UηU`, so `u_{i,j}·v_j ∈ U·η·U`; `exists_mul_eta_mul_of_bijOn`). -/
theorem isUpShape_certM1 {η : G} (hη : η ∈ levelM1 (p := p) θ) (hηa : ‖θ η 0 0‖ ≤ (p : ℝ)⁻¹)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
        Set (RightCosets U)))
    (i : ι) (t : Fin p) : (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hvt⟩ := QMF.Weight.exists_mul_eta_mul_of_bijOn U hv t
  have heq : certM1 θ U hU vRep hvΔ u i t
      = ⟨θ (((⟨(u i t : G) * u₁, mul_mem (u i t).2 hu₁⟩ : U) : G) * η * ((⟨u₂, hu₂⟩ : U) : G)),
          mul_mem (mul_mem (hU (⟨(u i t : G) * u₁, mul_mem (u i t).2 hu₁⟩ : U).2) hη)
            (hU (⟨u₂, hu₂⟩ : U).2)⟩ :=
    Subtype.ext (by
      change θ ((u i t : G) * vRep t) = θ ((u i t : G) * u₁ * η * u₂)
      simp only [hvt, mul_assoc])
  rw [heq]
  exact isUpShape_toLocalMat_mul_mul θ U hU _ _ hη hηa

/-- **The integral `U_p = [UηU]` on `S^D_int`** ([LWX, (2.5.1)] on the integral model,
[LWX, §2.7]: "the topological space `S^D_int` carries a continuous action of `U_p`, defined
using the same formula (2.5.1)") — the ring-generic `heckeOperatorSlash` at the
`(2.3.2)`-action. -/
def intHeckeOperator (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {η : G}
    (hη : η ∈ levelM1 (p := p) θ)
    (h : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    IntForms (Γ := Γ) θ hp2 ω U hU →ₗ[HaloInt p] IntForms (Γ := Γ) θ hp2 ω U hU :=
  letI := seqLevelSlashAction (p := p) θ hp2 ω
  haveI := seqLevelSMulSlash (p := p) θ hp2 ω
  heckeOperatorSlash (HaloInt p) hU hU hη h

/-- **[LWX, Prop 3.1] in full**: under evaluation at the class-set representatives, the
integral `U_p` is the block matrix of the certificate datum —
`intEvalAtReps ∘ [UηU] = (ofCerts).op ω ∘ intEvalAtReps` (`heckeOperatorSlash_apply_rep` +
`intEvalAtReps_comm`). -/
theorem intEvalAtReps_intHeckeOperator (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {η : G}
    (hη : η ∈ levelM1 (p := p) θ)
    (h : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite)
    (c : ι → G)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
        Set (RightCosets U)))
    (hvinj : Function.Injective vRep) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G))
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape)
    (φ : IntForms (Γ := Γ) θ hp2 ω U hU) :
    intEvalAtReps θ hp2 ω U hU c (intHeckeOperator θ U hU hp2 ω hη h φ)
      = (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape).op ω
          (intEvalAtReps θ hp2 ω U hU c φ) := by
  refine intEvalAtReps_comm θ hp2 ω U hU c (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape)
    (fun i t => certM1 θ U hU vRep hvΔ u i t) (fun _ _ => rfl)
    (intHeckeOperator θ U hU hp2 ω hη h) (fun φ i => ?_) φ
  letI := seqLevelSlashAction (p := p) θ hp2 ω
  haveI := seqLevelSMulSlash (p := p) θ hp2 ω
  exact AutomorphicFunction.heckeOperatorSlash_apply_rep (Γ := Γ) (HaloInt p) hU hη h φ vRep
    hvΔ hv hvinj (c i) (fun t => c (idx i t)) (d i) (hd i) (u i) (hfact i)
    (fun t => mul_mem (hU (u i t).2) (hvΔ t))

/-- **[LWX, (2.11.1)] at a neat level**: evaluation at a complete family of representatives
with trivial stabilisers is a bijection `S^D_int ≅ ⊕ᵢ c(ℕ, Λ^{>1/p})` (the ring-generic
`bijective_evalAtRepsSlash`, mirror of `QMF.Weight.bijective_evalAtReps_of_stabilizer_eq_bot`). -/
theorem bijective_intEvalAtReps_of_stabilizer_eq_bot (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    Function.Bijective (intEvalAtReps (Γ := Γ) θ hp2 ω U hU c) := by
  letI := seqLevelSlashAction (p := p) θ hp2 ω
  haveI := seqLevelSMulSlash (p := p) θ hp2 ω
  refine ⟨fun φ ψ hφψ => ?_, fun F => ?_⟩
  · have h : ∀ i, (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i)
        = (ψ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i) := fun i => by
      simpa only [blockProj_intEvalAtReps] using congrArg (cSpace.blockProj i) hφψ
    refine Subtype.ext (AutomorphicFunction.ext fun g => ?_)
    obtain ⟨i, hi⟩ := hc.2 (Quotient.mk'' g)
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi)
    calc (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (a * c i * b)
        = (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i * b) := by
          rw [mul_assoc]
          exact AutomorphicFunction.left_invt' _ ha _
      _ = (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i)
            ∣ₛ (⟨b, hU hb⟩ : levelM1 (p := p) θ) :=
          AutomorphicFunction.slash_apply_mul (HaloInt p) hU φ.2 ⟨b, hb⟩ (c i)
      _ = (ψ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i)
            ∣ₛ (⟨b, hU hb⟩ : levelM1 (p := p) θ) := by
          rw [h i]
      _ = (ψ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c i * b) :=
          (AutomorphicFunction.slash_apply_mul (HaloInt p) hU ψ.2 ⟨b, hb⟩ (c i)).symm
      _ = (ψ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (a * c i * b) := by
          rw [mul_assoc]
          exact (AutomorphicFunction.left_invt' _ ha _).symm
  · let e : ι ≃ DoubleCoset.Quotient (Γ : Set G) (U : Set G) := Equiv.ofBijective _ hc
    have hσ : ∀ q, (Quotient.mk'' (c (e.symm q)) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))
        = q := fun q => e.apply_symm_apply q
    obtain ⟨φ, hφ⟩ := (AutomorphicFunction.bijective_evalAtRepsSlash (A := c(ℕ, HaloInt p))
      (HaloInt p) hU (fun q => c (e.symm q)) hσ).2
      (fun q => ⟨cSpace.blockProj (e.symm q) F, fun w => by
        have hw1 : (w : G) = 1 := Subgroup.mem_bot.mp (hstab (e.symm q) ▸ w.2)
        have hw' : (⟨(w : G), hU w.2.1⟩ : levelM1 (p := p) θ) = 1 := Subtype.ext hw1
        exact (congrArg (fun v : levelM1 (p := p) θ => cSpace.blockProj (e.symm q) F ∣ₛ v)
          hw').trans (RightSlashAction.slash_one _)⟩)
    refine ⟨⟨φ.1, φ.2⟩, DFunLike.ext _ _ fun x => ?_⟩
    obtain ⟨i, n⟩ := x
    have h3 : (φ : AutomorphicFunction G Γ (c(ℕ, HaloInt p))) (c (e.symm (e i)))
        = cSpace.blockProj (e.symm (e i)) F :=
      congrArg Subtype.val (congrFun hφ (e i))
    rw [Equiv.symm_apply_apply] at h3
    rw [intEvalAtReps_apply]
    exact (congrArg (fun a => a n) h3).trans (cSpace.blockProj_apply _ _ _)

end LWX

end
