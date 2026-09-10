/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.AtkinLehnerMap
import PhD.LWX.DegreeFormula

/-!
# `U_p ∘ U'_p = p^{k+1}` and hypothesis H1

**H1b.**  With `U'_p := W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W` (the Atkin–Lehner conjugate of `U_p` at the partner
nebentypus), `U_p ∘ U'_p = p^{k+1}` on the classical disc forms of `(k, ψ)`.  Expanding both
Hecke operators over the representatives `v_c = (p 0; cp 1)` and `W` over `w`, the composite at
`x` is `∑_{b,c} φ(x·(w v_b w⁻¹ v_c)⁻¹) ∣_k (w v_b w⁻¹ v_c)`, and the key factorisation
`w v_b w⁻¹ v_c = ℓ_{b,c} · (p·1) · s_{−b}` (`wGL_mul_vGL_mul_wGL_inv_mul_vGL`) with
`ℓ_{b,c} ∈ Iw_p` fixing disc `0` turns the `(b,c)`-term into
`ψ_neb(1 + bcp)⁻¹ · (p^k · (disc b of φ(x)) ∣_k n(−b/p))`: the level-equivariance at `ℓ_{b,c}⁻¹`
produces the nebentypus value, the central `p` acts trivially (`AtkinLehnerData.central`) and
`Sym^k(p·1) = p^k`.  Summing over `c`: the `b = 0` terms give `p · p^k · φ(x)`, and for `b ≠ 0`
the sum `∑_c ψ_neb(1 + bcp)⁻¹` vanishes because the conductor is exactly `p²`
(`sum_inv_nebCharK_eq_zero`).  This is the double-coset expansion whose matrix identities were
worked out in `PhD/Test/AtkinLehnerIdentity.lean` ("`U_p` is invertible at ramified
nebentypus"; classical statement Miyake Thm 4.6.17 as cited at `bu04.txt:1122–1124`).

**H1a** is then `A' = W B W⁻¹` by the definition of `B := W⁻¹ A' W`, and the matrix form of
both follows by transporting along the block model of the classical forms at a neat level.

**The deliverable**: `atkinLehnerHypothesis_of_atkinLehnerData` — hypothesis H1 of
`PhD/LWX/AtkinLehnerInst.lean` holds at the classical points, with the partner datum at the
nebentypus `ω⁻¹ω₀^{2k}` and the point `T_{χ_k}(ζ⁻¹)`; and `degX_succ_of_atkinLehnerData` —
[LWX, Thm 1.3]'s degree formula with **no hypothesis left**, granted the adelic data.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash RightSlashAction
open scoped TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable (ψ : ℚ_[p] →+* K)
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
variable (k : ℕ) {UK : Subgroup Kˣ} {ρ : ℝ} (κ : AnalyticWeight UK (M1Kh 1 ψ) ρ)
variable {nebK : K → K} (D : AtkinLehnerData θG ψ U Γ nebK)

/-! ### The Hecke operator through the local representatives -/

/-- The `U_p`-representatives of the Atkin–Lehner data: `v_c = ιp (p 0; cp 1)`. -/
def vRepD (c : Fin p) : G := D.ιp (vGL p (c : ℕ))

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem vRepD_mem_levelM1 (c : Fin p) : vRepD θG ψ U D c ∈ levelM1 (p := p) θG := by
  show θG (D.ιp (vGL p (c : ℕ))) ∈ M1 p
  rw [D.theta_ιp, coe_vGL]
  exact vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)

/-- The `U_p`-element `η = ιp (p 0; 0 1)`. -/
def upEltD : G := D.ιp (vGL p 0)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem upEltD_mem_levelM1 : upEltD θG ψ U D ∈ levelM1 (p := p) θG := by
  show θG (D.ιp (vGL p 0)) ∈ M1 p
  rw [D.theta_ιp, coe_vGL]
  exact vQ_mem_M1 (by rw [norm_zero]; exact zero_le_one)

omit [CharZero K] in
/-- **The naive Hecke formula**: `(U_p φ)(x) = ∑_c φ(x v_c⁻¹) ∣ v_c`
(`heckeOperatorSlash_eq_finsetSum` at the representatives, `AutomorphicFunction.slash_apply`). -/
theorem discHeckeOperator_apply_eq_sum
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D))
    (φ : DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) :
    ((discHeckeOperator θG 1 ψ κ U hU (upEltD_mem_levelM1 θG ψ U D) hfin φ :
        DiscForms (Γ := Γ) θG 1 ψ κ U hU) : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) x
      = ∑ c : Fin p, discSlash 1 ψ κ ⟨θG (vRepD θG ψ U D c), vRepD_mem_levelM1 θG ψ U D c⟩
          ((φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x * (vRepD θG ψ U D c)⁻¹)) := by
  letI := discLevelSlashAction θG 1 ψ κ
  letI := discLevelSMulSlashClass θG 1 ψ κ
  have hrep := AutomorphicFunction.heckeOperatorSlash_apply_rep (Γ := Γ) K hU
    (upEltD_mem_levelM1 θG ψ U D) hfin φ (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) hv hvinj x
    (fun t => x * (vRepD θG ψ U D t)⁻¹) (fun _ => 1) (fun _ => one_mem _) (fun _ => 1)
    (fun t => by simp) (fun t => by simpa using vRepD_mem_levelM1 θG ψ U D t)
  refine hrep.trans (Finset.sum_congr rfl fun t _ => ?_)
  show discSlash 1 ψ κ (levelM1ToM1 (p := p) θG ⟨((1 : U) : G) * vRepD θG ψ U D t, _⟩) _ = _
  congr 2
  apply Subtype.ext
  show θG (((1 : U) : G) * vRepD θG ψ U D t) = θG (vRepD θG ψ U D t)
  rw [OneMemClass.coe_one, one_mul]

/-! ### Disc `0` of the ingredients -/

omit [CharZero K] in
/-- Disc `0` of a classical-shape disc slash at a matrix fixing disc `0` is the nebentypus
constant times the `Sym^k`-action of the disc conjugate (`blockProj_discSlash`,
`kappaSlash_eq_smul_symAct_of_shape`). -/
theorem blockProj_zero_discSlash_of_shape {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (δ : M1 p) (hδ : discImage 1 δ 0 = 0) {f : c(ZMod (p ^ 1) × ℕ, K)}
    (hf : f ∈ locPolyDegSubmodule p K 1 k) :
    cSpace.blockProj 0 (discSlash 1 ψ κ δ f)
      = u (ψ ((discConj 1 δ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj 1 δ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 f) := by
  have hf' : cSpace.blockProj 0 f ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact hf 0 j hj
  rw [blockProj_discSlash, hδ]
  exact kappaSlash_eq_smul_symAct_of_shape κ (discConjK 1 δ 0 ψ) (hκ _) hf'

omit [CharZero K] in
/-- **The central element acts trivially**: `φ(x · ιp(p·1)) = φ(x)` on disc forms
(`AtkinLehnerData.central`: `ιp(p·1) = γ u` with `γ ∈ Γ` central and `θ u = 1`). -/
theorem apply_mul_ιp_pGL {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) :
    φ (x * D.ιp (pGL p)) = φ x := by
  obtain ⟨γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central
  rw [hP, ← mul_assoc, ← hcomm x, mul_assoc, AutomorphicFunction.left_invt' φ hγ]
  exact apply_mul_of_theta_eq_one θG ψ U hU κ hφ x hu hθu

omit [CharZero K] in
theorem apply_mul_ιp_pGL_inv {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) :
    φ (x * (D.ιp (pGL p))⁻¹) = φ x := by
  have h := apply_mul_ιp_pGL θG ψ U hU κ D hφ (x * (D.ιp (pGL p))⁻¹)
  rw [inv_mul_cancel_right] at h
  exact h.symm

omit [CharZero K] in
/-- Level-equivariance at a lift `ιp g` of an Iwahori element fixing disc `0`, read on disc `0`
(`blockProj_zero_apply_mul_mem_U` at `v = ιp g`, `ιp_mem_U`, `theta_ιp`). -/
theorem blockProj_zero_apply_mul_ιp {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) {g : GL (Fin 2) ℚ_[p]}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1)
    (hg0 : discImage 1 (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 = 0) :
    cSpace.blockProj 0 (φ (x * D.ιp g))
      = u (ψ ((discConj 1 (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 :
            Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj 1
          (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 :
            Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ x)) := by
  have he : (⟨θG (D.ιp g), hU (D.ιp_mem_U g hg)⟩ : M1 p) = ⟨g, Iw_one_le_M1 hg⟩ :=
    Subtype.ext (D.theta_ιp g)
  have hv0 : discImage 1 (⟨θG (D.ιp g), hU (D.ιp_mem_U g hg)⟩ : M1 p) 0 = 0 :=
    (congrArg (fun δ => discImage 1 δ 0) he).trans hg0
  have key : ∀ δ₁ δ₂ : M1 p, δ₁ = δ₂ →
      u (ψ ((discConj 1 δ₁ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj 1 δ₁ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 (φ x))
      = u (ψ ((discConj 1 δ₂ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj 1 δ₂ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 (φ x)) := by
    rintro _ _ rfl; rfl
  exact (blockProj_zero_apply_mul_mem_U θG ψ U hU k κ hκ hφ x ⟨D.ιp g, D.ιp_mem_U g hg⟩ hv0).trans
    (key _ _ he)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **The group element of the `(b,c)`-term**: `x v_c⁻¹ w v_b⁻¹ w⁻¹ = x s_b · (ιp p)⁻¹ · ℓ_{b,c}⁻¹`
(`wGL_mul_vGL_mul_wGL_inv_mul_vGL`, inverted). -/
theorem term_elt_eq (x : G) (b c : ℚ_[p]) :
    x * (D.ιp (vGL p c))⁻¹ * D.ιp (wGL p) * (D.ιp (vGL p b))⁻¹ * (D.ιp (wGL p))⁻¹
      = x * D.ιp (sGL p b) * (D.ιp (pGL p))⁻¹ * (D.ιp (ℓGL p b c))⁻¹ := by
  have h := congrArg (fun g => (D.ιp g)⁻¹) (wGL_mul_vGL_mul_wGL_inv_mul_vGL b c)
  have hs : (D.ιp (sGL p (-b)))⁻¹ = D.ιp (sGL p b) := by rw [← map_inv, sGL_inv, neg_neg]
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv, hs] at h
  simp only [mul_assoc] at h ⊢
  rw [h]

omit [CharZero K] in
/-- **Disc `0` of `φ(x s_b p⁻¹ ℓ⁻¹)`**: the central `p` acts trivially and `ℓ⁻¹` fixes disc `0`
with `d`-entry `1 − bcp`, so it is `nebK(1 − bcp) · symAct(conj ℓ⁻¹)(φ(x)|_b)`. -/
theorem blockProj_zero_apply_term_elt
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) (b c : Fin p) :
    cSpace.blockProj 0
        (φ (x * D.ιp (sGL p (b : ℕ)) * (D.ιp (pGL p))⁻¹ * (D.ιp (ℓGL p (b : ℕ) (c : ℕ)))⁻¹))
      = nebK (ψ (1 - (b : ℚ_[p]) * c * p)) •
        symAct K k (RingHom.mapMatrix ψ (tMatInv p 0 * ℓQinv p (b : ℕ) (c : ℕ) * tMat p 0))
          (cSpace.blockProj (b : ZMod (p ^ 1)) (φ x)) := by
  obtain ⟨γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central
  have hb : ‖((b : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  have hc : ‖((c : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  set y := x * D.ιp (sGL p (b : ℕ)) with hy
  set ℓ := D.ιp (ℓGL p (b : ℕ) (c : ℕ)) with hℓ
  have hℓU : ℓ ∈ U := D.ιp_mem_U _ (ℓQ_mem_Iw hb hc)
  have hγc : ∀ z, γ⁻¹ * z = z * γ⁻¹ := fun z => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm z, mul_inv_cancel_right]
  have e1 : y * (u⁻¹ * γ⁻¹) * ℓ⁻¹ = γ⁻¹ * (y * u⁻¹ * ℓ⁻¹) := by
    rw [hγc (y * u⁻¹ * ℓ⁻¹)]
    simp only [mul_assoc]
    rw [hγc]
  have e2 : y * u⁻¹ * ℓ⁻¹ = y * ℓ⁻¹ * (ℓ * u⁻¹ * ℓ⁻¹) := by group
  have hθinv : θG u⁻¹ = 1 := by
    have h := map_mul θG u u⁻¹
    rw [mul_inv_cancel, map_one, hθu, one_mul] at h
    exact h.symm
  have hθ1 : θG (ℓ * u⁻¹ * ℓ⁻¹) = 1 := by
    rw [map_mul, map_mul, hθinv, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have hmove : φ (y * (D.ιp (pGL p))⁻¹ * ℓ⁻¹) = φ (y * ℓ⁻¹) := by
    rw [hP, mul_inv_rev, e1, AutomorphicFunction.left_invt' φ (inv_mem hγ), e2]
    exact apply_mul_of_theta_eq_one θG ψ U hU κ hφ.1 _
      (mul_mem (mul_mem hℓU (inv_mem hu)) (inv_mem hℓU)) hθ1
  have hg : (((ℓGL p (b : ℕ) (c : ℕ))⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      ∈ Iw p 1 := by
    rw [coe_ℓGL_inv]; exact ℓQinv_mem_Iw hb hc
  have hgM : (⟨(((ℓGL p (b : ℕ) (c : ℕ))⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]),
      Iw_one_le_M1 hg⟩ : M1 p) = ⟨ℓQinv p (b : ℕ) (c : ℕ), Iw_one_le_M1 (ℓQinv_mem_Iw hb hc)⟩ :=
    Subtype.ext (coe_ℓGL_inv _ _)
  have hg0 : discImage 1 (⟨(((ℓGL p (b : ℕ) (c : ℕ))⁻¹ : GL (Fin 2) ℚ_[p]) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 = 0 :=
    (congrArg (fun δ => discImage 1 δ 0) hgM).trans (discImage_ℓQinv_zero hb hc)
  have hmain := blockProj_zero_apply_mul_ιp θG ψ U hU k κ D hκ hφ y hg hg0
  rw [map_inv] at hmain
  have hsh : cSpace.blockProj 0 (φ y) = cSpace.blockProj (b : ZMod (p ^ 1)) (φ x) := by
    rw [shapiro_blockProj θG ψ U hU D κ hφ.1 x (b : ZMod (p ^ 1)), ZMod.val_natCast,
      Nat.mod_eq_of_lt (by rw [pow_one]; exact b.isLt)]
  rw [hmove, hmain, hgM, discConj_ℓQinv_zero_one_one hb hc, coe_discConj,
    discConjMat_zero_of_discImage_zero _ (discImage_ℓQinv_zero hb hc), hsh]

/-! ### The identity -/

variable {UK' : Subgroup Kˣ} {ρ' : ℝ} (κ' : AnalyticWeight UK' (M1Kh 1 ψ) ρ')

/-- The `(b, c)`-term of the double-coset expansion, read on disc `0`: the outer `U_p`
contributes `symAct(conj v_c)`, `W'` contributes `χ(x v_c⁻¹) · symAct w₂⁻¹`, the inner
`U_p^{(ψ⁻¹)}` contributes `symAct(conj v_b)`, and `W` is evaluated at `x v_c⁻¹ w v_b⁻¹`.  With
`w v_b w⁻¹ v_c = ℓ_{b,c} · p · s_{−b}` the term is `ψ_neb(1 + bcp)⁻¹` times a vector independent
of `c`: `p^k · (disc b of φ(x)) ∣_k (1 −b/p; 0 1)`. -/
theorem atkinLehner_term_eq
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) (b c : Fin p) :
    symAct K k (RingHom.mapMatrix ψ (discConj 1 (⟨vQ p c, vQ_mem_M1 (by
        exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] c)⟩ : M1 p) 0 :
          Matrix (Fin 2) (Fin 2) ℚ_[p]))
      (((D.χ (x * (vRepD θG ψ U D c)⁻¹) : Kˣ) : K) •
        symAct K k (atkinLehnerKinv ψ)
          (symAct K k (RingHom.mapMatrix ψ (discConj 1 (⟨vQ p b, vQ_mem_M1 (by
              exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b)⟩ : M1 p) 0 :
                Matrix (Fin 2) (Fin 2) ℚ_[p]))
            (cSpace.blockProj 0
              ((atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ :
                  AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
                (x * (vRepD θG ψ U D c)⁻¹ * D.ιp (wGL p) * (vRepD θG ψ U D b)⁻¹)))))
      = (nebK (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ •
        ((ψ p) ^ k • symAct K k (RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1])
          (cSpace.blockProj (b : ZMod (p ^ 1)) (φ.1 x))) := by
  have hb : ‖((b : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  have hc : ‖((c : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  have hV : cSpace.blockProj (b : ZMod (p ^ 1)) (φ.1 x) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact φ.2.2 x _ j hj
  have hMb : ((discConj 1 (⟨vQ p (b : ℕ), vQ_mem_M1 hb⟩ : M1 p) 0 : M1 p) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) = tMatInv p 0 * vQ p (b : ℕ) * tMat p 0 := by
    rw [coe_discConj, discConjMat_zero_of_discImage_zero _ (discImage_vQ_zero hb)]
  have hMc : ((discConj 1 (⟨vQ p (c : ℕ), vQ_mem_M1 hc⟩ : M1 p) 0 : M1 p) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) = tMatInv p 0 * vQ p (c : ℕ) * tMat p 0 := by
    rw [coe_discConj, discConjMat_zero_of_discImage_zero _ (discImage_vQ_zero hc)]
  have hin : cSpace.blockProj 0
      ((atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ :
          AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
        (x * (vRepD θG ψ U D c)⁻¹ * D.ιp (wGL p) * (vRepD θG ψ U D b)⁻¹))
      = ((D.χ (x * (vRepD θG ψ U D c)⁻¹) : Kˣ) : K)⁻¹ • nebK (ψ (1 - (b : ℚ_[p]) * c * p)) •
        symAct K k (RingHom.mapMatrix ψ (tMatInv p 0 * ℓQinv p (b : ℕ) (c : ℕ) * tMat p 0)
          * atkinLehnerK ψ) (cSpace.blockProj (b : ZMod (p ^ 1)) (φ.1 x)) := by
    change cSpace.blockProj 0 (atkinLehnerFun θG ψ U k D φ.1 _) = _
    rw [atkinLehnerFun_blockProj_zero]
    have hχ : D.χ (x * (vRepD θG ψ U D c)⁻¹ * D.ιp (wGL p) * (vRepD θG ψ U D b)⁻¹)
        = D.χ (x * (vRepD θG ψ U D c)⁻¹) := by
      simp only [vRepD, map_mul, map_inv, D.χ_wGL, D.χ_vGL, inv_one, mul_one]
    have hy : x * (vRepD θG ψ U D c)⁻¹ * D.ιp (wGL p) * (vRepD θG ψ U D b)⁻¹ * (D.ιp (wGL p))⁻¹
        = x * D.ιp (sGL p (b : ℕ)) * (D.ιp (pGL p))⁻¹ * (D.ιp (ℓGL p (b : ℕ) (c : ℕ)))⁻¹ :=
      term_elt_eq θG ψ U D x (b : ℕ) (c : ℕ)
    rw [hχ, hy, blockProj_zero_apply_term_elt θG ψ U hU k κ D hκ φ.2 x b c, map_smul,
      symAct_mul k _ _ hV]
  have hscal : RingHom.mapMatrix ψ ((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
      = ψ (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hmat : RingHom.mapMatrix ψ (tMatInv p 0 * ℓQinv p (b : ℕ) (c : ℕ) * tMat p 0)
        * atkinLehnerK ψ
        * RingHom.mapMatrix ψ ((discConj 1 (⟨vQ p (b : ℕ), vQ_mem_M1 hb⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p]) * atkinLehnerKinv ψ
        * RingHom.mapMatrix ψ ((discConj 1 (⟨vQ p (c : ℕ), vQ_mem_M1 hc⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (ψ (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) K))
        * RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1] := by
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    rw [hMb, hMc, atkinLehnerK_eq, atkinLehnerKinv_eq, ← hscal, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tMat, tMatInv, ℓQinv, wQ, wQinv, vQ, Matrix.mul_apply, Fin.sum_univ_two, hp0] <;>
      field_simp <;> ring
  have hbcp : ‖(b : ℚ_[p]) * c * p‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, norm_mul, Padic.norm_p]
    calc ‖(b : ℚ_[p])‖ * ‖(c : ℚ_[p])‖ * (p : ℝ)⁻¹ ≤ 1 * 1 * (p : ℝ)⁻¹ := by gcongr
      _ = (p : ℝ)⁻¹ := by ring
  rw [hin]
  simp only [map_smul, smul_smul]
  rw [symAct_mul k _ _ hV, symAct_mul k _ _ hV, symAct_mul k _ _ hV, hmat, ← symAct_mul k _ _ hV,
    symAct_smul_one k _ hV, map_smul, smul_smul]
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul,
    nebK_one_sub_eq_inv ψ hmul hne hcond hbcp]

set_option maxHeartbeats 1000000 in
/-- **`U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}` on disc `0`**: the double-coset expansion, the
key factorisation, and the character sum. -/
theorem blockProj_zero_discHecke_atkinLehner
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebK (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ = 0)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) :
    cSpace.blockProj 0
      ((discHeckeOperatorCl θG ψ U hU k κ hκ (upEltD_mem_levelM1 θG ψ U D) hfin
        (atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ'
          (discHeckeOperatorCl θG ψ U hU k κ' (u := fun x => (nebK x)⁻¹) hκ'
            (upEltD_mem_levelM1 θG ψ U D) hfin
            (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ))) :
        AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) x)
      = (ψ p) ^ (k + 1) • cSpace.blockProj 0 (φ.1 x) := by
  have hnebK1 : nebK (ψ 1) = 1 := nebK_one ψ hcond
  have hvc : ∀ c : Fin p, (⟨θG (vRepD θG ψ U D c), vRepD_mem_levelM1 θG ψ U D c⟩ : M1 p)
      = ⟨vQ p (c : ℕ), vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)⟩ :=
    fun c => Subtype.ext (D.theta_ιp _)
  have hvc11 : ∀ c : Fin p, ((discConj 1 (⟨vQ p (c : ℕ),
      vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)⟩ : M1 p) 0 : M1 p) :
        Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 := fun c => by
    simp [vQ]
  set Φ₁ := atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ with hΦ₁
  set Φ₂ := discHeckeOperatorCl θG ψ U hU k κ' (u := fun x => (nebK x)⁻¹) hκ'
    (upEltD_mem_levelM1 θG ψ U D) hfin Φ₁ with hΦ₂
  set Φ₃ := atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' Φ₂ with hΦ₃
  have hin : ∀ y : G, cSpace.blockProj 0 (Φ₂.1 y) = ∑ b : Fin p,
      symAct K k (RingHom.mapMatrix ψ ((discConj 1 (⟨vQ p (b : ℕ),
        vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p]))
        (cSpace.blockProj 0 (Φ₁.1 (y * (vRepD θG ψ U D b)⁻¹))) := by
    intro y
    change cSpace.blockProj 0 ((discHeckeOperator θG 1 ψ κ' U hU (upEltD_mem_levelM1 θG ψ U D) hfin
      ⟨Φ₁.1, Φ₁.2.1⟩).1 y) = _
    rw [discHeckeOperator_apply_eq_sum θG ψ U hU κ' D hfin hv hvinj, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hvc b, blockProj_zero_discSlash_of_shape ψ k κ' (u := fun x => (nebK x)⁻¹) hκ' _
      (discImage_vQ_zero (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)) (Φ₁.2.2 _), hvc11]
    simp only [hnebK1, inv_one, one_smul]
  have hterm : ∀ c : Fin p,
      symAct K k (RingHom.mapMatrix ψ ((discConj 1 (⟨vQ p (c : ℕ),
        vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p]))
        (cSpace.blockProj 0 (Φ₃.1 (x * (vRepD θG ψ U D c)⁻¹)))
      = ∑ b : Fin p, (nebK (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ •
        ((ψ p) ^ k • symAct K k (RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1])
          (cSpace.blockProj (b : ZMod (p ^ 1)) (φ.1 x))) := by
    intro c
    change symAct K k _ (cSpace.blockProj 0
      (atkinLehnerFunInv θG ψ U k D Φ₂.1 (x * (vRepD θG ψ U D c)⁻¹))) = _
    rw [atkinLehnerFunInv_blockProj_zero, hin, map_sum, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact atkinLehner_term_eq θG ψ U hU k κ D κ' hmul hne hcond hκ hκ' φ x b c
  change cSpace.blockProj 0 ((discHeckeOperator θG 1 ψ κ U hU (upEltD_mem_levelM1 θG ψ U D) hfin
    ⟨Φ₃.1, Φ₃.2.1⟩).1 x) = _
  rw [discHeckeOperator_apply_eq_sum θG ψ U hU κ D hfin hv hvinj, map_sum]
  have hout : ∀ c : Fin p, cSpace.blockProj 0 (discSlash 1 ψ κ
      ⟨θG (vRepD θG ψ U D c), vRepD_mem_levelM1 θG ψ U D c⟩
        ((⟨Φ₃.1, Φ₃.2.1⟩ : DiscForms (Γ := Γ) θG 1 ψ κ U hU).1 (x * (vRepD θG ψ U D c)⁻¹)))
      = ∑ b : Fin p, (nebK (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ •
        ((ψ p) ^ k • symAct K k (RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1])
          (cSpace.blockProj (b : ZMod (p ^ 1)) (φ.1 x))) := by
    intro c
    rw [hvc c, blockProj_zero_discSlash_of_shape ψ k κ hκ _
      (discImage_vQ_zero (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)) (Φ₃.2.2 _), hvc11,
      hnebK1, one_smul]
    exact hterm c
  rw [Finset.sum_congr rfl fun c _ => hout c, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (0 : Fin p)]
  · haveI : NeZero p := ⟨hp.out.ne_zero⟩
    have hV0 : cSpace.blockProj 0 (φ.1 x) ∈ polySubmodule K k := fun j hj => by
      rw [cSpace.blockProj_apply]; exact φ.2.2 x 0 j hj
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, hnebK1, inv_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, zero_div, neg_zero]
    rw [← Matrix.one_fin_two, map_one, symAct_one k hV0, smul_smul, ← map_natCast ψ p, ← pow_succ']
  · intro b _ hb
    have hbp : ¬ p ∣ (b : ℕ) :=
      Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (fun h => hb (Fin.ext h))) b.isLt
    have hs : ∑ c : Fin p, (nebK (ψ (1 + ((b : ℕ) : ℚ_[p]) * ((c : ℕ) : ℚ_[p]) * p)))⁻¹ = 0 :=
      (Fin.sum_univ_eq_sum_range (fun c => (nebK (ψ (1 + ((b : ℕ) : ℚ_[p]) * (c : ℚ_[p]) * p)))⁻¹)
        p).trans (hsum b hbp)
    rw [hs, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h


set_option maxHeartbeats 1000000 in
/-- **The operator identity** `U_p ∘ (W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W) = p^{k+1}` on the classical disc
forms (`shapiro_blockProj` carries the disc-`0` identity to every disc). -/
theorem discHeckeCl_comp_atkinLehner
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebK (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ = 0)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D)) :
    (discHeckeOperatorCl θG ψ U hU k κ hκ (upEltD_mem_levelM1 θG ψ U D) hfin).comp
        ((atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ').comp
          ((discHeckeOperatorCl θG ψ U hU k κ' (u := fun x => (nebK x)⁻¹) hκ'
            (upEltD_mem_levelM1 θG ψ U D) hfin).comp
            (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ')))
      = (ψ p) ^ (k + 1) • LinearMap.id := by
  refine LinearMap.ext fun φ => Subtype.ext (AutomorphicFunction.ext fun x => ?_)
  refine cSpace_ext_blockProj fun a => ?_
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  set Ψ := ((discHeckeOperatorCl θG ψ U hU k κ hκ (upEltD_mem_levelM1 θG ψ U D) hfin).comp
      ((atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ').comp
        ((discHeckeOperatorCl θG ψ U hU k κ' (u := fun x => (nebK x)⁻¹) hκ'
          (upEltD_mem_levelM1 θG ψ U D) hfin).comp
          (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ')))) φ with hΨ
  have hL := shapiro_blockProj θG ψ U hU D κ Ψ.2.1 x a
  have hR := shapiro_blockProj θG ψ U hU D κ φ.2.1 x a
  rw [hL, Submodule.coe_smul, AutomorphicFunction.smul_apply, map_smul, hR]
  exact blockProj_zero_discHecke_atkinLehner θG ψ U hU k κ D κ' hmul hne hcond hsum hκ hκ' hfin hv
    hvinj φ _

/-! ### Transport to the block matrices, and hypothesis H1 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharZero K] in
/-- Under the block model at a neat level, the classical Hecke operator is the block operator
of the certificates restricted to the classical subspace (`discEvalAtReps_discHeckeOperator`). -/
theorem discEvalAtRepsCl_discHeckeOperatorCl {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D)) (idx : ι → Fin p → ι) (uu : ι → Fin p → U)
    (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRepD θG ψ U D t)⁻¹ = d i t * c (idx i t) * (uu i t : G))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    (discEvalAtRepsCl θG ψ U hU k κ hκ c hc hstab
        (discHeckeOperatorCl θG ψ U hU k κ hκ (upEltD_mem_levelM1 θG ψ U D) hfin φ) :
          c(ι × (ZMod (p ^ 1) × ℕ), K))
      = discHeckeBlockOp θG 1 ψ κ U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu
          (discEvalAtRepsCl θG ψ U hU k κ hκ c hc hstab φ) := by
  rw [discEvalAtRepsCl_apply, discEvalAtRepsCl_apply]
  exact discEvalAtReps_discHeckeOperator θG 1 ψ κ U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D)
    idx uu (upEltD_mem_levelM1 θG ψ U D) hfin c hv hvinj d hd hfact ⟨φ.1, φ.2.1⟩

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq ι] in
/-- **Hypothesis H1 transports along similarities**: if `A B = c • 1` with `B` conjugate to `A'`
in the abstract, the same holds after conjugating `A` and `A'` separately. -/
theorem atkinLehnerHypothesis_of_conj
    {A B A' S S' S₁ S₁' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ 1)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ 1))) K}
    (h : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k A B A')
    (hS : S₁ * S = 1) (hS' : S₁' * S' = 1) (_hS'' : S' * S₁' = 1) :
    AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (S * A * S₁) (S * B * S₁)
      (S' * A' * S₁') := by
  obtain ⟨hAB, P, Q, hQP, hA'⟩ := h
  have hSS₁ : S * S₁ = 1 := mul_eq_one_comm.mp hS
  refine ⟨?_, S' * P * S₁, S * Q * S₁', ?_, ?_⟩
  · calc S * A * S₁ * (S * B * S₁) = S * (A * (S₁ * S) * B) * S₁ := by simp only [Matrix.mul_assoc]
      _ = S * (A * B) * S₁ := by rw [hS, Matrix.mul_one]
      _ = (ψ p) ^ (k + 1) • (S * S₁) := by
        rw [hAB, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = _ := by rw [hSS₁]
  · calc S * Q * S₁' * (S' * P * S₁) = S * (Q * (S₁' * S') * P) * S₁ := by
          simp only [Matrix.mul_assoc]
      _ = S * (Q * P) * S₁ := by rw [hS', Matrix.mul_one]
      _ = 1 := by rw [hQP, Matrix.mul_one, hSS₁]
  · calc S' * A' * S₁' = S' * (P * (S₁ * S) * B * (S₁ * S) * Q) * S₁' := by
          rw [hA', hS, Matrix.mul_one, Matrix.mul_one]
      _ = S' * P * S₁ * (S * B * S₁) * (S * Q * S₁') := by simp only [Matrix.mul_assoc]

set_option maxHeartbeats 2000000 in
/-- **Hypothesis H1 at the classical points, from the Atkin–Lehner data.**  With `A` the matrix
of `U_p` at `(k, ψ)`, `A'` at the partner `(k, ψ⁻¹)` (nebentypus `ω⁻¹ω₀^{2k}`, point
`T_{χ_k}(ζ⁻¹)`), and `B := W⁻¹ A' W`: `A B = p^{k+1}` is `discHeckeCl_comp_atkinLehner` in
the block model, and `A' = W B W⁻¹` by construction. -/
theorem atkinLehnerHypothesis_of_atkinLehnerData [Nonempty ι]
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹)
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
    (hfact : ∀ i t, c i * (vRepD θG ψ U D t)⁻¹ = d i t * c (idx i t) * (uu i t : G)) :
    ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k
      ((classicalData ψ ω θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ
        hpK k).matrix idx) B
      ((classicalData ψ (partnerChar p ω k) θG U hU (vRepD θG ψ U D)
        (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ.inv hpK k).matrix idx) := by
  classical
  set cd := classicalData ψ ω θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ
    hpK k with hcd
  set cd' := classicalData ψ (partnerChar p ω k) θG U hU (vRepD θG ψ U D)
    (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ.inv hpK k with hcd'
  have hκ := autFactor_haloWeightH_classicalPoint_eq_nebCharK ψ ω k ζ hp2 hψ hζ cd.h0 cd.h1 cd.hT
  have hκ' := autFactor_haloWeightH_partner_eq_inv_nebCharK ψ ω k ζ hp2 hψ hζ cd'.h0 cd'.h1 cd'.hT
  have hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 →
      nebCharK ψ ω k ζ (ψ (x * y)) = nebCharK ψ ω k ζ (ψ x) * nebCharK ψ ω k ζ (ψ y) :=
    fun _ _ hx hy => nebCharK_psi_mul ψ ω k ζ hp2 hψ hζ hpK hx hy
  have hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebCharK ψ ω k ζ (ψ x) ≠ 0 :=
    fun _ hx => nebCharK_psi_ne_zero ψ ω k ζ hp2 hψ hζ hpK hx
  have hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebCharK ψ ω k ζ (ψ x) = 1 :=
    fun _ hx => nebCharK_psi_of_norm_sub_one_le_sq ψ ω k ζ hp2 hψ hζ hpK hx
  have hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebCharK ψ ω k ζ (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ = 0 :=
    fun _ hb => sum_inv_nebCharK_eq_zero ψ ω k ζ hp2 hψ hζ hpK hb
  haveI := finite_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) 1 k
  let bas := Module.finBasisOfFinrankEq K (locPolyDegSubmoduleBlock p ι K 1 k)
    (finrank_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) 1 k)
  set T := ((discHeckeBlockOp θG 1 ψ cd.weight U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D)
      idx uu : c(ι × (ZMod (p ^ 1) × ℕ), K) →ₗ[K] _).restrict
        (p := locPolyDegSubmoduleBlock p ι K 1 k) (q := locPolyDegSubmoduleBlock p ι K 1 k)
        (fun _ hf => mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG 1 ψ U hU
          (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu cd.weight cd.shape hf)) with hT
  set T' := ((discHeckeBlockOp θG 1 ψ cd'.weight U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D)
      idx uu : c(ι × (ZMod (p ^ 1) × ℕ), K) →ₗ[K] _).restrict
        (p := locPolyDegSubmoduleBlock p ι K 1 k) (q := locPolyDegSubmoduleBlock p ι K 1 k)
        (fun _ hf => mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG 1 ψ U hU
          (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu cd'.weight cd'.shape hf)) with hT'
  have hA : cd.matrix idx = LinearMap.toMatrix bas bas T := rfl
  have hA' : cd'.matrix idx = LinearMap.toMatrix bas bas T' := rfl
  set E := discEvalAtRepsCl θG ψ U hU k cd.weight hκ c hc hstab with hE
  set E' := discEvalAtRepsCl θG ψ U hU k cd'.weight (u := fun x => (nebCharK ψ ω k ζ x)⁻¹) hκ' c hc
    hstab with hE'
  set AL := atkinLehnerEquiv θG ψ U hU k D cd.weight cd'.weight hmul hne hcond hκ hκ' with hAL
  set Wb : locPolyDegSubmoduleBlock p ι K 1 k ≃ₗ[K] locPolyDegSubmoduleBlock p ι K 1 k :=
    E.symm.trans (AL.trans E') with hWb
  have hTE : ∀ g, T (E g) = E (discHeckeOperatorCl θG ψ U hU k cd.weight hκ
      (upEltD_mem_levelM1 θG ψ U D) hfin g) := fun g =>
    Subtype.ext (discEvalAtRepsCl_discHeckeOperatorCl θG ψ U hU k cd.weight D hκ hfin c hc hstab hv
      hvinj idx uu d hd hfact g).symm
  have hTE' : ∀ g, T' (E' g) = E' (discHeckeOperatorCl θG ψ U hU k cd'.weight
      (u := fun x => (nebCharK ψ ω k ζ x)⁻¹) hκ' (upEltD_mem_levelM1 θG ψ U D) hfin g) := fun g =>
    Subtype.ext (discEvalAtRepsCl_discHeckeOperatorCl θG ψ U hU k cd'.weight D
      (u := fun x => (nebCharK ψ ω k ζ x)⁻¹) hκ' hfin c hc hstab hv hvinj idx uu d hd hfact g).symm
  have hkey : T ∘ₗ (Wb.symm.toLinearMap ∘ₗ T' ∘ₗ Wb.toLinearMap)
      = (ψ p) ^ (k + 1) • LinearMap.id := by
    refine LinearMap.ext fun f => ?_
    obtain ⟨g, rfl⟩ := E.surjective f
    have h1 : Wb (E g) = E' (AL g) := by
      rw [hWb, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have h2 : ∀ χ, Wb.symm (E' χ) = E (AL.symm χ) := fun χ => by
      rw [hWb, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    have h3 := LinearMap.congr_fun (discHeckeCl_comp_atkinLehner θG ψ U hU k cd.weight D cd'.weight
      hmul hne hcond hsum hκ hκ' hfin hv hvinj) g
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      LinearMap.id_apply] at h3 ⊢
    rw [h1, hTE', h2, hTE]
    change E (discHeckeOperatorCl θG ψ U hU k cd.weight hκ (upEltD_mem_levelM1 θG ψ U D) hfin
      (atkinLehnerMapInv θG ψ U hU k D cd.weight cd'.weight hmul hne hcond hκ hκ'
        (discHeckeOperatorCl θG ψ U hU k cd'.weight (u := fun x => (nebCharK ψ ω k ζ x)⁻¹) hκ'
          (upEltD_mem_levelM1 θG ψ U D) hfin
          (atkinLehnerMap θG ψ U hU k D cd.weight cd'.weight hmul hne hcond hκ hκ' g)))) = _
    rw [h3, map_smul]
  refine ⟨LinearMap.toMatrix bas bas (Wb.symm.toLinearMap ∘ₗ T' ∘ₗ Wb.toLinearMap), ?_,
    LinearMap.toMatrix bas bas Wb.toLinearMap, LinearMap.toMatrix bas bas Wb.symm.toLinearMap, ?_, ?_⟩
  · rw [hA, ← LinearMap.toMatrix_comp, hkey, map_smul, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp, LinearEquiv.symm_comp, LinearMap.toMatrix_id]
  · have hcomp : (Wb.toLinearMap ∘ₗ (Wb.symm.toLinearMap ∘ₗ T' ∘ₗ Wb.toLinearMap))
        ∘ₗ Wb.symm.toLinearMap = T' := LinearMap.ext fun f => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hA', ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, hcomp]


/-- **[LWX, Thm 1.3]'s degree formula with no hypothesis left**, granted the adelic data:
`deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})`. -/
theorem degX_succ_of_atkinLehnerData [Nonempty ι] [IsAlgClosed K]
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
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
      (vRepD_mem_levelM1 θG ψ U D) uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu i t :
      Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p) :
    degX (UpDatum.ofCerts θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu hshape)
        ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu
          hshape) (partnerChar p ω k)
        + ordDim (UpDatum.ofCerts θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu
          hshape) (targetChar p ω k) :=
  degX_succ_classicalPoint idx hp2 hψ hshape hdet hζ hζ.inv ω (partnerChar p ω k) k
    (atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ (norm_natCast_p ψ hψ) D hfin
      hv hvinj c hc hstab idx uu d hd hfact)

end LWX

end
