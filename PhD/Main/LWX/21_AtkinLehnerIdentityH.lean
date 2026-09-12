/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«20_AtkinLehnerMapH»
import PhD.Main.LWX.«19_AtkinLehnerIdentity»

/-!
# `U_p ∘ U'_p = p^{k+1}` and hypothesis H1 at conductor `p^{h+1}`

`19_AtkinLehnerIdentity.lean` at analyticity level `h`.  With `U'_p := W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W`,
`U_p ∘ U'_p = p^{k+1}` on the classical disc forms of `(k, ψ)`, `ψ` of conductor `p^{h+1}`:
the composite at `x` is `∑_{b,c} φ(x·(w_h v_b w_h⁻¹ v_c)⁻¹) ∣_k (w_h v_b w_h⁻¹ v_c)`, and the
key factorisation `w_h v_b w_h⁻¹ v_c = ℓ_{b,c} · (p·1) · s_{−b p^{h−1}}`
(`wGLH_mul_vGL_mul_wGLH_inv_mul_vGL`) with `ℓ_{b,c} ∈ Iw_p` fixing disc `0` turns the
`(b,c)`-term into `ψ_neb(1 + bcp^h)⁻¹ · (p^k · (disc `b p^{h−1}` of φ(x)) ∣_k n(−b/p))`.
Summing over `c`: the `b = 0` terms give `p·p^k·φ(x)`, and for `b ≠ 0` the sum
`∑_c ψ_neb(1 + bcp^h)⁻¹` vanishes because the conductor is exactly `p^{h+1}`
(`sum_inv_nebCharKH_eq_zero`).  The disc-coordinate translation `n(−b/p) = (1, −b/p; 0, 1)` is
the same at every level (`t₀⁻¹ s_{−b p^{h−1}} t₀` with `t₀ = (p^h 0; 0 1)`).

**The deliverable**: `atkinLehnerHypothesis_of_atkinLehnerDataH` — hypothesis H1 of
`13_AtkinLehnerInst.lean` at level `h` holds at the classical points of conductor `p^{h+1}`, with
the partner datum at the nebentypus `ω⁻¹ω₀^{2k}` and the point `T_{χ_k}(ζ⁻¹)`.  This is
[LWX, Prop 3.22] at conductor `p^m`, `m = h + 1`, as used in [LWX, §4.2]
(`lwx.txt:2340–2344`), without Jacquet–Langlands.
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
variable (h : ℕ) (k : ℕ) {UK : Subgroup Kˣ} {ρ : ℝ} (κ : AnalyticWeight UK (M1Kh h ψ) ρ)
variable {nebK : K → K} (D : AtkinLehnerDataH θG ψ U h Γ nebK)

/-! ### The Hecke operator through the local representatives -/

/-- The `U_p`-representatives of the level-`h` Atkin–Lehner data: `v_c = ιp (p 0; cp 1)`
(unchanged from level `1`: `U_p` is the `Iw_p`-double coset at every level). -/
def vRepDH (c : Fin p) : G := D.ιp (vGL p (c : ℕ))

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem vRepDH_mem_levelM1 (c : Fin p) : vRepDH θG ψ U h D c ∈ levelM1 (p := p) θG := by
  show θG (D.ιp (vGL p (c : ℕ))) ∈ M1 p
  rw [D.theta_ιp, coe_vGL]
  exact vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)

/-- The `U_p`-element `η = ιp (p 0; 0 1)`. -/
def upEltDH : G := D.ιp (vGL p 0)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem upEltDH_mem_levelM1 : upEltDH θG ψ U h D ∈ levelM1 (p := p) θG := by
  show θG (D.ιp (vGL p 0)) ∈ M1 p
  rw [D.theta_ιp, coe_vGL]
  exact vQ_mem_M1 (by rw [norm_zero]; exact zero_le_one)

omit [CharZero K] in
/-- **The naive Hecke formula** at level `h`: `(U_p φ)(x) = ∑_c φ(x v_c⁻¹) ∣ v_c`. -/
theorem discHeckeOperator_apply_eq_sumH
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D))
    (φ : DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) :
    ((discHeckeOperator θG h ψ κ U hU (upEltDH_mem_levelM1 θG ψ U h D) hfin φ :
        DiscForms (Γ := Γ) θG h ψ κ U hU) : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) x
      = ∑ c : Fin p, discSlash h ψ κ ⟨θG (vRepDH θG ψ U h D c), vRepDH_mem_levelM1 θG ψ U h D c⟩
          ((φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
            (x * (vRepDH θG ψ U h D c)⁻¹)) := by
  letI := discLevelSlashAction θG h ψ κ
  letI := discLevelSMulSlashClass θG h ψ κ
  have hrep := AutomorphicFunction.heckeOperatorSlash_apply_rep (Γ := Γ) K hU
    (upEltDH_mem_levelM1 θG ψ U h D) hfin φ (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D)
    hv hvinj x (fun t => x * (vRepDH θG ψ U h D t)⁻¹) (fun _ => 1) (fun _ => one_mem _)
    (fun _ => 1) (fun t => by simp) (fun t => by simpa using vRepDH_mem_levelM1 θG ψ U h D t)
  refine hrep.trans (Finset.sum_congr rfl fun t _ => ?_)
  show discSlash h ψ κ (levelM1ToM1 (p := p) θG ⟨((1 : U) : G) * vRepDH θG ψ U h D t, _⟩) _ = _
  congr 2
  apply Subtype.ext
  show θG (((1 : U) : G) * vRepDH θG ψ U h D t) = θG (vRepDH θG ψ U h D t)
  rw [OneMemClass.coe_one, one_mul]

/-! ### Disc `0` of the ingredients -/

omit [CharZero K] in
/-- Disc `0` of a classical-shape disc slash at a matrix fixing disc `0` is the nebentypus
constant times the `Sym^k`-action of the disc conjugate. -/
theorem blockProj_zero_discSlash_of_shapeH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (δ : M1 p) (hδ : discImage h δ 0 = 0) {f : c(ZMod (p ^ h) × ℕ, K)}
    (hf : f ∈ locPolyDegSubmodule p K h k) :
    cSpace.blockProj 0 (discSlash h ψ κ δ f)
      = u (ψ ((discConj h δ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj h δ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 f) := by
  have hf' : cSpace.blockProj 0 f ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact hf 0 j hj
  rw [blockProj_discSlash, hδ]
  exact kappaSlash_eq_smul_symAct_of_shape κ (discConjK h δ 0 ψ) (hκ _) hf'

omit [CharZero K] in
/-- **The central element acts trivially** on level-`h` disc forms. -/
theorem apply_mul_ιp_pGLH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) :
    φ (x * D.ιp (pGL p)) = φ x := by
  obtain ⟨γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central
  rw [hP, ← mul_assoc, ← hcomm x, mul_assoc, AutomorphicFunction.left_invt' φ hγ]
  exact apply_mul_of_theta_eq_oneH θG ψ U hU h κ hφ x hu hθu

omit [CharZero K] in
theorem apply_mul_ιp_pGL_invH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) :
    φ (x * (D.ιp (pGL p))⁻¹) = φ x := by
  have hres := apply_mul_ιp_pGLH θG ψ U hU h κ D hφ (x * (D.ιp (pGL p))⁻¹)
  rw [inv_mul_cancel_right] at hres
  exact hres.symm

omit [CharZero K] in
/-- Level-equivariance at a lift `ιp g` of an Iwahori element fixing disc `0`, read on disc `0`
(`blockProj_zero_apply_mul_mem_UH`). -/
theorem blockProj_zero_apply_mul_ιpH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) {g : GL (Fin 2) ℚ_[p]}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1)
    (hg0 : discImage h (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 = 0) :
    cSpace.blockProj 0 (φ (x * D.ιp g))
      = u (ψ ((discConj h (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 :
            Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj h
          (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 :
            Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ x)) := by
  have he : (⟨θG (D.ιp g), hU (D.ιp_mem_U g hg)⟩ : M1 p) = ⟨g, Iw_one_le_M1 hg⟩ :=
    Subtype.ext (D.theta_ιp g)
  have hv0 : discImage h (⟨θG (D.ιp g), hU (D.ιp_mem_U g hg)⟩ : M1 p) 0 = 0 :=
    (congrArg (fun δ => discImage h δ 0) he).trans hg0
  have key : ∀ δ₁ δ₂ : M1 p, δ₁ = δ₂ →
      u (ψ ((discConj h δ₁ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj h δ₁ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 (φ x))
      = u (ψ ((discConj h δ₂ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj h δ₂ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 (φ x)) := by
    rintro _ _ rfl; rfl
  exact (blockProj_zero_apply_mul_mem_UH θG ψ U hU h k κ hκ hφ x
    ⟨D.ιp g, D.ιp_mem_U g hg⟩ hv0).trans (key _ _ he)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **The group element of the `(b,c)`-term** at level `h`:
`x v_c⁻¹ w_h v_b⁻¹ w_h⁻¹ = x s_{b p^{h−1}} · (ιp p)⁻¹ · ℓ_{b,c}⁻¹`
(`wGLH_mul_vGL_mul_wGLH_inv_mul_vGL`, inverted). -/
theorem term_elt_eqH (x : G) (b c : ℚ_[p]) :
    x * (D.ιp (vGL p c))⁻¹ * D.ιp (wGLH p h) * (D.ιp (vGL p b))⁻¹ * (D.ιp (wGLH p h))⁻¹
      = x * D.ιp (sGL p (b * (p : ℚ_[p]) ^ h / p)) * (D.ιp (pGL p))⁻¹
        * (D.ιp (ℓGLH p h b c))⁻¹ := by
  have hres := congrArg (fun g => (D.ιp g)⁻¹) (wGLH_mul_vGL_mul_wGLH_inv_mul_vGL h b c)
  have hs : (D.ιp (sGL p (-(b * (p : ℚ_[p]) ^ h / p))))⁻¹
      = D.ιp (sGL p (b * (p : ℚ_[p]) ^ h / p)) := by
    rw [← map_inv, sGL_inv, neg_neg]
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv, hs] at hres
  simp only [mul_assoc] at hres ⊢
  rw [hres]

omit [CharZero K] in
/-- **Disc `0` of `φ(x s_{b p^{h−1}} p⁻¹ ℓ⁻¹)`**: the central `p` acts trivially and `ℓ⁻¹` fixes
disc `0` with `d`-entry `1 − bcp^h`, so it is
`nebK(1 − bcp^h) · symAct(conj ℓ⁻¹)(φ(x)|_{b p^{h−1}})`. -/
theorem blockProj_zero_apply_term_eltH (hh : 0 < h)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) (b c : Fin p) :
    cSpace.blockProj 0
        (φ (x * D.ιp (sGL p ((b : ℕ) * (p : ℚ_[p]) ^ h / p)) * (D.ιp (pGL p))⁻¹
          * (D.ιp (ℓGLH p h (b : ℕ) (c : ℕ)))⁻¹))
      = nebK (ψ (1 - (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)) •
        symAct K k (RingHom.mapMatrix ψ (tMatHInv p h 0 * ℓQHinv p h (b : ℕ) (c : ℕ)
          * tMatH p h 0))
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ x)) := by
  obtain ⟨γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central
  have hb : ‖((b : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  have hc : ‖((c : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  set y := x * D.ιp (sGL p ((b : ℕ) * (p : ℚ_[p]) ^ h / p)) with hy
  set ℓ := D.ιp (ℓGLH p h (b : ℕ) (c : ℕ)) with hℓ
  have hℓU : ℓ ∈ U := D.ιp_mem_U _ (ℓQH_mem_Iw hh hb hc)
  have hγc : ∀ z, γ⁻¹ * z = z * γ⁻¹ := fun z => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm z, mul_inv_cancel_right]
  have e1 : y * (u⁻¹ * γ⁻¹) * ℓ⁻¹ = γ⁻¹ * (y * u⁻¹ * ℓ⁻¹) := by
    rw [hγc (y * u⁻¹ * ℓ⁻¹)]
    simp only [mul_assoc]
    rw [hγc]
  have e2 : y * u⁻¹ * ℓ⁻¹ = y * ℓ⁻¹ * (ℓ * u⁻¹ * ℓ⁻¹) := by group
  have hθinv : θG u⁻¹ = 1 := by
    have hm := map_mul θG u u⁻¹
    rw [mul_inv_cancel, map_one, hθu, one_mul] at hm
    exact hm.symm
  have hθ1 : θG (ℓ * u⁻¹ * ℓ⁻¹) = 1 := by
    rw [map_mul, map_mul, hθinv, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have hmove : φ (y * (D.ιp (pGL p))⁻¹ * ℓ⁻¹) = φ (y * ℓ⁻¹) := by
    rw [hP, mul_inv_rev, e1, AutomorphicFunction.left_invt' φ (inv_mem hγ), e2]
    exact apply_mul_of_theta_eq_oneH θG ψ U hU h κ hφ.1 _
      (mul_mem (mul_mem hℓU (inv_mem hu)) (inv_mem hℓU)) hθ1
  have hg : (((ℓGLH p h (b : ℕ) (c : ℕ))⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      ∈ Iw p 1 := by
    rw [coe_ℓGLH_inv]; exact ℓQHinv_mem_Iw hh hb hc
  have hgM : (⟨(((ℓGLH p h (b : ℕ) (c : ℕ))⁻¹ : GL (Fin 2) ℚ_[p]) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p)
      = ⟨ℓQHinv p h (b : ℕ) (c : ℕ), Iw_one_le_M1 (ℓQHinv_mem_Iw hh hb hc)⟩ :=
    Subtype.ext (coe_ℓGLH_inv _ _ _)
  have hg0 : discImage h (⟨(((ℓGLH p h (b : ℕ) (c : ℕ))⁻¹ : GL (Fin 2) ℚ_[p]) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 = 0 :=
    (congrArg (fun δ => discImage h δ 0) hgM).trans (discImage_ℓQHinv_zero hh hb hc)
  have hmain := blockProj_zero_apply_mul_ιpH θG ψ U hU h k κ D hκ hφ y hg hg0
  rw [map_inv] at hmain
  have hsh : cSpace.blockProj 0 (φ y)
      = cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ x) := by
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    haveI : NeZero (p ^ (h' + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    have hlt : (b : ℕ) * p ^ (h' + 1 - 1) < p ^ (h' + 1) := by
      rw [Nat.add_sub_cancel, pow_succ]
      nlinarith [b.isLt, pow_pos hp.out.pos h']
    have hcast : (((b : ℕ) * p ^ (h' + 1 - 1) : ℕ) : ℚ_[p])
        = ((b : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ (h' + 1) / p := by
      rw [Nat.add_sub_cancel, pow_succ]
      push_cast
      rw [mul_div_assoc, mul_div_cancel_right₀ _ hp0]
    rw [shapiro_blockProjH θG ψ U hU (h' + 1) D κ hφ.1 x
      ((((b : ℕ) * p ^ (h' + 1 - 1) : ℕ) : ZMod (p ^ (h' + 1)))), ZMod.val_natCast,
      Nat.mod_eq_of_lt hlt, hcast]
  rw [hmove, hmain, hgM, discConj_ℓQHinv_zero_one_one hh hb hc, coe_discConj,
    discConjMat_zero_of_discImage_zero_prime_pow h _ (discImage_ℓQHinv_zero hh hb hc), hsh]

/-! ### The identity -/

variable {UK' : Subgroup Kˣ} {ρ' : ℝ} (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ')

omit [CharZero K] in
/-- The `(b, c)`-term of the double-coset expansion at level `h`, read on disc `0`: with
`w_h v_b w_h⁻¹ v_c = ℓ_{b,c} · p · s_{−b p^{h−1}}` the term is `ψ_neb(1 + bcp^h)⁻¹` times a
vector independent of `c`: `p^k · (disc `b p^{h−1}` of φ(x)) ∣_k (1 −b/p; 0 1)`. -/
theorem atkinLehner_term_eqH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) (b c : Fin p) :
    symAct K k (RingHom.mapMatrix ψ (discConj h (⟨vQ p (c : ℕ), vQ_mem_M1 (by
        exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] (c : ℕ))⟩ : M1 p) 0 :
          Matrix (Fin 2) (Fin 2) ℚ_[p]))
      (((D.χ (x * (vRepDH θG ψ U h D c)⁻¹) : Kˣ) : K) •
        symAct K k (atkinLehnerKHinv ψ h)
          (symAct K k (RingHom.mapMatrix ψ (discConj h (⟨vQ p (b : ℕ), vQ_mem_M1 (by
              exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] (b : ℕ))⟩ : M1 p) 0 :
                Matrix (Fin 2) (Fin 2) ℚ_[p]))
            (cSpace.blockProj 0
              ((atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ :
                  AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
                (x * (vRepDH θG ψ U h D c)⁻¹ * D.ιp (wGLH p h)
                  * (vRepDH θG ψ U h D b)⁻¹)))))
      = (nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ •
        ((ψ p) ^ k • symAct K k (RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1])
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ.1 x))) := by
  have hb : ‖((b : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  have hc : ‖((c : ℕ) : ℚ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  have hV : cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ.1 x)
      ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact φ.2.2 x _ j hj
  have hMb : ((discConj h (⟨vQ p (b : ℕ), vQ_mem_M1 hb⟩ : M1 p) 0 : M1 p) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) = tMatHInv p h 0 * vQ p (b : ℕ) * tMatH p h 0 := by
    rw [coe_discConj, discConjMat_zero_of_discImage_zero_prime_pow h _
      (discImage_vQ_zero_prime_pow h hb)]
  have hMc : ((discConj h (⟨vQ p (c : ℕ), vQ_mem_M1 hc⟩ : M1 p) 0 : M1 p) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) = tMatHInv p h 0 * vQ p (c : ℕ) * tMatH p h 0 := by
    rw [coe_discConj, discConjMat_zero_of_discImage_zero_prime_pow h _
      (discImage_vQ_zero_prime_pow h hc)]
  have hin : cSpace.blockProj 0
      ((atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ :
          AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
        (x * (vRepDH θG ψ U h D c)⁻¹ * D.ιp (wGLH p h) * (vRepDH θG ψ U h D b)⁻¹))
      = ((D.χ (x * (vRepDH θG ψ U h D c)⁻¹) : Kˣ) : K)⁻¹ •
        nebK (ψ (1 - (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)) •
        symAct K k (RingHom.mapMatrix ψ (tMatHInv p h 0 * ℓQHinv p h (b : ℕ) (c : ℕ)
          * tMatH p h 0) * atkinLehnerKH ψ h)
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ.1 x)) := by
    change cSpace.blockProj 0 (atkinLehnerFunH θG ψ U h k D φ.1 _) = _
    rw [atkinLehnerFunH_blockProj_zero]
    have hχ : D.χ (x * (vRepDH θG ψ U h D c)⁻¹ * D.ιp (wGLH p h) * (vRepDH θG ψ U h D b)⁻¹)
        = D.χ (x * (vRepDH θG ψ U h D c)⁻¹) := by
      simp only [vRepDH, map_mul, map_inv, D.χ_wGLH, D.χ_vGL, inv_one, mul_one]
    have hy : x * (vRepDH θG ψ U h D c)⁻¹ * D.ιp (wGLH p h) * (vRepDH θG ψ U h D b)⁻¹
          * (D.ιp (wGLH p h))⁻¹
        = x * D.ιp (sGL p ((b : ℕ) * (p : ℚ_[p]) ^ h / p)) * (D.ιp (pGL p))⁻¹
          * (D.ιp (ℓGLH p h (b : ℕ) (c : ℕ)))⁻¹ :=
      term_elt_eqH θG ψ U h D x (b : ℕ) (c : ℕ)
    rw [hχ, hy, blockProj_zero_apply_term_eltH θG ψ U hU h k κ D hh hκ φ.2 x b c, map_smul,
      symAct_mul k _ _ hV]
  have hscal : RingHom.mapMatrix ψ ((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
      = ψ (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hkey : tMatHInv p h 0 * ℓQHinv p h (b : ℕ) (c : ℕ) * tMatH p h 0
        * (tMatHInv p h 0 * wQH p h * tMatH p h 0)
        * (tMatHInv p h 0 * vQ p (b : ℕ) * tMatH p h 0)
        * (tMatHInv p h 0 * wQHinv p h * tMatH p h 0)
        * (tMatHInv p h 0 * vQ p (c : ℕ) * tMatH p h 0)
      = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) * !![1, -((b : ℚ_[p]) / p); 0, 1] := by
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
    have ht1 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], tMatH p h 0 * (tMatHInv p h 0 * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, tMatH_mul_tMatHInv, Matrix.one_mul]
    have hs : -(((b : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ h / p) / (p : ℚ_[p]) ^ h
        = -((b : ℚ_[p]) / p) := by
      rw [neg_div, div_div, mul_comm (p : ℚ_[p]) ((p : ℚ_[p]) ^ h), ← div_div,
        mul_div_cancel_right₀ _ hph]
    calc _ = tMatHInv p h 0 * (ℓQHinv p h (b : ℕ) (c : ℕ)
          * (wQH p h * vQ p (b : ℕ) * wQHinv p h * vQ p (c : ℕ))) * tMatH p h 0 := by
          simp only [Matrix.mul_assoc, ht1]
      _ = tMatHInv p h 0 * ((p : ℚ_[p]) • sQ p (-(((b : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ h / p)))
          * tMatH p h 0 := by
          rw [ℓQHinv_mul_wQH_mul_vQ_mul_wQHinv_mul_vQ]
      _ = (p : ℚ_[p]) • (tMatHInv p h 0 * sQ p (-(((b : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ h / p))
          * tMatH p h 0) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by
          rw [tMatHInv_zero_mul_sQ_mul_tMatH_zero, hs, smul_mul_assoc, one_mul]
  have hmat : RingHom.mapMatrix ψ (tMatHInv p h 0 * ℓQHinv p h (b : ℕ) (c : ℕ) * tMatH p h 0)
        * atkinLehnerKH ψ h
        * RingHom.mapMatrix ψ ((discConj h (⟨vQ p (b : ℕ), vQ_mem_M1 hb⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p]) * atkinLehnerKHinv ψ h
        * RingHom.mapMatrix ψ ((discConj h (⟨vQ p (c : ℕ), vQ_mem_M1 hc⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (ψ (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) K))
        * RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1] := by
    rw [hMb, hMc, atkinLehnerKH_eq, atkinLehnerKHinv_eq, ← hscal, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, ← map_mul, hkey]
  have hbcp : ‖(b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h‖ ≤ (p : ℝ)⁻¹ ^ h := by
    rw [norm_mul, norm_mul, norm_pow, Padic.norm_p]
    calc ‖(b : ℚ_[p])‖ * ‖(c : ℚ_[p])‖ * (p : ℝ)⁻¹ ^ h ≤ 1 * 1 * (p : ℝ)⁻¹ ^ h := by gcongr
      _ = (p : ℝ)⁻¹ ^ h := by ring
  rw [hin]
  simp only [map_smul, smul_smul]
  rw [symAct_mul k _ _ hV, symAct_mul k _ _ hV, symAct_mul k _ _ hV, hmat, ← symAct_mul k _ _ hV,
    symAct_smul_one k _ hV, map_smul, smul_smul]
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul,
    nebK_one_sub_eq_invH ψ h hh hmul hcond hbcp]

omit [CharZero K] in
set_option maxHeartbeats 1000000 in
/-- **`U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}` on disc `0`** at level `h`: the double-coset
expansion, the key factorisation, and the character sum `hsum`. -/
theorem blockProj_zero_discHecke_atkinLehnerH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ = 0)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) :
    cSpace.blockProj 0
      ((discHeckeOperatorClH θG ψ U hU h k κ hκ (upEltDH_mem_levelM1 θG ψ U h D) hfin
        (atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ'
          (discHeckeOperatorClH θG ψ U hU h k κ' (u := fun x => (nebK x)⁻¹) hκ'
            (upEltDH_mem_levelM1 θG ψ U h D) hfin
            (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ))) :
        AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) x)
      = (ψ p) ^ (k + 1) • cSpace.blockProj 0 (φ.1 x) := by
  have hnebK1 : nebK (ψ 1) = 1 := nebK_one_of_cond_pow ψ h hcond
  have hvc : ∀ c : Fin p, (⟨θG (vRepDH θG ψ U h D c), vRepDH_mem_levelM1 θG ψ U h D c⟩ : M1 p)
      = ⟨vQ p (c : ℕ), vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)⟩ :=
    fun c => Subtype.ext (D.theta_ιp _)
  have hvc11 : ∀ c : Fin p, ((discConj h (⟨vQ p (c : ℕ),
      vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)⟩ : M1 p) 0 : M1 p) :
        Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 := fun c => by
    simp [vQ]
  set Φ₁ := atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ with hΦ₁
  set Φ₂ := discHeckeOperatorClH θG ψ U hU h k κ' (u := fun x => (nebK x)⁻¹) hκ'
    (upEltDH_mem_levelM1 θG ψ U h D) hfin Φ₁ with hΦ₂
  set Φ₃ := atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' Φ₂ with hΦ₃
  have hin : ∀ y : G, cSpace.blockProj 0 (Φ₂.1 y) = ∑ b : Fin p,
      symAct K k (RingHom.mapMatrix ψ ((discConj h (⟨vQ p (b : ℕ),
        vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p]))
        (cSpace.blockProj 0 (Φ₁.1 (y * (vRepDH θG ψ U h D b)⁻¹))) := by
    intro y
    change cSpace.blockProj 0 ((discHeckeOperator θG h ψ κ' U hU (upEltDH_mem_levelM1 θG ψ U h D)
      hfin ⟨Φ₁.1, Φ₁.2.1⟩).1 y) = _
    rw [discHeckeOperator_apply_eq_sumH θG ψ U hU h κ' D hfin hv hvinj, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hvc b, blockProj_zero_discSlash_of_shapeH ψ h k κ' (u := fun x => (nebK x)⁻¹) hκ' _
      (discImage_vQ_zero_prime_pow h (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _))
      (Φ₁.2.2 _), hvc11]
    simp only [hnebK1, inv_one, one_smul]
  have hterm : ∀ c : Fin p,
      symAct K k (RingHom.mapMatrix ψ ((discConj h (⟨vQ p (c : ℕ),
        vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p]))
        (cSpace.blockProj 0 (Φ₃.1 (x * (vRepDH θG ψ U h D c)⁻¹)))
      = ∑ b : Fin p, (nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ •
        ((ψ p) ^ k • symAct K k (RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1])
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ.1 x))) := by
    intro c
    change symAct K k _ (cSpace.blockProj 0
      (atkinLehnerFunHInv θG ψ U h k D Φ₂.1 (x * (vRepDH θG ψ U h D c)⁻¹))) = _
    rw [atkinLehnerFunHInv_blockProj_zero, hin, map_sum, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact atkinLehner_term_eqH θG ψ U hU h k κ D κ' hh hmul hne hcond hκ hκ' φ x b c
  change cSpace.blockProj 0 ((discHeckeOperator θG h ψ κ U hU (upEltDH_mem_levelM1 θG ψ U h D)
    hfin ⟨Φ₃.1, Φ₃.2.1⟩).1 x) = _
  rw [discHeckeOperator_apply_eq_sumH θG ψ U hU h κ D hfin hv hvinj, map_sum]
  have hout : ∀ c : Fin p, cSpace.blockProj 0 (discSlash h ψ κ
      ⟨θG (vRepDH θG ψ U h D c), vRepDH_mem_levelM1 θG ψ U h D c⟩
        ((⟨Φ₃.1, Φ₃.2.1⟩ : DiscForms (Γ := Γ) θG h ψ κ U hU).1 (x * (vRepDH θG ψ U h D c)⁻¹)))
      = ∑ b : Fin p, (nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ •
        ((ψ p) ^ k • symAct K k (RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1])
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ.1 x))) := by
    intro c
    rw [hvc c, blockProj_zero_discSlash_of_shapeH ψ h k κ hκ _
      (discImage_vQ_zero_prime_pow h (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _))
      (Φ₃.2.2 _), hvc11, hnebK1, one_smul]
    exact hterm c
  rw [Finset.sum_congr rfl fun c _ => hout c, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (0 : Fin p)]
  · haveI : NeZero p := ⟨hp.out.ne_zero⟩
    have hV0 : cSpace.blockProj 0 (φ.1 x) ∈ polySubmodule K k := fun j hj => by
      rw [cSpace.blockProj_apply]; exact φ.2.2 x 0 j hj
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, hnebK1, inv_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, zero_div, neg_zero]
    rw [← Matrix.one_fin_two, map_one, symAct_one k hV0, smul_smul, ← map_natCast ψ p,
      ← pow_succ']
  · intro b _ hb
    have hbp : ¬ p ∣ (b : ℕ) :=
      Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (fun h0 => hb (Fin.ext h0))) b.isLt
    have hs : ∑ c : Fin p,
        (nebK (ψ (1 + ((b : ℕ) : ℚ_[p]) * ((c : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ h)))⁻¹ = 0 :=
      (Fin.sum_univ_eq_sum_range
        (fun c => (nebK (ψ (1 + ((b : ℕ) : ℚ_[p]) * (c : ℚ_[p]) * (p : ℚ_[p]) ^ h)))⁻¹) p).trans
        (hsum b hbp)
    rw [hs, zero_smul]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

omit [CharZero K] in
set_option maxHeartbeats 1000000 in
/-- **The operator identity** `U_p ∘ (W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W) = p^{k+1}` on the classical disc
forms at level `h` (`shapiro_blockProjH` carries the disc-`0` identity to every disc). -/
theorem discHeckeClH_comp_atkinLehnerH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ = 0)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D)) :
    (discHeckeOperatorClH θG ψ U hU h k κ hκ (upEltDH_mem_levelM1 θG ψ U h D) hfin).comp
        ((atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ').comp
          ((discHeckeOperatorClH θG ψ U hU h k κ' (u := fun x => (nebK x)⁻¹) hκ'
            (upEltDH_mem_levelM1 θG ψ U h D) hfin).comp
            (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ')))
      = (ψ p) ^ (k + 1) • LinearMap.id := by
  refine LinearMap.ext fun φ => Subtype.ext (AutomorphicFunction.ext fun x => ?_)
  refine cSpace_ext_blockProjH h fun a => ?_
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  set Ψ := ((discHeckeOperatorClH θG ψ U hU h k κ hκ (upEltDH_mem_levelM1 θG ψ U h D) hfin).comp
      ((atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ').comp
        ((discHeckeOperatorClH θG ψ U hU h k κ' (u := fun x => (nebK x)⁻¹) hκ'
          (upEltDH_mem_levelM1 θG ψ U h D) hfin).comp
          (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ')))) φ with hΨ
  have hL := shapiro_blockProjH θG ψ U hU h D κ Ψ.2.1 x a
  have hR := shapiro_blockProjH θG ψ U hU h D κ φ.2.1 x a
  rw [hL, Submodule.coe_smul, AutomorphicFunction.smul_apply, map_smul, hR]
  exact blockProj_zero_discHecke_atkinLehnerH θG ψ U hU h k κ D κ' hh hmul hne hcond hsum hκ hκ'
    hfin hv hvinj φ _

/-! ### Transport to the block matrices, and hypothesis H1 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharZero K] in
/-- Under the block model at a neat level, the classical Hecke operator at level `h` is the
block operator of the certificates restricted to the classical subspace
(`discEvalAtReps_discHeckeOperator`). -/
theorem discEvalAtRepsClH_discHeckeOperatorClH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D)) (idx : ι → Fin p → ι)
    (uu : ι → Fin p → U) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRepDH θG ψ U h D t)⁻¹ = d i t * c (idx i t) * (uu i t : G))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    (discEvalAtRepsClH θG ψ U hU h k κ hκ c hc hstab
        (discHeckeOperatorClH θG ψ U hU h k κ hκ (upEltDH_mem_levelM1 θG ψ U h D) hfin φ) :
          c(ι × (ZMod (p ^ h) × ℕ), K))
      = discHeckeBlockOp θG h ψ κ U hU (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D) idx
          uu (discEvalAtRepsClH θG ψ U hU h k κ hκ c hc hstab φ) := by
  rw [discEvalAtRepsClH_apply, discEvalAtRepsClH_apply]
  exact discEvalAtReps_discHeckeOperator θG h ψ κ U hU (vRepDH θG ψ U h D)
    (vRepDH_mem_levelM1 θG ψ U h D) idx uu (upEltDH_mem_levelM1 θG ψ U h D) hfin c hv hvinj d hd
    hfact ⟨φ.1, φ.2.1⟩

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq ι] in
/-- **Hypothesis H1 transports along similarities** at level `h`. -/
theorem atkinLehnerHypothesis_of_conjH
    {A B A' S S' S₁ S₁' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K}
    (hAL : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A B A')
    (hS : S₁ * S = 1) (hS' : S₁' * S' = 1) :
    AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (S * A * S₁) (S * B * S₁)
      (S' * A' * S₁') := by
  obtain ⟨hAB, P, Q, hQP, hA'⟩ := hAL
  have hSS₁ : S * S₁ = 1 := mul_eq_one_comm.mp hS
  refine ⟨?_, S' * P * S₁, S * Q * S₁', ?_, ?_⟩
  · calc S * A * S₁ * (S * B * S₁) = S * (A * (S₁ * S) * B) * S₁ := by
          simp only [Matrix.mul_assoc]
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
/-- **Hypothesis H1 at the classical points of conductor `p^{h+1}`, from the level-`h`
Atkin–Lehner data** ([LWX, Prop 3.22] at conductor `p^m`, `m = h + 1`).  With `A` the matrix
of `U_p` at `(k, ψ)`, `A'` at the partner `(k, ψ⁻¹)` (nebentypus `ω⁻¹ω₀^{2k}`, point
`T_{χ_k}(ζ⁻¹)`), and `B := W⁻¹ A' W`: `A B = p^{k+1}` is `discHeckeClH_comp_atkinLehnerH` in
the block model, and `A' = W B W⁻¹` by construction. -/
theorem atkinLehnerHypothesis_of_atkinLehnerDataH [Nonempty ι]
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹)
    (D : AtkinLehnerDataH θG ψ U h Γ (nebCharKH h ψ ω k ζ))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (idx : ι → Fin p → ι) (uu : ι → Fin p → U) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRepDH θG ψ U h D t)⁻¹ = d i t * c (idx i t) * (uu i t : G)) :
    ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k
      ((classicalDataH ψ ω θG U hU (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D) uu hp2
        hψ hh hζ hpK k).matrix idx) B
      ((classicalDataH ψ (partnerChar p ω k) θG U hU (vRepDH θG ψ U h D)
        (vRepDH_mem_levelM1 θG ψ U h D) uu hp2 hψ hh hζ.inv hpK k).matrix idx) := by
  classical
  set cd := classicalDataH ψ ω θG U hU (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D) uu hp2
    hψ hh hζ hpK k with hcd
  set cd' := classicalDataH ψ (partnerChar p ω k) θG U hU (vRepDH θG ψ U h D)
    (vRepDH_mem_levelM1 θG ψ U h D) uu hp2 hψ hh hζ.inv hpK k with hcd'
  have hκ := autFactor_haloWeightH_classicalPoint_eq_nebCharKH h ψ ω k ζ hp2 hψ hζ.pow_eq_one
    cd.h0 cd.h1 cd.hT
  have hκ' := autFactor_haloWeightH_partner_eq_inv_nebCharKH h ψ ω k ζ hp2 hψ hh hζ cd'.h0 cd'.h1
    cd'.hT
  have hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 →
      nebCharKH h ψ ω k ζ (ψ (x * y)) = nebCharKH h ψ ω k ζ (ψ x) * nebCharKH h ψ ω k ζ (ψ y) :=
    fun _ _ hx hy => nebCharKH_psi_mul h ψ ω k ζ hp2 hψ hh hζ hpK hx hy
  have hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebCharKH h ψ ω k ζ (ψ x) ≠ 0 :=
    fun _ hx => nebCharKH_psi_ne_zero h ψ ω k ζ hp2 hψ hh hζ hpK hx
  have hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebCharKH h ψ ω k ζ (ψ x) = 1 :=
    fun _ hx => nebCharKH_psi_of_norm_sub_one_le_pow h ψ ω k ζ hp2 hψ hh hζ hpK hx
  have hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p,
        (nebCharKH h ψ ω k ζ (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ = 0 :=
    fun _ hb => sum_inv_nebCharKH_eq_zero h ψ ω k ζ hp2 hψ hh hζ hpK hb
  haveI := finite_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k
  let bas := Module.finBasisOfFinrankEq K (locPolyDegSubmoduleBlock p ι K h k)
    (finrank_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k)
  set T := ((discHeckeBlockOp θG h ψ cd.weight U hU (vRepDH θG ψ U h D)
      (vRepDH_mem_levelM1 θG ψ U h D) idx uu : c(ι × (ZMod (p ^ h) × ℕ), K) →ₗ[K] _).restrict
        (p := locPolyDegSubmoduleBlock p ι K h k) (q := locPolyDegSubmoduleBlock p ι K h k)
        (fun _ hf => mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG h ψ U hU
          (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D) idx uu cd.weight cd.shape hf))
    with hT
  set T' := ((discHeckeBlockOp θG h ψ cd'.weight U hU (vRepDH θG ψ U h D)
      (vRepDH_mem_levelM1 θG ψ U h D) idx uu : c(ι × (ZMod (p ^ h) × ℕ), K) →ₗ[K] _).restrict
        (p := locPolyDegSubmoduleBlock p ι K h k) (q := locPolyDegSubmoduleBlock p ι K h k)
        (fun _ hf => mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG h ψ U hU
          (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D) idx uu cd'.weight cd'.shape hf))
    with hT'
  have hA : cd.matrix idx = LinearMap.toMatrix bas bas T := rfl
  have hA' : cd'.matrix idx = LinearMap.toMatrix bas bas T' := rfl
  set E := discEvalAtRepsClH θG ψ U hU h k cd.weight hκ c hc hstab with hE
  set E' := discEvalAtRepsClH θG ψ U hU h k cd'.weight (u := fun x => (nebCharKH h ψ ω k ζ x)⁻¹)
    hκ' c hc hstab with hE'
  set AL := atkinLehnerEquivH θG ψ U hU h k D cd.weight cd'.weight hh hmul hne hcond hκ hκ'
    with hAL
  set Wb : locPolyDegSubmoduleBlock p ι K h k ≃ₗ[K] locPolyDegSubmoduleBlock p ι K h k :=
    E.symm.trans (AL.trans E') with hWb
  have hTE : ∀ g, T (E g) = E (discHeckeOperatorClH θG ψ U hU h k cd.weight hκ
      (upEltDH_mem_levelM1 θG ψ U h D) hfin g) := fun g =>
    Subtype.ext (discEvalAtRepsClH_discHeckeOperatorClH θG ψ U hU h k cd.weight D hκ hfin c hc
      hstab hv hvinj idx uu d hd hfact g).symm
  have hTE' : ∀ g, T' (E' g) = E' (discHeckeOperatorClH θG ψ U hU h k cd'.weight
      (u := fun x => (nebCharKH h ψ ω k ζ x)⁻¹) hκ' (upEltDH_mem_levelM1 θG ψ U h D) hfin g) :=
    fun g => Subtype.ext (discEvalAtRepsClH_discHeckeOperatorClH θG ψ U hU h k cd'.weight D
      (u := fun x => (nebCharKH h ψ ω k ζ x)⁻¹) hκ' hfin c hc hstab hv hvinj idx uu d hd hfact
        g).symm
  have hkey : T ∘ₗ (Wb.symm.toLinearMap ∘ₗ T' ∘ₗ Wb.toLinearMap)
      = (ψ p) ^ (k + 1) • LinearMap.id := by
    refine LinearMap.ext fun f => ?_
    obtain ⟨g, rfl⟩ := E.surjective f
    have h1 : Wb (E g) = E' (AL g) := by
      rw [hWb, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have h2 : ∀ χ, Wb.symm (E' χ) = E (AL.symm χ) := fun χ => by
      rw [hWb, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    have h3 := LinearMap.congr_fun (discHeckeClH_comp_atkinLehnerH θG ψ U hU h k cd.weight D
      cd'.weight hh hmul hne hcond hsum hκ hκ' hfin hv hvinj) g
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      LinearMap.id_apply] at h3 ⊢
    rw [h1, hTE', h2, hTE]
    change E (discHeckeOperatorClH θG ψ U hU h k cd.weight hκ (upEltDH_mem_levelM1 θG ψ U h D) hfin
      (atkinLehnerMapHInv θG ψ U hU h k D cd.weight cd'.weight hh hmul hne hcond hκ hκ'
        (discHeckeOperatorClH θG ψ U hU h k cd'.weight (u := fun x => (nebCharKH h ψ ω k ζ x)⁻¹)
          hκ' (upEltDH_mem_levelM1 θG ψ U h D) hfin
          (atkinLehnerMapH θG ψ U hU h k D cd.weight cd'.weight hh hmul hne hcond hκ hκ' g)))) = _
    rw [h3, map_smul]
  refine ⟨LinearMap.toMatrix bas bas (Wb.symm.toLinearMap ∘ₗ T' ∘ₗ Wb.toLinearMap), ?_,
    LinearMap.toMatrix bas bas Wb.toLinearMap, LinearMap.toMatrix bas bas Wb.symm.toLinearMap, ?_,
    ?_⟩
  · rw [hA, ← LinearMap.toMatrix_comp, hkey, map_smul, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp, LinearEquiv.symm_comp, LinearMap.toMatrix_id]
  · have hcomp : (Wb.toLinearMap ∘ₗ (Wb.symm.toLinearMap ∘ₗ T' ∘ₗ Wb.toLinearMap))
        ∘ₗ Wb.symm.toLinearMap = T' := LinearMap.ext fun f => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hA', ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, hcomp]

end LWX

end
