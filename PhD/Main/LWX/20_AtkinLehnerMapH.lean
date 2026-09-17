/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«18_AtkinLehnerMap»
import PhD.Main.LWX.«19_NebCharH»
import PhD.Main.LWX.«11_AtkinLehnerLocalH»

/-!
# The Atkin–Lehner map on classical disc forms at conductor `p^{h+1}`

`18_AtkinLehnerMap.lean` at analyticity level `h`: [LWX, Prop 3.22] pairs
`S^D_{k+2}(K^pIw_{p^m}; ψ)` with `S^D_{k+2}(K^pIw_{p^m}; ψ⁻¹)` for a nebentypus `ψ` of
conductor `p^m` (`lwx.txt:1763–1768`; `m = h + 1`), and [LWX, §4.2] uses it at every
`m = M` ("by Atkin–Lehner theory (Proposition 3.22), in the `U_p`-slope sequence on
`S^D_{k+2}(K^pIw_{p^M}; ψ⁻¹)` …", `lwx.txt:2340–2344`).  Realised without Jacquet–Langlands
exactly as at level `1`: the Atkin–Lehner map `W : φ ↦ χ⁻¹ · (φ ∣ w_h)` with `w_h` the
Atkin–Lehner element of level `p^{h+1}` (`wQH h = (0 p^h; −p 0)` in the disc-model coordinate,
acting on the disc-`0` polynomial vectors through `t₀⁻¹ w_h t₀ = (0 1; −p^{h+1} 0)`,
`atkinLehnerKH`), and the twist by the Hecke character `χ = ψ_A ∘ ν`.

## The global data at level `h`

`AtkinLehnerDataH` is `AtkinLehnerData` with `w` replaced by `w_h` and the disc-`0` part of
the level replaced by the level-`p^{h+1}` part `{u ∈ U : p^h ∣ b(θ u)}`, which `w_h`
normalises (`wQH_conj_mem_Iw`).  The section `ιp`, the central element `ιp(p·1)` (with
`ιp_pGL_comm` and `central_pow`) and the character are unchanged; level `1` is
`AtkinLehnerData.toH`.

## The disc model at level `h`

The classical disc forms are the `U`-equivariant `φ : G → c(ℤ/p^h × ℕ, K)` with every value
locally polynomial of degree `≤ k` on each of the `p^h` discs
(`locPolyDegSubmodule p K h k`, [LWX, §2.3]'s `LP^{m−1,≤k}`); disc `a ∈ ℤ/p^h` of `φ(x)` is
disc `0` of `φ(x·s_a)` (`shapiro_blockProjH`); `nebK(a)·nebK(d) = nebK(det)` on the
level-`p^{h+1}` part because `bc/det ∈ p^{h+1}ℤ_p` there and the conductor is `p^{h+1}`
(`nebK_mul_nebK_eq_nebK_detH`, `hcond` at `p^{−(h+1)}`).  Everything else is the level-`1`
argument with `1` replaced by `h`.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash RightSlashAction
open scoped TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The level-`h` local elements as elements of `GL₂(ℚ_p)` -/

variable (p) in
/-- The Atkin–Lehner element `(0 p^h; −p 0)` of level `p^{h+1}` as an element of `GL₂(ℚ_p)`. -/
def wGLH (h : ℕ) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (wQH p h) (by
    rw [det_wQH]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero))

variable (p) in
/-- The Iwahori element `ℓQH h b c` as an element of `GL₂(ℚ_p)`. -/
def ℓGLH (h : ℕ) (b c : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (ℓQH p h b c) (by rw [det_ℓQH]; exact one_ne_zero)

@[simp] theorem coe_wGLH (h : ℕ) : (wGLH p h : Matrix (Fin 2) (Fin 2) ℚ_[p]) = wQH p h := rfl

@[simp] theorem coe_ℓGLH (h : ℕ) (b c : ℚ_[p]) :
    (ℓGLH p h b c : Matrix (Fin 2) (Fin 2) ℚ_[p]) = ℓQH p h b c := rfl

theorem coe_wGLH_inv (h : ℕ) :
    ((wGLH p h)⁻¹ : GL (Fin 2) ℚ_[p]) = (wQHinv p h : Matrix _ _ _) := by
  rw [Matrix.coe_units_inv, coe_wGLH]
  exact Matrix.inv_eq_right_inv (wQH_mul_wQHinv h)

theorem coe_ℓGLH_inv (h : ℕ) (b c : ℚ_[p]) :
    ((ℓGLH p h b c)⁻¹ : GL (Fin 2) ℚ_[p]) = (ℓQHinv p h b c : Matrix _ _ _) := by
  rw [Matrix.coe_units_inv, coe_ℓGLH]
  exact Matrix.inv_eq_right_inv (ℓQH_mul_ℓQHinv h b c)

theorem wGLH_one : wGLH p 1 = wGL p := by
  refine Units.ext ?_
  rw [coe_wGLH, coe_wGL, wQH_one]

/-- **The key factorisation in `GL₂(ℚ_p)` at level `h`**:
`w_h v_b w_h⁻¹ v_c = ℓ_{b,c} · (p·1) · s_{−b p^{h−1}}`. -/
theorem wGLH_mul_vGL_mul_wGLH_inv_mul_vGL (h : ℕ) (b c : ℚ_[p]) :
    wGLH p h * vGL p b * (wGLH p h)⁻¹ * vGL p c
      = ℓGLH p h b c * (pGL p * sGL p (-(b * (p : ℚ_[p]) ^ h / p))) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_wGLH, coe_vGL, coe_wGLH_inv, coe_ℓGLH, coe_sGL]
  rw [wQH_mul_vQ_mul_wQHinv_mul_vQ]
  show _ = ℓQH p h b c * (((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
    * sQ p (-(b * (p : ℚ_[p]) ^ h / p)))
  rw [smul_mul_assoc, one_mul]

/-- The disc-`0` conjugate of the level-`p^{h+1}` Atkin–Lehner element, in `K`:
`(0 1; −p^{h+1} 0)`. -/
def atkinLehnerKH (ψ : ℚ_[p] →+* K) (h : ℕ) : Matrix (Fin 2) (Fin 2) K :=
  RingHom.mapMatrix ψ (atkinLehner p (h + 1))

/-- Its inverse `(0 −p^{−(h+1)}; 1 0)`. -/
def atkinLehnerKHinv (ψ : ℚ_[p] →+* K) (h : ℕ) : Matrix (Fin 2) (Fin 2) K :=
  !![0, -((ψ p) ^ (h + 1))⁻¹; 1, 0]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem atkinLehnerKH_mul_atkinLehnerKHinv (ψ : ℚ_[p] →+* K) (h : ℕ) :
    atkinLehnerKH ψ h * atkinLehnerKHinv ψ h = 1 := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehnerKH, atkinLehnerKHinv, atkinLehner, Matrix.mul_apply, Fin.sum_univ_two, hp0]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem atkinLehnerKHinv_mul_atkinLehnerKH (ψ : ℚ_[p] →+* K) (h : ℕ) :
    atkinLehnerKHinv ψ h * atkinLehnerKH ψ h = 1 := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehnerKH, atkinLehnerKHinv, atkinLehner, Matrix.mul_apply, Fin.sum_univ_two, hp0]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `w_{2,h} = t₀⁻¹ w_h t₀` in `K`. -/
theorem atkinLehnerKH_eq (ψ : ℚ_[p] →+* K) (h : ℕ) :
    atkinLehnerKH ψ h = RingHom.mapMatrix ψ (tMatHInv p h 0 * wQH p h * tMatH p h 0) := by
  rw [atkinLehnerKH, discConjMat_wQH]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem atkinLehnerKHinv_eq (ψ : ℚ_[p] →+* K) (h : ℕ) :
    atkinLehnerKHinv ψ h
      = RingHom.mapMatrix ψ (tMatHInv p h 0 * wQHinv p h * tMatH p h 0) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehnerKHinv, wQHinv, tMatHInv, tMatH, hp0, pow_succ']

/-! ### The global data at level `h` -/

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable (ψ : ℚ_[p] →+* K)
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
variable (h : ℕ)

/-- **The Atkin–Lehner data at level `h`** (conductor `p^{h+1}`): `AtkinLehnerData` with the
Atkin–Lehner element `w_h` of level `p^{h+1}` and the disc-`0` normalisation on the
level-`p^{h+1}` part `{u ∈ U : ‖b(θ u)‖ ≤ p^{−h}}` (for `U = K^p·Iw_p` this is the local
computation `w_h (a b; c d) w_h⁻¹ = (d, −c p^{h−1}; −b p^{1−h}, a)`, `wQH_mul_mul_wQHinv`). -/
structure AtkinLehnerDataH (Γ : Subgroup G) (nebK : K → K) where
  /-- A section `GL₂(ℚ_p) → G` of the `p`-component `θ`. -/
  ιp : GL (Fin 2) ℚ_[p] →* G
  theta_ιp : ∀ g, θG (ιp g) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p])
  /-- The level contains the lifts of the local Iwahori subgroup `Iw_p`. -/
  ιp_mem_U : ∀ g : GL (Fin 2) ℚ_[p], (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1 → ιp g ∈ U
  /-- The local central element `p·1` is central in `G` (it is a scalar at `p` and `1` away
  from `p`). -/
  ιp_pGL_comm : ∀ x, ιp (pGL p) * x = x * ιp (pGL p)
  /-- Some power of the central element `p` (at `p`) is a global central element times an element
  of the level with trivial `p`-component: `p_p^N = p^N_global · ((p^{(p)})^N)⁻¹` — true for every
  open tame level, since the tame scalars form a compact group. -/
  central_pow : ∃ N, 0 < N ∧ ∃ γ ∈ Γ, ∃ u ∈ U,
    ιp (pGL p) ^ N = γ * u ∧ θG u = 1 ∧ ∀ x, γ * x = x * γ
  /-- The Hecke character `ψ_A ∘ ν`. -/
  χ : G →* Kˣ
  χ_Γ : ∀ γ ∈ Γ, χ γ = 1
  χ_U : ∀ u ∈ U, (χ u : K) = nebK (ψ (θG u).det)
  χ_vGL : ∀ c : ℚ_[p], χ (ιp (vGL p c)) = 1
  χ_wGLH : χ (ιp (wGLH p h)) = 1
  /-- **`w_h` normalises the level-`p^{h+1}` part of the level**: for `u ∈ U` with
  `p^h ∣ b(θ u)`, both `w_h u w_h⁻¹` and `w_h⁻¹ u w_h` lie in `U`. -/
  w_conj_mem_U : ∀ u ∈ U, ‖(θG u) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h →
    ιp (wGLH p h) * u * (ιp (wGLH p h))⁻¹ ∈ U ∧ (ιp (wGLH p h))⁻¹ * u * ιp (wGLH p h) ∈ U

variable (k : ℕ)

/-! ### Consequences of the data -/

variable {nebK : K → K} (D : AtkinLehnerDataH θG ψ U h Γ nebK)

section Bridge

variable {θG ψ U}

/-- Level `1` is the case `h = 1` (`wGLH_one`). -/
def _root_.LWX.AtkinLehnerData.toH (D₁ : AtkinLehnerData θG ψ U Γ nebK) :
    AtkinLehnerDataH θG ψ U 1 Γ nebK where
  ιp := D₁.ιp
  theta_ιp := D₁.theta_ιp
  ιp_mem_U := D₁.ιp_mem_U
  ιp_pGL_comm := D₁.ιp_pGL_comm
  central_pow := D₁.central_pow
  χ := D₁.χ
  χ_Γ := D₁.χ_Γ
  χ_U := D₁.χ_U
  χ_vGL := D₁.χ_vGL
  χ_wGLH := by rw [wGLH_one]; exact D₁.χ_wGL
  w_conj_mem_U := fun u hu hb => by
    rw [wGLH_one]; exact D₁.w_conj_mem_U u hu (by simpa using hb)

end Bridge

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The `p`-component of the central element `ιp(p·1)` is the scalar `p`: `θ(ιp p) = p • 1`. -/
theorem theta_ιp_pGLH :
    θG (D.ιp (pGL p)) = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
  D.theta_ιp (pGL p)

/-- **The disc-shifted level element** `u' := s_{a'}⁻¹ u s_a ∈ U`, `a' = discImage (θ u) a`,
at level `h`; it fixes disc `0` (with `p^h ∣ b`) and its disc-`0` conjugate is the disc-`a`
conjugate of `θ u`. -/
def discShiftH (u : U) (a : ZMod (p ^ h)) : G :=
  D.ιp (sGL p (-(((discImage h ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p]))) * u
    * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p]))

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem discShiftH_mem_U (u : U) (a : ZMod (p ^ h)) : discShiftH θG ψ U hU h D u a ∈ U := by
  refine mul_mem (mul_mem (D.ιp_mem_U _ (sQ_mem_Iw ?_)) u.2) (D.ιp_mem_U _ (sQ_mem_Iw ?_))
  · rw [norm_neg]; exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  · exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] _

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem theta_discShiftH (u : U) (a : ZMod (p ^ h)) :
    θG (discShiftH θG ψ U hU h D u a)
      = sQ p (-(((discImage h ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p])) * θG u
        * sQ p ((a.val : ℕ) : ℚ_[p]) := by
  rw [discShiftH, map_mul, map_mul, D.theta_ιp, D.theta_ιp, coe_sGL, coe_sGL]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `u s_a = s_{a'} u'`. -/
theorem mul_ιp_sGL_eqH (u : U) (a : ZMod (p ^ h)) :
    (u : G) * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p]))
      = D.ιp (sGL p (((discImage h ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p]))
        * discShiftH θG ψ U hU h D u a := by
  rw [discShiftH, ← mul_assoc, ← mul_assoc, ← map_mul, sGL_mul, add_neg_cancel, sGL_zero, map_one,
    one_mul]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The disc-shifted element lies in the level-`p^{h+1}` part: `p^h ∣ b(θ u')`
(`conj_sQ_eq_tMatH_mul_discConjMat`, `discConjMat_mem_Mh`). -/
theorem norm_theta_discShiftH_zero_one_le (u : U) (a : ZMod (p ^ h)) :
    ‖(θG (discShiftH θG ψ U hU h D u a)) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h := by
  have hc : sQ p (-(((discImage h ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p])) * θG u
        * sQ p ((a.val : ℕ) : ℚ_[p])
      = tMatH p h 0 * discConjMat h (⟨θG u, hU u.2⟩ : M1 p) a * tMatHInv p h 0 :=
    conj_sQ_eq_tMatH_mul_discConjMat h _ a
  have hM := discConjMat_mem_Mh h (⟨θG u, hU u.2⟩ : M1 p) a
  have h01 : (tMatH p h 0 * discConjMat h (⟨θG u, hU u.2⟩ : M1 p) a * tMatHInv p h 0) 0 1
      = (p : ℚ_[p]) ^ h * discConjMat h (⟨θG u, hU u.2⟩ : M1 p) a 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [tMatH, tMatHInv]
  rw [theta_discShiftH, hc, h01, norm_mul, norm_pow, Padic.norm_p]
  exact mul_le_of_le_one_right (by positivity) ((mem_Mh_iff.1 hM).1 0 1)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem discImage_discShiftH_zero (u : U) (a : ZMod (p ^ h)) :
    discImage h (⟨θG (discShiftH θG ψ U hU h D u a),
      hU (discShiftH_mem_U θG ψ U hU h D u a)⟩ : M1 p) 0 = 0 :=
  discImage_zero_of_norm_apply_zero_one_le_pow h _
    (norm_theta_discShiftH_zero_one_le θG ψ U hU h D u a)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The disc-`0` conjugate of `u'` is the disc-`a` conjugate of `θ u`. -/
theorem discConjMat_discShiftH_zero (u : U) (a : ZMod (p ^ h)) :
    discConjMat h
        (⟨θG (discShiftH θG ψ U hU h D u a),
          hU (discShiftH_mem_U θG ψ U hU h D u a)⟩ : M1 p) 0
      = discConjMat h (⟨θG u, hU u.2⟩ : M1 p) a := by
  have hc : sQ p (-(((discImage h ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p])) * θG u
        * sQ p ((a.val : ℕ) : ℚ_[p])
      = tMatH p h 0 * discConjMat h (⟨θG u, hU u.2⟩ : M1 p) a * tMatHInv p h 0 :=
    conj_sQ_eq_tMatH_mul_discConjMat h _ a
  rw [discConjMat_zero_of_discImage_zero_prime_pow h _
    (discImage_discShiftH_zero θG ψ U hU h D u a)]
  change tMatHInv p h 0 * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0 = _
  rw [theta_discShiftH, hc, ← mul_assoc, ← mul_assoc, tMatHInv_mul_tMatH, one_mul, mul_assoc,
    tMatHInv_mul_tMatH, mul_one]

omit hp [CharZero K] in
/-- Two functions on `ℤ/p^h × ℕ` agreeing on every disc are equal. -/
theorem cSpace_ext_blockProjH {f g : c(ZMod (p ^ h) × ℕ, K)}
    (hfg : ∀ a, cSpace.blockProj a f = cSpace.blockProj a g) : f = g := by
  refine DFunLike.ext _ _ fun x => ?_
  have hx := congrArg (fun F => F x.2) (hfg x.1)
  simpa [cSpace.blockProj_apply] using hx

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `nebK 1 = 1` (from the conductor hypothesis at level `h`). -/
theorem nebK_one_of_cond_pow
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1) :
    nebK (ψ 1) = 1 :=
  hcond 1 (by rw [sub_self, norm_zero]; positivity)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **`nebK(a)·nebK(d) = nebK(det)`** on the level-`p^{h+1}` part of `Iw_p` (`ad = det + bc`
with `p^h ∣ b`, `p ∣ c`, so `ad/det ≡ 1 (mod p^{h+1})`). -/
theorem nebK_mul_nebK_eq_nebK_detH
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1) (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹ ^ h) :
    nebK (ψ (g 0 0)) * nebK (ψ (g 1 1)) = nebK (ψ g.det) := by
  obtain ⟨he, hc, hdet⟩ := hg
  have hc' : ‖g 1 0‖ ≤ (p : ℝ)⁻¹ := by simpa using hc
  have ha : ‖g 0 0‖ = 1 := norm_apply_zero_zero_of_mem_Iw one_ne_zero ⟨he, hc, hdet⟩
  have hd : ‖g 1 1‖ = 1 := (Iw_one_le_M1 ⟨he, hc, hdet⟩).2.2.1
  have hdet0 : g.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hsplit : g 0 0 * g 1 1 = g.det * (1 + g 0 1 * g 1 0 / g.det) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ hdet0, Matrix.det_fin_two]
    ring
  have hen : ‖g 0 1 * g 1 0 / g.det‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [norm_div, hdet, div_one, norm_mul, pow_succ]
    exact mul_le_mul hb hc' (norm_nonneg _) (by positivity)
  have hel : ‖g 0 1 * g 1 0 / g.det‖ < 1 :=
    hen.trans_lt (pow_lt_one₀ (inv_nonneg.2 (Nat.cast_nonneg _)) (inv_lt_one_p (p := p))
      (Nat.succ_ne_zero h))
  have h1e : ‖(1 : ℚ_[p]) + g 0 1 * g 1 0 / g.det‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hel.ne'),
      norm_one, max_eq_left hel.le]
  rw [← hmul _ _ ha hd, hsplit, hmul _ _ hdet h1e,
    hcond (1 + g 0 1 * g 1 0 / g.det) (by rw [add_sub_cancel_left]; exact hen), mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `nebK(1 − x) = nebK(1 + x)⁻¹` for `‖x‖ ≤ p^{−h}`, `h ≥ 1` (`(1−x)(1+x) ≡ 1 (mod p^{h+1})`). -/
theorem nebK_one_sub_eq_invH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    {x : ℚ_[p]} (hx : ‖x‖ ≤ (p : ℝ)⁻¹ ^ h) :
    nebK (ψ (1 - x)) = (nebK (ψ (1 + x)))⁻¹ := by
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  have hxl : ‖x‖ < 1 :=
    hx.trans_lt (pow_lt_one₀ (inv_nonneg.2 (Nat.cast_nonneg _)) hp1 hh.ne')
  have hn1 : ‖(1 : ℚ_[p]) - x‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_one, norm_neg]; exact hxl.ne'), norm_one, norm_neg, max_eq_left hxl.le]
  have hn2 : ‖(1 : ℚ_[p]) + x‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hxl.ne'),
      norm_one, max_eq_left hxl.le]
  have hprod : nebK (ψ (1 - x)) * nebK (ψ (1 + x)) = 1 := by
    rw [← hmul _ _ hn1 hn2, show (1 - x) * (1 + x) = 1 - x ^ 2 by ring]
    refine hcond _ ?_
    rw [sub_sub_cancel_left, norm_neg, norm_pow]
    calc ‖x‖ ^ 2 ≤ ((p : ℝ)⁻¹ ^ h) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
      _ = (p : ℝ)⁻¹ ^ (2 * h) := by rw [← pow_mul, mul_comm h 2]
      _ ≤ (p : ℝ)⁻¹ ^ (h + 1) :=
          pow_le_pow_of_le_one (inv_nonneg.2 (Nat.cast_nonneg _)) hp1.le (by omega)
  exact eq_inv_of_mul_eq_one_left hprod

/-! ### Classical disc forms at level `h` -/

variable (p K) in
/-- The automorphic functions whose every value is locally polynomial of degree `≤ k` on the
`p^h` discs. -/
def locPolyFormsH : Submodule K (AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) where
  carrier := {φ | ∀ x, φ x ∈ locPolyDegSubmodule p K h k}
  add_mem' hφ hφ' x := Submodule.add_mem _ (hφ x) (hφ' x)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' r _ hφ x := Submodule.smul_mem _ r (hφ x)

variable {UK : Subgroup Kˣ} {ρ : ℝ} (κ : AnalyticWeight UK (M1Kh h ψ) ρ)

/-- **The classical disc forms** `S^D_{k+2}(K^p Iw_{p^{h+1}}; ψ)` in the level-`h` disc model
([LWX, §2.4] and (3.21.1): "isomorphic to the direct sum of `t` copies of
`LP^{m−v(q), deg ≤ k}(ℤ_p; E)`"). -/
def ClassicalDiscFormsH : Submodule K (AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :=
  DiscForms (Γ := Γ) θG h ψ κ U hU ⊓ locPolyFormsH p K h k

omit [CharZero K] in
theorem mem_classicalDiscFormsH_iff (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :
    φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ
      ↔ φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU ∧ ∀ x, φ x ∈ locPolyDegSubmodule p K h k :=
  Iff.rfl

omit [CharZero K] in
/-- `U_p` preserves the classical disc forms at a classical-shape weight. -/
theorem discHeckeOperator_mem_classicalDiscFormsH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite)
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    ((discHeckeOperator θG h ψ κ U hU hη hfin ⟨φ, hφ.1⟩ : DiscForms (Γ := Γ) θG h ψ κ U hU) :
        AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
      ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ := by
  letI := discLevelSlashAction θG h ψ κ
  letI := discLevelSMulSlashClass θG h ψ κ
  refine ⟨(discHeckeOperator θG h ψ κ U hU hη hfin ⟨φ, hφ.1⟩).2, fun x => ?_⟩
  have : Fintype (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)) := hfin.fintype
  have hev : ∀ (s : Finset (((Quotient.mk'' : G → RightCosets U) ''
        (({η} : Set G) * (U : Set G))) : Set (RightCosets U)))
      (F : _ → AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (g : G),
      (∑ i ∈ s, F i) g = ∑ i ∈ s, F i g := fun s F g =>
    map_sum (AddMonoidHom.mk' (fun φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K) => φ g)
      (fun _ _ => rfl)) F s
  change (AbstractHeckeOperatorSlash.heckeOperatorSlash K hU hU hη hfin ⟨φ, hφ.1⟩ :
    AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) x ∈ _
  rw [AbstractHeckeOperatorSlash.heckeOperatorSlash_apply, finsum_eq_sum_of_fintype, hev]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact discSlash_mem_locPolyDegSubmodule_of_shape h ψ κ _
    (u := fun a => u ((discConjK h (levelM1ToM1 (p := p) θG ⟨_, _⟩) a ψ :
      Matrix (Fin 2) (Fin 2) K) 1 1))
    (fun a => hκ _) (hφ.2 _)

/-- **`U_p` on the classical disc forms at level `h`.** -/
def discHeckeOperatorClH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ →ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ where
  toFun φ := ⟨(discHeckeOperator θG h ψ κ U hU hη hfin ⟨φ.1, φ.2.1⟩ :
      DiscForms (Γ := Γ) θG h ψ κ U hU).1,
    discHeckeOperator_mem_classicalDiscFormsH θG ψ U hU h k κ hκ hη hfin φ.2⟩
  map_add' φ φ' := by
    apply Subtype.ext
    change (discHeckeOperator θG h ψ κ U hU hη hfin (⟨φ.1, φ.2.1⟩ + ⟨φ'.1, φ'.2.1⟩) :
      DiscForms (Γ := Γ) θG h ψ κ U hU).1 = _
    rw [map_add]
    rfl
  map_smul' r φ := by
    apply Subtype.ext
    change (discHeckeOperator θG h ψ κ U hU hη hfin (r • ⟨φ.1, φ.2.1⟩) :
      DiscForms (Γ := Γ) θG h ψ κ U hU).1 = _
    rw [map_smul]
    rfl

/-! ### The tame central operator on the level-`h` classical disc forms -/

/-- **The tame central operator** at level `h`: `(Zφ)(x) = φ(x·ιp(p·1)⁻¹)`. -/
def centralOpH (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :
    AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K) :=
  translateOp (D.ιp (pGL p)) φ

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem centralOpH_apply (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G) :
    centralOpH θG ψ U h D φ x = φ (x * (D.ιp (pGL p))⁻¹) :=
  rfl

omit [CharZero K] in
theorem centralOpH_mem_classicalDiscFormsH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    centralOpH θG ψ U h D φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ :=
  ⟨translateOp_mem_discForms θG ψ κ U hU (fun u _ => D.ιp_pGL_comm u) hφ.1, fun _ => hφ.2 _⟩

/-- `Z` as a linear endomorphism of the level-`h` classical disc forms. -/
def centralOpClH :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ →ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ where
  toFun φ := ⟨centralOpH θG ψ U h D φ.1, centralOpH_mem_classicalDiscFormsH θG ψ U hU h k D κ φ.2⟩
  map_add' _ _ := Subtype.ext (translateOp_add _ _ _)
  map_smul' _ _ := Subtype.ext (translateOp_smul _ _ _)

omit [CharZero K] in
theorem centralOpClH_apply (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    (centralOpClH θG ψ U hU h k D κ φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
      = centralOpH θG ψ U h D φ.1 :=
  rfl

omit [CharZero K] in
/-- `Z` has finite order (`central_pow`). -/
theorem centralOpClH_pow_eq_one : ∃ N, 0 < N ∧ centralOpClH θG ψ U hU h k D κ ^ N = 1 := by
  obtain ⟨N, hN, γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central_pow
  refine ⟨N, hN, LinearMap.ext fun φ => Subtype.ext ?_⟩
  have hiter : ∀ m : ℕ, ((centralOpClH θG ψ U hU h k D κ ^ m) φ :
      AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) = translateOp (D.ιp (pGL p) ^ m) φ.1 := by
    intro m
    induction m with
    | zero => simp [translateOp_one]
    | succ m ih =>
      rw [pow_succ' (centralOpClH θG ψ U hU h k D κ) m, Module.End.mul_apply, centralOpClH_apply,
        centralOpH, ih, translateOp_translateOp, pow_succ (D.ιp (pGL p)) m]
  rw [hiter, hP]
  exact translateOp_eq_self_of_eq_mul θG ψ κ U hU hγ hcomm hu hθu rfl φ.2.1

omit [CharZero K] in
/-- `Z` commutes with `U_p`. -/
theorem discHeckeOperatorClH_comp_centralOpClH
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    (discHeckeOperatorClH θG ψ U hU h k κ hκ hη hfin).comp (centralOpClH θG ψ U hU h k D κ)
      = (centralOpClH θG ψ U hU h k D κ).comp
          (discHeckeOperatorClH θG ψ U hU h k κ hκ hη hfin) :=
  LinearMap.ext fun φ => Subtype.ext
    (translateOp_discHeckeOperator θG ψ κ U hU D.ιp_pGL_comm hη hfin ⟨φ.1, φ.2.1⟩)

/-! ### Reading disc `a` as disc `0` -/

omit [CharZero K] in
/-- **A level element with trivial `p`-component acts trivially**: `φ(x u) = φ(x)` for `u ∈ U`,
`θ u = 1`. -/
theorem apply_mul_of_theta_eq_oneH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) {u : G} (hu : u ∈ U) (hθ : θG u = 1) :
    φ (x * u) = φ x := by
  have hres := (mem_discForms_iff θG h ψ κ U hU φ).1 hφ ⟨u, hu⟩ x
  have h1 : (⟨θG ((⟨u, hu⟩ : U) : G), hU (⟨u, hu⟩ : U).2⟩ : M1 p) = 1 := Subtype.ext hθ
  rw [h1, discSlash_one] at hres
  exact hres

omit [CharZero K] in
/-- **Level-equivariance on disc `0`** at a level element fixing disc `0`, for a classical form
at a classical-shape weight. -/
theorem blockProj_zero_apply_mul_mem_UH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) (v : U)
    (hv0 : discImage h (⟨θG v, hU v.2⟩ : M1 p) 0 = 0) :
    cSpace.blockProj 0 (φ (x * v))
      = u (ψ ((discConj h (⟨θG v, hU v.2⟩ : M1 p) 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj h (⟨θG v, hU v.2⟩ : M1 p) 0 :
          Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ x)) := by
  have hres := (mem_discForms_iff θG h ψ κ U hU φ).1 hφ.1 v x
  have hf : cSpace.blockProj 0 (φ x) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact hφ.2 x 0 j hj
  change cSpace.blockProj 0 (φ.toFun (x * v)) = _
  rw [hres, blockProj_discSlash, hv0]
  exact kappaSlash_eq_smul_symAct_of_shape κ (discConjK h ⟨θG v, hU v.2⟩ 0 ψ) (hκ _) hf

omit [CharZero K] in
/-- **Disc `a` of `φ(x)` is disc `0` of `φ(x·s_a)`** at level `h` (`discImage_sQ_zero_prime_pow`,
`discConj_sQ_zero_prime_pow`). -/
theorem shapiro_blockProjH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) (a : ZMod (p ^ h)) :
    cSpace.blockProj a (φ x)
      = cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])))) := by
  haveI : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  have ha : a.val < p ^ h := ZMod.val_lt a
  have hs : sQ p ((a.val : ℕ) : ℚ_[p]) ∈ Iw p 1 :=
    sQ_mem_Iw (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)
  set v : U := ⟨D.ιp (sGL p (a.val : ℚ_[p])), D.ιp_mem_U _ hs⟩ with hv
  have hres := (mem_discForms_iff θG h ψ κ U hU φ).1 hφ v x
  have hθ : (⟨θG v, hU v.2⟩ : M1 p) = ⟨sQ p (a.val : ℕ), Iw_one_le_M1 hs⟩ :=
    Subtype.ext (D.theta_ιp _)
  have hK : discConjK h (⟨sQ p (a.val : ℕ), Iw_one_le_M1 hs⟩ : M1 p) 0 ψ = 1 := by
    refine Subtype.ext ?_
    rw [coe_discConjK, discConj_sQ_zero_prime_pow h ha]
    simp
  change cSpace.blockProj a (φ.toFun x) = cSpace.blockProj 0 (φ.toFun (x * v))
  rw [hres, hθ, blockProj_discSlash, discImage_sQ_zero_prime_pow, ZMod.natCast_zmod_val, hK,
    AnalyticWeight.kappaSlash_one]
  rfl

/-! ### The Atkin–Lehner map at level `h` -/

/-- **The underlying function of `Wφ`** at level `h`: on disc `a`,
`χ(x s_a)⁻¹ · (disc 0 of φ(x s_a w_h⁻¹)) ∣_k (0 1; −p^{h+1} 0)`. -/
def atkinLehnerFunH (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G) :
    c(ZMod (p ^ h) × ℕ, K) :=
  ∑ a : ZMod (p ^ h), cSpace.blockIncl a
    (((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K)⁻¹ •
      symAct K k (atkinLehnerKH ψ h)
        (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹))))

omit [CharZero K] in
theorem atkinLehnerFunH_blockProj (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G)
    (a : ZMod (p ^ h)) :
    cSpace.blockProj a (atkinLehnerFunH θG ψ U h k D φ x)
      = ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerKH ψ h)
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹))) := by
  rw [atkinLehnerFunH, map_sum, Finset.sum_eq_single a]
  · rw [cSpace.blockProj_blockIncl, if_pos rfl]
  · intro b _ hb
    rw [cSpace.blockProj_blockIncl, if_neg (fun hba => hb hba.symm)]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

omit [CharZero K] in
/-- Disc `0` of `Wφ(x)`: `χ(x)⁻¹ · (disc 0 of φ(x w_h⁻¹)) ∣_k w_{2,h}`. -/
theorem atkinLehnerFunH_blockProj_zero (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
    (x : G) :
    cSpace.blockProj 0 (atkinLehnerFunH θG ψ U h k D φ x)
      = ((D.χ x : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerKH ψ h) (cSpace.blockProj 0 (φ (x * (D.ιp (wGLH p h))⁻¹))) := by
  rw [atkinLehnerFunH_blockProj, ZMod.val_zero, Nat.cast_zero, sGL_zero, map_one, mul_one]

omit [CharZero K] in
/-- `Wφ` is left `Γ`-invariant. -/
theorem atkinLehnerFunH_left_invt (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
    {γ : G} (hγ : γ ∈ Γ) (x : G) :
    atkinLehnerFunH θG ψ U h k D φ (γ * x) = atkinLehnerFunH θG ψ U h k D φ x := by
  simp only [atkinLehnerFunH, mul_assoc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul D.χ γ, D.χ_Γ γ hγ, one_mul]
  congr 4
  exact φ.left_invt γ hγ _

omit [CharZero K] in
/-- `Wφ` is locally polynomial of degree `≤ k`. -/
theorem atkinLehnerFunH_mem_locPolyDegSubmodule
    (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G) :
    atkinLehnerFunH θG ψ U h k D φ x ∈ locPolyDegSubmodule p K h k := by
  intro a j hj
  have hres := symAct_mem_polySubmodule k (atkinLehnerKH ψ h)
    (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹))) j hj
  rw [← cSpace.blockProj_apply, atkinLehnerFunH_blockProj]
  exact (congrArg (fun t => ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K)⁻¹ * t) hres).trans
    (mul_zero _)

variable {UK' : Subgroup Kˣ} {ρ' : ℝ} (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ')

omit [CharZero K] in
set_option maxHeartbeats 1000000 in
/-- **`W` maps `ψ`-forms to `ψ⁻¹`-forms** at level `h`: for `u ∈ U`,
`(Wφ)(x u) = (Wφ)(x) ∣_{κ'} u` (`shapiro_blockProjH`, `mul_ιp_sGL_eqH`, `w_conj_mem_U` at the
disc-shifted element, `wQH_mul_mul_wQHinv`, `nebK_mul_nebK_eq_nebK_detH`). -/
theorem atkinLehnerFunH_slash (_hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (u : U) (x : G) :
    atkinLehnerFunH θG ψ U h k D φ (x * u)
      = discSlash h ψ κ' ⟨θG u, hU u.2⟩ (atkinLehnerFunH θG ψ U h k D φ x) := by
  refine cSpace_ext_blockProjH h fun a => ?_
  have hu'U : discShiftH θG ψ U hU h D u a ∈ U := discShiftH_mem_U θG ψ U hU h D u a
  have hgIw : θG (discShiftH θG ψ U hU h D u a) ∈ Iw p 1 :=
    theta_mem_Iw θG U hU ⟨discShiftH θG ψ U hU h D u a, hu'U⟩
  have hgb : ‖(θG (discShiftH θG ψ U hU h D u a)) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h :=
    norm_theta_discShiftH_zero_one_le θG ψ U hU h D u a
  have hus : x * ↑u * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p]))
      = x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))
        * discShiftH θG ψ U hU h D u a := by
    rw [mul_assoc, mul_ιp_sGL_eqH θG ψ U hU h D u a, ← mul_assoc]
  have hM2 : ((discConj h (⟨θG u, hU u.2⟩ : M1 p) a : M1 p) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = tMatHInv p h 0 * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0 := by
    rw [coe_discConj, ← discConjMat_discShiftH_zero θG ψ U hU h D u a,
      discConjMat_zero_of_discImage_zero_prime_pow h _
        (discImage_discShiftH_zero θG ψ U hU h D u a)]
  have hF11 : (tMatHInv p h 0 * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0) 1 1
      = (θG (discShiftH θG ψ U hU h D u a)) 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [tMatHInv, tMatH]
  have hK : ((discConjK h (⟨θG u, hU u.2⟩ : M1 p) a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
      = RingHom.mapMatrix ψ
        (tMatHInv p h 0 * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0) := by
    rw [coe_discConjK, hM2]
  have hK11 : ((discConjK h (⟨θG u, hU u.2⟩ : M1 p) a ψ : M1Kh h ψ) :
      Matrix (Fin 2) (Fin 2) K) 1 1 = ψ ((θG (discShiftH θG ψ U hU h D u a)) 1 1) := by
    rw [hK, RingHom.mapMatrix_apply, Matrix.map_apply, hF11]
  have h00 : ‖(θG (discShiftH θG ψ U hU h D u a)) 0 0‖ = 1 :=
    norm_apply_zero_zero_of_mem_Iw one_ne_zero hgIw
  have h11 : ‖(θG (discShiftH θG ψ U hU h D u a)) 1 1‖ = 1 := (Iw_one_le_M1 hgIw).2.2.1
  have hdet := nebK_mul_nebK_eq_nebK_detH ψ h hmul hcond hgIw hgb
  have ht1 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], tMatH p h 0 * (tMatHInv p h 0 * X) = X :=
    fun X => by rw [← Matrix.mul_assoc, tMatH_mul_tMatHInv, Matrix.one_mul]
  have hconjU : D.ιp (wGLH p h) * discShiftH θG ψ U hU h D u a * (D.ιp (wGLH p h))⁻¹ ∈ U :=
    (D.w_conj_mem_U _ hu'U hgb).1
  have hθW : θG (D.ιp (wGLH p h) * discShiftH θG ψ U hU h D u a * (D.ιp (wGLH p h))⁻¹)
      = wQH p h * θG (discShiftH θG ψ U hU h D u a) * wQHinv p h := by
    rw [map_mul, map_mul, ← map_inv D.ιp, D.theta_ιp, D.theta_ιp, coe_wGLH, coe_wGLH_inv]
  have hv0 : discImage h (⟨θG (D.ιp (wGLH p h) * discShiftH θG ψ U hU h D u a
      * (D.ιp (wGLH p h))⁻¹), hU hconjU⟩ : M1 p) 0 = 0 :=
    discImage_zero_of_norm_apply_zero_one_le_pow h _ (by
      refine (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[p] => ‖M 0 1‖) hθW).le.trans ?_
      exact (wQH_conj_mem_Iw h hgIw hgb).1.2)
  have hB : cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
      a).val : ℕ) : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹)) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact hφ.2 _ 0 j hj
  have hM1 : ((discConj h (⟨θG (D.ιp (wGLH p h) * discShiftH θG ψ U hU h D u a
      * (D.ιp (wGLH p h))⁻¹), hU hconjU⟩ : M1 p) 0 : M1 p) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = tMatHInv p h 0 * (wQH p h * θG (discShiftH θG ψ U hU h D u a) * wQHinv p h)
        * tMatH p h 0 := by
    rw [coe_discConj, discConjMat_zero_of_discImage_zero_prime_pow h _ hv0]
    show tMatHInv p h 0 * θG (D.ιp (wGLH p h) * discShiftH θG ψ U hU h D u a
      * (D.ιp (wGLH p h))⁻¹) * tMatH p h 0 = _
    rw [hθW]
  have hE11 : (tMatHInv p h 0 * (wQH p h * θG (discShiftH θG ψ U hU h D u a) * wQHinv p h)
      * tMatH p h 0) 1 1 = (θG (discShiftH θG ψ U hU h D u a)) 0 0 := by
    rw [wQH_mul_mul_wQHinv]
    simp [tMatHInv, tMatH, Matrix.mul_apply, Fin.sum_univ_two]
  have hE : cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
        a).val : ℕ) : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹
        * (D.ιp (wGLH p h) * discShiftH θG ψ U hU h D u a * (D.ιp (wGLH p h))⁻¹)))
      = nebK (ψ (((discConj h (⟨θG (D.ιp (wGLH p h) * discShiftH θG ψ U hU h D u a
          * (D.ιp (wGLH p h))⁻¹), hU hconjU⟩ : M1 p) 0 : M1 p) :
            Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ ((discConj h (⟨θG (D.ιp (wGLH p h)
          * discShiftH θG ψ U hU h D u a * (D.ιp (wGLH p h))⁻¹), hU hconjU⟩ : M1 p) 0 : M1 p) :
            Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
            a).val : ℕ) : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹))) :=
    blockProj_zero_apply_mul_mem_UH θG ψ U hU h k κ hκ hφ _ ⟨_, hconjU⟩ hv0
  have hLHS : cSpace.blockProj a (atkinLehnerFunH θG ψ U h k D φ (x * u))
      = (((D.χ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))
          * discShiftH θG ψ U hU h D u a)) : Kˣ) : K)⁻¹ •
        nebK (ψ ((θG (discShiftH θG ψ U hU h D u a)) 0 0)) •
        symAct K k (RingHom.mapMatrix ψ (tMatHInv p h 0 * (wQH p h
          * θG (discShiftH θG ψ U hU h D u a) * wQHinv p h) * tMatH p h 0) * atkinLehnerKH ψ h)
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
            a).val : ℕ) : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹))) := by
    rw [atkinLehnerFunH_blockProj, hus,
      show x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))
          * discShiftH θG ψ U hU h D u a * (D.ιp (wGLH p h))⁻¹
        = x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))
          * (D.ιp (wGLH p h))⁻¹
          * (D.ιp (wGLH p h) * discShiftH θG ψ U hU h D u a * (D.ιp (wGLH p h))⁻¹) by group,
      hE, hM1, hE11, map_smul, symAct_mul k _ _ hB]
  have hf' : cSpace.blockProj (discImage h (⟨θG u, hU u.2⟩ : M1 p) a)
      (atkinLehnerFunH θG ψ U h k D φ x) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]
    exact atkinLehnerFunH_mem_locPolyDegSubmodule θG ψ U h k D φ x _ j hj
  have hRHS : cSpace.blockProj a (discSlash h ψ κ' (⟨θG u, hU u.2⟩ : M1 p)
      (atkinLehnerFunH θG ψ U h k D φ x))
      = (nebK (ψ ((θG (discShiftH θG ψ U hU h D u a)) 1 1)))⁻¹ •
        (((D.χ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) :
          ℚ_[p])))) : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerKH ψ h * RingHom.mapMatrix ψ (tMatHInv p h 0
          * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0))
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
            a).val : ℕ) : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹))) := by
    rw [blockProj_discSlash, kappaSlash_eq_smul_symAct_of_shape κ'
      (discConjK h (⟨θG u, hU u.2⟩ : M1 p) a ψ) (hκ' _) hf', hK11, hK,
      atkinLehnerFunH_blockProj, map_smul, symAct_mul k _ _ hB]
  have hmat : RingHom.mapMatrix ψ (tMatHInv p h 0 * (wQH p h
        * θG (discShiftH θG ψ U hU h D u a) * wQHinv p h) * tMatH p h 0) * atkinLehnerKH ψ h
      = atkinLehnerKH ψ h * RingHom.mapMatrix ψ (tMatHInv p h 0
        * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0) := by
    have h2 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], wQHinv p h * (wQH p h * X) = X := fun X => by
      rw [← Matrix.mul_assoc, wQHinv_mul_wQH, Matrix.one_mul]
    have hQ : ∀ g : Matrix (Fin 2) (Fin 2) ℚ_[p],
        tMatHInv p h 0 * (wQH p h * g * wQHinv p h) * tMatH p h 0
          * (tMatHInv p h 0 * wQH p h * tMatH p h 0)
          = tMatHInv p h 0 * wQH p h * tMatH p h 0 * (tMatHInv p h 0 * g * tMatH p h 0) :=
      fun g => by simp only [Matrix.mul_assoc, ht1, h2]
    rw [atkinLehnerKH_eq, ← map_mul, ← map_mul, hQ]
  rw [hLHS, hRHS, hmat, smul_smul, smul_smul]
  congr 1
  have hn00 := hne _ h00
  have hn11 := hne _ h11
  rw [map_mul, Units.val_mul, D.χ_U _ hu'U, ← hdet]
  have hχ0 : (((D.χ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) :
      ℚ_[p])))) : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

/-- **The Atkin–Lehner map** `W : S^D_{k+2}(ψ) → S^D_{k+2}(ψ⁻¹)` on classical disc forms at
level `h`. -/
def atkinLehnerMapH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ →ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ' where
  toFun φ := ⟨⟨atkinLehnerFunH θG ψ U h k D φ.1, fun γ hγ x =>
      atkinLehnerFunH_left_invt θG ψ U h k D φ.1 hγ x⟩,
    ⟨(mem_discForms_iff θG h ψ κ' U hU _).2 fun u x =>
        atkinLehnerFunH_slash θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ.2 u x,
      fun x => atkinLehnerFunH_mem_locPolyDegSubmodule θG ψ U h k D φ.1 x⟩⟩
  map_add' φ φ' := by
    refine Subtype.ext (AutomorphicFunction.ext fun x => ?_)
    change atkinLehnerFunH θG ψ U h k D (φ.1 + φ'.1) x
      = atkinLehnerFunH θG ψ U h k D φ.1 x + atkinLehnerFunH θG ψ U h k D φ'.1 x
    simp only [atkinLehnerFunH, AutomorphicFunction.add_apply, map_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' r φ := by
    refine Subtype.ext (AutomorphicFunction.ext fun x => ?_)
    change atkinLehnerFunH θG ψ U h k D (r • φ.1) x = r • atkinLehnerFunH θG ψ U h k D φ.1 x
    rw [atkinLehnerFunH, atkinLehnerFunH, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [AutomorphicFunction.smul_apply, map_smul]
    exact smul_comm _ _ _

/-- **The inverse map** `W' : S^D_{k+2}(ψ⁻¹) → S^D_{k+2}(ψ)` at level `h`:
`χ(x s_a) · (disc 0 of φ(x s_a w_h)) ∣_k w_{2,h}⁻¹`. -/
def atkinLehnerFunHInv (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G) :
    c(ZMod (p ^ h) × ℕ, K) :=
  ∑ a : ZMod (p ^ h), cSpace.blockIncl a
    (((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K) •
      symAct K k (atkinLehnerKHinv ψ h)
        (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * D.ιp (wGLH p h)))))

omit [CharZero K] in
theorem atkinLehnerFunHInv_blockProj_zero (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
    (x : G) :
    cSpace.blockProj 0 (atkinLehnerFunHInv θG ψ U h k D φ x)
      = ((D.χ x : Kˣ) : K) •
        symAct K k (atkinLehnerKHinv ψ h) (cSpace.blockProj 0 (φ (x * D.ιp (wGLH p h)))) := by
  rw [atkinLehnerFunHInv, map_sum, Finset.sum_eq_single 0]
  · rw [cSpace.blockProj_blockIncl, if_pos rfl, ZMod.val_zero, Nat.cast_zero, sGL_zero, map_one,
      mul_one]
  · intro b _ hb
    rw [cSpace.blockProj_blockIncl, if_neg (fun hba => hb hba.symm)]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

omit [CharZero K] in
/-- `W'φ` is left `Γ`-invariant. -/
theorem atkinLehnerFunHInv_left_invt (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
    {γ : G} (hγ : γ ∈ Γ) (x : G) :
    atkinLehnerFunHInv θG ψ U h k D φ (γ * x) = atkinLehnerFunHInv θG ψ U h k D φ x := by
  simp only [atkinLehnerFunHInv, mul_assoc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul D.χ γ, D.χ_Γ γ hγ, one_mul]
  congr 4
  exact φ.left_invt γ hγ _

omit [CharZero K] in
/-- `W'φ` is locally polynomial of degree `≤ k`. -/
theorem atkinLehnerFunHInv_mem_locPolyDegSubmodule
    (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G) :
    atkinLehnerFunHInv θG ψ U h k D φ x ∈ locPolyDegSubmodule p K h k := by
  intro a j hj
  have hproj : cSpace.blockProj a (atkinLehnerFunHInv θG ψ U h k D φ x)
      = ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K) •
        symAct K k (atkinLehnerKHinv ψ h)
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * D.ιp (wGLH p h)))) := by
    rw [atkinLehnerFunHInv, map_sum, Finset.sum_eq_single a]
    · rw [cSpace.blockProj_blockIncl, if_pos rfl]
    · intro b _ hb
      rw [cSpace.blockProj_blockIncl, if_neg (fun hba => hb hba.symm)]
    · intro ha
      exact absurd (Finset.mem_univ _) ha
  have hres := symAct_mem_polySubmodule k (atkinLehnerKHinv ψ h)
    (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * D.ιp (wGLH p h)))) j hj
  rw [← cSpace.blockProj_apply, hproj]
  exact (congrArg (fun t => ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K) * t) hres).trans
    (mul_zero _)

omit [CharZero K] in
set_option maxHeartbeats 1000000 in
/-- **`W'` maps `ψ⁻¹`-forms to `ψ`-forms** at level `h` (the mirror of `atkinLehnerFunH_slash`,
with `w_h⁻¹ u' w_h`). -/
theorem atkinLehnerFunHInv_slash (_hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ') (u : U) (x : G) :
    atkinLehnerFunHInv θG ψ U h k D φ (x * u)
      = discSlash h ψ κ ⟨θG u, hU u.2⟩ (atkinLehnerFunHInv θG ψ U h k D φ x) := by
  refine cSpace_ext_blockProjH h fun a => ?_
  have hproj : ∀ y : G, ∀ a₀ : ZMod (p ^ h), cSpace.blockProj a₀ (atkinLehnerFunHInv θG ψ U h k D φ y)
      = ((D.χ (y * D.ιp (sGL p (a₀.val : ℚ_[p]))) : Kˣ) : K) •
        symAct K k (atkinLehnerKHinv ψ h)
          (cSpace.blockProj 0 (φ (y * D.ιp (sGL p (a₀.val : ℚ_[p])) * D.ιp (wGLH p h)))) := by
    intro y a₀
    rw [atkinLehnerFunHInv, map_sum, Finset.sum_eq_single a₀]
    · rw [cSpace.blockProj_blockIncl, if_pos rfl]
    · intro b _ hb
      rw [cSpace.blockProj_blockIncl, if_neg (fun hba => hb hba.symm)]
    · intro ha
      exact absurd (Finset.mem_univ _) ha
  have hu'U : discShiftH θG ψ U hU h D u a ∈ U := discShiftH_mem_U θG ψ U hU h D u a
  have hgIw : θG (discShiftH θG ψ U hU h D u a) ∈ Iw p 1 :=
    theta_mem_Iw θG U hU ⟨discShiftH θG ψ U hU h D u a, hu'U⟩
  have hgb : ‖(θG (discShiftH θG ψ U hU h D u a)) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h :=
    norm_theta_discShiftH_zero_one_le θG ψ U hU h D u a
  have hus : x * ↑u * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p]))
      = x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))
        * discShiftH θG ψ U hU h D u a := by
    rw [mul_assoc, mul_ιp_sGL_eqH θG ψ U hU h D u a, ← mul_assoc]
  have hM2 : ((discConj h (⟨θG u, hU u.2⟩ : M1 p) a : M1 p) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = tMatHInv p h 0 * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0 := by
    rw [coe_discConj, ← discConjMat_discShiftH_zero θG ψ U hU h D u a,
      discConjMat_zero_of_discImage_zero_prime_pow h _
        (discImage_discShiftH_zero θG ψ U hU h D u a)]
  have hF11 : (tMatHInv p h 0 * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0) 1 1
      = (θG (discShiftH θG ψ U hU h D u a)) 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [tMatHInv, tMatH]
  have hK : ((discConjK h (⟨θG u, hU u.2⟩ : M1 p) a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
      = RingHom.mapMatrix ψ
        (tMatHInv p h 0 * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0) := by
    rw [coe_discConjK, hM2]
  have hK11 : ((discConjK h (⟨θG u, hU u.2⟩ : M1 p) a ψ : M1Kh h ψ) :
      Matrix (Fin 2) (Fin 2) K) 1 1 = ψ ((θG (discShiftH θG ψ U hU h D u a)) 1 1) := by
    rw [hK, RingHom.mapMatrix_apply, Matrix.map_apply, hF11]
  have h00 : ‖(θG (discShiftH θG ψ U hU h D u a)) 0 0‖ = 1 :=
    norm_apply_zero_zero_of_mem_Iw one_ne_zero hgIw
  have h11 : ‖(θG (discShiftH θG ψ U hU h D u a)) 1 1‖ = 1 := (Iw_one_le_M1 hgIw).2.2.1
  have hdet := nebK_mul_nebK_eq_nebK_detH ψ h hmul hcond hgIw hgb
  have ht1 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], tMatH p h 0 * (tMatHInv p h 0 * X) = X :=
    fun X => by rw [← Matrix.mul_assoc, tMatH_mul_tMatHInv, Matrix.one_mul]
  have hconjU : (D.ιp (wGLH p h))⁻¹ * discShiftH θG ψ U hU h D u a * D.ιp (wGLH p h) ∈ U :=
    (D.w_conj_mem_U _ hu'U hgb).2
  have hθW : θG ((D.ιp (wGLH p h))⁻¹ * discShiftH θG ψ U hU h D u a * D.ιp (wGLH p h))
      = wQHinv p h * θG (discShiftH θG ψ U hU h D u a) * wQH p h := by
    rw [map_mul, map_mul, ← map_inv D.ιp, D.theta_ιp, D.theta_ιp, coe_wGLH, coe_wGLH_inv]
  have hv0 : discImage h (⟨θG ((D.ιp (wGLH p h))⁻¹ * discShiftH θG ψ U hU h D u a
      * D.ιp (wGLH p h)), hU hconjU⟩ : M1 p) 0 = 0 :=
    discImage_zero_of_norm_apply_zero_one_le_pow h _ (by
      refine (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[p] => ‖M 0 1‖) hθW).le.trans ?_
      exact (wQH_conj_mem_Iw h hgIw hgb).2.2)
  have hB : cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
      a).val : ℕ) : ℚ_[p])) * D.ιp (wGLH p h))) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact hφ.2 _ 0 j hj
  have hM1 : ((discConj h (⟨θG ((D.ιp (wGLH p h))⁻¹ * discShiftH θG ψ U hU h D u a
      * D.ιp (wGLH p h)), hU hconjU⟩ : M1 p) 0 : M1 p) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = tMatHInv p h 0 * (wQHinv p h * θG (discShiftH θG ψ U hU h D u a) * wQH p h)
        * tMatH p h 0 := by
    rw [coe_discConj, discConjMat_zero_of_discImage_zero_prime_pow h _ hv0]
    show tMatHInv p h 0 * θG ((D.ιp (wGLH p h))⁻¹ * discShiftH θG ψ U hU h D u a
      * D.ιp (wGLH p h)) * tMatH p h 0 = _
    rw [hθW]
  have hE11 : (tMatHInv p h 0 * (wQHinv p h * θG (discShiftH θG ψ U hU h D u a) * wQH p h)
      * tMatH p h 0) 1 1 = (θG (discShiftH θG ψ U hU h D u a)) 0 0 := by
    rw [wQHinv_mul_mul_wQH]
    simp [tMatHInv, tMatH, Matrix.mul_apply, Fin.sum_univ_two]
  have hE : cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
        a).val : ℕ) : ℚ_[p])) * D.ιp (wGLH p h)
        * ((D.ιp (wGLH p h))⁻¹ * discShiftH θG ψ U hU h D u a * D.ιp (wGLH p h))))
      = (nebK (ψ (((discConj h (⟨θG ((D.ιp (wGLH p h))⁻¹ * discShiftH θG ψ U hU h D u a
          * D.ιp (wGLH p h)), hU hconjU⟩ : M1 p) 0 : M1 p) :
            Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)))⁻¹ •
        symAct K k (RingHom.mapMatrix ψ ((discConj h (⟨θG ((D.ιp (wGLH p h))⁻¹
          * discShiftH θG ψ U hU h D u a * D.ιp (wGLH p h)), hU hconjU⟩ : M1 p) 0 : M1 p) :
            Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
            a).val : ℕ) : ℚ_[p])) * D.ιp (wGLH p h)))) :=
    blockProj_zero_apply_mul_mem_UH θG ψ U hU h k κ' (u := fun x => (nebK x)⁻¹) hκ' hφ _
      ⟨_, hconjU⟩ hv0
  have hLHS : cSpace.blockProj a (atkinLehnerFunHInv θG ψ U h k D φ (x * u))
      = (((D.χ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))
          * discShiftH θG ψ U hU h D u a)) : Kˣ) : K) •
        (nebK (ψ ((θG (discShiftH θG ψ U hU h D u a)) 0 0)))⁻¹ •
        symAct K k (RingHom.mapMatrix ψ (tMatHInv p h 0 * (wQHinv p h
          * θG (discShiftH θG ψ U hU h D u a) * wQH p h) * tMatH p h 0) * atkinLehnerKHinv ψ h)
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
            a).val : ℕ) : ℚ_[p])) * D.ιp (wGLH p h)))) := by
    rw [hproj, hus,
      show x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))
          * discShiftH θG ψ U hU h D u a * D.ιp (wGLH p h)
        = x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))
          * D.ιp (wGLH p h)
          * ((D.ιp (wGLH p h))⁻¹ * discShiftH θG ψ U hU h D u a * D.ιp (wGLH p h)) by group,
      hE, hM1, hE11, map_smul, symAct_mul k _ _ hB]
  have hf' : cSpace.blockProj (discImage h (⟨θG u, hU u.2⟩ : M1 p) a)
      (atkinLehnerFunHInv θG ψ U h k D φ x) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]
    exact atkinLehnerFunHInv_mem_locPolyDegSubmodule θG ψ U h k D φ x _ j hj
  have hRHS : cSpace.blockProj a (discSlash h ψ κ (⟨θG u, hU u.2⟩ : M1 p)
      (atkinLehnerFunHInv θG ψ U h k D φ x))
      = nebK (ψ ((θG (discShiftH θG ψ U hU h D u a)) 1 1)) •
        (((D.χ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) :
          ℚ_[p])))) : Kˣ) : K) •
        symAct K k (atkinLehnerKHinv ψ h * RingHom.mapMatrix ψ (tMatHInv p h 0
          * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0))
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p)
            a).val : ℕ) : ℚ_[p])) * D.ιp (wGLH p h)))) := by
    rw [blockProj_discSlash, kappaSlash_eq_smul_symAct_of_shape κ
      (discConjK h (⟨θG u, hU u.2⟩ : M1 p) a ψ) (hκ _) hf', hK11, hK, hproj, map_smul,
      symAct_mul k _ _ hB]
  have hmat : RingHom.mapMatrix ψ (tMatHInv p h 0 * (wQHinv p h
        * θG (discShiftH θG ψ U hU h D u a) * wQH p h) * tMatH p h 0) * atkinLehnerKHinv ψ h
      = atkinLehnerKHinv ψ h * RingHom.mapMatrix ψ (tMatHInv p h 0
        * θG (discShiftH θG ψ U hU h D u a) * tMatH p h 0) := by
    have h2 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], wQH p h * (wQHinv p h * X) = X := fun X => by
      rw [← Matrix.mul_assoc, wQH_mul_wQHinv, Matrix.one_mul]
    have hQ : ∀ g : Matrix (Fin 2) (Fin 2) ℚ_[p],
        tMatHInv p h 0 * (wQHinv p h * g * wQH p h) * tMatH p h 0
          * (tMatHInv p h 0 * wQHinv p h * tMatH p h 0)
          = tMatHInv p h 0 * wQHinv p h * tMatH p h 0 * (tMatHInv p h 0 * g * tMatH p h 0) :=
      fun g => by simp only [Matrix.mul_assoc, ht1, h2]
    rw [atkinLehnerKHinv_eq, ← map_mul, ← map_mul, hQ]
  rw [hLHS, hRHS, hmat, smul_smul, smul_smul]
  congr 1
  have hn00 := hne _ h00
  have hn11 := hne _ h11
  rw [map_mul, Units.val_mul, D.χ_U _ hu'U, ← hdet]
  have hχ0 : (((D.χ (x * D.ιp (sGL p (((discImage h (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) :
      ℚ_[p])))) : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

/-- The inverse map on classical disc forms at level `h`. -/
def atkinLehnerMapHInv (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ' →ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ where
  toFun φ := ⟨⟨atkinLehnerFunHInv θG ψ U h k D φ.1, fun γ hγ x =>
      atkinLehnerFunHInv_left_invt θG ψ U h k D φ.1 hγ x⟩,
    ⟨(mem_discForms_iff θG h ψ κ U hU _).2 fun u x =>
        atkinLehnerFunHInv_slash θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ.2 u x,
      fun x => atkinLehnerFunHInv_mem_locPolyDegSubmodule θG ψ U h k D φ.1 x⟩⟩
  map_add' φ φ' := by
    refine Subtype.ext (AutomorphicFunction.ext fun x => ?_)
    change atkinLehnerFunHInv θG ψ U h k D (φ.1 + φ'.1) x
      = atkinLehnerFunHInv θG ψ U h k D φ.1 x + atkinLehnerFunHInv θG ψ U h k D φ'.1 x
    simp only [atkinLehnerFunHInv, AutomorphicFunction.add_apply, map_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' r φ := by
    refine Subtype.ext (AutomorphicFunction.ext fun x => ?_)
    change atkinLehnerFunHInv θG ψ U h k D (r • φ.1) x = r • atkinLehnerFunHInv θG ψ U h k D φ.1 x
    rw [atkinLehnerFunHInv, atkinLehnerFunHInv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [AutomorphicFunction.smul_apply, map_smul]
    exact smul_comm _ _ _

/-- `W' ∘ W = 1` at level `h`. -/
theorem atkinLehnerMapHInv_atkinLehnerMapH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ'
        (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ) = φ := by
  refine Subtype.ext (AutomorphicFunction.ext fun x => cSpace_ext_blockProjH h fun a => ?_)
  set Φ := atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ'
    (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ) with hΦ
  rw [shapiro_blockProjH θG ψ U hU h D κ Φ.2.1 x a, shapiro_blockProjH θG ψ U hU h D κ φ.2.1 x a]
  set y := x * D.ιp (sGL p (a.val : ℚ_[p])) with hy
  have hf : cSpace.blockProj 0 (φ.1 y) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact φ.2.2 y 0 j hj
  change cSpace.blockProj 0 (atkinLehnerFunHInv θG ψ U h k D
      (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ).1 y)
    = cSpace.blockProj 0 (φ.1 y)
  rw [atkinLehnerFunHInv_blockProj_zero]
  change _ • symAct K k _
      (cSpace.blockProj 0 (atkinLehnerFunH θG ψ U h k D φ.1 (y * D.ιp (wGLH p h)))) = _
  rw [atkinLehnerFunH_blockProj_zero, mul_inv_cancel_right, map_smul, symAct_mul k _ _ hf,
    atkinLehnerKH_mul_atkinLehnerKHinv, symAct_one k hf, smul_smul,
    map_mul D.χ y (D.ιp (wGLH p h)), D.χ_wGLH, mul_one, mul_inv_cancel₀ (Units.ne_zero _),
    one_smul]

/-- `W ∘ W' = 1` at level `h`. -/
theorem atkinLehnerMapH_atkinLehnerMapHInv (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ') :
    atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ'
        (atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ) = φ := by
  refine Subtype.ext (AutomorphicFunction.ext fun x => cSpace_ext_blockProjH h fun a => ?_)
  set Φ := atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ'
    (atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ) with hΦ
  rw [shapiro_blockProjH θG ψ U hU h D κ' Φ.2.1 x a,
    shapiro_blockProjH θG ψ U hU h D κ' φ.2.1 x a]
  set y := x * D.ιp (sGL p (a.val : ℚ_[p])) with hy
  have hf : cSpace.blockProj 0 (φ.1 y) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact φ.2.2 y 0 j hj
  change cSpace.blockProj 0 (atkinLehnerFunH θG ψ U h k D
      (atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ).1 y)
    = cSpace.blockProj 0 (φ.1 y)
  rw [atkinLehnerFunH_blockProj_zero]
  change _ • symAct K k _
      (cSpace.blockProj 0 (atkinLehnerFunHInv θG ψ U h k D φ.1 (y * (D.ιp (wGLH p h))⁻¹))) = _
  rw [atkinLehnerFunHInv_blockProj_zero, inv_mul_cancel_right, map_smul, symAct_mul k _ _ hf,
    atkinLehnerKHinv_mul_atkinLehnerKH, symAct_one k hf, smul_smul,
    map_mul D.χ y (D.ιp (wGLH p h))⁻¹, map_inv D.χ, D.χ_wGLH, inv_one, mul_one,
    inv_mul_cancel₀ (Units.ne_zero _), one_smul]

/-- **The Atkin–Lehner isomorphism** `S^D_{k+2}(ψ) ≃ S^D_{k+2}(ψ⁻¹)` at level `h`. -/
def atkinLehnerEquivH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ ≃ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ' :=
  LinearEquiv.ofLinear (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ')
    (atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ')
    (LinearMap.ext fun φ =>
      atkinLehnerMapH_atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ)
    (LinearMap.ext fun φ =>
      atkinLehnerMapHInv_atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ)

/-! ### The block model of the classical disc forms at level `h` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharZero K] in
/-- Evaluation at the representatives sends classical disc forms into the block-model
classical subspace. -/
theorem discEvalAtReps_mem_locPolyDegSubmoduleBlockH (c : ι → G)
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    discEvalAtReps θG h ψ κ U hU c ⟨φ.1, φ.2.1⟩ ∈ locPolyDegSubmoduleBlock p ι K h k := by
  intro i a j hj
  rw [discEvalAtReps_apply]
  exact φ.2.2 (c i) a j hj

/-- **The block model of the classical disc forms at a neat level**, at level `h`
(`bijective_discEvalAtReps_of_stabilizer_eq_bot`). -/
def discEvalAtRepsClH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ ≃ₗ[K] locPolyDegSubmoduleBlock p ι K h k :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (locPolyDegSubmoduleBlock p ι K h k)
      ((discEvalAtReps θG h ψ κ U hU c).comp (Submodule.inclusion inf_le_left))
      (fun φ => discEvalAtReps_mem_locPolyDegSubmoduleBlockH θG ψ U hU h k κ c φ))
    (by
      have hbij := bijective_discEvalAtReps_of_stabilizer_eq_bot θG h ψ κ U hU c hc hstab
      refine ⟨fun φ φ' hφφ' => ?_, fun F => ?_⟩
      · exact Submodule.inclusion_injective _ (hbij.1 (congrArg Subtype.val hφφ'))
      · obtain ⟨Φ, hΦ⟩ := hbij.2 F.1
        have hloc : ∀ g, (Φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) g
            ∈ locPolyDegSubmodule p K h k := by
          intro g
          obtain ⟨i, hi⟩ := hc.2 (Quotient.mk'' g)
          obtain ⟨γ, hγ, v, hv, rfl⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi)
          have hci : (Φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (c i)
              ∈ locPolyDegSubmodule p K h k := by
            intro a j hj
            rw [← discEvalAtReps_apply θG h ψ κ U hU c Φ i (a, j), hΦ]
            exact F.2 i a j hj
          rw [mul_assoc, AutomorphicFunction.left_invt' _ hγ]
          have hres := (mem_discForms_iff θG h ψ κ U hU _).1 Φ.2 ⟨v, hv⟩ (c i)
          change (Φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)).toFun (c i * v) ∈ _
          rw [hres]
          exact discSlash_mem_locPolyDegSubmodule_of_shape h ψ κ _ (fun a => hκ _) hci
        exact ⟨⟨Φ.1, Φ.2, hloc⟩, Subtype.ext hΦ⟩)

omit [CharZero K] in
theorem discEvalAtRepsClH_apply {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    (discEvalAtRepsClH θG ψ U hU h k κ hκ c hc hstab φ : c(ι × (ZMod (p ^ h) × ℕ), K))
      = discEvalAtReps θG h ψ κ U hU c ⟨φ.1, φ.2.1⟩ :=
  rfl

end LWX

end
