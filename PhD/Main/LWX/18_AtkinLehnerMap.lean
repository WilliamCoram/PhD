/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«15_SymPow»
import PhD.Main.LWX.«17_NebChar»
import PhD.Main.LWX.«10_AtkinLehnerLocal»

/-!
# The Atkin–Lehner map on classical disc forms

[LWX, Prop 3.22]'s proof pairs `S^D_{k+2}(K^pIw_{p^m}; ψ)` with `S^D_{k+2}(K^pIw_{p^m}; ψ⁻¹)` by
"twist[ing] the representation `π` by a central Hecke character associated to `ψ⁻¹`"
(`lwx.txt:1783–1786`).  Realised without Jacquet–Langlands, the pairing is the **Atkin–Lehner
map** `W : φ ↦ χ⁻¹ · (φ ∣ w)`, `(φ ∣ w)(x) = φ(x w⁻¹) ∣_k w` (Buzzard's `(f|η)(g) = f(gη⁻¹)·η_p`,
`bu04.txt:633`), with `w` the Atkin–Lehner element of level `p²` and `χ` the Hecke character
`ψ_A ∘ ν` of the reduced norm: `w` normalises `Iw_{p²}` and swaps the diagonal
(`atkinLehnerConj_apply_one_one`), which inverts the nebentypus up to `ψ(det)`, and the twist
by `χ` removes that `ψ(det)`.

The map lives on the **classical** disc forms — locally polynomial of degree `≤ k` — because
`w` acts on polynomials of degree `≤ k` through `symAct` (it is not in the disc model's monoid
`M₁`).  Its definition on the disc model reads disc `a` of `φ(x)` as disc `0` of `φ(x·s_a)`
(`shapiro_blockProj`, the translation `s_a = (1 a; 0 1)`), where `w` acts through its disc-`0`
conjugate `t₀⁻¹ w t₀ = (0 1; −p² 0)`.

## The global data

`AtkinLehnerData` bundles what the abstract group `G` must supply, all satisfied by the finite
adèles of a definite quaternion algebra: a section `ιp : GL₂(ℚ_p) → G` of the `p`-component
(the local elements `v_c`, `s_b`, `w`, `p·1` as elements of `G`), the level `U ⊇ ιp(Iw_p)`, the
central element `p` lying in `Γ · (U ∩ ker θ)` (so it acts trivially), and the Hecke character
`χ` with `χ|_Γ = 1`, `χ(u) = ψ_neb(det θ u)` on `U`, `χ(v_c) = χ(w) = 1`.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash RightSlashAction
open scoped TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The local elements as elements of `GL₂(ℚ_p)` -/

variable (p) in
/-- The `U_p`-representative `(p 0; cp 1)` as an element of `GL₂(ℚ_p)`. -/
def vGL (c : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (vQ p c) (by
    rw [det_vQ]; exact Nat.cast_ne_zero.2 hp.out.ne_zero)

variable (p) in
/-- The translation `(1 b; 0 1)` as an element of `GL₂(ℚ_p)`. -/
def sGL (b : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (sQ p b) (by rw [det_sQ]; exact one_ne_zero)

variable (p) in
/-- The Atkin–Lehner element `(0 p; −p 0)` as an element of `GL₂(ℚ_p)`. -/
def wGL : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (wQ p) (by
    rw [det_wQ]; exact pow_ne_zero 2 (Nat.cast_ne_zero.2 hp.out.ne_zero))

variable (p) in
/-- The central element `p·1` as an element of `GL₂(ℚ_p)`. -/
def pGL : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])) (by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_ne_zero 2 (Nat.cast_ne_zero.2 hp.out.ne_zero))

variable (p) in
/-- The Iwahori element `ℓQ b c` as an element of `GL₂(ℚ_p)`. -/
def ℓGL (b c : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (ℓQ p b c) (by rw [det_ℓQ]; exact one_ne_zero)

@[simp] theorem coe_vGL (c : ℚ_[p]) : (vGL p c : Matrix (Fin 2) (Fin 2) ℚ_[p]) = vQ p c := rfl
@[simp] theorem coe_sGL (b : ℚ_[p]) : (sGL p b : Matrix (Fin 2) (Fin 2) ℚ_[p]) = sQ p b := rfl
@[simp] theorem coe_wGL : (wGL p : Matrix (Fin 2) (Fin 2) ℚ_[p]) = wQ p := rfl
@[simp] theorem coe_ℓGL (b c : ℚ_[p]) : (ℓGL p b c : Matrix (Fin 2) (Fin 2) ℚ_[p]) = ℓQ p b c := rfl

theorem coe_wGL_inv : ((wGL p)⁻¹ : GL (Fin 2) ℚ_[p]) = (wQinv p : Matrix _ _ _) := by
  rw [Matrix.coe_units_inv, coe_wGL]
  exact Matrix.inv_eq_right_inv wQ_mul_wQinv

theorem coe_ℓGL_inv (b c : ℚ_[p]) :
    ((ℓGL p b c)⁻¹ : GL (Fin 2) ℚ_[p]) = (ℓQinv p b c : Matrix _ _ _) := by
  rw [Matrix.coe_units_inv, coe_ℓGL]
  exact Matrix.inv_eq_right_inv (ℓQ_mul_ℓQinv b c)

@[simp] theorem sGL_zero : sGL p 0 = 1 := by
  refine Units.ext ?_
  rw [coe_sGL, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sQ]

theorem sGL_mul (a b : ℚ_[p]) : sGL p a * sGL p b = sGL p (a + b) := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_sGL, coe_sGL, coe_sGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sQ, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sGL_inv (b : ℚ_[p]) : (sGL p b)⁻¹ = sGL p (-b) := by
  rw [inv_eq_iff_mul_eq_one, sGL_mul, add_neg_cancel, sGL_zero]

/-- **The key factorisation in `GL₂(ℚ_p)`**: `w v_b w⁻¹ v_c = ℓ_{b,c} · (p·1) · s_{−b}`
(`wQ_mul_vQ_mul_wQinv_mul_vQ`, `Units.ext`). -/
theorem wGL_mul_vGL_mul_wGL_inv_mul_vGL (b c : ℚ_[p]) :
    wGL p * vGL p b * (wGL p)⁻¹ * vGL p c = ℓGL p b c * (pGL p * sGL p (-b)) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_wGL, coe_vGL, coe_wGL_inv, coe_ℓGL, coe_sGL]
  rw [wQ_mul_vQ_mul_wQinv_mul_vQ]
  show _ = ℓQ p b c * (((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])) * sQ p (-b))
  rw [smul_mul_assoc, one_mul]

/-- The disc-`0` conjugate of the Atkin–Lehner element, in `K`: `(0 1; −p² 0)`. -/
def atkinLehnerK (ψ : ℚ_[p] →+* K) : Matrix (Fin 2) (Fin 2) K :=
  RingHom.mapMatrix ψ (atkinLehner p 2)

/-- Its inverse `(0 −p⁻²; 1 0)`. -/
def atkinLehnerKinv (ψ : ℚ_[p] →+* K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, -((ψ p) ^ 2)⁻¹; 1, 0]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem atkinLehnerK_mul_atkinLehnerKinv (ψ : ℚ_[p] →+* K) :
    atkinLehnerK ψ * atkinLehnerKinv ψ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehnerK, atkinLehnerKinv, atkinLehner, Matrix.mul_apply, Fin.sum_univ_two]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem atkinLehnerKinv_mul_atkinLehnerK (ψ : ℚ_[p] →+* K) :
    atkinLehnerKinv ψ * atkinLehnerK ψ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehnerK, atkinLehnerKinv, atkinLehner, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The global data -/

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable (ψ : ℚ_[p] →+* K)
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)

/-- **The Atkin–Lehner data** ([LWX, §2.4] setup plus the Hecke character of
`lwx.txt:1783–1786`): a section of the `p`-component, the level containing the local Iwahori,
the central `p` acting trivially, and the twist `χ`. -/
structure AtkinLehnerData (Γ : Subgroup G) (nebK : K → K) where
  /-- A section `GL₂(ℚ_p) → G` of the `p`-component `θ`. -/
  ιp : GL (Fin 2) ℚ_[p] →* G
  theta_ιp : ∀ g, θG (ιp g) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p])
  /-- The level contains the lifts of the local Iwahori subgroup `Iw_p`. -/
  ιp_mem_U : ∀ g : GL (Fin 2) ℚ_[p], (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1 → ιp g ∈ U
  /-- The central element `p` (at `p`) is a global central element times an element of the
  level with trivial `p`-component: `p_p = p_global · (p^{(p)})⁻¹`. -/
  central : ∃ γ ∈ Γ, ∃ u ∈ U, ιp (pGL p) = γ * u ∧ θG u = 1 ∧ ∀ x, γ * x = x * γ
  /-- The Hecke character `ψ_A ∘ ν`. -/
  χ : G →* Kˣ
  χ_Γ : ∀ γ ∈ Γ, χ γ = 1
  χ_U : ∀ u ∈ U, (χ u : K) = nebK (ψ (θG u).det)
  χ_vGL : ∀ c : ℚ_[p], χ (ιp (vGL p c)) = 1
  χ_wGL : χ (ιp (wGL p)) = 1
  /-- **`w` normalises the disc-`0` part of the level**: for `u ∈ U` with `p ∣ b(θ u)`, both
  `w u w⁻¹` and `w⁻¹ u w` lie in `U` (for `U = K^p·Iw_p` this is the local computation
  `w (a b; c d) w⁻¹ = (d, −c; −b, a)`). -/
  w_conj_mem_U : ∀ u ∈ U, ‖(θG u) 0 1‖ ≤ (p : ℝ)⁻¹ →
    ιp (wGL p) * u * (ιp (wGL p))⁻¹ ∈ U ∧ (ιp (wGL p))⁻¹ * u * ιp (wGL p) ∈ U

variable (k : ℕ)

/-! ### Consequences of the data -/

variable {nebK : K → K} (D : AtkinLehnerData θG ψ U Γ nebK)

include hU in
/-- `θ(u) ∈ Iw_p` for `u ∈ U`: `θ u` and `θ u⁻¹` are both in `M₁`, so `‖det θ u‖ = 1`. -/
theorem theta_mem_Iw (u : U) : θG u ∈ Iw p 1 := by
  have h1 : θG u ∈ M1 p := hU u.2
  have h2 : θG (u : G)⁻¹ ∈ M1 p := hU (inv_mem u.2)
  obtain ⟨he, hc, -, -⟩ := h1
  refine mem_Iw_iff.2 ⟨he, by simpa using hc, ?_⟩
  have hdet : (θG u).det * (θG (u : G)⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]
  have hn1 : ‖(θG u).det‖ ≤ 1 := norm_det_fin_two_le_one he
  have hn2 : ‖(θG (u : G)⁻¹).det‖ ≤ 1 := norm_det_fin_two_le_one h2.1
  have hprod : ‖(θG u).det‖ * ‖(θG (u : G)⁻¹).det‖ = 1 := by rw [← norm_mul, hdet, norm_one]
  nlinarith [norm_nonneg (θG u).det, mul_nonneg (norm_nonneg (θG u).det) (sub_nonneg.2 hn2)]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The central element `p` (at `p`) acts trivially on the level: `θ(ιp p) = p • 1`. -/
theorem theta_ιp_pGL : θG (D.ιp (pGL p)) = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
  D.theta_ιp (pGL p)

/-- **The disc-shifted level element** `u' := s_{a'}⁻¹ u s_a ∈ U`, `a' = discImage (θ u) a`;
it fixes disc `0` and its disc-`0` conjugate is the disc-`a` conjugate of `θ u`. -/
def discShift (u : U) (a : ZMod (p ^ 1)) : G :=
  D.ιp (sGL p (-(((discImage 1 ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p]))) * u
    * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p]))

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem discShift_mem_U (u : U) (a : ZMod (p ^ 1)) : discShift θG ψ U hU D u a ∈ U := by
  refine mul_mem (mul_mem (D.ιp_mem_U _ (sQ_mem_Iw ?_)) u.2) (D.ιp_mem_U _ (sQ_mem_Iw ?_))
  · rw [norm_neg]; exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  · exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] _

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem theta_discShift (u : U) (a : ZMod (p ^ 1)) :
    θG (discShift θG ψ U hU D u a)
      = sQ p (-(((discImage 1 ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p])) * θG u
        * sQ p ((a.val : ℕ) : ℚ_[p]) := by
  rw [discShift, map_mul, map_mul, D.theta_ιp, D.theta_ιp, coe_sGL, coe_sGL]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `u s_a = s_{a'} u'`. -/
theorem mul_ιp_sGL_eq (u : U) (a : ZMod (p ^ 1)) :
    (u : G) * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p]))
      = D.ιp (sGL p (((discImage 1 ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p]))
        * discShift θG ψ U hU D u a := by
  rw [discShift, ← mul_assoc, ← mul_assoc, ← map_mul, sGL_mul, add_neg_cancel, sGL_zero, map_one,
    one_mul]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem norm_theta_discShift_zero_one_le (u : U) (a : ZMod (p ^ 1)) :
    ‖(θG (discShift θG ψ U hU D u a)) 0 1‖ ≤ (p : ℝ)⁻¹ := by
  have hc : sQ p (-(((discImage 1 ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p])) * θG u
        * sQ p ((a.val : ℕ) : ℚ_[p])
      = tMat p 0 * discConjMat 1 (⟨θG u, hU u.2⟩ : M1 p) a * tMatInv p 0 :=
    conj_sQ_eq_tMat_mul_discConjMat _ a
  have hM := discConjMat_mem_Mh 1 (⟨θG u, hU u.2⟩ : M1 p) a
  have h01 : (tMat p 0 * discConjMat 1 (⟨θG u, hU u.2⟩ : M1 p) a * tMatInv p 0) 0 1
      = (p : ℚ_[p]) * discConjMat 1 (⟨θG u, hU u.2⟩ : M1 p) a 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [tMat, tMatInv]
  rw [theta_discShift, hc, h01, norm_mul, Padic.norm_p]
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) ((mem_Mh_iff.1 hM).1 0 1)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem discImage_discShift_zero (u : U) (a : ZMod (p ^ 1)) :
    discImage 1 (⟨θG (discShift θG ψ U hU D u a), hU (discShift_mem_U θG ψ U hU D u a)⟩ : M1 p) 0
      = 0 :=
  discImage_zero_of_norm_apply_zero_one_le _ (norm_theta_discShift_zero_one_le θG ψ U hU D u a)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The disc-`0` conjugate of `u'` is the disc-`a` conjugate of `θ u`. -/
theorem discConjMat_discShift_zero (u : U) (a : ZMod (p ^ 1)) :
    discConjMat 1
        (⟨θG (discShift θG ψ U hU D u a), hU (discShift_mem_U θG ψ U hU D u a)⟩ : M1 p) 0
      = discConjMat 1 (⟨θG u, hU u.2⟩ : M1 p) a := by
  have hc : sQ p (-(((discImage 1 ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p])) * θG u
        * sQ p ((a.val : ℕ) : ℚ_[p])
      = tMat p 0 * discConjMat 1 (⟨θG u, hU u.2⟩ : M1 p) a * tMatInv p 0 :=
    conj_sQ_eq_tMat_mul_discConjMat _ a
  rw [discConjMat_zero_of_discImage_zero _ (discImage_discShift_zero θG ψ U hU D u a)]
  change tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0 = _
  rw [theta_discShift, hc, ← mul_assoc, ← mul_assoc, tMatInv_mul_tMat, one_mul, mul_assoc,
    tMatInv_mul_tMat, mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `w₂ = t₀⁻¹ w t₀` in `K`. -/
theorem atkinLehnerK_eq : atkinLehnerK ψ = RingHom.mapMatrix ψ (tMatInv p 0 * wQ p * tMat p 0) := by
  have h1 : tMatInv p 0 = !![(p : ℚ_[p])⁻¹, 0; 0, 1] := by simp [tMatInv]
  have h2 : tMat p 0 = !![(p : ℚ_[p]), 0; 0, 1] := rfl
  rw [atkinLehnerK, h1, h2, discConjMat_wQ]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `w₂⁻¹ = t₀⁻¹ w⁻¹ t₀` in `K`. -/
theorem atkinLehnerKinv_eq :
    atkinLehnerKinv ψ = RingHom.mapMatrix ψ (tMatInv p 0 * wQinv p * tMat p 0) := by
  have h1 : tMatInv p 0 = !![(p : ℚ_[p])⁻¹, 0; 0, 1] := by simp [tMatInv]
  have h2 : tMat p 0 = !![(p : ℚ_[p]), 0; 0, 1] := rfl
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehnerKinv, wQinv, hp0, sq]

omit hp [CharZero K] in
/-- Two block functions agree iff all their blocks do. -/
theorem cSpace_ext_blockProj {f g : c(ZMod (p ^ 1) × ℕ, K)}
    (h : ∀ a, cSpace.blockProj a f = cSpace.blockProj a g) : f = g := by
  refine DFunLike.ext _ _ fun x => ?_
  have hx := congrArg (fun F => F x.2) (h x.1)
  simpa [cSpace.blockProj_apply] using hx

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `nebK 1 = 1` (from the conductor hypothesis). -/
theorem nebK_one (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1) :
    nebK (ψ 1) = 1 :=
  hcond 1 (by rw [sub_self, norm_zero]; positivity)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **`nebK(a)·nebK(d) = nebK(det)`** on the disc-`0` stabiliser of `Iw_p` (`ad = det + bc` with
`p ∣ b`, `p ∣ c`, so `ad/det ≡ 1 (mod p²)`). -/
theorem nebK_mul_nebK_eq_nebK_det
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1) (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹) :
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
  have hen : ‖g 0 1 * g 1 0 / g.det‖ ≤ (p : ℝ)⁻¹ ^ 2 := by
    rw [norm_div, hdet, div_one, norm_mul, sq]
    exact mul_le_mul hb hc' (norm_nonneg _) (inv_nonneg.2 (Nat.cast_nonneg _))
  have hel : ‖g 0 1 * g 1 0 / g.det‖ < 1 := by
    refine hen.trans_lt ?_
    rw [sq]
    exact mul_lt_one_of_nonneg_of_lt_one_left (inv_nonneg.2 (Nat.cast_nonneg _))
      (inv_lt_one_p (p := p)) (inv_lt_one_p (p := p)).le
  have h1e : ‖(1 : ℚ_[p]) + g 0 1 * g 1 0 / g.det‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hel.ne'),
      norm_one, max_eq_left hel.le]
  rw [← hmul _ _ ha hd, hsplit, hmul _ _ hdet h1e,
    hcond (1 + g 0 1 * g 1 0 / g.det) (by rw [add_sub_cancel_left]; exact hen), mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `nebK(1 − x) = nebK(1 + x)⁻¹` for `‖x‖ ≤ p⁻¹` (`(1−x)(1+x) ≡ 1 (mod p²)`). -/
theorem nebK_one_sub_eq_inv
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (_hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    {x : ℚ_[p]} (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
    nebK (ψ (1 - x)) = (nebK (ψ (1 + x)))⁻¹ := by
  have hxl : ‖x‖ < 1 := hx.trans_lt (inv_lt_one_p (p := p))
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
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  exact eq_inv_of_mul_eq_one_left hprod

/-! ### Classical disc forms -/

variable (p K) in
/-- The automorphic functions whose every value is locally polynomial of degree `≤ k`. -/
def locPolyForms : Submodule K (AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) where
  carrier := {φ | ∀ x, φ x ∈ locPolyDegSubmodule p K 1 k}
  add_mem' hφ hφ' x := Submodule.add_mem _ (hφ x) (hφ' x)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' r _ hφ x := Submodule.smul_mem _ r (hφ x)

variable {UK : Subgroup Kˣ} {ρ : ℝ} (κ : AnalyticWeight UK (M1Kh 1 ψ) ρ)

/-- **The classical disc forms** `S^D_{k+2}(K^p Iw_{p²}; ψ)` in the disc model ([LWX, §2.4]:
values in `Ind^{Iw_q}_B(χ)^{m,alg}`, the locally polynomial functions of degree `≤ k`
on the `p`-discs). -/
def ClassicalDiscForms : Submodule K (AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) :=
  DiscForms (Γ := Γ) θG 1 ψ κ U hU ⊓ locPolyForms p K (Γ := Γ) k

omit [CharZero K] in
theorem mem_classicalDiscForms_iff (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) :
    φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ
      ↔ φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU ∧ ∀ x, φ x ∈ locPolyDegSubmodule p K 1 k :=
  Iff.rfl

omit [CharZero K] in
/-- `U_p` preserves the classical disc forms at a classical-shape weight
(`discSlash_mem_locPolyDegSubmodule_of_shape` at every representative). -/
theorem discHeckeOperator_mem_classicalDiscForms {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite)
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    ((discHeckeOperator θG 1 ψ κ U hU hη hfin ⟨φ, hφ.1⟩ : DiscForms (Γ := Γ) θG 1 ψ κ U hU) :
        AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ := by
  letI := discLevelSlashAction θG 1 ψ κ
  letI := discLevelSMulSlashClass θG 1 ψ κ
  refine ⟨(discHeckeOperator θG 1 ψ κ U hU hη hfin ⟨φ, hφ.1⟩).2, fun x => ?_⟩
  have : Fintype (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)) := hfin.fintype
  have hev : ∀ (s : Finset (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
        Set (RightCosets U)))
      (F : _ → AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (g : G),
      (∑ i ∈ s, F i) g = ∑ i ∈ s, F i g := fun s F g =>
    map_sum (AddMonoidHom.mk' (fun φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K) => φ g)
      (fun _ _ => rfl)) F s
  change (AbstractHeckeOperatorSlash.heckeOperatorSlash K hU hU hη hfin ⟨φ, hφ.1⟩ :
    AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) x ∈ _
  rw [AbstractHeckeOperatorSlash.heckeOperatorSlash_apply, finsum_eq_sum_of_fintype, hev]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact discSlash_mem_locPolyDegSubmodule_of_shape 1 ψ κ _
    (u := fun a => u ((discConjK 1 (levelM1ToM1 (p := p) θG ⟨_, _⟩) a ψ : Matrix (Fin 2) (Fin 2) K) 1 1))
    (fun a => hκ _) (hφ.2 _)

/-- **`U_p` on the classical disc forms.** -/
def discHeckeOperatorCl {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ →ₗ[K] ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ where
  toFun φ := ⟨(discHeckeOperator θG 1 ψ κ U hU hη hfin ⟨φ.1, φ.2.1⟩ :
      DiscForms (Γ := Γ) θG 1 ψ κ U hU).1,
    discHeckeOperator_mem_classicalDiscForms θG ψ U hU k κ hκ hη hfin φ.2⟩
  map_add' φ φ' := by
    apply Subtype.ext
    change (discHeckeOperator θG 1 ψ κ U hU hη hfin (⟨φ.1, φ.2.1⟩ + ⟨φ'.1, φ'.2.1⟩) :
      DiscForms (Γ := Γ) θG 1 ψ κ U hU).1 = _
    rw [map_add]
    rfl
  map_smul' r φ := by
    apply Subtype.ext
    change (discHeckeOperator θG 1 ψ κ U hU hη hfin (r • ⟨φ.1, φ.2.1⟩) :
      DiscForms (Γ := Γ) θG 1 ψ κ U hU).1 = _
    rw [map_smul]
    rfl

/-! ### Reading disc `a` as disc `0` -/

omit [CharZero K] in
/-- **A level element with trivial `p`-component acts trivially**: `φ(x u) = φ(x)` for `u ∈ U`,
`θ u = 1`. -/
theorem apply_mul_of_theta_eq_one {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) {u : G} (hu : u ∈ U) (hθ : θG u = 1) :
    φ (x * u) = φ x := by
  have h := (mem_discForms_iff θG 1 ψ κ U hU φ).1 hφ ⟨u, hu⟩ x
  have h1 : (⟨θG ((⟨u, hu⟩ : U) : G), hU (⟨u, hu⟩ : U).2⟩ : M1 p) = 1 := Subtype.ext hθ
  rw [h1, discSlash_one] at h
  exact h

omit [CharZero K] in
/-- **Level-equivariance on disc `0`** at a level element fixing disc `0`, for a classical form
at a classical-shape weight (`mem_discForms_iff`, `blockProj_discSlash`,
`kappaSlash_eq_smul_symAct_of_shape`). -/
theorem blockProj_zero_apply_mul_mem_U {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) (v : U)
    (hv0 : discImage 1 (⟨θG v, hU v.2⟩ : M1 p) 0 = 0) :
    cSpace.blockProj 0 (φ (x * v))
      = u (ψ ((discConj 1 (⟨θG v, hU v.2⟩ : M1 p) 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj 1 (⟨θG v, hU v.2⟩ : M1 p) 0 :
          Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ x)) := by
  have h := (mem_discForms_iff θG 1 ψ κ U hU φ).1 hφ.1 v x
  have hf : cSpace.blockProj 0 (φ x) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact hφ.2 x 0 j hj
  change cSpace.blockProj 0 (φ.toFun (x * v)) = _
  rw [h, blockProj_discSlash, hv0]
  exact kappaSlash_eq_smul_symAct_of_shape κ (discConjK 1 ⟨θG v, hU v.2⟩ 0 ψ) (hκ _) hf

omit [CharZero K] in
/-- **Disc `a` of `φ(x)` is disc `0` of `φ(x·s_a)`**: the translation `s_a` lies in `U`, moves
disc `0` to disc `a` and has trivial disc conjugate (`discImage_sQ_zero`, `discConj_sQ_zero`). -/
theorem shapiro_blockProj {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) (a : ZMod (p ^ 1)) :
    cSpace.blockProj a (φ x) = cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])))) := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  have ha : a.val < p := by simpa using ZMod.val_lt a
  have hs : sQ p ((a.val : ℕ) : ℚ_[p]) ∈ Iw p 1 :=
    sQ_mem_Iw (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)
  set v : U := ⟨D.ιp (sGL p (a.val : ℚ_[p])), D.ιp_mem_U _ hs⟩ with hv
  have h := (mem_discForms_iff θG 1 ψ κ U hU φ).1 hφ v x
  have hθ : (⟨θG v, hU v.2⟩ : M1 p) = ⟨sQ p (a.val : ℕ), Iw_one_le_M1 hs⟩ :=
    Subtype.ext (D.theta_ιp _)
  have hK : discConjK 1 (⟨sQ p (a.val : ℕ), Iw_one_le_M1 hs⟩ : M1 p) 0 ψ = 1 := by
    refine Subtype.ext ?_
    rw [coe_discConjK, discConj_sQ_zero ha]
    simp
  change cSpace.blockProj a (φ.toFun x) = cSpace.blockProj 0 (φ.toFun (x * v))
  rw [h, hθ, blockProj_discSlash, discImage_sQ_zero, ZMod.natCast_zmod_val, hK,
    AnalyticWeight.kappaSlash_one]
  rfl

/-! ### The Atkin–Lehner map -/

/-- **The underlying function of `Wφ`**: on disc `a`,
`χ(x s_a)⁻¹ · (disc 0 of φ(x s_a w⁻¹)) ∣_k (0 1; −p² 0)`. -/
def atkinLehnerFun (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x : G) :
    c(ZMod (p ^ 1) × ℕ, K) :=
  ∑ a : ZMod (p ^ 1), cSpace.blockIncl a
    (((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K)⁻¹ •
      symAct K k (atkinLehnerK ψ)
        (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * (D.ιp (wGL p))⁻¹))))

omit [CharZero K] in
theorem atkinLehnerFun_blockProj (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x : G)
    (a : ZMod (p ^ 1)) :
    cSpace.blockProj a (atkinLehnerFun θG ψ U k D φ x)
      = ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerK ψ)
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * (D.ιp (wGL p))⁻¹))) := by
  rw [atkinLehnerFun, map_sum, Finset.sum_eq_single a]
  · rw [cSpace.blockProj_blockIncl, if_pos rfl]
  · intro b _ hb
    rw [cSpace.blockProj_blockIncl, if_neg (fun h => hb h.symm)]
  · intro h
    exact absurd (Finset.mem_univ a) h

omit [CharZero K] in
/-- Disc `0` of `Wφ(x)`: `χ(x)⁻¹ · (disc 0 of φ(x w⁻¹)) ∣_k w₂`. -/
theorem atkinLehnerFun_blockProj_zero (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
    (x : G) :
    cSpace.blockProj 0 (atkinLehnerFun θG ψ U k D φ x)
      = ((D.χ x : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerK ψ) (cSpace.blockProj 0 (φ (x * (D.ιp (wGL p))⁻¹))) := by
  rw [atkinLehnerFun_blockProj, ZMod.val_zero, Nat.cast_zero, sGL_zero, map_one, mul_one]

omit [CharZero K] in
/-- `Wφ` is left `Γ`-invariant. -/
theorem atkinLehnerFun_left_invt (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
    {γ : G} (hγ : γ ∈ Γ) (x : G) :
    atkinLehnerFun θG ψ U k D φ (γ * x) = atkinLehnerFun θG ψ U k D φ x := by
  simp only [atkinLehnerFun, mul_assoc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul D.χ γ, D.χ_Γ γ hγ, one_mul]
  congr 4
  exact φ.left_invt γ hγ _

omit [CharZero K] in
/-- `Wφ` is locally polynomial of degree `≤ k` (`symAct_mem_polySubmodule`). -/
theorem atkinLehnerFun_mem_locPolyDegSubmodule
    (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x : G) :
    atkinLehnerFun θG ψ U k D φ x ∈ locPolyDegSubmodule p K 1 k := by
  intro a j hj
  have h := symAct_mem_polySubmodule k (atkinLehnerK ψ)
    (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * (D.ιp (wGL p))⁻¹))) j hj
  rw [← cSpace.blockProj_apply, atkinLehnerFun_blockProj]
  exact (congrArg (fun t => ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K)⁻¹ * t) h).trans
    (mul_zero _)

variable {UK' : Subgroup Kˣ} {ρ' : ℝ} (κ' : AnalyticWeight UK' (M1Kh 1 ψ) ρ')

omit [CharZero K] in
set_option maxHeartbeats 1000000 in
/-- **`W` maps `ψ`-forms to `ψ⁻¹`-forms**: for `u ∈ U`, `(Wφ)(x u) = (Wφ)(x) ∣_{κ'} u`.  Through
`shapiro_blockProj`, `u s_a = s_{a'} u'` with `u'` fixing disc `0`; `w u' w⁻¹` is again in the
level, its `d`-entry is the `a`-entry of `u'` (`atkinLehnerConj_apply_one_one`), and
`nebK(a)·nebK(d) = nebK(det)` on `Iw^{(1)}` cancels against `χ(u') = nebK(det θ u')`. -/
theorem atkinLehnerFun_slash
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (u : U) (x : G) :
    atkinLehnerFun θG ψ U k D φ (x * u)
      = discSlash 1 ψ κ' ⟨θG u, hU u.2⟩ (atkinLehnerFun θG ψ U k D φ x) := by
  refine cSpace_ext_blockProj fun a => ?_
  have hu'U : discShift θG ψ U hU D u a ∈ U := discShift_mem_U θG ψ U hU D u a
  have hgIw : θG (discShift θG ψ U hU D u a) ∈ Iw p 1 := theta_mem_Iw θG U hU ⟨discShift θG ψ U hU D u a, hu'U⟩
  have hgb : ‖(θG (discShift θG ψ U hU D u a)) 0 1‖ ≤ (p : ℝ)⁻¹ := norm_theta_discShift_zero_one_le θG ψ U hU D u a
  have hus : x * ↑u * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p])) = x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * discShift θG ψ U hU D u a := by
    rw [mul_assoc, mul_ιp_sGL_eq θG ψ U hU D u a, ← mul_assoc]
  have hM2 : ((discConj 1 (⟨θG u, hU u.2⟩ : M1 p) a : M1 p) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0 := by
    rw [coe_discConj, ← discConjMat_discShift_zero θG ψ U hU D u a,
      discConjMat_zero_of_discImage_zero _ (discImage_discShift_zero θG ψ U hU D u a)]
  have hF11 : (tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0) 1 1 = (θG (discShift θG ψ U hU D u a)) 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [tMatInv, tMat]
  have hK : ((discConjK 1 (⟨θG u, hU u.2⟩ : M1 p) a ψ : M1Kh 1 ψ) : Matrix (Fin 2) (Fin 2) K)
      = RingHom.mapMatrix ψ (tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0) := by
    rw [coe_discConjK, hM2]
  have hK11 : ((discConjK 1 (⟨θG u, hU u.2⟩ : M1 p) a ψ : M1Kh 1 ψ) : Matrix (Fin 2) (Fin 2) K) 1 1 = ψ ((θG (discShift θG ψ U hU D u a)) 1 1) := by
    rw [hK, RingHom.mapMatrix_apply, Matrix.map_apply, hF11]
  have h00 : ‖(θG (discShift θG ψ U hU D u a)) 0 0‖ = 1 := norm_apply_zero_zero_of_mem_Iw one_ne_zero hgIw
  have h11 : ‖(θG (discShift θG ψ U hU D u a)) 1 1‖ = 1 := (Iw_one_le_M1 hgIw).2.2.1
  have hdet := nebK_mul_nebK_eq_nebK_det ψ hmul hcond hgIw hgb
  have ht1 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], tMat p 0 * (tMatInv p 0 * X) = X := fun X => by
    rw [← Matrix.mul_assoc, tMat_mul_tMatInv, Matrix.one_mul]
  have hconjU : D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹ ∈ U := (D.w_conj_mem_U _ hu'U hgb).1
  have hθW : θG (D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹) = wQ p * θG (discShift θG ψ U hU D u a) * wQinv p := by
    rw [map_mul, map_mul, ← map_inv D.ιp, D.theta_ιp, D.theta_ιp, coe_wGL, coe_wGL_inv]
  have hv0 : discImage 1 (⟨θG (D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹), hU hconjU⟩ : M1 p) 0 = 0 :=
    discImage_zero_of_norm_apply_zero_one_le _ (by
      refine (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[p] => ‖M 0 1‖) hθW).le.trans ?_
      exact (wQ_conj_mem_Iw hgIw hgb).1.2)
  have hB : cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * (D.ιp (wGL p))⁻¹)) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact hφ.2 _ 0 j hj
  have hM1 : ((discConj 1 (⟨θG (D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹), hU hconjU⟩ : M1 p) 0 : M1 p) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) = tMatInv p 0 * (wQ p * θG (discShift θG ψ U hU D u a) * wQinv p) * tMat p 0 := by
    rw [coe_discConj, discConjMat_zero_of_discImage_zero _ hv0]
    show tMatInv p 0 * θG (D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹) * tMat p 0 = _
    rw [hθW]
  have hE11 : (tMatInv p 0 * (wQ p * θG (discShift θG ψ U hU D u a) * wQinv p) * tMat p 0) 1 1 = (θG (discShift θG ψ U hU D u a)) 0 0 := by
    rw [wQ_mul_mul_wQinv]
    simp [tMatInv, tMat, Matrix.mul_apply, Fin.sum_univ_two]
  have hE : cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * (D.ιp (wGL p))⁻¹ * (D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹)))
      = nebK (ψ (((discConj 1 (⟨θG (D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹), hU hconjU⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ ((discConj 1 (⟨θG (D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹), hU hconjU⟩ :
          M1 p) 0 : M1 p) : Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * (D.ιp (wGL p))⁻¹))) :=
    blockProj_zero_apply_mul_mem_U θG ψ U hU k κ hκ hφ _ ⟨_, hconjU⟩ hv0
  have hLHS : cSpace.blockProj a (atkinLehnerFun θG ψ U k D φ (x * u))
      = (((D.χ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * discShift θG ψ U hU D u a)) : Kˣ) : K)⁻¹ • nebK (ψ ((θG (discShift θG ψ U hU D u a)) 0 0)) •
        symAct K k (RingHom.mapMatrix ψ (tMatInv p 0 * (wQ p * θG (discShift θG ψ U hU D u a) * wQinv p) * tMat p 0)
          * atkinLehnerK ψ) (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * (D.ιp (wGL p))⁻¹))) := by
    rw [atkinLehnerFun_blockProj, hus,
      show x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹ = x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * (D.ιp (wGL p))⁻¹ * (D.ιp (wGL p) * discShift θG ψ U hU D u a * (D.ιp (wGL p))⁻¹) by group,
      hE, hM1, hE11, map_smul, symAct_mul k _ _ hB]
  have hf' : cSpace.blockProj (discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a) (atkinLehnerFun θG ψ U k D φ x) ∈ polySubmodule K k :=
    fun j hj => by
      rw [cSpace.blockProj_apply]
      exact atkinLehnerFun_mem_locPolyDegSubmodule θG ψ U k D φ x _ j hj
  have hRHS : cSpace.blockProj a (discSlash 1 ψ κ' (⟨θG u, hU u.2⟩ : M1 p) (atkinLehnerFun θG ψ U k D φ x))
      = (nebK (ψ ((θG (discShift θG ψ U hU D u a)) 1 1)))⁻¹ • (((D.χ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])))) : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerK ψ * RingHom.mapMatrix ψ (tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0))
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * (D.ιp (wGL p))⁻¹))) := by
    rw [blockProj_discSlash, kappaSlash_eq_smul_symAct_of_shape κ' (discConjK 1 (⟨θG u, hU u.2⟩ : M1 p) a ψ) (hκ' _) hf',
      hK11, hK, atkinLehnerFun_blockProj, map_smul, symAct_mul k _ _ hB]
  have hmat : RingHom.mapMatrix ψ (tMatInv p 0 * (wQ p * θG (discShift θG ψ U hU D u a) * wQinv p) * tMat p 0) * atkinLehnerK ψ
      = atkinLehnerK ψ * RingHom.mapMatrix ψ (tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0) := by
    have h2 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], wQinv p * (wQ p * X) = X := fun X => by
      rw [← Matrix.mul_assoc, wQinv_mul_wQ, Matrix.one_mul]
    have hQ : ∀ g : Matrix (Fin 2) (Fin 2) ℚ_[p],
        tMatInv p 0 * (wQ p * g * wQinv p) * tMat p 0 * (tMatInv p 0 * wQ p * tMat p 0)
          = tMatInv p 0 * wQ p * tMat p 0 * (tMatInv p 0 * g * tMat p 0) := fun g => by
      simp only [Matrix.mul_assoc, ht1, h2]
    rw [atkinLehnerK_eq, ← map_mul, ← map_mul, hQ]
  rw [hLHS, hRHS, hmat, smul_smul, smul_smul]
  congr 1
  have hn00 := hne _ h00
  have hn11 := hne _ h11
  rw [map_mul, Units.val_mul, D.χ_U _ hu'U, ← hdet]
  have hχ0 : (((D.χ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])))) : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

/-- **The Atkin–Lehner map** `W : S^D_{k+2}(ψ) → S^D_{k+2}(ψ⁻¹)` on classical disc forms. -/
def atkinLehnerMap
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ →ₗ[K] ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ' where
  toFun φ := ⟨⟨atkinLehnerFun θG ψ U k D φ.1, fun γ hγ x =>
      atkinLehnerFun_left_invt θG ψ U k D φ.1 hγ x⟩,
    ⟨(mem_discForms_iff θG 1 ψ κ' U hU _).2 fun u x =>
        atkinLehnerFun_slash θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ.2 u x,
      fun x => atkinLehnerFun_mem_locPolyDegSubmodule θG ψ U k D φ.1 x⟩⟩
  map_add' φ φ' := by
    refine Subtype.ext (AutomorphicFunction.ext fun x => ?_)
    change atkinLehnerFun θG ψ U k D (φ.1 + φ'.1) x = atkinLehnerFun θG ψ U k D φ.1 x + atkinLehnerFun θG ψ U k D φ'.1 x
    simp only [atkinLehnerFun, AutomorphicFunction.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r φ := by
    refine Subtype.ext (AutomorphicFunction.ext fun x => ?_)
    change atkinLehnerFun θG ψ U k D (r • φ.1) x = r • atkinLehnerFun θG ψ U k D φ.1 x
    rw [atkinLehnerFun, atkinLehnerFun, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [AutomorphicFunction.smul_apply, map_smul]
    exact smul_comm _ _ _

/-- **The inverse map** `W' : S^D_{k+2}(ψ⁻¹) → S^D_{k+2}(ψ)`: `χ(x s_a) · (disc 0 of φ(x s_a w))
∣_k w₂⁻¹`. -/
def atkinLehnerFunInv (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x : G) :
    c(ZMod (p ^ 1) × ℕ, K) :=
  ∑ a : ZMod (p ^ 1), cSpace.blockIncl a
    (((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K) •
      symAct K k (atkinLehnerKinv ψ)
        (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * D.ιp (wGL p)))))

omit [CharZero K] in
theorem atkinLehnerFunInv_blockProj_zero (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
    (x : G) :
    cSpace.blockProj 0 (atkinLehnerFunInv θG ψ U k D φ x)
      = ((D.χ x : Kˣ) : K) •
        symAct K k (atkinLehnerKinv ψ) (cSpace.blockProj 0 (φ (x * D.ιp (wGL p)))) := by
  rw [atkinLehnerFunInv, map_sum, Finset.sum_eq_single 0]
  · rw [cSpace.blockProj_blockIncl, if_pos rfl, ZMod.val_zero, Nat.cast_zero, sGL_zero, map_one,
      mul_one]
  · intro b _ hb
    rw [cSpace.blockProj_blockIncl, if_neg (fun h => hb h.symm)]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [CharZero K] in
/-- `W'φ` is left `Γ`-invariant. -/
theorem atkinLehnerFunInv_left_invt (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
    {γ : G} (hγ : γ ∈ Γ) (x : G) :
    atkinLehnerFunInv θG ψ U k D φ (γ * x) = atkinLehnerFunInv θG ψ U k D φ x := by
  simp only [atkinLehnerFunInv, mul_assoc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul D.χ γ, D.χ_Γ γ hγ, one_mul]
  congr 4
  exact φ.left_invt γ hγ _

omit [CharZero K] in
/-- `W'φ` is locally polynomial of degree `≤ k`. -/
theorem atkinLehnerFunInv_mem_locPolyDegSubmodule
    (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x : G) :
    atkinLehnerFunInv θG ψ U k D φ x ∈ locPolyDegSubmodule p K 1 k := by
  intro a j hj
  have hproj : cSpace.blockProj a (atkinLehnerFunInv θG ψ U k D φ x)
      = ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K) •
        symAct K k (atkinLehnerKinv ψ)
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * D.ιp (wGL p)))) := by
    rw [atkinLehnerFunInv, map_sum, Finset.sum_eq_single a]
    · rw [cSpace.blockProj_blockIncl, if_pos rfl]
    · intro b _ hb
      rw [cSpace.blockProj_blockIncl, if_neg (fun h => hb h.symm)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h := symAct_mem_polySubmodule k (atkinLehnerKinv ψ)
    (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * D.ιp (wGL p)))) j hj
  rw [← cSpace.blockProj_apply, hproj]
  exact (congrArg (fun t => ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K) * t) h).trans
    (mul_zero _)

set_option maxHeartbeats 1000000 in
/-- **`W'` maps `ψ⁻¹`-forms to `ψ`-forms** (the mirror of `atkinLehnerFun_slash`, with
`w⁻¹ u' w` in place of `w u' w⁻¹`). -/
theorem atkinLehnerFunInv_slash
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ') (u : U) (x : G) :
    atkinLehnerFunInv θG ψ U k D φ (x * u)
      = discSlash 1 ψ κ ⟨θG u, hU u.2⟩ (atkinLehnerFunInv θG ψ U k D φ x) := by
  refine cSpace_ext_blockProj fun a => ?_
  have hu'U : discShift θG ψ U hU D u a ∈ U := discShift_mem_U θG ψ U hU D u a
  have hgIw : θG (discShift θG ψ U hU D u a) ∈ Iw p 1 := theta_mem_Iw θG U hU ⟨discShift θG ψ U hU D u a, hu'U⟩
  have hgb : ‖(θG (discShift θG ψ U hU D u a)) 0 1‖ ≤ (p : ℝ)⁻¹ := norm_theta_discShift_zero_one_le θG ψ U hU D u a
  have hus : x * ↑u * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p])) = x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * discShift θG ψ U hU D u a := by
    rw [mul_assoc, mul_ιp_sGL_eq θG ψ U hU D u a, ← mul_assoc]
  have hM2 : ((discConj 1 (⟨θG u, hU u.2⟩ : M1 p) a : M1 p) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0 := by
    rw [coe_discConj, ← discConjMat_discShift_zero θG ψ U hU D u a,
      discConjMat_zero_of_discImage_zero _ (discImage_discShift_zero θG ψ U hU D u a)]
  have hF11 : (tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0) 1 1 = (θG (discShift θG ψ U hU D u a)) 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [tMatInv, tMat]
  have hK : ((discConjK 1 (⟨θG u, hU u.2⟩ : M1 p) a ψ : M1Kh 1 ψ) : Matrix (Fin 2) (Fin 2) K)
      = RingHom.mapMatrix ψ (tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0) := by
    rw [coe_discConjK, hM2]
  have hK11 : ((discConjK 1 (⟨θG u, hU u.2⟩ : M1 p) a ψ : M1Kh 1 ψ) : Matrix (Fin 2) (Fin 2) K) 1 1 = ψ ((θG (discShift θG ψ U hU D u a)) 1 1) := by
    rw [hK, RingHom.mapMatrix_apply, Matrix.map_apply, hF11]
  have h00 : ‖(θG (discShift θG ψ U hU D u a)) 0 0‖ = 1 := norm_apply_zero_zero_of_mem_Iw one_ne_zero hgIw
  have h11 : ‖(θG (discShift θG ψ U hU D u a)) 1 1‖ = 1 := (Iw_one_le_M1 hgIw).2.2.1
  have hdet := nebK_mul_nebK_eq_nebK_det ψ hmul hcond hgIw hgb
  have ht1 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], tMat p 0 * (tMatInv p 0 * X) = X := fun X => by
    rw [← Matrix.mul_assoc, tMat_mul_tMatInv, Matrix.one_mul]
  have hconjU : (D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p) ∈ U := (D.w_conj_mem_U _ hu'U hgb).2
  have hθW : θG ((D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p)) = wQinv p * θG (discShift θG ψ U hU D u a) * wQ p := by
    rw [map_mul, map_mul, ← map_inv D.ιp, D.theta_ιp, D.theta_ιp, coe_wGL, coe_wGL_inv]
  have hv0 : discImage 1 (⟨θG ((D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p)), hU hconjU⟩ : M1 p) 0 = 0 :=
    discImage_zero_of_norm_apply_zero_one_le _ (by
      refine (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[p] => ‖M 0 1‖) hθW).le.trans ?_
      exact (wQ_conj_mem_Iw hgIw hgb).2.2)
  have hB : cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * D.ιp (wGL p))) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact hφ.2 _ 0 j hj
  have hM1 : ((discConj 1 (⟨θG ((D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p)), hU hconjU⟩ : M1 p) 0 : M1 p) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) = tMatInv p 0 * (wQinv p * θG (discShift θG ψ U hU D u a) * wQ p) * tMat p 0 := by
    rw [coe_discConj, discConjMat_zero_of_discImage_zero _ hv0]
    show tMatInv p 0 * θG ((D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p)) * tMat p 0 = _
    rw [hθW]
  have hE11 : (tMatInv p 0 * (wQinv p * θG (discShift θG ψ U hU D u a) * wQ p) * tMat p 0) 1 1 = (θG (discShift θG ψ U hU D u a)) 0 0 := by
    rw [wQinv_mul_mul_wQ]
    simp [tMatInv, tMat, Matrix.mul_apply, Fin.sum_univ_two]
  have hE : cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * D.ιp (wGL p) * ((D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p))))
      = (nebK (ψ (((discConj 1 (⟨θG ((D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p)), hU hconjU⟩ : M1 p) 0 : M1 p) :
          Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)))⁻¹ •
        symAct K k (RingHom.mapMatrix ψ ((discConj 1 (⟨θG ((D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p)), hU hconjU⟩ :
          M1 p) 0 : M1 p) : Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * D.ιp (wGL p)))) :=
    blockProj_zero_apply_mul_mem_U θG ψ U hU k κ' (u := fun x => (nebK x)⁻¹) hκ' hφ _
      ⟨_, hconjU⟩ hv0
  have hLHS : cSpace.blockProj a (atkinLehnerFunInv θG ψ U k D φ (x * u))
      = (((D.χ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * discShift θG ψ U hU D u a)) : Kˣ) : K) • (nebK (ψ ((θG (discShift θG ψ U hU D u a)) 0 0)))⁻¹ •
        symAct K k (RingHom.mapMatrix ψ (tMatInv p 0 * (wQinv p * θG (discShift θG ψ U hU D u a) * wQ p) * tMat p 0)
          * atkinLehnerKinv ψ) (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * D.ιp (wGL p)))) := by
    have hproj : ∀ y : G, ∀ a₀ : ZMod (p ^ 1), cSpace.blockProj a₀ (atkinLehnerFunInv θG ψ U k D φ y)
        = ((D.χ (y * D.ιp (sGL p (a₀.val : ℚ_[p]))) : Kˣ) : K) •
          symAct K k (atkinLehnerKinv ψ)
            (cSpace.blockProj 0 (φ (y * D.ιp (sGL p (a₀.val : ℚ_[p])) * D.ιp (wGL p)))) := by
      intro y a₀
      rw [atkinLehnerFunInv, map_sum, Finset.sum_eq_single a₀]
      · rw [cSpace.blockProj_blockIncl, if_pos rfl]
      · intro b _ hb
        rw [cSpace.blockProj_blockIncl, if_neg (fun h => hb h.symm)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hproj, hus, show x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * discShift θG ψ U hU D u a * D.ιp (wGL p) = x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * D.ιp (wGL p) * ((D.ιp (wGL p))⁻¹ * discShift θG ψ U hU D u a * D.ιp (wGL p)) by group,
      hE, hM1, hE11, map_smul, symAct_mul k _ _ hB]
  have hf' : cSpace.blockProj (discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a) (atkinLehnerFunInv θG ψ U k D φ x) ∈ polySubmodule K k :=
    fun j hj => by
      rw [cSpace.blockProj_apply]
      exact atkinLehnerFunInv_mem_locPolyDegSubmodule θG ψ U k D φ x _ j hj
  have hRHS : cSpace.blockProj a (discSlash 1 ψ κ (⟨θG u, hU u.2⟩ : M1 p) (atkinLehnerFunInv θG ψ U k D φ x))
      = nebK (ψ ((θG (discShift θG ψ U hU D u a)) 1 1)) • (((D.χ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])))) : Kˣ) : K) •
        symAct K k (atkinLehnerKinv ψ * RingHom.mapMatrix ψ (tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0))
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * D.ιp (wGL p)))) := by
    have hproj : cSpace.blockProj (discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a) (atkinLehnerFunInv θG ψ U k D φ x)
        = ((D.χ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p]))) : Kˣ) : K) • symAct K k (atkinLehnerKinv ψ) (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])) * D.ιp (wGL p)))) := by
      rw [atkinLehnerFunInv, map_sum, Finset.sum_eq_single (discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a)]
      · rw [cSpace.blockProj_blockIncl, if_pos rfl]
      · intro b _ hb
        rw [cSpace.blockProj_blockIncl, if_neg (fun h => hb h.symm)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [blockProj_discSlash, kappaSlash_eq_smul_symAct_of_shape κ (discConjK 1 (⟨θG u, hU u.2⟩ : M1 p) a ψ) (hκ _) hf',
      hK11, hK, hproj, map_smul, symAct_mul k _ _ hB]
  have hmat : RingHom.mapMatrix ψ (tMatInv p 0 * (wQinv p * θG (discShift θG ψ U hU D u a) * wQ p) * tMat p 0) * atkinLehnerKinv ψ
      = atkinLehnerKinv ψ * RingHom.mapMatrix ψ (tMatInv p 0 * θG (discShift θG ψ U hU D u a) * tMat p 0) := by
    have h2 : ∀ X : Matrix (Fin 2) (Fin 2) ℚ_[p], wQ p * (wQinv p * X) = X := fun X => by
      rw [← Matrix.mul_assoc, wQ_mul_wQinv, Matrix.one_mul]
    have hQ : ∀ g : Matrix (Fin 2) (Fin 2) ℚ_[p],
        tMatInv p 0 * (wQinv p * g * wQ p) * tMat p 0 * (tMatInv p 0 * wQinv p * tMat p 0)
          = tMatInv p 0 * wQinv p * tMat p 0 * (tMatInv p 0 * g * tMat p 0) := fun g => by
      simp only [Matrix.mul_assoc, ht1, h2]
    rw [atkinLehnerKinv_eq, ← map_mul, ← map_mul, hQ]
  rw [hLHS, hRHS, hmat, smul_smul, smul_smul]
  congr 1
  have hn00 := hne _ h00
  have hn11 := hne _ h11
  rw [map_mul, Units.val_mul, D.χ_U _ hu'U, ← hdet]
  have hχ0 : (((D.χ (x * D.ιp (sGL p (((discImage 1 (⟨θG u, hU u.2⟩ : M1 p) a).val : ℕ) : ℚ_[p])))) : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

/-- The inverse map on classical disc forms (the mirror of `atkinLehnerMap`, with `w⁻¹`). -/
def atkinLehnerMapInv
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ' →ₗ[K] ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ where
  toFun φ := ⟨⟨atkinLehnerFunInv θG ψ U k D φ.1, fun γ hγ x =>
      atkinLehnerFunInv_left_invt θG ψ U k D φ.1 hγ x⟩,
    ⟨(mem_discForms_iff θG 1 ψ κ U hU _).2 fun u x =>
        atkinLehnerFunInv_slash θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ.2 u x,
      fun x => atkinLehnerFunInv_mem_locPolyDegSubmodule θG ψ U k D φ.1 x⟩⟩
  map_add' φ φ' := by
    refine Subtype.ext (AutomorphicFunction.ext fun x => ?_)
    change atkinLehnerFunInv θG ψ U k D (φ.1 + φ'.1) x = atkinLehnerFunInv θG ψ U k D φ.1 x + atkinLehnerFunInv θG ψ U k D φ'.1 x
    simp only [atkinLehnerFunInv, AutomorphicFunction.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r φ := by
    refine Subtype.ext (AutomorphicFunction.ext fun x => ?_)
    change atkinLehnerFunInv θG ψ U k D (r • φ.1) x = r • atkinLehnerFunInv θG ψ U k D φ.1 x
    rw [atkinLehnerFunInv, atkinLehnerFunInv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [AutomorphicFunction.smul_apply, map_smul]
    exact smul_comm _ _ _

/-- `W' ∘ W = 1` (`χ(w) = 1`, `symAct_mul`, `symAct_one`, `shapiro_blockProj`). -/
theorem atkinLehnerMapInv_atkinLehnerMap
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ'
        (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ) = φ := by
  refine Subtype.ext (AutomorphicFunction.ext fun x => cSpace_ext_blockProj fun a => ?_)
  set Φ := atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ'
    (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ) with hΦ
  rw [shapiro_blockProj θG ψ U hU D κ Φ.2.1 x a, shapiro_blockProj θG ψ U hU D κ φ.2.1 x a]
  set y := x * D.ιp (sGL p (a.val : ℚ_[p])) with hy
  have hf : cSpace.blockProj 0 (φ.1 y) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact φ.2.2 y 0 j hj
  change cSpace.blockProj 0
      (atkinLehnerFunInv θG ψ U k D (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ).1 y)
    = cSpace.blockProj 0 (φ.1 y)
  rw [atkinLehnerFunInv_blockProj_zero]
  change _ • symAct K k _ (cSpace.blockProj 0 (atkinLehnerFun θG ψ U k D φ.1 (y * D.ιp (wGL p)))) = _
  rw [atkinLehnerFun_blockProj_zero, mul_inv_cancel_right, map_smul, symAct_mul k _ _ hf,
    atkinLehnerK_mul_atkinLehnerKinv, symAct_one k hf, smul_smul, map_mul D.χ y (D.ιp (wGL p)),
    D.χ_wGL, mul_one, mul_inv_cancel₀ (Units.ne_zero _), one_smul]

/-- `W ∘ W' = 1`. -/
theorem atkinLehnerMap_atkinLehnerMapInv
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ') :
    atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ'
        (atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ) = φ := by
  refine Subtype.ext (AutomorphicFunction.ext fun x => cSpace_ext_blockProj fun a => ?_)
  set Φ := atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ'
    (atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ) with hΦ
  rw [shapiro_blockProj θG ψ U hU D κ' Φ.2.1 x a, shapiro_blockProj θG ψ U hU D κ' φ.2.1 x a]
  set y := x * D.ιp (sGL p (a.val : ℚ_[p])) with hy
  have hf : cSpace.blockProj 0 (φ.1 y) ∈ polySubmodule K k := fun j hj => by
    rw [cSpace.blockProj_apply]; exact φ.2.2 y 0 j hj
  change cSpace.blockProj 0
      (atkinLehnerFun θG ψ U k D (atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ).1 y)
    = cSpace.blockProj 0 (φ.1 y)
  rw [atkinLehnerFun_blockProj_zero]
  change _ • symAct K k _
      (cSpace.blockProj 0 (atkinLehnerFunInv θG ψ U k D φ.1 (y * (D.ιp (wGL p))⁻¹))) = _
  rw [atkinLehnerFunInv_blockProj_zero, inv_mul_cancel_right, map_smul, symAct_mul k _ _ hf,
    atkinLehnerKinv_mul_atkinLehnerK, symAct_one k hf, smul_smul,
    map_mul D.χ y (D.ιp (wGL p))⁻¹, map_inv D.χ, D.χ_wGL, inv_one, mul_one,
    inv_mul_cancel₀ (Units.ne_zero _), one_smul]

/-- **The Atkin–Lehner isomorphism** `S^D_{k+2}(ψ) ≃ S^D_{k+2}(ψ⁻¹)`. -/
def atkinLehnerEquiv
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ ≃ₗ[K] ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ' :=
  LinearEquiv.ofLinear (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ')
    (atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ')
    (LinearMap.ext fun φ => atkinLehnerMap_atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ)
    (LinearMap.ext fun φ => atkinLehnerMapInv_atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ)

/-! ### The block model of the classical disc forms -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharZero K] in
/-- Evaluation at the representatives sends classical disc forms into the block-model classical
subspace (`discEvalAtReps_apply`). -/
theorem discEvalAtReps_mem_locPolyDegSubmoduleBlock (c : ι → G)
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    discEvalAtReps θG 1 ψ κ U hU c ⟨φ.1, φ.2.1⟩
      ∈ locPolyDegSubmoduleBlock p ι K 1 k := by
  intro i a j hj
  rw [discEvalAtReps_apply]
  exact φ.2.2 (c i) a j hj

/-- **The block model of the classical disc forms at a neat level**: evaluation at
representatives with trivial stabilisers is a linear isomorphism onto the block-model
classical subspace (`bijective_discEvalAtReps_of_stabilizer_eq_bot`, with the classical
condition transported both ways through the classical shape). -/
def discEvalAtRepsCl {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ ≃ₗ[K] locPolyDegSubmoduleBlock p ι K 1 k :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (locPolyDegSubmoduleBlock p ι K 1 k)
      ((discEvalAtReps θG 1 ψ κ U hU c).comp (Submodule.inclusion inf_le_left))
      (fun φ => discEvalAtReps_mem_locPolyDegSubmoduleBlock θG ψ U hU k κ c φ))
    (by
      have hbij := bijective_discEvalAtReps_of_stabilizer_eq_bot θG 1 ψ κ U hU c hc hstab
      refine ⟨fun φ φ' hφφ' => ?_, fun F => ?_⟩
      · exact Submodule.inclusion_injective _ (hbij.1 (congrArg Subtype.val hφφ'))
      · obtain ⟨Φ, hΦ⟩ := hbij.2 F.1
        have hloc : ∀ g, (Φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) g
            ∈ locPolyDegSubmodule p K 1 k := by
          intro g
          obtain ⟨i, hi⟩ := hc.2 (Quotient.mk'' g)
          obtain ⟨γ, hγ, v, hv, rfl⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi)
          have hci : (Φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (c i)
              ∈ locPolyDegSubmodule p K 1 k := by
            intro a j hj
            rw [← discEvalAtReps_apply θG 1 ψ κ U hU c Φ i (a, j), hΦ]
            exact F.2 i a j hj
          rw [mul_assoc, AutomorphicFunction.left_invt' _ hγ]
          have h := (mem_discForms_iff θG 1 ψ κ U hU _).1 Φ.2 ⟨v, hv⟩ (c i)
          change (Φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)).toFun (c i * v) ∈ _
          rw [h]
          exact discSlash_mem_locPolyDegSubmodule_of_shape 1 ψ κ _ (fun a => hκ _) hci
        exact ⟨⟨Φ.1, Φ.2, hloc⟩, Subtype.ext hΦ⟩)

omit [CharZero K] in
theorem discEvalAtRepsCl_apply {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    (discEvalAtRepsCl θG ψ U hU k κ hκ c hc hstab φ : c(ι × (ZMod (p ^ 1) × ℕ), K))
      = discEvalAtReps θG 1 ψ κ U hU c ⟨φ.1, φ.2.1⟩ :=
  rfl

end LWX

end
