/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«05_AtkinLehner»
import PhD.LWX.«09_DiscModel»

/-!
# The local matrix identities behind `U_p ∘ U'_p = p^{k+1}`

The `p`-adic matrices of the Atkin–Lehner argument at conductor `p²`, written in the coordinate
of the disc model at level `Iw_p` (`h = 1`; the disc-`0` conjugate `t₀⁻¹ · t₀`, `t₀ = (p 0; 0 1)`,
carries them to the level-`p²` matrices of `PhD/Test/AtkinLehnerIdentity.lean`, whose identities
are transplanted here):

* `vQ c = (p 0; cp 1)` — the `U_p`-representatives ([LWX, §2.5]: "`Iw_q (p 0; 0 1) Iw_q =
  ∐ Iw_q v_j`, for example with `v_j = (p 0; jq 1)`");
* `wQ = (0 p; −p 0)` — the Atkin–Lehner element in this coordinate (`t₀⁻¹ wQ t₀ = (0 1; −p² 0)`,
  `LWX.atkinLehner p 2`);
* `sQ b = (1 b; 0 1)` — the translations, which move disc `0` to disc `b`;
* `ℓQ b c` — the Iwahori element of [the scratch file]'s `conjTwist`, in this coordinate.

**The key factorisation** (`atkinLehnerConj_vQ_mul_vQ`): `(wQ vQ b wQ⁻¹) · vQ c = ℓQ b c · (p • sQ (−b))`
— a `U'_p`-representative times a `U_p`-representative is an Iwahori element (whose `d`-entry
`1 + bcp` carries the nebentypus) times the central `p` times a translation.  For `b = 0` the
translation is trivial and the term is central; for `b ≠ 0` the sum over `c` of the nebentypus
values vanishes (`17_NebChar.lean`).
-/

open Matrix

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The matrices -/

variable (p) in
/-- The `U_p`-representative `(p 0; cp 1)`. -/
noncomputable def vQ (c : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![(p : ℚ_[p]), 0; c * (p : ℚ_[p]), 1]

variable (p) in
/-- The translation `(1 b; 0 1)`. -/
noncomputable def sQ (b : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] := !![1, b; 0, 1]

variable (p) in
/-- The Atkin–Lehner element of level `p²` in the disc-model coordinate: `(0 p; −p 0)`. -/
noncomputable def wQ : Matrix (Fin 2) (Fin 2) ℚ_[p] := !![0, (p : ℚ_[p]); -(p : ℚ_[p]), 0]

variable (p) in
/-- The inverse `(0 −1/p; 1/p 0)` of the Atkin–Lehner element. -/
noncomputable def wQinv : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![0, -((p : ℚ_[p])⁻¹); (p : ℚ_[p])⁻¹, 0]

variable (p) in
/-- The Iwahori element `(1 − bcp, −b²cp; cp, 1 + bcp)` of the key factorisation. -/
noncomputable def ℓQ (b c : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![1 - b * c * (p : ℚ_[p]), -(b ^ 2 * c * (p : ℚ_[p])); c * (p : ℚ_[p]), 1 + b * c * (p : ℚ_[p])]

variable (p) in
/-- The disc-model coordinate change `t_a = (p a; 0 1)` at level `h = 1`. -/
noncomputable def tMat (a : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] := !![(p : ℚ_[p]), a; 0, 1]

variable (p) in
/-- Its inverse `t_a⁻¹ = (1/p, −a/p; 0, 1)`. -/
noncomputable def tMatInv (a : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![(p : ℚ_[p])⁻¹, -(a / (p : ℚ_[p])); 0, 1]

variable (p) in
/-- The inverse `(1 + bcp, b²cp; −cp, 1 − bcp)` of `ℓQ b c` (determinant `1`). -/
noncomputable def ℓQinv (b c : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![1 + b * c * (p : ℚ_[p]), b ^ 2 * c * (p : ℚ_[p]); -(c * (p : ℚ_[p])), 1 - b * c * (p : ℚ_[p])]

/-! ### Determinants and inverses -/

@[simp] theorem det_vQ (c : ℚ_[p]) : (vQ p c).det = (p : ℚ_[p]) := by
  simp [vQ, Matrix.det_fin_two_of]

@[simp] theorem det_sQ (b : ℚ_[p]) : (sQ p b).det = 1 := by
  simp [sQ, Matrix.det_fin_two_of]

@[simp] theorem det_wQ : (wQ p).det = (p : ℚ_[p]) ^ 2 := by
  rw [wQ, Matrix.det_fin_two_of]
  ring

@[simp] theorem det_ℓQ (b c : ℚ_[p]) : (ℓQ p b c).det = 1 := by
  rw [ℓQ, Matrix.det_fin_two_of]
  ring

theorem wQ_mul_wQinv : wQ p * wQinv p = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wQ, wQinv, Matrix.mul_apply, Fin.sum_univ_two, hp0]

theorem wQinv_mul_wQ : wQinv p * wQ p = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wQ, wQinv, Matrix.mul_apply, Fin.sum_univ_two, hp0]

theorem ℓQ_mul_ℓQinv (b c : ℚ_[p]) : ℓQ p b c * ℓQinv p b c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ℓQ, ℓQinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem ℓQinv_mul_ℓQ (b c : ℚ_[p]) : ℓQinv p b c * ℓQ p b c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ℓQ, ℓQinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem tMat_mul_tMatInv (a : ℚ_[p]) : tMat p a * tMatInv p a = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, tMatInv, Matrix.mul_apply, Fin.sum_univ_two, hp0]
  field_simp
  ring

theorem tMatInv_mul_tMat (a : ℚ_[p]) : tMatInv p a * tMat p a = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, tMatInv, Matrix.mul_apply, Fin.sum_univ_two, hp0]
  field_simp
  ring

/-- `s_b · t_a = t_{a+b}`. -/
theorem sQ_mul_tMat (a b : ℚ_[p]) : sQ p b * tMat p a = tMat p (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sQ, tMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `t₀⁻¹ · s_{−a} = t_a⁻¹`. -/
theorem tMatInv_zero_mul_sQ_neg (a : ℚ_[p]) : tMatInv p 0 * sQ p (-a) = tMatInv p a := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMatInv, sQ, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

/-- `t₀⁻¹ · s_b · t₀ = (1, b/p; 0, 1)`: the translation in the disc-`0` coordinate. -/
theorem tMatInv_zero_mul_sQ_mul_tMat_zero (b : ℚ_[p]) :
    tMatInv p 0 * sQ p b * tMat p 0 = !![1, b / (p : ℚ_[p]); 0, 1] := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMatInv, sQ, tMat, Matrix.mul_apply, Fin.sum_univ_two, hp0]
  field_simp

/-- `t₀⁻¹ wQ t₀ = (0 1; −p² 0)` is the level-`p²` Atkin–Lehner element of `05_AtkinLehner.lean`. -/
theorem discConjMat_wQ :
    !![(p : ℚ_[p])⁻¹, 0; 0, 1] * wQ p * !![(p : ℚ_[p]), 0; 0, 1] = atkinLehner p 2 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wQ, atkinLehner, Matrix.mul_apply, Fin.sum_univ_two, hp0]
  field_simp

/-! ### The key factorisation -/

/-- The `U'_p`-representative: `wQ · vQ b · wQ⁻¹ = (1 −bp; 0 p)`. -/
theorem wQ_mul_vQ_mul_wQinv (b : ℚ_[p]) :
    wQ p * vQ p b * wQinv p = !![1, -(b * (p : ℚ_[p])); 0, (p : ℚ_[p])] := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wQ, vQ, wQinv, Matrix.mul_apply, Fin.sum_univ_two, hp0]
  field_simp

/-- **The key factorisation**: `(1 −bp; 0 p) · vQ c = ℓQ b c · (p • sQ (−b))`. -/
theorem upAdjRep_mul_vQ (b c : ℚ_[p]) :
    !![1, -(b * (p : ℚ_[p])); 0, (p : ℚ_[p])] * vQ p c
      = ℓQ p b c * ((p : ℚ_[p]) • sQ p (-b)) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vQ, ℓQ, sQ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- The factorisation with the Atkin–Lehner conjugate spelled out. -/
theorem wQ_mul_vQ_mul_wQinv_mul_vQ (b c : ℚ_[p]) :
    wQ p * vQ p b * wQinv p * vQ p c = ℓQ p b c * ((p : ℚ_[p]) • sQ p (-b)) := by
  rw [wQ_mul_vQ_mul_wQinv, upAdjRep_mul_vQ]

/-- The factorisation solved for the Iwahori element: `ℓ_{b,c}⁻¹ · w v_b w⁻¹ v_c = p • s_{−b}`. -/
theorem ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ (b c : ℚ_[p]) :
    ℓQinv p b c * (wQ p * vQ p b * wQinv p * vQ p c) = (p : ℚ_[p]) • sQ p (-b) := by
  rw [wQ_mul_vQ_mul_wQinv_mul_vQ, ← mul_assoc, ℓQinv_mul_ℓQ, one_mul]

/-- Conjugation by the Atkin–Lehner element: `wQ · g · wQ⁻¹ = (d, −c; −b, a)`. -/
theorem wQ_mul_mul_wQinv (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    wQ p * g * wQinv p = !![g 1 1, -(g 1 0); -(g 0 1), g 0 0] := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [wQ, wQinv] <;> (try field_simp)

/-- Conjugation by the inverse Atkin–Lehner element: `wQ⁻¹ · g · wQ = (d, −c; −b, a)`. -/
theorem wQinv_mul_mul_wQ (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    wQinv p * g * wQ p = !![g 1 1, -(g 1 0); -(g 0 1), g 0 0] := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [wQ, wQinv] <;> (try field_simp)

/-! ### Membership in the level monoids -/

/-- `vQ c ∈ M₁` for `c` integral. -/
theorem vQ_mem_M1 {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) : vQ p c ∈ M1 p := by
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hnp : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have hcp : ‖c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, hnp]; exact mul_le_of_le_one_left (by positivity) hc
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j
    · simpa [vQ, hnp] using hpinv
    · simp [vQ]
    · simpa [vQ] using hcp.trans hpinv
    · simp [vQ]
  · simpa [vQ] using hcp
  · simp [vQ]
  · rw [det_vQ]; exact Nat.cast_ne_zero.2 hp.out.ne_zero

/-- `vQ c` has the `U_p`-shape `‖a‖ ≤ p⁻¹`. -/
theorem norm_vQ_zero_zero (c : ℚ_[p]) : ‖vQ p c 0 0‖ ≤ (p : ℝ)⁻¹ := by
  simp [vQ]

/-- `sQ b ∈ Iw_p` for `b` integral. -/
theorem sQ_mem_Iw {b : ℚ_[p]} (hb : ‖b‖ ≤ 1) : sQ p b ∈ Iw p 1 := by
  refine mem_Iw_iff.2 ⟨fun i j => ?_, by simp [sQ], by simp⟩
  fin_cases i <;> fin_cases j <;> simp [sQ, hb]

/-- `ℓQ b c ∈ Iw_p` for `b, c` integral. -/
theorem ℓQ_mem_Iw {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) : ℓQ p b c ∈ Iw p 1 := by
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hnp : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have hcp : ‖c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, hnp]; exact mul_le_of_le_one_left (by positivity) hc
  have hbcp : ‖b * c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [mul_assoc, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans hcp
  have hb2cp : ‖b ^ 2 * c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [mul_assoc, norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)).trans hcp
  have hadd : ‖(1 : ℚ_[p]) + b * c * p‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) (hbcp.trans hpinv))
  have hsub : ‖(1 : ℚ_[p]) - b * c * p‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (by simp) (by rw [norm_neg]; exact hbcp.trans hpinv))
  refine mem_Iw_iff.2 ⟨fun i j => ?_, ?_, by rw [det_ℓQ, norm_one]⟩
  · fin_cases i <;> fin_cases j
    · simpa [ℓQ] using hsub
    · simpa [ℓQ] using hb2cp.trans hpinv
    · simpa [ℓQ] using hcp.trans hpinv
    · simpa [ℓQ] using hadd
  · simpa [ℓQ] using hcp

/-- `ℓQinv b c ∈ Iw_p` for `b, c` integral. -/
theorem ℓQinv_mem_Iw {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) : ℓQinv p b c ∈ Iw p 1 := by
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hnp : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have hcp : ‖c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, hnp]; exact mul_le_of_le_one_left (by positivity) hc
  have hbcp : ‖b * c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [mul_assoc, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans hcp
  have hb2cp : ‖b ^ 2 * c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [mul_assoc, norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)).trans hcp
  have hadd : ‖(1 : ℚ_[p]) + b * c * p‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) (hbcp.trans hpinv))
  have hsub : ‖(1 : ℚ_[p]) - b * c * p‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (by simp) (by rw [norm_neg]; exact hbcp.trans hpinv))
  have hdet : (ℓQinv p b c).det = 1 := by
    rw [ℓQinv, Matrix.det_fin_two_of]; ring
  refine mem_Iw_iff.2 ⟨fun i j => ?_, ?_, by rw [hdet, norm_one]⟩
  · fin_cases i <;> fin_cases j
    · simpa [ℓQinv] using hadd
    · simpa [ℓQinv] using hb2cp.trans hpinv
    · simpa [ℓQinv] using hcp.trans hpinv
    · simpa [ℓQinv] using hsub
  · simpa [ℓQinv] using hcp

/-- **`w` normalises the disc-`0` part of `Iw_p`**: for `g ∈ Iw_p` with `p ∣ b`, both
`wQ g wQ⁻¹` and `wQ⁻¹ g wQ` (each equal to `(d, −c; −b, a)`) lie in `Iw_p` with `p ∣ b`. -/
theorem wQ_conj_mem_Iw {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1)
    (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹) :
    (wQ p * g * wQinv p ∈ Iw p 1 ∧ ‖(wQ p * g * wQinv p) 0 1‖ ≤ (p : ℝ)⁻¹)
      ∧ (wQinv p * g * wQ p ∈ Iw p 1 ∧ ‖(wQinv p * g * wQ p) 0 1‖ ≤ (p : ℝ)⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hswap : (!![g 1 1, -(g 1 0); -(g 0 1), g 0 0] : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1 ∧
      ‖(!![g 1 1, -(g 1 0); -(g 0 1), g 0 0] : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖
        ≤ (p : ℝ)⁻¹ := by
    refine ⟨mem_Iw_iff.2 ⟨fun i j => ?_, by simpa using hb, ?_⟩, by simpa using h2⟩
    · fin_cases i <;> fin_cases j <;> simp [h1]
    · rw [Matrix.det_fin_two_of, ← h3, Matrix.det_fin_two]
      congr 1
      ring
  rw [wQ_mul_mul_wQinv, wQinv_mul_mul_wQ]
  exact ⟨hswap, hswap⟩

/-- `Iw_p ≤ M₁`: the Iwahori subgroup lies in the level monoid of the disc model. -/
theorem Iw_one_le_M1 : (Iw p 1 : Set (Matrix (Fin 2) (Fin 2) ℚ_[p])) ⊆ M1 p := by
  intro g hg
  obtain ⟨h1, h2, h3⟩ := hg
  have hd : ‖g 1 1‖ = 1 := by
    have hmem : (!![g 1 1, g 0 1; g 1 0, g 0 0] : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1 := by
      refine mem_Iw_iff.2 ⟨fun i j => ?_, by simpa using h2, ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [h1]
      · rw [Matrix.det_fin_two_of, ← h3, Matrix.det_fin_two]
        congr 1
        ring
    simpa using norm_apply_zero_zero_of_mem_Iw one_ne_zero hmem
  refine ⟨h1, by simpa using h2, hd, fun h0 => ?_⟩
  rw [h0, norm_zero] at h3
  exact zero_ne_one h3

/-- The determinant of a `2 × 2` matrix with integral entries is integral. -/
theorem norm_det_fin_two_le_one {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : ∀ i j, ‖g i j‖ ≤ 1) :
    ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hg 0 0) (norm_nonneg _) (hg 1 1)
  · rw [norm_neg, norm_mul]; exact mul_le_one₀ (hg 0 1) (norm_nonneg _) (hg 1 0)

/-! ### The disc bookkeeping at disc `0` -/

/-- **A matrix with `p ∣ b` fixes disc `0`** (`discImage 1 δ 0 = (b/d) mod p`). -/
theorem discImage_zero_of_norm_apply_zero_one_le (δ : M1 p)
    (hb : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ (p : ℝ)⁻¹) : discImage 1 δ 0 = 0 := by
  rw [discImage, ZMod.val_zero, Nat.cast_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow, LocalMat.mobiusFun, mul_zero, zero_add, mul_zero,
    zero_add, Ring.inverse_unit, norm_mul, PadicInt.norm_units, mul_one, PadicInt.norm_def,
    M1.coe_toLocalMat_b]
  simpa using hb

/-- **The disc conjugate is `t_{a'}⁻¹ δ t_a`** — the entry-wise definition of `discConjMat`
read as a matrix product (`a' = discImage 1 δ a`). -/
theorem discConjMat_eq_tMatInv_mul_mul_tMat (δ : M1 p) (a : ZMod (p ^ 1)) :
    discConjMat 1 δ a
      = tMatInv p (((discImage 1 δ a).val : ℕ) : ℚ_[p]) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p])
          * tMat p ((a.val : ℕ) : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [discConjMat, tMat, tMatInv] <;> (try field_simp) <;> (try ring)

/-- At a matrix fixing disc `0`, the disc-`0` conjugate is `t₀⁻¹ δ t₀`. -/
theorem discConjMat_zero_of_discImage_zero (δ : M1 p) (hδ : discImage 1 δ 0 = 0) :
    discConjMat 1 δ 0 = tMatInv p 0 * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) * tMat p 0 := by
  rw [discConjMat_eq_tMatInv_mul_mul_tMat, hδ, ZMod.val_zero, Nat.cast_zero]

/-- The disc-shifted matrix `s_{a'}⁻¹ δ s_a` is the disc-`0` coordinate change of the disc-`a`
conjugate: `s_{−a'} δ s_a = t₀ · discConjMat δ a · t₀⁻¹`. -/
theorem conj_sQ_eq_tMat_mul_discConjMat (δ : M1 p) (a : ZMod (p ^ 1)) :
    sQ p (-(((discImage 1 δ a).val : ℕ) : ℚ_[p])) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p])
        * sQ p ((a.val : ℕ) : ℚ_[p])
      = tMat p 0 * discConjMat 1 δ a * tMatInv p 0 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [discConjMat_eq_tMatInv_mul_mul_tMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [tMat, tMatInv, sQ, hp0] <;> (try field_simp)

/-- `vQ c` fixes disc `0`. -/
theorem discImage_vQ_zero {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    discImage 1 (⟨vQ p c, vQ_mem_M1 hc⟩ : M1 p) 0 = 0 :=
  discImage_zero_of_norm_apply_zero_one_le _ (by simp [vQ])

/-- `ℓQ b c` fixes disc `0` (its `b`-entry is divisible by `p`). -/
theorem discImage_ℓQ_zero {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    discImage 1 (⟨ℓQ p b c, Iw_one_le_M1 (ℓQ_mem_Iw hb hc)⟩ : M1 p) 0 = 0 := by
  have hcp : ‖c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, Padic.norm_p]; exact mul_le_of_le_one_left (by positivity) hc
  have hb2cp : ‖b ^ 2 * c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [mul_assoc, norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)).trans hcp
  exact discImage_zero_of_norm_apply_zero_one_le _ (by simpa [ℓQ] using hb2cp)

/-- `ℓQinv b c` fixes disc `0`. -/
theorem discImage_ℓQinv_zero {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    discImage 1 (⟨ℓQinv p b c, Iw_one_le_M1 (ℓQinv_mem_Iw hb hc)⟩ : M1 p) 0 = 0 := by
  have hcp : ‖c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, Padic.norm_p]; exact mul_le_of_le_one_left (by positivity) hc
  have hb2cp : ‖b ^ 2 * c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [mul_assoc, norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)).trans hcp
  exact discImage_zero_of_norm_apply_zero_one_le _ (by simpa [ℓQinv] using hb2cp)

/-- The `d`-entry of the disc-`0` conjugate of `ℓQ b c` is `1 + bcp`. -/
theorem discConj_ℓQ_zero_one_one {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    (discConj 1 (⟨ℓQ p b c, Iw_one_le_M1 (ℓQ_mem_Iw hb hc)⟩ : M1 p) 0 :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 + b * c * (p : ℚ_[p]) := by
  simp [ℓQ]

/-- The `d`-entry of the disc-`0` conjugate of `ℓQinv b c` is `1 − bcp`. -/
theorem discConj_ℓQinv_zero_one_one {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    (discConj 1 (⟨ℓQinv p b c, Iw_one_le_M1 (ℓQinv_mem_Iw hb hc)⟩ : M1 p) 0 :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 - b * c * (p : ℚ_[p]) := by
  simp [ℓQinv]

/-- The translation `sQ b` moves disc `0` to disc `b`, with trivial conjugate. -/
theorem discImage_sQ_zero (b : ℕ) :
    discImage 1 (⟨sQ p b, Iw_one_le_M1 (sQ_mem_Iw (by
      exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b))⟩ : M1 p) 0 = (b : ZMod (p ^ 1)) := by
  suffices key : ∀ g : M1 p, (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = sQ p b →
      discImage 1 g 0 = (b : ZMod (p ^ 1)) from key _ rfl
  intro g hg
  have hb' : ((M1.toLocalMat g).b : ℤ_[p]) = (b : ℤ_[p]) := by
    refine Subtype.ext ?_
    rw [M1.coe_toLocalMat_b, hg]
    simp [sQ]
  have hd : (((M1.toLocalMat g).d : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    refine Subtype.ext ?_
    rw [M1.coe_toLocalMat_d, hg]
    simp [sQ]
  rw [discImage, ZMod.val_zero, Nat.cast_zero, LocalMat.mobiusFun, mul_zero, zero_add, mul_zero,
    zero_add, hb', hd, Ring.inverse_one, mul_one, map_natCast]

theorem discConj_sQ_zero {b : ℕ} (hb : b < p) :
    discConj 1 (⟨sQ p b, Iw_one_le_M1 (sQ_mem_Iw (by
      exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b))⟩ : M1 p) 0 = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  refine Subtype.ext ?_
  rw [coe_discConj, discConjMat_eq_tMatInv_mul_mul_tMat, discImage_sQ_zero, ZMod.val_natCast,
    pow_one, Nat.mod_eq_of_lt hb, ZMod.val_zero, Nat.cast_zero, OneMemClass.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, tMatInv, sQ, Matrix.mul_apply, Fin.sum_univ_two, hp0]
  field_simp
  ring

end LWX
