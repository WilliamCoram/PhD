/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«10_AtkinLehnerLocal»

/-!
# The local matrix identities behind `U_p ∘ U'_p = p^{k+1}` at conductor `p^{h+1}`

`10_AtkinLehnerLocal.lean` at analyticity level `h` (conductor `p^{h+1}`, [LWX, §2.2]'s
`Iw_{p^{h+1}}`).  The disc model at level `h` uses the coordinate change `t_a = (p^h a; 0 1)`
(`discConjMat`, `09_DiscModel.lean`), in which the level-`p^{h+1}` matrices read:

* `vQ c = (p 0; cp 1)` and `sQ b = (1 b; 0 1)` — **unchanged** (`U_p` is still the `Iw_p`
  double coset `Iw_p (p 0; 0 1) Iw_p`, [LWX, §2.5]);
* `wQH h = (0 p^h; −p 0)` — the Atkin–Lehner element of level `p^{h+1}` in this coordinate
  (`t₀⁻¹ wQH t₀ = (0 1; −p^{h+1} 0)`, `LWX.atkinLehner p (h+1)`); conjugation by it is
  `g ↦ (d, −c p^{h−1}; −b p^{1−h}, a)`, which normalises the disc-`0` part
  `{p^h ∣ b}` of `Iw_p`, i.e. `Iw_{p^{h+1}}` in the original coordinate;
* `ℓQH h b c = (1 − bcp^h, −b²c p^{2h−1}; cp, 1 + bcp^h)` — the Iwahori element of the key
  factorisation `(wQH vQ b wQH⁻¹) vQ c = ℓQH b c · (p • sQ(−b p^{h−1}))`
  (`upAdjRepH_mul_vQ`): its `d`-entry `1 + bcp^h` is what the nebentypus of conductor
  exactly `p^{h+1}` sees, and the translation moves disc `0` to disc `b p^{h−1}`.

The entries `p^{2h−1}` and `b p^{h−1}` are written `p^h·p^h/p` and `b·p^h/p` in `ℚ_p`, so that
every algebraic identity holds for all `h`; the integrality statements (`ℓQH_mem_Iw`, the disc
bookkeeping) carry `0 < h`.  Level `1` is recovered by `wQH_one`, `ℓQH_one`, `tMatH_one`.
-/

open Matrix

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The matrices -/

variable (p) in
/-- The Atkin–Lehner element of level `p^{h+1}` in the disc-model coordinate: `(0 p^h; −p 0)`. -/
noncomputable def wQH (h : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![0, (p : ℚ_[p]) ^ h; -(p : ℚ_[p]), 0]

variable (p) in
/-- The inverse `(0 −1/p; 1/p^h 0)` of the Atkin–Lehner element. -/
noncomputable def wQHinv (h : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![0, -((p : ℚ_[p])⁻¹); ((p : ℚ_[p]) ^ h)⁻¹, 0]

variable (p) in
/-- The Iwahori element `(1 − bcp^h, −b²c p^{2h−1}; cp, 1 + bcp^h)` of the key factorisation
(`p^{2h−1}` written as `p^h·p^h/p`). -/
noncomputable def ℓQH (h : ℕ) (b c : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![1 - b * c * (p : ℚ_[p]) ^ h, -(b ^ 2 * c * ((p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / p));
    c * (p : ℚ_[p]), 1 + b * c * (p : ℚ_[p]) ^ h]

variable (p) in
/-- The inverse `(1 + bcp^h, b²c p^{2h−1}; −cp, 1 − bcp^h)` of `ℓQH h b c` (determinant `1`). -/
noncomputable def ℓQHinv (h : ℕ) (b c : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![1 + b * c * (p : ℚ_[p]) ^ h, b ^ 2 * c * ((p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / p);
    -(c * (p : ℚ_[p])), 1 - b * c * (p : ℚ_[p]) ^ h]

variable (p) in
/-- The disc-model coordinate change `t_a = (p^h a; 0 1)` at level `h`. -/
noncomputable def tMatH (h : ℕ) (a : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![(p : ℚ_[p]) ^ h, a; 0, 1]

variable (p) in
/-- Its inverse `t_a⁻¹ = (1/p^h, −a/p^h; 0, 1)`. -/
noncomputable def tMatHInv (h : ℕ) (a : ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![((p : ℚ_[p]) ^ h)⁻¹, -(a / (p : ℚ_[p]) ^ h); 0, 1]

/-! ### Level `1` -/

theorem wQH_one : wQH p 1 = wQ p := by
  rw [wQH, pow_one]
  rfl

theorem ℓQH_one (b c : ℚ_[p]) : ℓQH p 1 b c = ℓQ p b c := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [ℓQH, ℓQ, pow_one, mul_div_cancel_right₀ _ hp0]

theorem tMatH_one (a : ℚ_[p]) : tMatH p 1 a = tMat p a := by
  rw [tMatH, pow_one]
  rfl

/-! ### Determinants and inverses -/

@[simp] theorem det_wQH (h : ℕ) : (wQH p h).det = (p : ℚ_[p]) ^ (h + 1) := by
  rw [wQH, Matrix.det_fin_two_of]
  ring

@[simp] theorem det_ℓQH (h : ℕ) (b c : ℚ_[p]) : (ℓQH p h b c).det = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [ℓQH, Matrix.det_fin_two_of]
  field_simp
  ring

@[simp] theorem det_tMatH (h : ℕ) (a : ℚ_[p]) : (tMatH p h a).det = (p : ℚ_[p]) ^ h := by
  rw [tMatH, Matrix.det_fin_two_of]
  ring

theorem wQH_mul_wQHinv (h : ℕ) : wQH p h * wQHinv p h = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wQH, wQHinv, Matrix.mul_apply, Fin.sum_univ_two, hp0, hph]

theorem wQHinv_mul_wQH (h : ℕ) : wQHinv p h * wQH p h = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wQH, wQHinv, Matrix.mul_apply, Fin.sum_univ_two, hp0, hph]

theorem ℓQH_mul_ℓQHinv (h : ℕ) (b c : ℚ_[p]) : ℓQH p h b c * ℓQHinv p h b c = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ℓQH, ℓQHinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring)

theorem ℓQHinv_mul_ℓQH (h : ℕ) (b c : ℚ_[p]) : ℓQHinv p h b c * ℓQH p h b c = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ℓQH, ℓQHinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring)

theorem tMatH_mul_tMatHInv (h : ℕ) (a : ℚ_[p]) : tMatH p h a * tMatHInv p h a = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMatH, tMatHInv, Matrix.mul_apply, Fin.sum_univ_two, hph]
  field_simp
  ring

theorem tMatHInv_mul_tMatH (h : ℕ) (a : ℚ_[p]) : tMatHInv p h a * tMatH p h a = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMatH, tMatHInv, Matrix.mul_apply, Fin.sum_univ_two, hph]
  field_simp
  ring

/-! ### Translations and the coordinate change -/

theorem sQ_mul_tMatH (h : ℕ) (a b : ℚ_[p]) : sQ p b * tMatH p h a = tMatH p h (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sQ, tMatH, Matrix.mul_apply, Fin.sum_univ_two]

theorem tMatHInv_zero_mul_sQ_neg (h : ℕ) (a : ℚ_[p]) :
    tMatHInv p h 0 * sQ p (-a) = tMatHInv p h a := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMatHInv, sQ, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

/-- The translation `sQ b` in the disc-`0` coordinate is `(1, b/p^h; 0, 1)`. -/
theorem tMatHInv_zero_mul_sQ_mul_tMatH_zero (h : ℕ) (b : ℚ_[p]) :
    tMatHInv p h 0 * sQ p b * tMatH p h 0 = !![1, b / (p : ℚ_[p]) ^ h; 0, 1] := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMatHInv, sQ, tMatH, Matrix.mul_apply, Fin.sum_univ_two, hph]
  field_simp

/-- `t₀⁻¹ wQH t₀ = (0 1; −p^{h+1} 0)` is the level-`p^{h+1}` Atkin–Lehner element of
`05_AtkinLehner.lean`. -/
theorem discConjMat_wQH (h : ℕ) :
    tMatHInv p h 0 * wQH p h * tMatH p h 0 = atkinLehner p (h + 1) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wQH, tMatH, tMatHInv, atkinLehner, Matrix.mul_apply, Fin.sum_univ_two, hph]
  field_simp
  ring

/-! ### The key factorisation -/

/-- The `U'_p`-representative: `wQH · vQ b · wQH⁻¹ = (1 −bp^h; 0 p)`. -/
theorem wQH_mul_vQ_mul_wQHinv (h : ℕ) (b : ℚ_[p]) :
    wQH p h * vQ p b * wQHinv p h = !![1, -(b * (p : ℚ_[p]) ^ h); 0, (p : ℚ_[p])] := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wQH, vQ, wQHinv, Matrix.mul_apply, Fin.sum_univ_two, hp0, hph]
  field_simp

/-- **The key factorisation at level `h`**:
`(1 −bp^h; 0 p) · vQ c = ℓQH b c · (p • sQ (−b p^{h−1}))`. -/
theorem upAdjRepH_mul_vQ (h : ℕ) (b c : ℚ_[p]) :
    !![1, -(b * (p : ℚ_[p]) ^ h); 0, (p : ℚ_[p])] * vQ p c
      = ℓQH p h b c * ((p : ℚ_[p]) • sQ p (-(b * (p : ℚ_[p]) ^ h / p))) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vQ, ℓQH, sQ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring)

/-- The factorisation with the Atkin–Lehner conjugate spelled out. -/
theorem wQH_mul_vQ_mul_wQHinv_mul_vQ (h : ℕ) (b c : ℚ_[p]) :
    wQH p h * vQ p b * wQHinv p h * vQ p c
      = ℓQH p h b c * ((p : ℚ_[p]) • sQ p (-(b * (p : ℚ_[p]) ^ h / p))) := by
  rw [wQH_mul_vQ_mul_wQHinv, upAdjRepH_mul_vQ]

/-- The factorisation solved for the Iwahori element. -/
theorem ℓQHinv_mul_wQH_mul_vQ_mul_wQHinv_mul_vQ (h : ℕ) (b c : ℚ_[p]) :
    ℓQHinv p h b c * (wQH p h * vQ p b * wQHinv p h * vQ p c)
      = (p : ℚ_[p]) • sQ p (-(b * (p : ℚ_[p]) ^ h / p)) := by
  rw [wQH_mul_vQ_mul_wQHinv_mul_vQ, ← mul_assoc, ℓQHinv_mul_ℓQH, one_mul]

/-- Conjugation by the level-`h` Atkin–Lehner element:
`wQH · g · wQH⁻¹ = (d, −c p^h/p; −b p/p^h, a)`. -/
theorem wQH_mul_mul_wQHinv (h : ℕ) (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    wQH p h * g * wQHinv p h
      = !![g 1 1, -(g 1 0 * (p : ℚ_[p]) ^ h / p);
          -(g 0 1 * (p : ℚ_[p]) / (p : ℚ_[p]) ^ h), g 0 0] := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [wQH, wQHinv] <;> (try field_simp)

/-- Conjugation by the inverse: the same matrix (`wQH² = −p^{h+1}` is central). -/
theorem wQHinv_mul_mul_wQH (h : ℕ) (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    wQHinv p h * g * wQH p h
      = !![g 1 1, -(g 1 0 * (p : ℚ_[p]) ^ h / p);
          -(g 0 1 * (p : ℚ_[p]) / (p : ℚ_[p]) ^ h), g 0 0] := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [wQH, wQHinv] <;> (try field_simp)

/-! ### Membership in the level monoids -/

/-- `‖p^h·p^h/p‖ = p^{−(2h−1)} ≤ p^{−h}` for `h ≥ 1`. -/
private theorem norm_pow_mul_pow_div_le {h : ℕ} (hh : 0 < h) :
    ‖(p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ h := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [show (p : ℚ_[p]) ^ (h' + 1) * (p : ℚ_[p]) ^ (h' + 1) / (p : ℚ_[p])
      = (p : ℚ_[p]) ^ h' * (p : ℚ_[p]) ^ (h' + 1) by rw [div_eq_iff hp0]; ring,
    norm_mul, norm_pow, norm_pow, Padic.norm_p]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by positivity) hpinv)

/-- `ℓQH b c ∈ Iw_p` for `b, c` integral and `h ≥ 1`. -/
theorem ℓQH_mem_Iw {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ℓQH p h b c ∈ Iw p 1 := by
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hnp : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have hcp : ‖c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, hnp]; exact mul_le_of_le_one_left (by positivity) hc
  have hph : ‖(p : ℚ_[p]) ^ h‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_pow, hnp]; exact pow_le_of_le_one (by positivity) hpinv hh.ne'
  have hbcp : ‖b * c * (p : ℚ_[p]) ^ h‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, norm_mul]
    calc ‖b‖ * ‖c‖ * ‖(p : ℚ_[p]) ^ h‖ ≤ 1 * 1 * (p : ℝ)⁻¹ := by gcongr
      _ = (p : ℝ)⁻¹ := by ring
  have hP1 : ‖(p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p])‖ ≤ 1 :=
    (norm_pow_mul_pow_div_le hh).trans (pow_le_one₀ (by positivity) hpinv)
  have hb2cP : ‖b ^ 2 * c * ((p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p]))‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖b‖ ^ 2 * ‖c‖ * ‖(p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p])‖
        ≤ 1 ^ 2 * 1 * 1 := by gcongr
      _ = 1 := by ring
  have hadd : ‖(1 : ℚ_[p]) + b * c * (p : ℚ_[p]) ^ h‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) (hbcp.trans hpinv))
  have hsub : ‖(1 : ℚ_[p]) - b * c * (p : ℚ_[p]) ^ h‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (by simp) (by rw [norm_neg]; exact hbcp.trans hpinv))
  refine mem_Iw_iff.2 ⟨fun i j => ?_, ?_, by rw [det_ℓQH, norm_one]⟩
  · fin_cases i <;> fin_cases j
    · simpa [ℓQH] using hsub
    · simpa [ℓQH] using hb2cP
    · simpa [ℓQH] using hcp.trans hpinv
    · simpa [ℓQH] using hadd
  · simpa [ℓQH] using hcp

/-- `ℓQHinv b c ∈ Iw_p` for `b, c` integral and `h ≥ 1`. -/
theorem ℓQHinv_mem_Iw {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ℓQHinv p h b c ∈ Iw p 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  have hnp : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have hcp : ‖c * (p : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, hnp]; exact mul_le_of_le_one_left (by positivity) hc
  have hph : ‖(p : ℚ_[p]) ^ h‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_pow, hnp]; exact pow_le_of_le_one (by positivity) hpinv hh.ne'
  have hbcp : ‖b * c * (p : ℚ_[p]) ^ h‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, norm_mul]
    calc ‖b‖ * ‖c‖ * ‖(p : ℚ_[p]) ^ h‖ ≤ 1 * 1 * (p : ℝ)⁻¹ := by gcongr
      _ = (p : ℝ)⁻¹ := by ring
  have hP1 : ‖(p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p])‖ ≤ 1 :=
    (norm_pow_mul_pow_div_le hh).trans (pow_le_one₀ (by positivity) hpinv)
  have hb2cP : ‖b ^ 2 * c * ((p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p]))‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖b‖ ^ 2 * ‖c‖ * ‖(p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p])‖
        ≤ 1 ^ 2 * 1 * 1 := by gcongr
      _ = 1 := by ring
  have hadd : ‖(1 : ℚ_[p]) + b * c * (p : ℚ_[p]) ^ h‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) (hbcp.trans hpinv))
  have hsub : ‖(1 : ℚ_[p]) - b * c * (p : ℚ_[p]) ^ h‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (by simp) (by rw [norm_neg]; exact hbcp.trans hpinv))
  have hdet : (ℓQHinv p h b c).det = 1 := by
    rw [ℓQHinv, Matrix.det_fin_two_of]
    field_simp
    ring
  refine mem_Iw_iff.2 ⟨fun i j => ?_, ?_, by rw [hdet, norm_one]⟩
  · fin_cases i <;> fin_cases j
    · simpa [ℓQHinv] using hadd
    · simpa [ℓQHinv] using hb2cP
    · simpa [ℓQHinv] using hcp.trans hpinv
    · simpa [ℓQHinv] using hsub
  · simpa [ℓQHinv] using hcp

/-- **`wQH` normalises the disc-`0` part of `Iw_p` at level `h`**: for `g ∈ Iw_p` with
`p^h ∣ b`, both `wQH g wQH⁻¹` and `wQH⁻¹ g wQH` lie in `Iw_p` with `p^h ∣ b`. -/
theorem wQH_conj_mem_Iw (h : ℕ) {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1)
    (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹ ^ h) :
    (wQH p h * g * wQHinv p h ∈ Iw p 1 ∧ ‖(wQH p h * g * wQHinv p h) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h)
      ∧ (wQHinv p h * g * wQH p h ∈ Iw p 1
        ∧ ‖(wQHinv p h * g * wQH p h) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph0 : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  have hnp : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  obtain ⟨h1, h2, h3⟩ := hg
  have h2' : ‖g 1 0‖ ≤ (p : ℝ)⁻¹ := by simpa using h2
  have hc' : ‖-(g 1 0 * (p : ℚ_[p]) ^ h / (p : ℚ_[p]))‖ ≤ (p : ℝ)⁻¹ ^ h := by
    rw [norm_neg, norm_div, norm_mul, norm_pow, hnp]
    calc ‖g 1 0‖ * (p : ℝ)⁻¹ ^ h / (p : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ h / (p : ℝ)⁻¹ := by
          gcongr
      _ = (p : ℝ)⁻¹ ^ h := mul_div_cancel_left₀ _ hpos.ne'
  have hb' : ‖-(g 0 1 * (p : ℚ_[p]) / (p : ℚ_[p]) ^ h)‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_neg, norm_div, norm_mul, norm_pow, hnp]
    calc ‖g 0 1‖ * (p : ℝ)⁻¹ / (p : ℝ)⁻¹ ^ h ≤ (p : ℝ)⁻¹ ^ h * (p : ℝ)⁻¹ / (p : ℝ)⁻¹ ^ h := by
          gcongr
      _ = (p : ℝ)⁻¹ := mul_div_cancel_left₀ _ (pow_ne_zero _ hpos.ne')
  have hswap : (!![g 1 1, -(g 1 0 * (p : ℚ_[p]) ^ h / p);
        -(g 0 1 * (p : ℚ_[p]) / (p : ℚ_[p]) ^ h), g 0 0] : Matrix (Fin 2) (Fin 2) ℚ_[p])
        ∈ Iw p 1 ∧
      ‖(!![g 1 1, -(g 1 0 * (p : ℚ_[p]) ^ h / p);
        -(g 0 1 * (p : ℚ_[p]) / (p : ℚ_[p]) ^ h), g 0 0] : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖
        ≤ (p : ℝ)⁻¹ ^ h := by
    refine ⟨mem_Iw_iff.2 ⟨fun i j => ?_, by simpa using hb', ?_⟩, by simpa using hc'⟩
    · fin_cases i <;> fin_cases j
      · simpa using h1 1 1
      · simpa using hc'.trans (pow_le_one₀ hpos.le hpinv)
      · simpa using hb'.trans hpinv
      · simpa using h1 0 0
    · rw [Matrix.det_fin_two_of, ← h3, Matrix.det_fin_two]
      congr 1
      field_simp
  rw [wQH_mul_mul_wQHinv, wQHinv_mul_mul_wQH]
  exact ⟨hswap, hswap⟩

/-! ### The disc bookkeeping at disc `0`, level `h` -/

/-- **A matrix with `p^h ∣ b` fixes disc `0`** (`discImage h δ 0 = (b/d) mod p^h`). -/
theorem discImage_zero_of_norm_apply_zero_one_le_pow (h : ℕ) (δ : M1 p)
    (hb : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h) : discImage h δ 0 = 0 := by
  rw [discImage, ZMod.val_zero, Nat.cast_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow, LocalMat.mobiusFun, mul_zero, zero_add, mul_zero,
    zero_add, Ring.inverse_unit, norm_mul, PadicInt.norm_units, mul_one, PadicInt.norm_def,
    M1.coe_toLocalMat_b]
  simpa using hb

/-- **The disc conjugate is `t_{a'}⁻¹ δ t_a`** at level `h` (`a' = discImage h δ a`). -/
theorem discConjMat_eq_tMatHInv_mul_mul_tMatH (h : ℕ) (δ : M1 p) (a : ZMod (p ^ h)) :
    discConjMat h δ a
      = tMatHInv p h (((discImage h δ a).val : ℕ) : ℚ_[p]) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p])
          * tMatH p h ((a.val : ℕ) : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [discConjMat, tMatH, tMatHInv] <;> (try field_simp) <;> (try ring)

/-- At a matrix fixing disc `0`, the disc-`0` conjugate is `t₀⁻¹ δ t₀`. -/
theorem discConjMat_zero_of_discImage_zero_prime_pow (h : ℕ) (δ : M1 p)
    (hδ : discImage h δ 0 = 0) :
    discConjMat h δ 0 = tMatHInv p h 0 * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) * tMatH p h 0 := by
  rw [discConjMat_eq_tMatHInv_mul_mul_tMatH, hδ, ZMod.val_zero, Nat.cast_zero]

/-- `s_{−a'} δ s_a = t₀ · discConjMat δ a · t₀⁻¹` at level `h`. -/
theorem conj_sQ_eq_tMatH_mul_discConjMat (h : ℕ) (δ : M1 p) (a : ZMod (p ^ h)) :
    sQ p (-(((discImage h δ a).val : ℕ) : ℚ_[p])) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p])
        * sQ p ((a.val : ℕ) : ℚ_[p])
      = tMatH p h 0 * discConjMat h δ a * tMatHInv p h 0 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  rw [discConjMat_eq_tMatHInv_mul_mul_tMatH]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [tMatH, tMatHInv, sQ, hph] <;> (try field_simp)

/-- `vQ c` fixes disc `0` at every level. -/
theorem discImage_vQ_zero_prime_pow (h : ℕ) {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    discImage h (⟨vQ p c, vQ_mem_M1 hc⟩ : M1 p) 0 = 0 := by
  refine discImage_zero_of_norm_apply_zero_one_le_pow h _ ?_
  have h01 : (vQ p c) 0 1 = 0 := by simp [vQ]
  change ‖(vQ p c) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h
  rw [h01, norm_zero]
  positivity

/-- `ℓQH b c` fixes disc `0` (its `b`-entry is divisible by `p^{2h−1}`, hence by `p^h`). -/
theorem discImage_ℓQH_zero {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    discImage h (⟨ℓQH p h b c, Iw_one_le_M1 (ℓQH_mem_Iw hh hb hc)⟩ : M1 p) 0 = 0 := by
  refine discImage_zero_of_norm_apply_zero_one_le_pow h _ ?_
  have hP := norm_pow_mul_pow_div_le (p := p) hh
  have h01 : (ℓQH p h b c) 0 1 = -(b ^ 2 * c * ((p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / p)) := by
    simp [ℓQH]
  change ‖(ℓQH p h b c) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h
  rw [h01, norm_neg, norm_mul, norm_mul, norm_pow]
  calc ‖b‖ ^ 2 * ‖c‖ * ‖(p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p])‖
      ≤ 1 ^ 2 * 1 * (p : ℝ)⁻¹ ^ h := by gcongr
    _ = (p : ℝ)⁻¹ ^ h := by ring

/-- `ℓQHinv b c` fixes disc `0`. -/
theorem discImage_ℓQHinv_zero {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    discImage h (⟨ℓQHinv p h b c, Iw_one_le_M1 (ℓQHinv_mem_Iw hh hb hc)⟩ : M1 p) 0 = 0 := by
  refine discImage_zero_of_norm_apply_zero_one_le_pow h _ ?_
  have hP := norm_pow_mul_pow_div_le (p := p) hh
  have h01 : (ℓQHinv p h b c) 0 1 = b ^ 2 * c * ((p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / p) := by
    simp [ℓQHinv]
  change ‖(ℓQHinv p h b c) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h
  rw [h01, norm_mul, norm_mul, norm_pow]
  calc ‖b‖ ^ 2 * ‖c‖ * ‖(p : ℚ_[p]) ^ h * (p : ℚ_[p]) ^ h / (p : ℚ_[p])‖
      ≤ 1 ^ 2 * 1 * (p : ℝ)⁻¹ ^ h := by gcongr
    _ = (p : ℝ)⁻¹ ^ h := by ring

/-- The `d`-entry of the disc-`0` conjugate of `ℓQH b c` is `1 + bcp^h`. -/
theorem discConj_ℓQH_zero_one_one {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    (discConj h (⟨ℓQH p h b c, Iw_one_le_M1 (ℓQH_mem_Iw hh hb hc)⟩ : M1 p) 0 :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 + b * c * (p : ℚ_[p]) ^ h := by
  simp [ℓQH]

/-- The `d`-entry of the disc-`0` conjugate of `ℓQHinv b c` is `1 − bcp^h`. -/
theorem discConj_ℓQHinv_zero_one_one {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    (discConj h (⟨ℓQHinv p h b c, Iw_one_le_M1 (ℓQHinv_mem_Iw hh hb hc)⟩ : M1 p) 0 :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 - b * c * (p : ℚ_[p]) ^ h := by
  simp [ℓQHinv]

/-- The translation `sQ b` moves disc `0` to disc `b mod p^h`. -/
theorem discImage_sQ_zero_prime_pow (h : ℕ) (b : ℕ) :
    discImage h (⟨sQ p b, Iw_one_le_M1 (sQ_mem_Iw (by
      exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b))⟩ : M1 p) 0 = (b : ZMod (p ^ h)) := by
  suffices key : ∀ g : M1 p, (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = sQ p b →
      discImage h g 0 = (b : ZMod (p ^ h)) from key _ rfl
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

/-- The translation `sQ b`, `b < p^h`, has trivial disc-`0` conjugate. -/
theorem discConj_sQ_zero_prime_pow (h : ℕ) {b : ℕ} (hb : b < p ^ h) :
    discConj h (⟨sQ p b, Iw_one_le_M1 (sQ_mem_Iw (by
      exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b))⟩ : M1 p) 0 = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hph : (p : ℚ_[p]) ^ h ≠ 0 := pow_ne_zero _ hp0
  refine Subtype.ext ?_
  rw [coe_discConj, discConjMat_eq_tMatHInv_mul_mul_tMatH, discImage_sQ_zero_prime_pow,
    ZMod.val_natCast, Nat.mod_eq_of_lt hb, ZMod.val_zero, Nat.cast_zero, OneMemClass.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMatH, tMatHInv, sQ, Matrix.mul_apply, Fin.sum_univ_two, hph]
  field_simp
  ring

end LWX
