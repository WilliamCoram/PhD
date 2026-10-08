/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Instances.Matrix

/-!
# Iwahori subgroups, the monoids `M_t` and the coset decomposition of `U η U`

For a valued field `K`: the monoid `M(γ) = {g ∈ M₂(𝒪) | v(c) ≤ γ, v(d) = 1, det g ≠ 0}` — Buzzard's
`M_t` at `γ = v(ϖ)^t` — the Iwahori subgroup `Iw(γ) ⊆ GL₂(𝒪)`, its subgroups `Iw₁(γ)` (`d ≡ 1`) and
`Iw₁₁(γ)` (`a ≡ d ≡ 1`), and the element `η = diag(ϖ, 1)`. The main result is the coset
decomposition `U η U = ∐_α U · ((ϖ 0), (α ϖ^t 1))`, over a residue system `α`, for every subgroup
`Iw₁₁(γ) ≤ U ≤ Iw(γ)`, and its left-coset companion `= ∐_β ((ϖ β), (0 1)) · U`.

[Buz07, §9, p. 68]: "define `M_t` to be the elements `(γ_j)` of `M₂(𝒪_p)` with the property that if
`γ_j = ((a_j b_j), (c_j d_j))` then `det(γ_j) ≠ 0`, `π_j^{t_j}` divides `c_j`, and `π_j` does not
divide `d_j`. Then `M_t` is a monoid under multiplication." [Buz07, proof of Lemma 12.1]: "the
natural left coset decomposition of the double coset `U₀(π^t) ((π 0), (0 1)) U₀(π^t)` is
`∐_{α ∈ 𝒪/π} U₀(π^t) ((π 0), (α π^t 1))`."

## Main definitions

* `LocalLevel.monoidM`, `LocalLevel.iwahori`, `LocalLevel.iwahoriOne`,
  `LocalLevel.iwahoriPrincipal`.
* `LocalLevel.etaGL`, `LocalLevel.lowerUnip`, `LocalLevel.etaRep`, `LocalLevel.upperRep`.
* `LocalLevel.ballIdeal`: the ideal `𝔞_γ = {x ∈ 𝒪 | v(x) ≤ γ}`.
* `LocalLevel.lowerRightResidue`: the character `((a b), (c d)) ↦ d mod 𝔞_γ` of `Iw(γ)`.

## Main results

* `LocalLevel.mem_iwahori_iff`: `Iw(γ)` is the unit group of `M(γ)`.
* `LocalLevel.iwahoriOne_normal`, `LocalLevel.iwahoriPrincipal_normal`,
  `LocalLevel.ker_lowerRightResidue`, `LocalLevel.lowerRightResidue_surjective`:
  `Iw(γ) / Iw₁(γ) ≃ (𝒪/𝔞_γ)^×`.
* `LocalLevel.isOpen_iwahori`, `LocalLevel.isOpen_iwahoriOne`, `LocalLevel.isOpen_iwahoriPrincipal`.
* `LocalLevel.valued_le_one_of_etaConj_mem`, `LocalLevel.inv_mul_etaGL_mul_mem_iwahoriPrincipal`:
  the residue is integral and the correction factor is principal.
* `LocalLevel.existsUnique_etaRep`, `LocalLevel.bijOn_etaRep`: the right-coset decomposition of
  `U η U`.
* `LocalLevel.existsUnique_upperRep`: the left-coset decomposition.
* `LocalLevel.etaGL_not_unit`: `η` is not a unit of `M(γ)`.
* `LocalLevel.valued_det_of_mem_doubleCoset`, `LocalLevel.mem_monoidM_iff_norm`: the determinant
  on `U η U` and the norm form of `M_t`.

Roadmap: §0.4.1, §0.4.2. Tau Ceti home: `TauCeti/NumberTheory/AutomorphicForm/LocalLevel.lean`.
-/

open scoped Pointwise

noncomputable section

namespace LocalLevel

variable (K : Type*) [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

variable {K} in
private theorem v_add_le {x y : K} {γ : Γ₀} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

variable {K} in
private theorem v_sub_le {x y : K} {γ : Γ₀} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ :=
  (Valuation.map_sub _ x y).trans (max_le hx hy)

variable {K} in
private theorem v_mul_le_left {x y : K} {γ : Γ₀} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ γ) :
    Valued.v (x * y) ≤ γ := by
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ 1 * γ := mul_le_mul' hx hy
    _ = γ := one_mul γ

variable {K} in
private theorem v_mul_le_right {x y : K} {γ : Γ₀} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ γ := by
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ γ * 1 := mul_le_mul' hx hy
    _ = γ := mul_one γ

variable {K} in
private theorem ne_zero_of_v_eq_one {x : K} (h : Valued.v x = (1 : Γ₀)) : x ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  exact zero_ne_one h

variable {K} in
private theorem v_inv_mul_of_v_eq_one {d : K} (hd : Valued.v d = (1 : Γ₀)) (x : K) :
    Valued.v (d⁻¹ * x) = Valued.v x := by
  rw [map_mul, map_inv₀, hd, inv_one, one_mul]

variable {K} in
private theorem mul_apply₂ (g h : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

variable {K} in
private theorem v_det_le_one {m : Matrix (Fin 2) (Fin 2) K}
    (hm : ∀ i j, Valued.v (m i j) ≤ (1 : Γ₀)) : Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  exact v_sub_le (v_mul_le_left (hm 0 0) (hm 1 1)) (v_mul_le_left (hm 0 1) (hm 1 0))

variable {K} in
private theorem coe_inv_apply (g : GL (Fin 2) K) (i j : Fin 2) :
    (g⁻¹ : GL (Fin 2) K).1 i j = g.1.det⁻¹ * g.1.adjugate i j := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]

variable {K} in
private theorem inv_apply_zero_zero (g : GL (Fin 2) K) :
    (g⁻¹ : GL (Fin 2) K).1 0 0 = g.1.det⁻¹ * g.1 1 1 := by
  rw [coe_inv_apply, Matrix.adjugate_fin_two]
  rfl

variable {K} in
private theorem inv_apply_zero_one (g : GL (Fin 2) K) :
    (g⁻¹ : GL (Fin 2) K).1 0 1 = g.1.det⁻¹ * -g.1 0 1 := by
  rw [coe_inv_apply, Matrix.adjugate_fin_two]
  rfl

variable {K} in
private theorem inv_apply_one_zero (g : GL (Fin 2) K) :
    (g⁻¹ : GL (Fin 2) K).1 1 0 = g.1.det⁻¹ * -g.1 1 0 := by
  rw [coe_inv_apply, Matrix.adjugate_fin_two]
  rfl

variable {K} in
private theorem inv_apply_one_one (g : GL (Fin 2) K) :
    (g⁻¹ : GL (Fin 2) K).1 1 1 = g.1.det⁻¹ * g.1 0 0 := by
  rw [coe_inv_apply, Matrix.adjugate_fin_two]
  rfl

/-- **The monoid `M(γ)`**: integral matrices with `v(c) ≤ γ`, `v(d) = 1` and nonzero determinant.
Buzzard's `M_t` is `M(v(ϖ)^t)`. -/
def monoidM (γ : Γ₀) (hγ : γ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) K) where
  carrier := {g | (∀ i j, Valued.v (g i j) ≤ 1) ∧ Valued.v (g 1 0) ≤ γ ∧ Valued.v (g 1 1) = 1 ∧
    g.det ≠ 0}
  mul_mem' {g h} hg hh := by
    obtain ⟨hgi, hgc, hgd, hgdet⟩ := hg
    obtain ⟨hhi, hhc, hhd, hhdet⟩ := hh
    have hlt : Valued.v (g 1 0 * h 0 1) < Valued.v (g 1 1 * h 1 1) := by
      refine (v_mul_le_right hgc (hhi 0 1)).trans_lt ?_
      rw [map_mul, hgd, hhd, one_mul]
      exact hγ
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · rw [mul_apply₂]
      exact v_add_le (v_mul_le_left (hgi i 0) (hhi 0 j)) (v_mul_le_left (hgi i 1) (hhi 1 j))
    · rw [mul_apply₂]
      exact v_add_le (v_mul_le_right hgc (hhi 0 0)) (v_mul_le_left (hgi 1 1) hhc)
    · rw [mul_apply₂, Valuation.map_add_eq_of_lt_right _ hlt, map_mul, hgd, hhd, one_mul]
    · rw [Matrix.det_mul]
      exact mul_ne_zero hgdet hhdet
  one_mem' := ⟨fun i j => by rw [Matrix.one_apply]; split_ifs <;> simp, by simp, by simp,
    by simp⟩

/-- **The Iwahori subgroup `Iw(γ)`**: integral matrices with unit determinant and `v(c) ≤ γ`. -/
def iwahori (γ : Γ₀) : Subgroup (GL (Fin 2) K) where
  carrier := {g | (∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1) ∧
    Valued.v (g : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
    Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ≤ γ}
  mul_mem' {g h} hg hh := by
    obtain ⟨hgi, hgd, hgc⟩ := hg
    obtain ⟨hhi, hhd, hhc⟩ := hh
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [Units.val_mul, mul_apply₂]
      exact v_add_le (v_mul_le_left (hgi i 0) (hhi 0 j)) (v_mul_le_left (hgi i 1) (hhi 1 j))
    · rw [Units.val_mul, Matrix.det_mul, map_mul, hgd, hhd, one_mul]
    · rw [Units.val_mul, mul_apply₂]
      exact v_add_le (v_mul_le_right hgc (hhi 0 0)) (v_mul_le_left (hgi 1 1) hhc)
  one_mem' := ⟨fun i j => by rw [Units.val_one, Matrix.one_apply]; split_ifs <;> simp,
    by simp, by simp⟩
  inv_mem' {g} hg := by
    obtain ⟨hgi, hgd, hgc⟩ := hg
    refine ⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_, ?_⟩
    · rw [inv_apply_zero_zero, v_inv_mul_of_v_eq_one hgd]
      exact hgi 1 1
    · rw [inv_apply_zero_one, v_inv_mul_of_v_eq_one hgd, Valuation.map_neg]
      exact hgi 0 1
    · rw [inv_apply_one_zero, v_inv_mul_of_v_eq_one hgd, Valuation.map_neg]
      exact hgi 1 0
    · rw [inv_apply_one_one, v_inv_mul_of_v_eq_one hgd]
      exact hgi 0 0
    · have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) K => Valued.v m.det) (Units.mul_inv g)
      simp only [Matrix.det_mul, map_mul, hgd, one_mul, Matrix.det_one, map_one] at h
      exact h
    · rw [inv_apply_one_zero, v_inv_mul_of_v_eq_one hgd, Valuation.map_neg]
      exact hgc

variable {K} in
private theorem v_mul_zero_zero_sub_le {γ : Γ₀} {x y : GL (Fin 2) K} (hx : x ∈ iwahori K γ)
    (hy : y ∈ iwahori K γ) : Valued.v ((x * y).1 0 0 - x.1 0 0 * y.1 0 0) ≤ γ := by
  rw [Units.val_mul, mul_apply₂, add_sub_cancel_left]
  exact v_mul_le_left (hx.1 0 1) hy.2.2

variable {K} in
private theorem v_mul_one_one_sub_le {γ : Γ₀} {x y : GL (Fin 2) K} (hx : x ∈ iwahori K γ)
    (hy : y ∈ iwahori K γ) : Valued.v ((x * y).1 1 1 - x.1 1 1 * y.1 1 1) ≤ γ := by
  rw [Units.val_mul, mul_apply₂, add_sub_cancel_right]
  exact v_mul_le_right hx.2.2 (hy.1 0 1)

variable {K} in
private theorem v_zero_zero_mul_sub_one {γ : Γ₀} {x y : GL (Fin 2) K} (hx : x ∈ iwahori K γ)
    (hy : y ∈ iwahori K γ) (hx1 : Valued.v (x.1 0 0 - 1) ≤ γ)
    (hy1 : Valued.v (y.1 0 0 - 1) ≤ γ) : Valued.v ((x * y).1 0 0 - 1) ≤ γ := by
  have e : (x * y).1 0 0 - 1 =
      ((x * y).1 0 0 - x.1 0 0 * y.1 0 0) + (x.1 0 0 - 1) * y.1 0 0 + (y.1 0 0 - 1) := by ring
  rw [e]
  exact v_add_le (v_add_le (v_mul_zero_zero_sub_le hx hy) (v_mul_le_right hx1 (hy.1 0 0))) hy1

variable {K} in
private theorem v_one_one_mul_sub_one {γ : Γ₀} {x y : GL (Fin 2) K} (hx : x ∈ iwahori K γ)
    (hy : y ∈ iwahori K γ) (hx1 : Valued.v (x.1 1 1 - 1) ≤ γ)
    (hy1 : Valued.v (y.1 1 1 - 1) ≤ γ) : Valued.v ((x * y).1 1 1 - 1) ≤ γ := by
  have e : (x * y).1 1 1 - 1 =
      ((x * y).1 1 1 - x.1 1 1 * y.1 1 1) + (x.1 1 1 - 1) * y.1 1 1 + (y.1 1 1 - 1) := by ring
  rw [e]
  exact v_add_le (v_add_le (v_mul_one_one_sub_le hx hy) (v_mul_le_right hx1 (hy.1 1 1))) hy1

variable {K} in
private theorem v_zero_zero_inv_sub_one {γ : Γ₀} {x : GL (Fin 2) K} (hx : x ∈ iwahori K γ)
    (hx1 : Valued.v (x.1 0 0 - 1) ≤ γ) : Valued.v ((x⁻¹ : GL (Fin 2) K).1 0 0 - 1) ≤ γ := by
  have hP : (x⁻¹ * x : GL (Fin 2) K).1 0 0 = 1 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  have e : (x⁻¹ : GL (Fin 2) K).1 0 0 - 1 =
      -((x⁻¹ * x : GL (Fin 2) K).1 0 0 - (x⁻¹ : GL (Fin 2) K).1 0 0 * x.1 0 0) -
        (x⁻¹ : GL (Fin 2) K).1 0 0 * (x.1 0 0 - 1) := by
    rw [hP]; ring
  rw [e]
  exact v_sub_le (by rw [Valuation.map_neg]; exact v_mul_zero_zero_sub_le (inv_mem hx) hx)
    (v_mul_le_left ((inv_mem hx).1 0 0) hx1)

variable {K} in
private theorem v_one_one_inv_sub_one {γ : Γ₀} {x : GL (Fin 2) K} (hx : x ∈ iwahori K γ)
    (hx1 : Valued.v (x.1 1 1 - 1) ≤ γ) : Valued.v ((x⁻¹ : GL (Fin 2) K).1 1 1 - 1) ≤ γ := by
  have hP : (x⁻¹ * x : GL (Fin 2) K).1 1 1 = 1 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  have e : (x⁻¹ : GL (Fin 2) K).1 1 1 - 1 =
      -((x⁻¹ * x : GL (Fin 2) K).1 1 1 - (x⁻¹ : GL (Fin 2) K).1 1 1 * x.1 1 1) -
        (x⁻¹ : GL (Fin 2) K).1 1 1 * (x.1 1 1 - 1) := by
    rw [hP]; ring
  rw [e]
  exact v_sub_le (by rw [Valuation.map_neg]; exact v_mul_one_one_sub_le (inv_mem hx) hx)
    (v_mul_le_left ((inv_mem hx).1 1 1) hx1)

variable {K} in
private theorem v_zero_zero_conj {γ : Γ₀} {g n : GL (Fin 2) K} (hg : g ∈ iwahori K γ)
    (hn : n ∈ iwahori K γ) (hn1 : Valued.v (n.1 0 0 - 1) ≤ γ) :
    Valued.v ((g * n * g⁻¹).1 0 0 - 1) ≤ γ := by
  have hgi := inv_mem hg
  have hP : (g * g⁻¹ : GL (Fin 2) K).1 0 0 = 1 := by
    rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  have e : (g * n * g⁻¹).1 0 0 - 1 =
      ((g * n * g⁻¹).1 0 0 - (g * n).1 0 0 * (g⁻¹ : GL (Fin 2) K).1 0 0) +
        ((g * n).1 0 0 - g.1 0 0 * n.1 0 0) * (g⁻¹ : GL (Fin 2) K).1 0 0 +
        g.1 0 0 * (n.1 0 0 - 1) * (g⁻¹ : GL (Fin 2) K).1 0 0 -
        ((g * g⁻¹ : GL (Fin 2) K).1 0 0 - g.1 0 0 * (g⁻¹ : GL (Fin 2) K).1 0 0) := by
    rw [hP]; ring
  rw [e]
  exact v_sub_le (v_add_le (v_add_le (v_mul_zero_zero_sub_le (mul_mem hg hn) hgi)
    (v_mul_le_right (v_mul_zero_zero_sub_le hg hn) (hgi.1 0 0)))
    (v_mul_le_right (v_mul_le_left (hg.1 0 0) hn1) (hgi.1 0 0)))
    (v_mul_zero_zero_sub_le hg hgi)

variable {K} in
private theorem v_one_one_conj {γ : Γ₀} {g n : GL (Fin 2) K} (hg : g ∈ iwahori K γ)
    (hn : n ∈ iwahori K γ) (hn1 : Valued.v (n.1 1 1 - 1) ≤ γ) :
    Valued.v ((g * n * g⁻¹).1 1 1 - 1) ≤ γ := by
  have hgi := inv_mem hg
  have hP : (g * g⁻¹ : GL (Fin 2) K).1 1 1 = 1 := by
    rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  have e : (g * n * g⁻¹).1 1 1 - 1 =
      ((g * n * g⁻¹).1 1 1 - (g * n).1 1 1 * (g⁻¹ : GL (Fin 2) K).1 1 1) +
        ((g * n).1 1 1 - g.1 1 1 * n.1 1 1) * (g⁻¹ : GL (Fin 2) K).1 1 1 +
        g.1 1 1 * (n.1 1 1 - 1) * (g⁻¹ : GL (Fin 2) K).1 1 1 -
        ((g * g⁻¹ : GL (Fin 2) K).1 1 1 - g.1 1 1 * (g⁻¹ : GL (Fin 2) K).1 1 1) := by
    rw [hP]; ring
  rw [e]
  exact v_sub_le (v_add_le (v_add_le (v_mul_one_one_sub_le (mul_mem hg hn) hgi)
    (v_mul_le_right (v_mul_one_one_sub_le hg hn) (hgi.1 1 1)))
    (v_mul_le_right (v_mul_le_left (hg.1 1 1) hn1) (hgi.1 1 1)))
    (v_mul_one_one_sub_le hg hgi)

variable {K} in
private theorem v_inv_mul_zero_zero_sub_one {γ : Γ₀} {u w : GL (Fin 2) K}
    (hu : u ∈ iwahori K γ) (hw : w ∈ iwahori K γ) (h : Valued.v (w.1 0 0 - u.1 0 0) ≤ γ) :
    Valued.v ((u⁻¹ * w).1 0 0 - 1) ≤ γ := by
  have hui := inv_mem hu
  have hP : (u⁻¹ * u : GL (Fin 2) K).1 0 0 = 1 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  have e : (u⁻¹ * w).1 0 0 - 1 =
      ((u⁻¹ * w).1 0 0 - (u⁻¹ : GL (Fin 2) K).1 0 0 * w.1 0 0) +
        (u⁻¹ : GL (Fin 2) K).1 0 0 * (w.1 0 0 - u.1 0 0) -
        ((u⁻¹ * u : GL (Fin 2) K).1 0 0 - (u⁻¹ : GL (Fin 2) K).1 0 0 * u.1 0 0) := by
    rw [hP]; ring
  rw [e]
  exact v_sub_le (v_add_le (v_mul_zero_zero_sub_le hui hw) (v_mul_le_left (hui.1 0 0) h))
    (v_mul_zero_zero_sub_le hui hu)

variable {K} in
private theorem v_inv_mul_one_one_sub_one {γ : Γ₀} {u w : GL (Fin 2) K}
    (hu : u ∈ iwahori K γ) (hw : w ∈ iwahori K γ) (h : Valued.v (w.1 1 1 - u.1 1 1) ≤ γ) :
    Valued.v ((u⁻¹ * w).1 1 1 - 1) ≤ γ := by
  have hui := inv_mem hu
  have hP : (u⁻¹ * u : GL (Fin 2) K).1 1 1 = 1 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  have e : (u⁻¹ * w).1 1 1 - 1 =
      ((u⁻¹ * w).1 1 1 - (u⁻¹ : GL (Fin 2) K).1 1 1 * w.1 1 1) +
        (u⁻¹ : GL (Fin 2) K).1 1 1 * (w.1 1 1 - u.1 1 1) -
        ((u⁻¹ * u : GL (Fin 2) K).1 1 1 - (u⁻¹ : GL (Fin 2) K).1 1 1 * u.1 1 1) := by
    rw [hP]; ring
  rw [e]
  exact v_sub_le (v_add_le (v_mul_one_one_sub_le hui hw) (v_mul_le_left (hui.1 1 1) h))
    (v_mul_one_one_sub_le hui hu)

variable {K} in
private theorem v_one_one_eq_one {γ : Γ₀} (hγ : γ < 1) {g : GL (Fin 2) K}
    (hg : g ∈ iwahori K γ) : Valued.v (g.1 1 1) = 1 := by
  obtain ⟨hgi, hgd, hgc⟩ := hg
  have h01 : Valued.v (g.1 0 1 * g.1 1 0) < 1 := (v_mul_le_left (hgi 0 1) hgc).trans_lt hγ
  have hprod : 1 ≤ Valued.v (g.1 0 0 * g.1 1 1) := by
    by_contra hlt
    have hdet : Valued.v g.1.det < 1 := by
      rw [Matrix.det_fin_two]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt (not_le.mp hlt) h01)
    exact hdet.ne hgd
  refine le_antisymm (hgi 1 1) (hprod.trans ?_)
  rw [map_mul]
  calc Valued.v (g.1 0 0) * Valued.v (g.1 1 1) ≤ 1 * Valued.v (g.1 1 1) :=
        mul_le_mul' (hgi 0 0) le_rfl
    _ = Valued.v (g.1 1 1) := one_mul _

variable {K} in
private theorem v_residue_mul_eq_one {γ : Γ₀} {x y : GL (Fin 2) K} (hx : x ∈ iwahori K γ)
    (hy : y ∈ iwahori K γ) (hxy : x * y = 1) : Valued.v (x.1 1 1 * y.1 1 1 - 1) ≤ γ := by
  have h1 : (x * y).1 1 1 = (1 : K) := by rw [hxy, Units.val_one, Matrix.one_apply_eq]
  rw [← h1, Valuation.map_sub_swap]
  exact v_mul_one_one_sub_le hx hy

/-- **`Iw₁(γ)`**: the elements of `Iw(γ)` with `d ≡ 1`. -/
def iwahoriOne (γ : Γ₀) : Subgroup (GL (Fin 2) K) where
  carrier := {g | g ∈ iwahori K γ ∧ Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ γ}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, v_one_one_mul_sub_one hg.1 hh.1 hg.2 hh.2⟩
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, v_one_one_inv_sub_one hg.1 hg.2⟩

/-- **`Iw₁₁(γ)`**: the elements of `Iw(γ)` with `a ≡ d ≡ 1`, the kernel of the diagonal residues. -/
def iwahoriPrincipal (γ : Γ₀) : Subgroup (GL (Fin 2) K) where
  carrier := {g | g ∈ iwahori K γ ∧ Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ≤ γ ∧
    Valued.v ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ γ}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, v_zero_zero_mul_sub_one hg.1 hh.1 hg.2.1 hh.2.1,
    v_one_one_mul_sub_one hg.1 hh.1 hg.2.2 hh.2.2⟩
  one_mem' := ⟨one_mem _, by simp, by simp⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, v_zero_zero_inv_sub_one hg.1 hg.2.1,
    v_one_one_inv_sub_one hg.1 hg.2.2⟩

variable {K}

/-- Membership in `M(γ)`: integral entries, `v(c) ≤ γ`, `v(d) = 1` and `det ≠ 0`. -/
theorem mem_monoidM_iff {γ : Γ₀} {hγ : γ < 1} {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ monoidM K γ hγ ↔
      (∀ i j, Valued.v (g i j) ≤ 1) ∧ Valued.v (g 1 0) ≤ γ ∧ Valued.v (g 1 1) = 1 ∧ g.det ≠ 0 :=
  Iff.rfl

/-- `Iw₁₁(γ) ⊆ Iw₁(γ)`. -/
theorem iwahoriPrincipal_le_iwahoriOne (γ : Γ₀) : iwahoriPrincipal K γ ≤ iwahoriOne K γ :=
  fun _ hg => ⟨hg.1, hg.2.2⟩

/-- `Iw₁(γ) ⊆ Iw(γ)`. -/
theorem iwahoriOne_le_iwahori (γ : Γ₀) : iwahoriOne K γ ≤ iwahori K γ :=
  fun _ hg => hg.1

/-- `Iw(γ)` shrinks as `γ` does: `M_{t+1} ⊆ M_t`. -/
theorem iwahori_mono {γ γ' : Γ₀} (h : γ ≤ γ') : iwahori K γ ≤ iwahori K γ' :=
  fun _ hg => ⟨hg.1, hg.2.1, hg.2.2.trans h⟩

/-- `M(γ)` shrinks as `γ` does. -/
theorem monoidM_mono {γ γ' : Γ₀} (hγ : γ < 1) (hγ' : γ' < 1) (h : γ ≤ γ') :
    monoidM K γ hγ ≤ monoidM K γ' hγ' :=
  fun _ hg => ⟨hg.1, hg.2.1.trans h, hg.2.2⟩

/-- **`Iw(γ) ⊆ M(γ)`.** -/
theorem coe_mem_monoidM {γ : Γ₀} (hγ : γ < 1) {g : GL (Fin 2) K} (hg : g ∈ iwahori K γ) :
    (g : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ :=
  ⟨hg.1, hg.2.2, v_one_one_eq_one hγ hg, ne_zero_of_v_eq_one hg.2.1⟩

/-- The units of `M(γ)` are `Iw(γ)`. -/
theorem mem_iwahori_iff {γ : Γ₀} (hγ : γ < 1) {g : GL (Fin 2) K} :
    g ∈ iwahori K γ ↔ (g : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ ∧
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ := by
  refine ⟨fun hg => ⟨coe_mem_monoidM hγ hg, coe_mem_monoidM hγ (inv_mem hg)⟩, fun h => ?_⟩
  have hd1 : Valued.v g.1.det ≤ 1 := v_det_le_one h.1.1
  have hd2 : Valued.v (g⁻¹ : GL (Fin 2) K).1.det ≤ 1 := v_det_le_one h.2.1
  have hmul : Valued.v g.1.det * Valued.v (g⁻¹ : GL (Fin 2) K).1.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  exact ⟨h.1.1, le_antisymm hd1 (not_lt.mp fun hlt =>
    (Left.mul_lt_one_of_lt_of_le hlt hd2).ne hmul), h.1.2.1⟩

/-- **`Iw₁(γ)` is normal in `Iw(γ)`.** -/
theorem iwahoriOne_normal (γ : Γ₀) : ((iwahoriOne K γ).subgroupOf (iwahori K γ)).Normal :=
  ⟨fun n hn g => ⟨(g * n * g⁻¹).2, v_one_one_conj g.2 n.2 hn.2⟩⟩

/-- **`Iw₁₁(γ)` is normal in `Iw(γ)`.** -/
theorem iwahoriPrincipal_normal (γ : Γ₀) :
    ((iwahoriPrincipal K γ).subgroupOf (iwahori K γ)).Normal :=
  ⟨fun n hn g => ⟨(g * n * g⁻¹).2, v_zero_zero_conj g.2 n.2 hn.2.1,
    v_one_one_conj g.2 n.2 hn.2.2⟩⟩

/-- The diagonal matrices `diag(x, d)` with `x ≠ 0` integral and `d` a unit lie in `M(γ)`. -/
theorem diagonal_mem_monoidM {γ : Γ₀} (hγ : γ < 1) {x d : K} (hx : Valued.v x ≤ 1) (hx0 : x ≠ 0)
    (hd : Valued.v d = 1) : Matrix.diagonal ![x, d] ∈ monoidM K γ hγ := by
  refine ⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_, ?_, ?_⟩ <;>
    simp [Matrix.det_diagonal, Fin.prod_univ_two, hx, hd, hx0, ne_zero_of_v_eq_one hd]

/-- Integral unit scalars lie in `M(γ)`; the scalar `ϖ` does not. -/
theorem smul_one_mem_monoidM_iff {γ : Γ₀} (hγ : γ < 1) {x : K} :
    x • (1 : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ ↔ Valued.v x = 1 := by
  constructor
  · rintro ⟨-, -, h, -⟩
    simpa using h
  · intro hx
    refine ⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_, ?_, ?_⟩ <;>
      simp [hx, ne_zero_of_v_eq_one hx]

section Residue

variable (K)

/-- The ideal `𝔞_γ = {x ∈ 𝒪 | v(x) ≤ γ}` of the valuation ring, for `γ ≤ 1`. -/
def ballIdeal (γ : Γ₀) : Ideal (Valued.v : Valuation K Γ₀).integer where
  carrier := {x | Valued.v (x : K) ≤ γ}
  add_mem' hx hy := v_add_le hx hy
  zero_mem' := (map_zero Valued.v).trans_le zero_le
  smul_mem' c _ hx := v_mul_le_left c.2 hx

/-- **The lower-right residue** `((a b), (c d)) ↦ d mod 𝔞_γ`, a character of `Iw(γ)`. -/
def lowerRightResidue (γ : Γ₀) :
    iwahori K γ →* ((Valued.v : Valuation K Γ₀).integer ⧸ ballIdeal K γ)ˣ where
  toFun g :=
    ⟨Ideal.Quotient.mk _ ⟨(g : GL (Fin 2) K).1 1 1, g.2.1 1 1⟩,
      Ideal.Quotient.mk _ ⟨((g : GL (Fin 2) K)⁻¹).1 1 1, (inv_mem g.2).1 1 1⟩,
      by
        rw [← map_mul, ← map_one (Ideal.Quotient.mk (ballIdeal K γ)), Ideal.Quotient.eq]
        exact v_residue_mul_eq_one g.2 (inv_mem g.2) (mul_inv_cancel _),
      by
        rw [← map_mul, ← map_one (Ideal.Quotient.mk (ballIdeal K γ)), Ideal.Quotient.eq]
        exact v_residue_mul_eq_one (inv_mem g.2) g.2 (inv_mul_cancel _)⟩
  map_one' := Units.ext <| by
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ 1
    congr 1
  map_mul' g h := Units.ext <| by
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _
    rw [← map_mul, Ideal.Quotient.eq]
    exact v_mul_one_one_sub_le g.2 h.2

variable {K}

/-- **`Iw(γ) / Iw₁(γ) ≃ (𝒪/𝔞_γ)^×` via `d`**: the kernel. -/
theorem ker_lowerRightResidue (γ : Γ₀) :
    (lowerRightResidue K γ).ker = (iwahoriOne K γ).subgroupOf (iwahori K γ) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Units.ext_iff]
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ 1 ↔ _
  rw [Ideal.Quotient.eq]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

/-- **`Iw(γ) / Iw₁(γ) ≃ (𝒪/𝔞_γ)^×` via `d`**: surjectivity, through `diag(1, d)`. -/
theorem lowerRightResidue_surjective {γ : Γ₀} (hγ : γ < 1) :
    Function.Surjective (lowerRightResidue K γ) := by
  intro u
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective
    (u : (Valued.v : Valuation K Γ₀).integer ⧸ ballIdeal K γ)
  obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective
    ((u⁻¹ : ((Valued.v : Valuation K Γ₀).integer ⧸ ballIdeal K γ)ˣ) :
      (Valued.v : Valuation K Γ₀).integer ⧸ ballIdeal K γ)
  have hde : Valued.v ((d : K) * e - 1) ≤ γ := by
    have h : Ideal.Quotient.mk (ballIdeal K γ) (d * e) =
        Ideal.Quotient.mk (ballIdeal K γ) 1 := by
      rw [map_mul, hd, he, Units.mul_inv, map_one]
    exact Ideal.Quotient.eq.mp h
  have hvd : Valued.v (d : K) = 1 := by
    have hlt : Valued.v ((d : K) * e - 1) < Valued.v (1 : K) := by
      rw [map_one]
      exact hde.trans_lt hγ
    have hde1 : Valued.v ((d : K) * e) = 1 := by
      calc Valued.v ((d : K) * e) = Valued.v (((d : K) * e - 1) + 1) := by rw [sub_add_cancel]
        _ = Valued.v (1 : K) := Valuation.map_add_eq_of_lt_right _ hlt
        _ = 1 := map_one _
    rw [map_mul] at hde1
    exact le_antisymm (d.2 : Valued.v (d : K) ≤ 1) (not_lt.mp fun h =>
      (Left.mul_lt_one_of_lt_of_le h (e.2 : Valued.v (e : K) ≤ 1)).ne hde1)
  let m : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, (d : K)])
    (by simpa [Matrix.det_diagonal, Fin.prod_univ_two] using ne_zero_of_v_eq_one hvd)
  have hmval : (m : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![1, (d : K)] := rfl
  have hm : m ∈ iwahori K γ := by
    refine ⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;>
      simp [hmval, Matrix.det_diagonal, Fin.prod_univ_two, hvd]
  refine ⟨⟨m, hm⟩, Units.ext ?_⟩
  rw [← hd]
  rfl

end Residue

section Topology

private theorem isOpen_setOf_v_le {γ : Γ₀} (hγ : ∃ x : K, x ≠ 0 ∧ Valued.v x ≤ γ) :
    IsOpen {y : K | Valued.v y ≤ γ} := by
  obtain ⟨x, hx0, hxγ⟩ := hγ
  have hr : (Valued.v : Valuation K Γ₀).restrict x ≠ 0 := fun h =>
    hx0 ((Valuation.zero_iff _).mp ((Valuation.restrict_eq_zero_iff (v := Valued.v)).mp h))
  refine isOpen_iff_mem_nhds.mpr fun y hy =>
    Valued.mem_nhds.mpr ⟨Units.mk0 _ hr, fun z hz => ?_⟩
  have hz' : Valued.v (z - y) < Valued.v x := (Valuation.restrict_lt_iff (v := Valued.v)).mp hz
  show Valued.v z ≤ γ
  rw [← sub_add_cancel z y]
  exact v_add_le (hz'.le.trans hxγ) hy

private theorem isOpen_setOf_v_eq_one : IsOpen {y : K | Valued.v y = (1 : Γ₀)} := by
  have hr : (Valued.v : Valuation K Γ₀).restrict 1 ≠ 0 := by
    rw [map_one]
    exact one_ne_zero
  refine isOpen_iff_mem_nhds.mpr fun y hy =>
    Valued.mem_nhds.mpr ⟨Units.mk0 _ hr, fun z hz => ?_⟩
  have hz' : Valued.v (z - y) < Valued.v y := by
    have h := (Valuation.restrict_lt_iff (v := Valued.v)).mp hz
    rwa [map_one, ← hy] at h
  show Valued.v z = 1
  rw [← hy, ← sub_add_cancel z y, Valuation.map_add_eq_of_lt_right _ hz']

/-- **`Iw(γ)` is open in `GL₂(K)`**, for `γ` at least the valuation of a nonzero element. -/
theorem isOpen_iwahori {γ : Γ₀} (hγ : ∃ x : K, x ≠ 0 ∧ Valued.v x ≤ γ) :
    IsOpen (iwahori K γ : Set (GL (Fin 2) K)) := by
  have hent : ∀ i j, Continuous fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have hdet : Continuous fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).det :=
    Units.continuous_val.matrix_det
  have h1 : IsOpen {y : K | Valued.v y ≤ (1 : Γ₀)} :=
    isOpen_setOf_v_le ⟨1, one_ne_zero, (map_one _).le⟩
  have e : (iwahori K γ : Set (GL (Fin 2) K)) =
      (⋂ i, ⋂ j, (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) i j) ⁻¹'
        {y | Valued.v y ≤ (1 : Γ₀)}) ∩
      ((fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).det) ⁻¹'
          {y | Valued.v y = (1 : Γ₀)} ∩
        (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) ⁻¹'
          {y | Valued.v y ≤ γ}) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    rfl
  rw [e]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    h1.preimage (hent i j)).inter ((isOpen_setOf_v_eq_one.preimage hdet).inter
      ((isOpen_setOf_v_le hγ).preimage (hent 1 0)))

/-- `Iw₁(γ)` is open. -/
theorem isOpen_iwahoriOne {γ : Γ₀} (hγ : ∃ x : K, x ≠ 0 ∧ Valued.v x ≤ γ) :
    IsOpen (iwahoriOne K γ : Set (GL (Fin 2) K)) :=
  (isOpen_iwahori hγ).inter ((isOpen_setOf_v_le hγ).preimage
    ((Units.continuous_val.matrix_elem 1 1).sub
      (continuous_const : Continuous fun _ : GL (Fin 2) K => (1 : K))))

/-- `Iw₁₁(γ)` is open. -/
theorem isOpen_iwahoriPrincipal {γ : Γ₀} (hγ : ∃ x : K, x ≠ 0 ∧ Valued.v x ≤ γ) :
    IsOpen (iwahoriPrincipal K γ : Set (GL (Fin 2) K)) :=
  (isOpen_iwahori hγ).inter (((isOpen_setOf_v_le hγ).preimage
    ((Units.continuous_val.matrix_elem 0 0).sub
      (continuous_const : Continuous fun _ : GL (Fin 2) K => (1 : K)))).inter
    ((isOpen_setOf_v_le hγ).preimage ((Units.continuous_val.matrix_elem 1 1).sub
      (continuous_const : Continuous fun _ : GL (Fin 2) K => (1 : K)))))

end Topology

section Eta

/-- **`η = diag(ϖ, 1)`.** -/
def etaGL (ϖ : K) (hϖ : ϖ ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![ϖ, 1])
    (by simpa [Matrix.det_diagonal, Fin.prod_univ_two] using hϖ)

/-- The lower unipotent `((1 0), (c 1))`. -/
def lowerUnip (c : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; c, 1] (by simp [Matrix.det_fin_two_of])

/-- **The right-coset representative** `x_α = η u_α = ((ϖ 0), (α ϖ^t 1))`. -/
def etaRep (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) : GL (Fin 2) K :=
  etaGL ϖ hϖ * lowerUnip (α * ϖ ^ t)

/-- **The left-coset representative** `((ϖ β), (0 1))`. -/
def upperRep (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![ϖ, β; 0, 1]
    (by simpa [Matrix.det_fin_two_of] using hϖ)

private theorem coe_etaGL (ϖ : K) (hϖ : ϖ ≠ 0) :
    (etaGL ϖ hϖ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![ϖ, 1] :=
  rfl

private theorem coe_lowerUnip (c : K) :
    (lowerUnip c : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] :=
  rfl

private theorem coe_upperRep (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) :
    (upperRep ϖ hϖ β : Matrix (Fin 2) (Fin 2) K) = !![ϖ, β; 0, 1] :=
  rfl

private theorem det_etaGL (ϖ : K) (hϖ : ϖ ≠ 0) :
    (etaGL ϖ hϖ : Matrix (Fin 2) (Fin 2) K).det = ϖ := by
  simp [coe_etaGL, Matrix.det_diagonal, Fin.prod_univ_two]

private theorem det_upperRep (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) :
    (upperRep ϖ hϖ β : Matrix (Fin 2) (Fin 2) K).det = ϖ := by
  rw [coe_upperRep, Matrix.det_fin_two_of]
  ring

/-- `x_α = ((ϖ 0), (α ϖ^t 1))`. -/
theorem coe_etaRep (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) :
    (etaRep ϖ hϖ t α : Matrix (Fin 2) (Fin 2) K) = !![ϖ, 0; α * ϖ ^ t, 1] := by
  rw [etaRep, Units.val_mul, coe_etaGL, coe_lowerUnip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `det x_α = ϖ`. -/
theorem det_etaRep (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) :
    (etaRep ϖ hϖ t α : Matrix (Fin 2) (Fin 2) K).det = ϖ := by
  rw [coe_etaRep, Matrix.det_fin_two_of]
  ring

/-- **`η ∈ M(γ)`.** -/
theorem coe_etaGL_mem_monoidM {γ : Γ₀} (hγ : γ < 1) {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ ≤ 1) :
    (etaGL ϖ hϖ : Matrix (Fin 2) (Fin 2) K) ∈ monoidM K γ hγ := by
  rw [coe_etaGL]
  exact diagonal_mem_monoidM hγ hϖ1 hϖ (map_one _)

/-- **`η` is not a unit of `M(γ)`**: `η⁻¹ = diag(ϖ⁻¹, 1)` is not integral. -/
theorem etaGL_not_unit {γ : Γ₀} (hγ : γ < 1) {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) :
    ((etaGL ϖ hϖ)⁻¹ : GL (Fin 2) K).1 ∉ monoidM K γ hγ := by
  intro h
  have h00 := h.1 0 0
  rw [inv_apply_zero_zero, det_etaGL, coe_etaGL] at h00
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_zero, mul_one,
    map_inv₀] at h00
  have hv0 : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ
  have h1 : (1 : Γ₀) ≤ Valued.v ϖ :=
    calc (1 : Γ₀) = Valued.v ϖ * (Valued.v ϖ)⁻¹ := (mul_inv_cancel₀ hv0).symm
      _ ≤ Valued.v ϖ * 1 := mul_le_mul' le_rfl h00
      _ = Valued.v ϖ := mul_one _
  exact absurd hϖ1 (not_lt.mpr h1)

/-- `((1 0), (c 1)) ∈ Iw₁₁(γ)` when `v(c) ≤ γ`. -/
theorem lowerUnip_mem_iwahoriPrincipal {γ : Γ₀} {c : K} (hc : Valued.v c ≤ γ) (hγ : γ ≤ 1) :
    lowerUnip c ∈ iwahoriPrincipal K γ := by
  refine ⟨⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [coe_lowerUnip, Matrix.det_fin_two_of, hc, hc.trans hγ]

/-- **`x_α ∈ M(v(ϖ)^t)`.** -/
theorem coe_etaRep_mem_monoidM {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {α : K} (hα : Valued.v α ≤ 1) :
    (etaRep ϖ hϖ t α : Matrix (Fin 2) (Fin 2) K) ∈
      monoidM K (Valued.v ϖ ^ t) (pow_lt_one₀ zero_le hϖ1 (by omega)) := by
  have hαt : Valued.v (α * ϖ ^ t) ≤ Valued.v ϖ ^ t :=
    v_mul_le_left hα (map_pow Valued.v ϖ t).le
  have hpow : Valued.v ϖ ^ t ≤ 1 := pow_le_one₀ zero_le hϖ1.le
  rw [coe_etaRep]
  refine ⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · simpa using hϖ1.le
  · simp
  · simpa using hαt.trans hpow
  · simp
  · simpa using hαt
  · simp
  · simpa [Matrix.det_fin_two_of] using hϖ

end Eta

section Decomposition

variable {ι : Type*}

private theorem etaConj_mul (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) (u : GL (Fin 2) K) :
    (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 * (etaRep ϖ hϖ t α).1 =
      Matrix.diagonal ![ϖ, 1] * u.1 := by
  rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul, coe_etaGL]

private theorem etaConj_zero_one (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) (u : GL (Fin 2) K) :
    (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 0 1 = ϖ * u.1 0 1 := by
  have h := congrFun (congrFun (etaConj_mul ϖ hϖ t α u) 0) 1
  rw [coe_etaRep, mul_apply₂, Matrix.diagonal_mul] at h
  change (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 0 0 * 0 +
      (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 0 1 * 1 = ϖ * u.1 0 1 at h
  linear_combination h

private theorem etaConj_one_one (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) (u : GL (Fin 2) K) :
    (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 1 = u.1 1 1 := by
  have h := congrFun (congrFun (etaConj_mul ϖ hϖ t α u) 1) 1
  rw [coe_etaRep, mul_apply₂, Matrix.diagonal_mul] at h
  change (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 0 * 0 +
      (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 1 * 1 = 1 * u.1 1 1 at h
  linear_combination h

private theorem etaConj_zero_zero (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) (u : GL (Fin 2) K) :
    (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 0 0 = u.1 0 0 - u.1 0 1 * (α * ϖ ^ t) := by
  have h := congrFun (congrFun (etaConj_mul ϖ hϖ t α u) 0) 0
  rw [coe_etaRep, mul_apply₂, Matrix.diagonal_mul] at h
  change (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 0 0 * ϖ +
      (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 0 1 * (α * ϖ ^ t) = ϖ * u.1 0 0 at h
  apply mul_right_cancel₀ hϖ
  linear_combination h - (α * ϖ ^ t) * etaConj_zero_one ϖ hϖ t α u

private theorem etaConj_one_zero_mul (ϖ : K) (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) (u : GL (Fin 2) K) :
    (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 0 * ϖ = u.1 1 0 - u.1 1 1 * (α * ϖ ^ t) := by
  have h := congrFun (congrFun (etaConj_mul ϖ hϖ t α u) 1) 0
  rw [coe_etaRep, mul_apply₂, Matrix.diagonal_mul] at h
  change (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 0 * ϖ +
      (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 1 * (α * ϖ ^ t) = 1 * u.1 1 0 at h
  linear_combination h - (α * ϖ ^ t) * etaConj_one_one ϖ hϖ t α u

private theorem v_etaConj_one_zero {ϖ : K} (hϖ : ϖ ≠ 0) (t : ℕ) (α : K) {u : GL (Fin 2) K}
    (hd : Valued.v (u.1 1 1) = 1) :
    Valued.v ((etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 0) * Valued.v ϖ =
      Valued.v ϖ ^ t * Valued.v (u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - α) := by
  have hne : u.1 1 1 * ϖ ^ t ≠ 0 := mul_ne_zero (ne_zero_of_v_eq_one hd) (pow_ne_zero t hϖ)
  have e : u.1 1 0 - u.1 1 1 * (α * ϖ ^ t) =
      u.1 1 1 * ϖ ^ t * (u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - α) := by
    rw [mul_sub, mul_comm (u.1 1 0), mul_inv_cancel_left₀ hne]
    ring
  rw [← map_mul, etaConj_one_zero_mul, e, map_mul, map_mul, hd, one_mul, map_pow]

private theorem etaConj_mem_iwahori {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ}
    (ht : 1 ≤ t) {u : GL (Fin 2) K} (hu : u ∈ iwahori K (Valued.v ϖ ^ t)) {α : K}
    (hα : Valued.v α ≤ 1) (h : Valued.v (u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - α) ≤ Valued.v ϖ) :
    etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹ ∈ iwahori K (Valued.v ϖ ^ t) := by
  have hγ : Valued.v ϖ ^ t < 1 := pow_lt_one₀ zero_le hϖ1 (by omega)
  have hd := v_one_one_eq_one hγ hu
  have hv0 : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ
  have h10 : Valued.v ((etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 0) ≤ Valued.v ϖ ^ t := by
    have hmul : Valued.v ((etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1 1 0) * Valued.v ϖ ≤
        Valued.v ϖ ^ t * Valued.v ϖ := by
      rw [v_etaConj_one_zero hϖ t α hd]
      exact mul_le_mul' le_rfl h
    exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne zero_le (Ne.symm hv0))).mp hmul
  have hdet : (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1.det = u.1.det := by
    have hm := congrArg Matrix.det (etaConj_mul ϖ hϖ t α u)
    rw [Matrix.det_mul, Matrix.det_mul, det_etaRep, Matrix.det_diagonal, Fin.prod_univ_two] at hm
    change (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹).1.det * ϖ = ϖ * 1 * u.1.det at hm
    exact mul_right_cancel₀ hϖ (hm.trans (by ring))
  refine ⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_, h10⟩
  · rw [etaConj_zero_zero]
    exact v_sub_le (hu.1 0 0) (v_mul_le_left (hu.1 0 1)
      (v_mul_le_left hα ((map_pow Valued.v ϖ t).trans_le hγ.le)))
  · rw [etaConj_zero_one]
    exact v_mul_le_left hϖ1.le (hu.1 0 1)
  · exact h10.trans hγ.le
  · rw [etaConj_one_one]
    exact hu.1 1 1
  · rw [hdet]
    exact hu.2.1

private theorem v_sub_le_of_etaConj_mem {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ}
    (ht : 1 ≤ t) {u : GL (Fin 2) K} (hu : u ∈ iwahori K (Valued.v ϖ ^ t)) {α : K}
    (h : etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹ ∈ iwahori K (Valued.v ϖ ^ t)) :
    Valued.v (u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - α) ≤ Valued.v ϖ := by
  have hγ : Valued.v ϖ ^ t < 1 := pow_lt_one₀ zero_le hϖ1 (by omega)
  have hd := v_one_one_eq_one hγ hu
  have hpow0 : Valued.v ϖ ^ t ≠ 0 := pow_ne_zero t ((Valuation.ne_zero_iff _).mpr hϖ)
  have hmul : Valued.v ϖ ^ t * Valued.v (u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - α) ≤
      Valued.v ϖ ^ t * Valued.v ϖ := by
    rw [← v_etaConj_one_zero hϖ t α hd]
    exact mul_le_mul' h.2.2 le_rfl
  exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne zero_le (Ne.symm hpow0))).mp hmul

private theorem v_ratio_le_one {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {u : GL (Fin 2) K} (hu : u ∈ iwahori K (Valued.v ϖ ^ t)) :
    Valued.v (u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹) ≤ 1 := by
  have hd := v_one_one_eq_one (pow_lt_one₀ zero_le hϖ1 (by omega)) hu
  rw [map_mul, map_inv₀, map_mul, hd, one_mul, map_pow]
  calc Valued.v (u.1 1 0) * (Valued.v ϖ ^ t)⁻¹ ≤ Valued.v ϖ ^ t * (Valued.v ϖ ^ t)⁻¹ :=
        mul_le_mul' hu.2.2 le_rfl
    _ = 1 := mul_inv_cancel₀ (pow_ne_zero t ((Valuation.ne_zero_iff _).mpr hϖ))

/-- **The residue of a representative is integral**: once `η u x_α⁻¹ ∈ Iw(γ)` for `u ∈ Iw(γ)`, the
residue `α` is congruent to the integral element `c / (ϖ^t d)`. -/
theorem valued_le_one_of_etaConj_mem {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ}
    (ht : 1 ≤ t) {u : GL (Fin 2) K} (hu : u ∈ iwahori K (Valued.v ϖ ^ t)) {α : K}
    (h : etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹ ∈ iwahori K (Valued.v ϖ ^ t)) :
    Valued.v α ≤ 1 := by
  have e : α = u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - (u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - α) := by ring
  rw [e]
  exact v_sub_le (v_ratio_le_one hϖ hϖ1 ht hu)
    ((v_sub_le_of_etaConj_mem hϖ hϖ1 ht hu h).trans hϖ1.le)

/-- **The correction factor is principal**: for `u ∈ Iw(γ)`, once `u' = η u x_α⁻¹` lies in `Iw(γ)`
the quotient `u⁻¹ u'` lies in `Iw₁₁(γ)`, because `u'` and `u` have the same diagonal modulo `𝔞_γ`.
This is what transports the decomposition from `Iw(γ)` to every `Iw₁₁(γ) ≤ U ≤ Iw(γ)`, and from
`GL₂(F_v)` to `D_f^×`. -/
theorem inv_mul_etaGL_mul_mem_iwahoriPrincipal {ϖ : K} (hϖ : ϖ ≠ 0) {t : ℕ} {u : GL (Fin 2) K}
    (hu : u ∈ iwahori K (Valued.v ϖ ^ t)) {α : K} (hα : Valued.v α ≤ 1)
    (h : etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹ ∈ iwahori K (Valued.v ϖ ^ t)) :
    u⁻¹ * (etaGL ϖ hϖ * u * (etaRep ϖ hϖ t α)⁻¹) ∈ iwahoriPrincipal K (Valued.v ϖ ^ t) := by
  refine ⟨mul_mem (inv_mem hu) h, v_inv_mul_zero_zero_sub_one hu h ?_,
    v_inv_mul_one_one_sub_one hu h ?_⟩
  · rw [etaConj_zero_zero]
    have e : u.1 0 0 - u.1 0 1 * (α * ϖ ^ t) - u.1 0 0 = -(u.1 0 1 * (α * ϖ ^ t)) := by ring
    rw [e, Valuation.map_neg]
    exact v_mul_le_left (hu.1 0 1) (v_mul_le_left hα (map_pow Valued.v ϖ t).le)
  · rw [etaConj_one_one, sub_self, map_zero]
    exact zero_le

/-- **The right-coset decomposition `U η U = ∐_α U x_α`**: for every `u ∈ U` there is exactly one
residue `α` with `η u ∈ U x_α`, namely `α ≡ c / (ϖ^t d)`. -/
theorem existsUnique_etaRep {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : K, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ} (ht : 1 ≤ t)
    {U : Subgroup (GL (Fin 2) K)} (hlow : iwahoriPrincipal K (Valued.v ϖ ^ t) ≤ U)
    (hup : U ≤ iwahori K (Valued.v ϖ ^ t)) (r : ι → K)
    (hr : ∀ x : K, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1) {u : GL (Fin 2) K}
    (hu : u ∈ U) : ∃! i, etaGL ϖ hϖ * u * (etaRep ϖ hϖ t (r i))⁻¹ ∈ U := by
  have huI := hup hu
  have hx0 := v_ratio_le_one hϖ hϖ1 ht huI
  obtain ⟨i, hi, huniq⟩ := hr _ hx0
  refine ⟨i, ?_, fun j hj =>
    huniq j ((v_sub_le_of_etaConj_mem hϖ hϖ1 ht huI (hup hj)).trans_lt hϖ1)⟩
  have hαi : Valued.v (r i) ≤ 1 := by
    have e : r i = u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - (u.1 1 0 * (u.1 1 1 * ϖ ^ t)⁻¹ - r i) := by
      ring
    rw [e]
    exact v_sub_le hx0 hi.le
  have hmem := etaConj_mem_iwahori hϖ hϖ1 ht huI hαi (hunif _ hi)
  have hcorr := U.mul_mem hu (hlow (inv_mul_etaGL_mul_mem_iwahoriPrincipal hϖ huI hαi hmem))
  rwa [mul_inv_cancel_left] at hcorr

/-- The representatives `x_α` lie in `η U`. -/
theorem etaRep_mem_doubleCoset {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ}
    {U : Subgroup (GL (Fin 2) K)} (hlow : iwahoriPrincipal K (Valued.v ϖ ^ t) ≤ U) (r : ι → K)
    (hr : ∀ i, Valued.v (r i) ≤ 1) (i : ι) :
    etaRep ϖ hϖ t (r i) ∈ ({etaGL ϖ hϖ} : Set (GL (Fin 2) K)) * (U : Set (GL (Fin 2) K)) :=
  Set.mul_mem_mul rfl (hlow (lowerUnip_mem_iwahoriPrincipal
    (v_mul_le_left (hr i) (map_pow Valued.v ϖ t).le) (pow_le_one₀ zero_le hϖ1.le)))

/-- **The decomposition in bijective form**, as consumed by a Hecke operator: the classes of the
`x_α` are exactly the right cosets in `U η U`, without repetition. -/
theorem bijOn_etaRep {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : K, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ} (ht : 1 ≤ t)
    {U : Subgroup (GL (Fin 2) K)} (hlow : iwahoriPrincipal K (Valued.v ϖ ^ t) ≤ U)
    (hup : U ≤ iwahori K (Valued.v ϖ ^ t)) (r : ι → K) (hr1 : ∀ i, Valued.v (r i) ≤ 1)
    (hr : ∀ x : K, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1) :
    Set.BijOn (Quotient.mk'' : GL (Fin 2) K → Quotient (QuotientGroup.rightRel U))
      (Set.range fun i ↦ etaRep ϖ hϖ t (r i))
      ((Quotient.mk'' : GL (Fin 2) K → Quotient (QuotientGroup.rightRel U)) ''
        (({etaGL ϖ hϖ} : Set (GL (Fin 2) K)) * (U : Set (GL (Fin 2) K)))) := by
  have hmk : ∀ a b : GL (Fin 2) K,
      (Quotient.mk'' a : Quotient (QuotientGroup.rightRel U)) = Quotient.mk'' b ↔ b * a⁻¹ ∈ U :=
    fun _ _ => Quotient.eq''.trans QuotientGroup.rightRel_apply
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · obtain ⟨i, rfl⟩ := hx
    exact Set.mem_image_of_mem _ (etaRep_mem_doubleCoset hϖ hϖ1 hlow r hr1 i)
  · obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have hu : lowerUnip (r i * ϖ ^ t) ∈ U := hlow (lowerUnip_mem_iwahoriPrincipal
      (v_mul_le_left (hr1 i) (map_pow Valued.v ϖ t).le) (pow_le_one₀ zero_le hϖ1.le))
    obtain ⟨k, -, huniq⟩ := existsUnique_etaRep hϖ hϖ1 hunif ht hlow hup r hr hu
    have hi : etaGL ϖ hϖ * lowerUnip (r i * ϖ ^ t) * (etaRep ϖ hϖ t (r i))⁻¹ ∈ U := by
      rw [show etaGL ϖ hϖ * lowerUnip (r i * ϖ ^ t) = etaRep ϖ hϖ t (r i) from rfl,
        mul_inv_cancel]
      exact one_mem U
    have hj : etaGL ϖ hϖ * lowerUnip (r i * ϖ ^ t) * (etaRep ϖ hϖ t (r j))⁻¹ ∈ U := by
      rw [show etaGL ϖ hϖ * lowerUnip (r i * ϖ ^ t) = etaRep ϖ hϖ t (r i) from rfl]
      simpa using U.inv_mem ((hmk _ _).mp hxy)
    obtain rfl := (huniq i hi).trans (huniq j hj).symm
    rfl
  · obtain ⟨x, ⟨e, he, u, hu, rfl⟩, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at he
    subst he
    obtain ⟨i, hi, -⟩ := existsUnique_etaRep hϖ hϖ1 hunif ht hlow hup r hr hu
    exact ⟨etaRep ϖ hϖ t (r i), ⟨i, rfl⟩, (hmk _ _).mpr hi⟩

/-- Distinct residues give distinct representatives. -/
theorem etaRep_injective {ϖ : K} (hϖ : ϖ ≠ 0) (t : ℕ) (r : ι → K)
    (hr : Function.Injective r) : Function.Injective fun i ↦ etaRep ϖ hϖ t (r i) := by
  intro i j h
  have h10 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simp only [coe_etaRep, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at h10
  exact hr (mul_right_cancel₀ (pow_ne_zero t hϖ) h10)

private theorem upperConj_mul (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) (u : GL (Fin 2) K) :
    (upperRep ϖ hϖ β).1 * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 =
      u.1 * Matrix.diagonal ![ϖ, 1] := by
  rw [← Units.val_mul, mul_assoc, mul_inv_cancel_left, Units.val_mul, coe_etaGL]

private theorem upperConj_one_zero (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) (u : GL (Fin 2) K) :
    ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 1 0 = u.1 1 0 * ϖ := by
  have h := congrFun (congrFun (upperConj_mul ϖ hϖ β u) 1) 0
  rw [coe_upperRep, mul_apply₂, Matrix.mul_diagonal] at h
  change 0 * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 0 +
      1 * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 1 0 = u.1 1 0 * ϖ at h
  linear_combination h

private theorem upperConj_one_one (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) (u : GL (Fin 2) K) :
    ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 1 1 = u.1 1 1 := by
  have h := congrFun (congrFun (upperConj_mul ϖ hϖ β u) 1) 1
  rw [coe_upperRep, mul_apply₂, Matrix.mul_diagonal] at h
  change 0 * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 1 +
      1 * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 1 1 = u.1 1 1 * 1 at h
  linear_combination h

private theorem upperConj_zero_zero (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) (u : GL (Fin 2) K) :
    ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 0 = u.1 0 0 - β * u.1 1 0 := by
  have h := congrFun (congrFun (upperConj_mul ϖ hϖ β u) 0) 0
  rw [coe_upperRep, mul_apply₂, Matrix.mul_diagonal] at h
  change ϖ * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 0 +
      β * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 1 0 = u.1 0 0 * ϖ at h
  apply mul_left_cancel₀ hϖ
  linear_combination h - β * upperConj_one_zero ϖ hϖ β u

private theorem upperConj_zero_one_mul (ϖ : K) (hϖ : ϖ ≠ 0) (β : K) (u : GL (Fin 2) K) :
    ϖ * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 1 = u.1 0 1 - β * u.1 1 1 := by
  have h := congrFun (congrFun (upperConj_mul ϖ hϖ β u) 0) 1
  rw [coe_upperRep, mul_apply₂, Matrix.mul_diagonal] at h
  change ϖ * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 1 +
      β * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 1 1 = u.1 0 1 * 1 at h
  linear_combination h - β * upperConj_one_one ϖ hϖ β u

private theorem v_upperConj_zero_one {ϖ : K} (hϖ : ϖ ≠ 0) (β : K) {u : GL (Fin 2) K}
    (hd : Valued.v (u.1 1 1) = 1) :
    Valued.v ϖ * Valued.v (((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 1) =
      Valued.v (u.1 0 1 * (u.1 1 1)⁻¹ - β) := by
  have hd0 := ne_zero_of_v_eq_one hd
  have e : u.1 0 1 - β * u.1 1 1 = u.1 1 1 * (u.1 0 1 * (u.1 1 1)⁻¹ - β) := by
    rw [mul_sub, mul_comm (u.1 0 1), mul_inv_cancel_left₀ hd0]
    ring
  rw [← map_mul, upperConj_zero_one_mul, e, map_mul, hd, one_mul]

private theorem upperConj_mem_iwahori {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ}
    (ht : 1 ≤ t) {u : GL (Fin 2) K} (hu : u ∈ iwahori K (Valued.v ϖ ^ t)) {β : K}
    (hβ : Valued.v β ≤ 1) (h : Valued.v (u.1 0 1 * (u.1 1 1)⁻¹ - β) ≤ Valued.v ϖ) :
    (upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ ∈ iwahori K (Valued.v ϖ ^ t) := by
  have hγ : Valued.v ϖ ^ t < 1 := pow_lt_one₀ zero_le hϖ1 (by omega)
  have hd := v_one_one_eq_one hγ hu
  have hv0 : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ
  have h01 : Valued.v (((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 1) ≤ 1 := by
    have hmul : Valued.v ϖ * Valued.v (((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 1) ≤
        Valued.v ϖ * 1 := by
      rw [v_upperConj_zero_one hϖ β hd, mul_one]
      exact h
    exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne zero_le (Ne.symm hv0))).mp hmul
  have hdet : ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1.det = u.1.det := by
    have hm := congrArg Matrix.det (upperConj_mul ϖ hϖ β u)
    rw [Matrix.det_mul, Matrix.det_mul, det_upperRep, Matrix.det_diagonal,
      Fin.prod_univ_two] at hm
    change ϖ * ((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1.det = u.1.det * (ϖ * 1) at hm
    exact mul_left_cancel₀ hϖ (hm.trans (by ring))
  refine ⟨Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, h01⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · rw [upperConj_zero_zero]
    exact v_sub_le (hu.1 0 0) (v_mul_le_left hβ (hu.1 1 0))
  · rw [upperConj_one_zero]
    exact v_mul_le_left (hu.1 1 0) hϖ1.le
  · rw [upperConj_one_one]
    exact hu.1 1 1
  · rw [hdet]
    exact hu.2.1
  · rw [upperConj_one_zero]
    exact v_mul_le_right hu.2.2 hϖ1.le

private theorem v_sub_le_of_upperConj_mem {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1) {t : ℕ}
    (ht : 1 ≤ t) {u : GL (Fin 2) K} (hu : u ∈ iwahori K (Valued.v ϖ ^ t)) {β : K}
    (h : (upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ ∈ iwahori K (Valued.v ϖ ^ t)) :
    Valued.v (u.1 0 1 * (u.1 1 1)⁻¹ - β) ≤ Valued.v ϖ := by
  have hγ : Valued.v ϖ ^ t < 1 := pow_lt_one₀ zero_le hϖ1 (by omega)
  have hd := v_one_one_eq_one hγ hu
  rw [← v_upperConj_zero_one hϖ β hd]
  calc Valued.v ϖ * Valued.v (((upperRep ϖ hϖ β)⁻¹ * u * etaGL ϖ hϖ).1 0 1) ≤
        Valued.v ϖ * 1 := mul_le_mul' le_rfl (h.1 0 1)
    _ = Valued.v ϖ := mul_one _

/-- **The left-coset decomposition `U η U = ∐_β ((ϖ β), (0 1)) U`**: for every `u ∈ U` there is
exactly one residue `β` with `u η ∈ ((ϖ β), (0 1)) U`, namely `β ≡ b / d`. -/
theorem existsUnique_upperRep {ϖ : K} (hϖ : ϖ ≠ 0) (hϖ1 : Valued.v ϖ < 1)
    (hunif : ∀ x : K, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ) {t : ℕ} (ht : 1 ≤ t)
    {U : Subgroup (GL (Fin 2) K)} (hlow : iwahoriPrincipal K (Valued.v ϖ ^ t) ≤ U)
    (hup : U ≤ iwahori K (Valued.v ϖ ^ t)) (r : ι → K)
    (hr : ∀ x : K, Valued.v x ≤ 1 → ∃! i, Valued.v (x - r i) < 1) {u : GL (Fin 2) K}
    (hu : u ∈ U) : ∃! i, (upperRep ϖ hϖ (r i))⁻¹ * u * etaGL ϖ hϖ ∈ U := by
  have hγ : Valued.v ϖ ^ t < 1 := pow_lt_one₀ zero_le hϖ1 (by omega)
  have huI := hup hu
  have hd := v_one_one_eq_one hγ huI
  have hy0 : Valued.v (u.1 0 1 * (u.1 1 1)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, hd, inv_one, mul_one]
    exact huI.1 0 1
  obtain ⟨i, hi, huniq⟩ := hr _ hy0
  refine ⟨i, ?_, fun j hj =>
    huniq j ((v_sub_le_of_upperConj_mem hϖ hϖ1 ht huI (hup hj)).trans_lt hϖ1)⟩
  have hβi : Valued.v (r i) ≤ 1 := by
    have e : r i = u.1 0 1 * (u.1 1 1)⁻¹ - (u.1 0 1 * (u.1 1 1)⁻¹ - r i) := by ring
    rw [e]
    exact v_sub_le hy0 hi.le
  have hmem := upperConj_mem_iwahori hϖ hϖ1 ht huI hβi (hunif _ hi)
  have hcorr : u⁻¹ * ((upperRep ϖ hϖ (r i))⁻¹ * u * etaGL ϖ hϖ) ∈
      iwahoriPrincipal K (Valued.v ϖ ^ t) := by
    refine ⟨mul_mem (inv_mem huI) hmem, v_inv_mul_zero_zero_sub_one huI hmem ?_,
      v_inv_mul_one_one_sub_one huI hmem ?_⟩
    · rw [upperConj_zero_zero]
      have e : u.1 0 0 - r i * u.1 1 0 - u.1 0 0 = -(r i * u.1 1 0) := by ring
      rw [e, Valuation.map_neg]
      exact v_mul_le_left hβi huI.2.2
    · rw [upperConj_one_one, sub_self, map_zero]
      exact zero_le
  have hmemU := U.mul_mem hu (hlow hcorr)
  rwa [mul_inv_cancel_left] at hmemU

/-- Every element of `U η U` has determinant of valuation `v(ϖ)`. -/
theorem valued_det_of_mem_doubleCoset {ϖ : K} (hϖ : ϖ ≠ 0) {γ : Γ₀}
    {U : Subgroup (GL (Fin 2) K)} (hup : U ≤ iwahori K γ) {x : GL (Fin 2) K}
    (hx : x ∈ (U : Set (GL (Fin 2) K)) * ({etaGL ϖ hϖ} : Set (GL (Fin 2) K)) *
      (U : Set (GL (Fin 2) K))) :
    Valued.v (x : Matrix (Fin 2) (Fin 2) K).det = Valued.v ϖ := by
  obtain ⟨y, ⟨u₁, hu₁, e, he, rfl⟩, u₂, hu₂, rfl⟩ := hx
  rw [Set.mem_singleton_iff] at he
  subst he
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul,
    (hup hu₁).2.1, (hup hu₂).2.1, det_etaGL, one_mul, mul_one]

end Decomposition

section Norm

variable [hv : (Valued.v : Valuation K Γ₀).RankOne]

/-- **The norm form of `M_t`**: `‖c‖ ≤ ‖ϖ‖^t` and `‖d‖ = 1`, for the norm of the rank-one
valuation. -/
theorem mem_monoidM_iff_norm {ϖ : K} (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {g : Matrix (Fin 2) (Fin 2) K} :
    letI := Valued.toNormedField K Γ₀
    g ∈ monoidM K (Valued.v ϖ ^ t) (pow_lt_one₀ zero_le hϖ1 (by omega)) ↔
      (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ‖ϖ‖ ^ t ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0 := by
  letI := Valued.toNormedField K Γ₀
  rw [mem_monoidM_iff]
  refine and_congr (forall₂_congr fun i j => Valued.toNormedField.norm_le_one_iff.symm)
    (and_congr ?_ (and_congr ?_ Iff.rfl))
  · rw [← norm_pow, Valued.toNormedField.norm_le_iff, map_pow]
  · exact ⟨fun h => le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr h.le)
      (Valued.toNormedField.one_le_norm_iff.mpr h.ge),
      fun h => le_antisymm (Valued.toNormedField.norm_le_one_iff.mp h.le)
        (Valued.toNormedField.one_le_norm_iff.mp h.ge)⟩

end Norm

end LocalLevel
