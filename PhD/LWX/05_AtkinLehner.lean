/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«04_IntegralModel»
import PhD.TateFredholm.«01_CharpolyPairing»

/-!
# The Atkin–Lehner element, and the reduction of [LWX, Prop 3.22]

[LWX, Prop 3.22] states that the `U_p`-slopes on the classical space at nebentypus `ψ` and at `ψ⁻¹`
pair up to `k + 1`.  Its proof in [LWX, p. 24] applies Jacquet–Langlands and classifies the local
component as a principal series; both are out of reach here.  This file replaces that proof by a
**reduction**: everything except one operator identity is proved, and that identity is carried as an
explicit hypothesis.

See `.mathlib-quality/lwx-stepone/JL-AUDIT.md` for the per-result Jacquet–Langlands audit.

## The Atkin–Lehner element

`w = (0, 1; −p^m, 0)` has determinant `p^m`, normalises the Iwahori subgroup `Iw_{p^m}`, exchanges
the two diagonal entries (hence inverts the nebentypus), and conjugates `diag(1,p)` to `diag(p,1)`
(hence `U_p` to `U'_p`).  Conjugation is expressed by the inverse-free identity
`w * atkinLehnerConj γ = γ * w`, so no matrix inverses appear.

## What stays hypothetical

The operator identity `U_p ∘ U'_p = p^{k+1}` on the classical space.  Expected route: expanding the
product over coset representatives leaves, besides the central term, contributions that are traces
from level `p^{m−1}`, which vanish by character orthogonality exactly when the conductor is `p^m`
("`U_p` is invertible at ramified nebentypus").  **No source stating this in the quaternionic
setting has been found**, so per the `/develop` quote-or-delete rule it is not ticketed.

## Out of scope for this board

Instantiating the reduction at the genuine classical space `S^D_{k+2}(K^p Iw_{p^m};ψ)`.  That space
does not exist in Lean yet — it is built by the theta layer on the companion board — so the assembly
here is stated for abstract matrices, to be applied once that layer lands.

## Main declarations

* `LWX.atkinLehner`, `LWX.atkinLehnerConj` — the element and its conjugation action.
* `LWX.atkinLehner_mul_atkinLehnerConj` — `w * conj γ = γ * w`, the defining identity.
* `LWX.Iw`, `LWX.atkinLehnerConj_mem_Iw` — the Iwahori subgroup and its normalisation.
* `LWX.atkinLehnerConj_apply_one_one` — the diagonal swap (nebentypus inversion).
* `LWX.atkinLehnerConj_upElt` — `w⁻¹ diag(1,p) w = diag(p,1)`, i.e. `U_p ↦ U'_p`.
* `LWX.roots_charpoly_atkinLehner` — **the reduction**: [LWX, Prop 3.22] in multiset form, from
  the hypothesis.
-/

namespace LWX

open Matrix

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-! ### The Atkin–Lehner element -/

variable (p) in
/-- The Atkin–Lehner element `w = (0, 1; −p^m, 0)` at level `p^m`. -/
noncomputable def atkinLehner (m : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![0, 1; -(p : ℚ_[p]) ^ m, 0]

variable (p) in
/-- The Atkin–Lehner conjugate `w⁻¹ γ w = (d, −c/p^m; −b p^m, a)`, written without inverses. -/
noncomputable def atkinLehnerConj (m : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![γ 1 1, -(γ 1 0) / (p : ℚ_[p]) ^ m; -(γ 0 1) * (p : ℚ_[p]) ^ m, γ 0 0]

/-- `p ^ m` is nonzero in `ℚ_[p]`. -/
theorem pow_ne_zero_padic (m : ℕ) : ((p : ℚ_[p]) ^ m) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.pos.ne')

/-- `det w = p ^ m`. -/
@[simp]
theorem det_atkinLehner : (atkinLehner p m).det = (p : ℚ_[p]) ^ m := by
  simp [atkinLehner, Matrix.det_fin_two_of]

/-- **The defining conjugation identity** `w * conj γ = γ * w`.  Stated multiplicatively so that no
matrix inverse occurs. -/
theorem atkinLehner_mul_atkinLehnerConj (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    atkinLehner p m * atkinLehnerConj p m γ = γ * atkinLehner p m := by
  have hP := pow_ne_zero_padic (p := p) m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehner, atkinLehnerConj, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

/-- Conjugation preserves the determinant. -/
@[simp]
theorem det_atkinLehnerConj (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    (atkinLehnerConj p m γ).det = γ.det := by
  have hP := pow_ne_zero_padic (p := p) m
  rw [atkinLehnerConj, Matrix.det_fin_two_of, Matrix.det_fin_two]
  field_simp

/-! ### The diagonal swap: inversion of the nebentypus -/

/-- The `(0,0)` entry of the conjugate is the `(1,1)` entry of the original. -/
@[simp]
theorem atkinLehnerConj_apply_zero_zero (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    atkinLehnerConj p m γ 0 0 = γ 1 1 := by
  simp [atkinLehnerConj]

/-- The `(1,1)` entry of the conjugate is the `(0,0)` entry of the original: conjugation by `w`
**swaps the diagonal**, which is why it inverts the nebentypus. -/
@[simp]
theorem atkinLehnerConj_apply_one_one (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    atkinLehnerConj p m γ 1 1 = γ 0 0 := by
  simp [atkinLehnerConj]

/-- The exact form of "the nebentypus inverts": `a * d = det γ + b * c`, so modulo `p^m` (where
`p^m ∣ c` on the Iwahori) the two diagonal characters multiply to the central one. -/
theorem mul_diagonal_eq_det_add (γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    γ 0 0 * γ 1 1 = γ.det + γ 0 1 * γ 1 0 := by
  rw [Matrix.det_fin_two]
  ring

/-! ### Conjugation of the `U_p` element -/

variable (p) in
/-- The `U_p` element `η = diag(1, p)`. -/
noncomputable def upElt : Matrix (Fin 2) (Fin 2) ℚ_[p] := !![1, 0; 0, (p : ℚ_[p])]

variable (p) in
/-- The `U'_p` element `η' = diag(p, 1)`, the Atkin–Lehner conjugate of `η`. -/
noncomputable def upEltAdj : Matrix (Fin 2) (Fin 2) ℚ_[p] := !![(p : ℚ_[p]), 0; 0, 1]

/-- **`w⁻¹ diag(1,p) w = diag(p,1)`**: conjugation by the Atkin–Lehner element carries the `U_p`
element to the `U'_p` element.  This is what makes `U_p` and `U'_p` Atkin–Lehner conjugates. -/
theorem atkinLehnerConj_upElt : atkinLehnerConj p m (upElt p) = upEltAdj p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atkinLehnerConj, upElt, upEltAdj]

/-! ### The Iwahori subgroup and its normalisation -/

variable (p) in
/-- The Iwahori subgroup `Iw_{p^m}`: integral matrices with `p^m ∣ c` and unit determinant. -/
def Iw (m : ℕ) : Submonoid (Matrix (Fin 2) (Fin 2) ℚ_[p]) where
  carrier := {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ (p : ℝ)⁻¹ ^ m ∧ ‖g.det‖ = 1}
  mul_mem' := by
    rintro g k ⟨hg1, hg2, hg3⟩ ⟨hk1, hk2, hk3⟩
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
        · rw [norm_mul]
          exact mul_le_one₀ (hg1 _ _) (norm_nonneg _) (hk1 _ _)
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        calc ‖g 1 0‖ * ‖k 0 0‖ ≤ (p : ℝ)⁻¹ ^ m * 1 :=
              mul_le_mul hg2 (hk1 0 0) (norm_nonneg _) (by positivity)
          _ = (p : ℝ)⁻¹ ^ m := mul_one _
      · rw [norm_mul]
        calc ‖g 1 1‖ * ‖k 1 0‖ ≤ 1 * (p : ℝ)⁻¹ ^ m :=
              mul_le_mul (hg1 1 1) hk2 (norm_nonneg _) zero_le_one
          _ = (p : ℝ)⁻¹ ^ m := one_mul _
    · rw [Matrix.det_mul, norm_mul, hg3, hk3, one_mul]
  one_mem' := by
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), norm_zero]
      positivity
    · simp

theorem mem_Iw_iff {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} :
    g ∈ Iw p m ↔ (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ (p : ℝ)⁻¹ ^ m ∧ ‖g.det‖ = 1 :=
  Iff.rfl

/-- On the Iwahori subgroup both diagonal entries are units: `p ∣ c` forces `det ≡ a d`. -/
theorem norm_apply_zero_zero_of_mem_Iw {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hm : m ≠ 0)
    (hg : g ∈ Iw p m) : ‖g 0 0‖ = 1 := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hppos : (0 : ℝ) < (p : ℝ)⁻¹ ^ m := by positivity
  have hplt : ((p : ℝ))⁻¹ ^ m < 1 :=
    pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)) hm
  have hbc : ‖g 0 1 * g 1 0‖ < 1 := by
    rw [norm_mul]
    calc ‖g 0 1‖ * ‖g 1 0‖ ≤ 1 * (p : ℝ)⁻¹ ^ m :=
          mul_le_mul (h1 0 1) h2 (norm_nonneg _) zero_le_one
      _ < 1 := by rw [one_mul]; exact hplt
  have hmax : ‖g.det‖ ≤ max ‖g 0 0 * g 1 1‖ ‖g 0 1 * g 1 0‖ := by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    simpa using IsUltrametricDist.norm_add_le_max (g 0 0 * g 1 1) (-(g 0 1 * g 1 0))
  rw [h3] at hmax
  have hge : 1 ≤ ‖g 0 0‖ * ‖g 1 1‖ := by
    rw [← norm_mul]
    rcases max_cases ‖g 0 0 * g 1 1‖ ‖g 0 1 * g 1 0‖ with ⟨he, _⟩ | ⟨he, _⟩
    · rwa [he] at hmax
    · rw [he] at hmax; linarith
  have hd := h1 1 1
  have ha := h1 0 0
  nlinarith [norm_nonneg (g 0 0), norm_nonneg (g 1 1)]

/-- **`w` normalises `Iw_{p^m}`.**  Together with `atkinLehner_mul_atkinLehnerConj` this says
conjugation by `w` is an automorphism of the Iwahori subgroup. -/
theorem atkinLehnerConj_mem_Iw {g : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    (hg : g ∈ Iw p m) : atkinLehnerConj p m g ∈ Iw p m := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hppos : (0 : ℝ) < (p : ℝ)⁻¹ ^ m := by positivity
  have hpow1 : ((p : ℝ))⁻¹ ^ m ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
  have hP : ‖((p : ℚ_[p]) ^ m)‖ = (p : ℝ)⁻¹ ^ m := by rw [norm_pow, Padic.norm_p]
  have e01 : ‖atkinLehnerConj p m g 0 1‖ ≤ 1 := by
    have : atkinLehnerConj p m g 0 1 = -(g 1 0) / (p : ℚ_[p]) ^ m := by simp [atkinLehnerConj]
    rw [this, norm_div, norm_neg, hP, div_le_one hppos]
    exact h2
  have e10 : ‖atkinLehnerConj p m g 1 0‖ ≤ (p : ℝ)⁻¹ ^ m := by
    have : atkinLehnerConj p m g 1 0 = -(g 0 1) * (p : ℚ_[p]) ^ m := by simp [atkinLehnerConj]
    rw [this, norm_mul, norm_neg, hP]
    calc ‖g 0 1‖ * (p : ℝ)⁻¹ ^ m ≤ 1 * (p : ℝ)⁻¹ ^ m :=
          mul_le_mul_of_nonneg_right (h1 0 1) hppos.le
      _ = (p : ℝ)⁻¹ ^ m := one_mul _
  refine ⟨fun i j => ?_, e10, by rw [det_atkinLehnerConj]; exact h3⟩
  fin_cases i <;> fin_cases j
  · simpa [atkinLehnerConj] using h1 1 1
  · exact e01
  · exact e10.trans hpow1
  · simpa [atkinLehnerConj] using h1 0 0

/-! ### The reduction of [LWX, Prop 3.22] -/

section Reduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section CommRing

variable {R : Type*} [CommRing R]

/-- **The reduction, determinant form.**  If `A` is the matrix of `U_p` on the `ψ`-space, `A'` that
of `U_p` on the `ψ⁻¹`-space, and `A'` is conjugate to the matrix `B` of `U'_p` on the `ψ`-space
(which `atkinLehnerConj_upElt` and `atkinLehnerConj_mem_Iw` supply), then the hypothesis
`A * B = c • 1` gives `det A * det A' = c ^ n`.  With `c = p^{k+1}` this is the slope-sum
statement [LWX, Step I] consumes. -/
theorem det_mul_det_atkinLehner {A B A' P Q : Matrix ι ι R} {c : R}
    (hAB : A * B = c • (1 : Matrix ι ι R)) (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A.det * A'.det = c ^ Fintype.card ι := by
  have hQPdet : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
  subst hA'
  rw [Matrix.det_mul, Matrix.det_mul]
  calc A.det * (P.det * B.det * Q.det)
      = Q.det * P.det * (A.det * B.det) := by ring
    _ = A.det * B.det := by rw [hQPdet, one_mul]
    _ = c ^ Fintype.card ι := Matrix.det_mul_det_of_mul_eq_smul hAB

end CommRing

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- **The reduction, root form** — [LWX, Prop 3.22] granted the operator identity.  The
characteristic roots of `U_p` on the `ψ⁻¹`-space are those on the `ψ`-space inverted and scaled by
`c`; with `c = p^{k+1}` and `-log‖·‖` this is the slope symmetry
`α_i(ψ) = k + 1 − α_{n−1−i}(ψ⁻¹)` in multiset form. -/
theorem roots_charpoly_atkinLehner {A B A' P Q : Matrix ι ι K} {c : K} (hc : c ≠ 0)
    (hAB : A * B = c • (1 : Matrix ι ι K)) (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A'.charpoly.roots = A.charpoly.roots.map (fun x => c / x) := by
  rw [hA', Matrix.charpoly_conj P Q B hQP]
  exact Matrix.roots_charpoly_of_mul_eq_smul hc hAB

end AlgClosed

end Reduction

section Slopes

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [NormedField K] [IsAlgClosed K]

/-- **The reduction, slope form.**  Norms of the characteristic roots on the `ψ⁻¹`-space are `‖c‖`
divided by those on the `ψ`-space, with multiplicity.  Applying `-log` and `c = p^{k+1}` turns this
into `α(ψ⁻¹) = k + 1 − α(ψ)`, which is [LWX, Prop 3.22]. -/
theorem norm_roots_charpoly_atkinLehner {A B A' P Q : Matrix ι ι K} {c : K} (hc : c ≠ 0)
    (hAB : A * B = c • (1 : Matrix ι ι K)) (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A'.charpoly.roots.map (fun x => ‖x‖) = A.charpoly.roots.map (fun x => ‖c‖ / ‖x‖) := by
  rw [roots_charpoly_atkinLehner hc hAB hQP hA', Multiset.map_map]
  exact Multiset.map_congr rfl fun x _ => norm_div c x

end Slopes

end LWX
