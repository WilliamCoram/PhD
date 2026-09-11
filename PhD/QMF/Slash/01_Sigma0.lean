/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Sigma0
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The right-handed monoid `Σ₀'(γ)` and the adjugate dictionary

`Sigma0 K γ hγ` (see `PhD/QMF/Sigma0.lean`, incl. the design note on the left/right
convention seam) is the *left-handed* (Pollack–Stevens) monoid: `(0,0)`-entry a unit.
This file introduces its right-handed mirror `Sigma0' K γ hγ` — Buzzard's `Mₜ`
[*Eigenvarieties*, §9 p. 68: entries integral, `d` a unit, `π^t ∣ c`, nonzero
determinant] — together with the adjugate dictionary between the two:

* `Sigma0' K γ hγ` — the submonoid of `M₂(𝒪)` with `(1,1)`-entry a unit,
  `(1,0)`-entry of valuation `≤ γ`, nonzero determinant;
* `Sigma0'.adj : Sigma0' K γ hγ → Sigma0 K γ hγ` and `Sigma0.adj` in the reverse
  direction — both induced by `Matrix.adjugate` (`(a b; c d) ↦ (d −b; −c a)`), which
  swaps the two unit conditions while preserving the level entry (up to sign);
* the anti-homomorphism laws (`adj_mul`, via `Matrix.adjugate_mul_distrib`), the
  involutivity `adj_adj` (2×2: `adjugate (adjugate A) = A`), and `det_adj`;
* `Sigma0'.eta` — the thesis-form `η = (ϖ 0; 0 1)` [Jacobs `η₃ = (3 0; 0 1)`], with
  `adj_eta` identifying its adjugate with the library's `Sigma0.eta = (1 0; 0 ϖ)`.

This is the foundation of the right-slash dialect (`PhD/QMF/Slash/Basic.lean`): statements
in the classical/Buzzard/Jacobs right-handed convention are *stated* over `Σ₀'` and
*proved* by transport along `adj` to the left-handed library.
-/

open Valued

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀]

variable (K) in
/-- The right-handed monoid `Σ₀'(γ)`: `2×2` matrices over the valuation ring with
`(1,1)`-entry a unit, `(1,0)`-entry of valuation `≤ γ`, and nonzero determinant.
Buzzard's `Mₜ` [*Eigenvarieties*, §9 p. 68] on the nose; the adjugate image of
`Sigma0 K γ hγ`.  Requires `γ < 1` for closure under multiplication. -/
def Sigma0' (γ : Γ₀) (hγ : γ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) K) where
  carrier := {g | (∀ i j, v (g i j) ≤ 1) ∧ v (g 1 0) ≤ γ ∧ v (g 1 1) = 1 ∧ g.det ≠ 0}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨haInt, hac, had, hadet⟩ := ha
    obtain ⟨hbInt, hbc, hbd, hbdet⟩ := hb
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine le_trans (Valued.v.map_add _ _) (max_le ?_ ?_) <;>
        · rw [map_mul]; exact mul_le_one' (haInt _ _) (hbInt _ _)
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine le_trans (Valued.v.map_add _ _) (max_le ?_ ?_)
      · rw [map_mul]
        exact le_trans (mul_le_mul' hac (hbInt _ _)) (by rw [mul_one])
      · rw [map_mul]
        exact le_trans (mul_le_mul' (haInt _ _) hbc) (by rw [one_mul])
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      have h1 : v (a 1 1 * b 1 1) = 1 := by rw [map_mul, had, hbd, mul_one]
      have h2 : v (a 1 0 * b 0 1) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_mul' hac (hbInt _ _)) (by rwa [mul_one])
      rw [Valued.v.map_add_eq_of_lt_right (lt_of_lt_of_eq h2 h1.symm), h1]
    · rw [Matrix.det_mul]
      exact mul_ne_zero hadet hbdet
  one_mem' := by
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · rcases eq_or_ne i j with rfl | h
      · simp
      · simp [h]
    · simp
    · simp
    · simp

namespace Sigma0'

variable {γ : Γ₀} {hγ : γ < 1}

lemma mem_iff {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ Sigma0' K γ hγ ↔
      (∀ i j, v (g i j) ≤ 1) ∧ v (g 1 0) ≤ γ ∧ v (g 1 1) = 1 ∧ g.det ≠ 0 := Iff.rfl

lemma entry_le_one (g : Sigma0' K γ hγ) (i j : Fin 2) : v (g.1 i j) ≤ 1 := g.2.1 i j

lemma v_c_le (g : Sigma0' K γ hγ) : v (g.1 1 0) ≤ γ := g.2.2.1

lemma v_d_eq_one (g : Sigma0' K γ hγ) : v (g.1 1 1) = 1 := g.2.2.2.1

lemma det_ne_zero (g : Sigma0' K γ hγ) : g.1.det ≠ 0 := g.2.2.2.2

/-- The adjugate `(a b; c d) ↦ (d −b; −c a)` carries the right-handed monoid to the
left-handed one: the `d`-unit condition becomes the `a`-unit condition and the level
entry `c` is only negated. -/
def adj (g : Sigma0' K γ hγ) : Sigma0 K γ hγ :=
  ⟨g.1.adjugate, by
    obtain ⟨hInt, hc, hd, hdet⟩ := g.2
    have hadj : g.1.adjugate = !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0] :=
      Matrix.adjugate_fin_two _
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · rw [hadj]
      fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg] <;> exact hInt _ _
    · rw [hadj]
      simpa using hc
    · rw [hadj]
      simpa using hd
    · rw [Matrix.det_adjugate]
      simpa using hdet⟩

@[simp] lemma coe_adj (g : Sigma0' K γ hγ) : (adj g).1 = g.1.adjugate := rfl

/-- `adj` is an anti-homomorphism (from `Matrix.adjugate_mul_distrib`). -/
lemma adj_mul (g h : Sigma0' K γ hγ) : adj (g * h) = adj h * adj g :=
  Subtype.ext (by simp [Matrix.adjugate_mul_distrib])

@[simp] lemma adj_one : adj (1 : Sigma0' K γ hγ) = 1 :=
  Subtype.ext (by simp [Matrix.adjugate_one])

/-- The determinant is preserved by the dictionary (2×2: `det (adjugate A) = det A`). -/
lemma det_adj (g : Sigma0' K γ hγ) : (adj g).1.det = g.1.det := by
  simp [Matrix.det_adjugate]

variable (γ hγ) in
/-- The thesis-form element `η = (ϖ 0; 0 1)` implementing the `U_ϖ` direction
[Jacobs `η₃ = (3 0; 0 1)`, p. 20; Buzzard §9 p. 69].  Lies in `Σ₀'(γ)` for any
integral `ϖ ≠ 0`, and is not invertible in it. -/
def eta (ϖ : K) (hϖ : v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) : Sigma0' K γ hγ :=
  ⟨Matrix.of ![![ϖ, 0], ![0, 1]], by
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [hϖ]
    · simp
    · simp
    · simp [Matrix.det_fin_two, hϖ0]⟩

end Sigma0'

namespace Sigma0

variable {γ : Γ₀} {hγ : γ < 1}

/-- The reverse dictionary, `Σ₀(γ) → Σ₀'(γ)`, again induced by the adjugate. -/
def adj (g : Sigma0 K γ hγ) : Sigma0' K γ hγ :=
  ⟨g.1.adjugate, by
    obtain ⟨hInt, hc, ha, hdet⟩ := g.2
    have hadj : g.1.adjugate = !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0] :=
      Matrix.adjugate_fin_two _
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · rw [hadj]
      fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg] <;> exact hInt _ _
    · rw [hadj]
      simpa using hc
    · rw [hadj]
      simpa using ha
    · rw [Matrix.det_adjugate]
      simpa using hdet⟩

@[simp] lemma coe_adj (g : Sigma0 K γ hγ) : (adj g).1 = g.1.adjugate := rfl

lemma adj_mul (g h : Sigma0 K γ hγ) : adj (g * h) = adj h * adj g :=
  Subtype.ext (by simp [Matrix.adjugate_mul_distrib])

@[simp] lemma adj_one : adj (1 : Sigma0 K γ hγ) = 1 :=
  Subtype.ext (by simp [Matrix.adjugate_one])

lemma det_adj (g : Sigma0 K γ hγ) : (adj g).1.det = g.1.det := by
  simp [Matrix.det_adjugate]

/-- The two dictionaries are mutually inverse (`adjugate_adjugate` at `n = 2`). -/
@[simp] lemma adj_adj (g : Sigma0 K γ hγ) : Sigma0'.adj (adj g) = g :=
  Subtype.ext (by
    show (g.1.adjugate).adjugate = g.1
    rw [Matrix.adjugate_adjugate _ (by simp : Fintype.card (Fin 2) ≠ 1)]
    simp)

end Sigma0

namespace Sigma0'

variable {γ : Γ₀} {hγ : γ < 1}

@[simp] lemma adj_adj (g : Sigma0' K γ hγ) : Sigma0.adj (adj g) = g :=
  Subtype.ext (by
    show (g.1.adjugate).adjugate = g.1
    rw [Matrix.adjugate_adjugate _ (by simp : Fintype.card (Fin 2) ≠ 1)]
    simp)

/-- The thesis-form `η` and the library `η` correspond under the dictionary. -/
lemma adj_eta (ϖ : K) (hϖ : v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) :
    adj (eta γ hγ ϖ hϖ hϖ0) = Sigma0.eta γ hγ ϖ hϖ hϖ0 :=
  Subtype.ext (by
    show (Matrix.of ![![ϖ, 0], ![0, 1]] : Matrix (Fin 2) (Fin 2) K).adjugate = _
    ext i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [Sigma0.eta])

end Sigma0'
