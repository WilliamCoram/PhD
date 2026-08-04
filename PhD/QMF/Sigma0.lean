/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The local monoid `Σ₀(γ)` at a nonarchimedean place

Buzzard's monoid [*Eigenvarieties*, §9 p. 68]:

> "If `t ∈ ℤ^J_{≥1}` then define `Mₜ` to be the elements `(γⱼ)` of `M₂(𝒪ₚ)` with the
> property that if `γⱼ = (aⱼ bⱼ; cⱼ dⱼ)` then `det(γⱼ) ≠ 0`, `πⱼ^{tⱼ}` divides `cⱼ`, and
> `πⱼ` does not divide `dⱼ`.  Then `Mₜ` is a monoid under multiplication."

We use the *left-action* (Pollack–Stevens `Σ₀(p)`) convention: the unit condition is on the
`a`-entry rather than the `d`-entry, i.e.

  `Σ₀(γ) = { g ∈ M₂(𝒪) : v(g₀₀) = 1, v(g₁₀) ≤ γ, det g ≠ 0 }`

for a threshold `γ < 1` in the value group (Buzzard's `Mₜ` is `γ = v(π)^t`).

## Why the left convention, and why the adjugate (design note)

This is the one global convention choice of the development, so it is recorded in full.

**Both conventions are standard; they belong to neighbouring literatures.**  The classical
slash operator `f ∣_k γ` is a *right* action, essentially universally — Shimura,
Diamond–Shurman, Buzzard's *Eigenvarieties*, and Jacobs's thesis all use it, as does the
adelic phrasing `φ(dgu) = φ(g) ∣κ u_p` (left-invariant under the global group,
right-transforming under the level).  Meanwhile `Σ₀(p)` as a *left*-action monoid is the
established object of the overconvergent-modular-symbols literature (Pollack–Stevens,
Ash–Stevens).  So "canonical" depends on the subfield; neither choice is unusual.

**Why we take the left one.**  Mathlib's `Module` / `DistribMulAction` / `SMulCommClass`
are left-handed by default; a right module is an `Mᵐᵒᵖ`-module, which would put
`MulOpposite` into every statement and every instance search in the library.  FLT makes
the same choice for the same reason.

**Why the adjugate is the right dictionary — not an arbitrary pick.**  Passing between the
conventions needs an *anti*-automorphism of the acting object.  Two candidates fail:

* `g ↦ g⁻¹` does not exist here.  `Σ₀(γ)` is a monoid, **not** a group — the whole point of
  the `U_ϖ` direction is that `η = (1 0; 0 ϖ)` lies in `Σ₀` and is *not* invertible in it
  (`Sigma0.eta` below).  So group inversion is unavailable.
* the transpose is an anti-automorphism, but it sends the level condition `π^t ∣ c` to
  `π^t ∣ b` — the wrong congruence subgroup.

The adjugate `(a b; c d) ↦ (d −b; −c a)` swaps `a ↔ d` and negates the off-diagonal, so it
carries Buzzard's "`d` a unit, `π^t ∣ c`" to "`a` a unit, `π^t ∣ c`" — which is *exactly*
Pollack–Stevens' `Σ₀(p)`.  It is the anti-automorphism that preserves the level structure,
which is why it, and not another, is the standard bridge.

**Consequence to watch.**  `adj g * g = det g`, so the adjugate carries a determinant
twist; weight actions transported across it pick up `det^v`-type scalars.  Any scalar
mismatch surfacing downstream against a transcribed generating function is this twist, and
is to be handled as an explicit statement amendment rather than a proof-side patch (see
the AG-B board's L4.3 note, `.mathlib-quality/qmf/decomposition.md`).

We work over an arbitrary `Valued` field so that the definition applies uniformly to
`v.adicCompletion F` (value group `ℤₘ₀`) and to any other local situation.
-/

open Valued

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀]

variable (K) in
/-- The monoid `Σ₀(γ)` of `2×2` matrices over the valuation ring with `(0,0)`-entry a unit,
`(1,0)`-entry of valuation `≤ γ`, and nonzero determinant.  Requires `γ < 1` for closure
under multiplication.  Left-handed version of Buzzard's `Mₜ` [*Eigenvarieties*, §9 p. 68]. -/
def Sigma0 (γ : Γ₀) (hγ : γ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) K) where
  carrier := {g | (∀ i j, v (g i j) ≤ 1) ∧ v (g 1 0) ≤ γ ∧ v (g 0 0) = 1 ∧ g.det ≠ 0}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨haInt, hac, haa, had⟩ := ha
    obtain ⟨hbInt, hbc, hba, hbd⟩ := hb
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
      have h1 : v (a 0 0 * b 0 0) = 1 := by rw [map_mul, haa, hba, mul_one]
      have h2 : v (a 0 1 * b 1 0) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_mul' (haInt _ _) hbc) (by rwa [one_mul])
      rw [Valued.v.map_add_eq_of_lt_left (lt_of_lt_of_eq h2 h1.symm), h1]
    · rw [Matrix.det_mul]
      exact mul_ne_zero had hbd
  one_mem' := by
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · rcases eq_or_ne i j with rfl | h
      · simp
      · simp [h]
    · simp
    · simp
    · simp

namespace Sigma0

variable {γ : Γ₀} {hγ : γ < 1}

lemma mem_iff {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ Sigma0 K γ hγ ↔
      (∀ i j, v (g i j) ≤ 1) ∧ v (g 1 0) ≤ γ ∧ v (g 0 0) = 1 ∧ g.det ≠ 0 := Iff.rfl

lemma entry_le_one (g : Sigma0 K γ hγ) (i j : Fin 2) : v (g.1 i j) ≤ 1 := g.2.1 i j

lemma v_c_le (g : Sigma0 K γ hγ) : v (g.1 1 0) ≤ γ := g.2.2.1

lemma v_a_eq_one (g : Sigma0 K γ hγ) : v (g.1 0 0) = 1 := g.2.2.2.1

lemma det_ne_zero (g : Sigma0 K γ hγ) : g.1.det ≠ 0 := g.2.2.2.2

variable (γ hγ) in
/-- The determinant as a monoid homomorphism `Σ₀(γ) →* Kˣ` (the determinant of an
element of `Σ₀` is nonzero, hence a unit of the field `K`). -/
noncomputable def detUnits : Sigma0 K γ hγ →* Kˣ where
  toFun g := Units.mk0 g.1.det (det_ne_zero g)
  map_one' := by simp
  map_mul' g h := by simp [Matrix.det_mul]

variable (γ hγ) in
/-- The element `η = (1 0; 0 ϖ)` implementing the `U_ϖ` (Atkin–Lehner) direction: it lies
in `Σ₀(γ)` for any integral `ϖ ≠ 0`, but is not invertible in it.
(In Buzzard's right-handed convention this is `(π 0; 0 1)`, loc. cit. §9 p. 69.) -/
def eta (ϖ : K) (hϖ : v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) : Sigma0 K γ hγ :=
  ⟨Matrix.of ![![1, 0], ![0, ϖ]], by
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [hϖ]
    · simp
    · simp
    · simp [Matrix.det_fin_two, hϖ0]⟩

end Sigma0
