/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.«02_Decomposition»

/-!
# The matrix of a Hecke operator in the class-set basis

[Jacobs, *Slopes of Compact Hecke Operators*, Ch. 1 §1.6 pp. 20–21] computes the matrix of
`U_p = [UϖU]` with respect to the class-set decomposition `L(U, A) ≅ ⊕ᵢ A^{Γᵢ}`:

> "(Up φ)(cᵢ) = Σ_t (φ|vₜ)(cᵢ) … Next, we decompose cᵢv_t⁻¹ as d(i,t)c(i,t)u(i,t) with
> d(i,t) ∈ D, c(i,t) ∈ {c₀,c₁,c₂} and u(i,t) ∈ U.  Therefore, (Up φ)(cᵢ) =
> Σ_t φ(c(i,t))|κ(u(i,t)vₜ)_p."

This file proves the abstract form of that computation, for the monoid-action
`AutomorphicFunction` framework (left-action conventions; Jacobs's right-handed
`cᵢvₜ⁻¹ = d·c·u` becomes a factorisation of `cᵢ·wₜ`).  It is the AG-B analogue of
`bijective_evalAtReps` — pure group-and-module bookkeeping, no quaternions.

## Main results

* `AutomorphicFunction.heckeOperator_apply_rep`: the matrix recipe.  Given a left-coset
  decomposition `UηU = ⋃ₜ wₜU` and factorisations `c·wₜ = dₜ·cₜ'·uₜ` with `dₜ ∈ Γ` and
  `uₜ ∈ U`, the Hecke operator evaluates as `([UηU]φ)(c) = ∑ₜ ⟨wₜ·uₜ⁻¹⟩ • φ(cₜ')`.
-/

namespace AutomorphicFunction

open AbstractHeckeOperator
open scoped Pointwise

variable {G : Type*} [Group G] {Γ : Subgroup G} {A : Type*} [AddCommMonoid A]
  {Δ : Submonoid G} [DistribMulAction Δ A]
  (R : Type*) [Semiring R] [Module R A] [SMulCommClass Δ R A]
  {U : Subgroup G} (hU : (U : Set G) ⊆ Δ)

/-- **The matrix recipe** [Jacobs, Ch. 1 §1.6 pp. 20–21], abstract form.  Suppose the
double coset `U·η·U` decomposes into the left cosets `wₜ·U`, `t ∈ T` (finite), with each
`wₜ ∈ Δ`, and suppose each translate `c·wₜ` of a point `c : G` factors as
`c·wₜ = dₜ · cₜ' · uₜ` with `dₜ ∈ Γ`, `uₜ ∈ U`.  Then for `φ ∈ L(U, A)`,

  `([UηU]φ)(c) = ∑ₜ ⟨wₜ·uₜ⁻¹⟩ • φ(cₜ')`.

(The acting element `wₜ·uₜ⁻¹` is Jacobs's `(u(i,t)vₜ)_p` read through the left-action
dictionary.)  -/
theorem heckeOperator_apply_rep {η : G} (hη : η ∈ Δ)
    (h : (QuotientGroup.mk '' ((U : Set G) * {η}) : Set (G ⧸ U)).Finite)
    (φ : levelSubmodule (Γ := Γ) (A := A) R U hU) {T : Type*} [Fintype T] (w : T → G)
    (hwΔ : ∀ t, w t ∈ Δ) (hw : Set.BijOn QuotientGroup.mk (Set.range w)
      (QuotientGroup.mk '' ((U : Set G) * {η}) : Set (G ⧸ U))) (hwinj : Function.Injective w)
    (c : G) (c' : T → G) (d : T → G) (hd : ∀ t, d t ∈ Γ) (u : T → U)
    (hfact : ∀ t, c * w t = d t * c' t * (u t : G)) (hact : ∀ t, w t * ((u t : G))⁻¹ ∈ Δ) :
    ((heckeOperator R hU hU hη h φ : levelSubmodule (Γ := Γ) (A := A) R U hU) :
        AutomorphicFunction G Γ A) c =
      ∑ t : T, (⟨w t * ((u t : G))⁻¹, hact t⟩ : Δ) • (φ : AutomorphicFunction G Γ A) (c' t) := by
  classical
  obtain ⟨s, hcoe, hmem⟩ : ∃ s : Finset G, (s : Set G) = Set.range w ∧ ∀ t : T, w t ∈ s :=
    ⟨Finset.image w Finset.univ, by simp, fun t => by simp⟩
  have hsΔ : (s : Set G) ⊆ Δ := hcoe.subset.trans (Set.range_subset_iff.mpr hwΔ)
  have hsbij : Set.BijOn QuotientGroup.mk (s : Set G)
      (QuotientGroup.mk '' ((U : Set G) * {η}) : Set (G ⧸ U)) := by rwa [hcoe]
  let ev : AutomorphicFunction G Γ A →+ A := ⟨⟨fun ψ => ψ c, rfl⟩, fun _ _ => rfl⟩
  have hev := congrArg ev (heckeOperator_eq_finsetSum R hU hU hη h φ s hsΔ hsbij)
  rw [map_sum] at hev
  refine hev.trans (Fintype.sum_bijective (fun t : T => (⟨w t, hmem t⟩ : {x // x ∈ s}))
    ⟨fun t₁ t₂ h => hwinj (congrArg Subtype.val h), fun y => ?_⟩ _ _ fun t => ?_).symm
  · obtain ⟨t, ht⟩ : (y : G) ∈ Set.range w := hcoe.subset y.2
    exact ⟨t, Subtype.ext ht⟩
  · change (⟨w t * ((u t : G))⁻¹, hact t⟩ : Δ) • (φ : AutomorphicFunction G Γ A) (c' t)
      = (⟨w t, hsΔ (hmem t)⟩ : Δ) • (φ : AutomorphicFunction G Γ A) (c * w t)
    rw [hfact t, mul_assoc, (φ : AutomorphicFunction G Γ A).left_invt' (hd t),
      apply_mul_coe R hU φ.2 (u t) (c' t), ← mul_smul]
    rfl

end AutomorphicFunction
