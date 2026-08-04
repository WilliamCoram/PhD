/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Decomposition

/-!
# The matrix of a Hecke operator in the class-set basis

[Jacobs, *Slopes of Compact Hecke Operators*, Ch. 1 §1.6 pp. 20–21] computes the matrix of
`U_p = [UϖU]` with respect to the class-set decomposition `L(U, A) ≅ ⊕ᵢ A^{Γᵢ}`:

> "(Up φ)(cᵢ) = Σ_t (φ|vₜ)(cᵢ) … Next, we decompose cᵢv_t⁻¹ as d(i,t)c(i,t)u(i,t) with
> d(i,t) ∈ D, c(i,t) ∈ {c₀,c₁,c₂} and u(i,t) ∈ U.  Therefore, (Up φ)(cᵢ) =
> Σ_t φ(c(i,t))|κ(u(i,t)vₜ)_p."

This file proves the abstract form of that computation, for the monoid-action
`AutomorphicFunction` framework (left-action conventions; Jacobs's right-handed
`cᵢvₜ⁻¹ = d·c·u` becomes a factorisation of `cᵢ·wₜ`):
`heckeOperator_apply_rep` below.  It is the AG-B analogue of `bijective_evalAtReps` —
pure group-and-module bookkeeping, no quaternions.
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
    (φ : levelSubmodule (Γ := Γ) (A := A) R U hU)
    {T : Type*} [Fintype T] (w : T → G) (hwΔ : ∀ t, w t ∈ Δ)
    (hw : Set.BijOn QuotientGroup.mk (Set.range w)
      (QuotientGroup.mk '' ((U : Set G) * {η}) : Set (G ⧸ U)))
    (hwinj : Function.Injective w)
    (c : G) (c' : T → G) (d : T → G) (hd : ∀ t, d t ∈ Γ) (u : T → U)
    (hfact : ∀ t, c * w t = d t * c' t * (u t : G))
    (hact : ∀ t, w t * ((u t : G))⁻¹ ∈ Δ) :
    ((heckeOperator R hU hU hη h φ : levelSubmodule (Γ := Γ) (A := A) R U hU) :
        AutomorphicFunction G Γ A) c =
      ∑ t : T, (⟨w t * ((u t : G))⁻¹, hact t⟩ : Δ) • (φ : AutomorphicFunction G Γ A) (c' t) := by
  sorry

end AutomorphicFunction
