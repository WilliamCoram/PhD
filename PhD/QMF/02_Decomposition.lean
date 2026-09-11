/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.AutomorphicFunction
import Mathlib.Algebra.Module.Pi
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-!
# Decomposition of `L(U, A)` over the class set

Buzzard, *Eigenvarieties*, §9 p. 69:

> "Say `D^×_f = ∐_{λ=1}^{μ} D^× τ_λ U`.  Then the groups `Γ_λ := τ_λ⁻¹ D^× τ_λ ∩ U` …
> Note that `f ∈ L(U,A)` is determined by `f(τ_λ)` for `1 ≤ λ ≤ μ`, and one checks easily
> that the map `f ↦ (f(τ_λ))_{1≤λ≤μ}` induces an isomorphism `L(U,A) → ⊕_{λ=1}^{μ} A^{Γ_λ}`."

We state this for a section `σ` of the double-coset projection (mirroring FLT's
`LevelStruct.formEquivOfSection`).  No finiteness of the class set is needed for the
bijection itself; finiteness (Fujisaki — `NumberField.FiniteAdeleRing.DivisionAlgebra.
finiteDoubleCoset` in FLT, `FLT/DivisionAlgebra/Finiteness.lean`) upgrades the product
to a finite direct sum in the quaternionic instantiation.

For trivial coefficients the invariants disappear and `L(U, A) ≃ (Γ\G/U → A)`,
recovering the weight-2 description underlying FLT's `WeightTwoAutomorphicForm`.
-/

namespace AutomorphicFunction

open AbstractHeckeOperator

variable {G : Type*} [Group G] {Γ : Subgroup G} {A : Type*} [AddCommMonoid A]
  {Δ : Submonoid G} [DistribMulAction Δ A]
  (R : Type*) [Semiring R] [Module R A] [SMulCommClass Δ R A]
  {U : Subgroup G} (hU : (U : Set G) ⊆ Δ)

/-- Buzzard's `Γ_λ` at a representative `τ`: the subgroup `{u ∈ U : τuτ⁻¹ ∈ Γ}`,
i.e. `τ⁻¹Γτ ∩ U` [*Eigenvarieties*, §9 p. 68]. -/
def stabilizerAt (Γ U : Subgroup G) (τ : G) : Subgroup G :=
  U ⊓ Γ.comap (MulAut.conj τ).toMonoidHom

lemma mem_stabilizerAt_iff {Γ U : Subgroup G} {τ u : G} :
    u ∈ stabilizerAt Γ U τ ↔ u ∈ U ∧ τ * u * τ⁻¹ ∈ Γ := Iff.rfl

lemma stabilizerAt_le (hU : (U : Set G) ⊆ Δ) (Γ : Subgroup G) (τ : G) :
    ((stabilizerAt Γ U τ : Subgroup G) : Set G) ⊆ (Δ : Set G) := fun _ h => hU h.1

/-- Evaluation of a level-`U` automorphic function at a family of double-coset
representatives, valued in the `Γ_λ`-invariants. -/
noncomputable def evalAtReps (σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G) :
    levelSubmodule (Γ := Γ) (A := A) R U hU →ₗ[R]
      Π q : DoubleCoset.Quotient (Γ : Set G) (U : Set G),
        fixedPointsOfLE (V := stabilizerAt Γ U (σ q)) R A (stabilizerAt_le hU Γ (σ q)) where
  toFun φ q := ⟨φ.1 (σ q), fun u => by
    obtain ⟨hu1, hu2⟩ := mem_stabilizerAt_iff.mp u.2
    have harg : φ.1 (σ q * (u : G)) = φ.1 (σ q) := by
      rw [show σ q * (u : G) = σ q * u * (σ q)⁻¹ * σ q from (inv_mul_cancel_right _ _).symm]
      exact φ.1.left_invt' hu2 (σ q)
    exact harg ▸ (mem_levelSubmodule_iff R hU).mp φ.2 ⟨u.1, hu1⟩ (σ q)⟩
  map_add' φ ψ := funext fun q => Subtype.ext rfl
  map_smul' r φ := funext fun q => Subtype.ext rfl

/- Every `g` decomposes as `γ · σ ⟦g⟧ · u` with `γ ∈ Γ` and `u ∈ U`, for `σ` a section of
the double-coset projection. -/
private lemma exists_decomposition {σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G}
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q) :
    ∀ g : G, ∃ p : Γ × U, g = p.1 * σ (Quotient.mk'' g) * p.2 := fun g => by
  obtain ⟨γ, hγ, u, hu, hy⟩ :=
    DoubleCoset.rel_iff.mp (Quotient.eq''.mp (hσ (Quotient.mk'' g)))
  exact ⟨(⟨γ, hγ⟩, ⟨u, hu⟩), hy⟩

/- Well-definedness of the inverse of `evalAtReps`: the value built from a chosen
decomposition `p` agrees with the one read off any other decomposition `g = γ · σ q · u`,
because `c q` is `Γ_λ`-invariant. -/
private lemma smul_decomp_eq {σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G}
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q)
    (c : Π q : DoubleCoset.Quotient (Γ : Set G) (U : Set G),
      fixedPointsOfLE (V := stabilizerAt Γ U (σ q)) R A (stabilizerAt_le hU Γ (σ q)))
    (p : G → Γ × U) (hp : ∀ g, g = (p g).1 * σ (Quotient.mk'' g) * (p g).2)
    (q : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) (γ : Γ) (u : U) (g : G)
    (hg : g = γ.1 * σ q * u.1) :
    (⟨((p g).2⁻¹).1, hU ((p g).2⁻¹).2⟩ : Δ) • (c (Quotient.mk'' g)).1
      = (⟨(u⁻¹).1, hU (u⁻¹).2⟩ : Δ) • (c q).1 := by
  have hq : (Quotient.mk'' g : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q := by
    rw [hg]
    exact (Quotient.eq''.mpr
      (DoubleCoset.rel_iff.mpr ⟨γ.1, γ.2, u.1, u.2, rfl⟩)).symm.trans (hσ q)
  have hpg := hp g
  rw [hq] at hpg ⊢
  have hgg := hpg.symm.trans hg
  have h2 : σ q * (((p g).2 * u⁻¹ : U) : G) * (σ q)⁻¹ = (((p g).1 : G))⁻¹ * γ.1 := by
    push_cast
    rw [show (γ : G) = (p g).1 * σ q * (p g).2 * ((u : G))⁻¹ * (σ q)⁻¹ by rw [hgg]; group]
    group
  have hwmem : (((p g).2 * u⁻¹ : U) : G) ∈ stabilizerAt Γ U (σ q) :=
    mem_stabilizerAt_iff.mpr
      ⟨((p g).2 * u⁻¹ : U).2, h2 ▸ Γ.mul_mem (Γ.inv_mem ((p g).1).2) γ.2⟩
  have hfix := (c q).2 ⟨_, hwmem⟩
  conv_lhs => rw [← hfix]
  rw [← mul_smul]
  congr 1
  refine Subtype.ext ?_
  push_cast
  group

/-- `f ↦ (f(τ_λ))_λ` is bijective onto `∏_λ A^{Γ_λ}` when `σ` is a section of the
double-coset projection.  [Buzzard, *Eigenvarieties*, §9 p. 69.]  The inverse is
constructed as in FLT's `LevelStruct.formEquivOfSection`. -/
theorem bijective_evalAtReps (σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G)
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q) :
    Function.Bijective (evalAtReps (A := A) R hU σ) := by
  constructor
  · intro φ ψ hφψ
    have h : ∀ q, φ.1 (σ q) = ψ.1 (σ q) := fun q => congrArg Subtype.val (congrFun hφψ q)
    refine Subtype.ext (AutomorphicFunction.ext fun g => ?_)
    obtain ⟨⟨γ, u⟩, hy⟩ := exists_decomposition hσ g
    rw [hy, mul_assoc, φ.1.left_invt' γ.2, ψ.1.left_invt' γ.2,
      apply_mul_coe R hU φ.2 u, apply_mul_coe R hU ψ.2 u]
    exact congrArg _ (h _)
  · intro c
    choose p hp using exists_decomposition hσ
    refine ⟨⟨⟨fun g => (⟨((p g).2⁻¹).1, hU ((p g).2⁻¹).2⟩ : Δ) • (c (Quotient.mk'' g)).1,
        fun γ₀ hγ₀ g => ?_⟩, ?_⟩, funext fun q => Subtype.ext ?_⟩
    · -- left `Γ`-invariance
      exact smul_decomp_eq R hU hσ c p hp (Quotient.mk'' g)
        ⟨γ₀ * ((p g).1).1, Γ.mul_mem hγ₀ ((p g).1).2⟩ (p g).2 (γ₀ * g)
        (by (conv_lhs => rw [hp g]); group)
    · -- level `U`-fixedness
      rw [mem_levelSubmodule_iff]
      intro u₀ g
      simp only [coe_mk]
      rw [smul_decomp_eq R hU hσ c p hp (Quotient.mk'' g) (p g).1 ((p g).2 * u₀) (g * u₀)
          (by (conv_lhs => rw [hp g]); push_cast; group), ← mul_smul]
      congr 1
      refine Subtype.ext ?_
      push_cast
      group
    · -- evaluation at the section
      show (⟨((p (σ q)).2⁻¹).1, hU ((p (σ q)).2⁻¹).2⟩ : Δ) • (c (Quotient.mk'' (σ q))).1
        = (c q).1
      rw [smul_decomp_eq R hU hσ c p hp q 1 1 (σ q) (by simp),
        show (⟨(((1 : U))⁻¹).1, hU (((1 : U))⁻¹).2⟩ : Δ) = 1 from Subtype.ext (by simp),
        one_smul]

/-- Weight-2 degeneration: if `Δ` acts trivially on `A`, level-`U` automorphic functions
are exactly the `A`-valued functions on the class set `Γ\G/U`.  This is the bridge to
FLT's `WeightTwoAutomorphicForm` (level-`U`, trivial central character aside). -/
theorem bijective_eval_of_trivial_smul (htriv : ∀ (δ : Δ) (a : A), δ • a = a)
    (σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G)
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q) :
    Function.Bijective
      (fun (φ : levelSubmodule (Γ := Γ) (A := A) R U hU)
          (q : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) => φ.1 (σ q)) := by
  have h2 : Function.Bijective
      (fun (c : ∀ q : DoubleCoset.Quotient (Γ : Set G) (U : Set G),
          ↥(fixedPointsOfLE (V := stabilizerAt Γ U (σ q)) R A (stabilizerAt_le hU Γ (σ q))))
        (q : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) => (c q).1) :=
    ⟨fun c d hcd => funext fun q => Subtype.ext (congrFun hcd q),
      fun f => ⟨fun q => ⟨f q, fun _ => htriv _ _⟩, rfl⟩⟩
  exact h2.comp (bijective_evalAtReps (A := A) R hU σ hσ)

end AutomorphicFunction
