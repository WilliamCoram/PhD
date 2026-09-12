/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.Slash.«03_AutomorphicFunction»
import PhD.Main.QMF.Slash.«03_HeckeMonoid»
import Mathlib.Algebra.Module.Pi
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-!
# The matrix of a right-slash Hecke operator, and the class-set decomposition

Right-handed mirror of `PhD/Main/QMF/03_HeckeMatrix.lean` + `PhD/Main/QMF/02_Decomposition.lean`, in the
thesis's own shape [Jacobs, Ch. 1 §1.6 pp. 20–21]:

> "(Up φ)(cᵢ) = Σ_t (φ|vₜ)(cᵢ) … Next, we decompose cᵢv_t⁻¹ as d(i,t)c(i,t)u(i,t) with
> d(i,t) ∈ D, c(i,t) ∈ {c₀,c₁,c₂} and u(i,t) ∈ U.  Therefore, (Up φ)(cᵢ) =
> Σ_t φ(c(i,t))|κ(u(i,t)vₜ)_p."

With the right slash the display is stated *verbatim*: the double coset decomposes into
right cosets `U·vₜ`, the factorisations are of `c·vₜ⁻¹`, and the acting elements are the
thesis's `uₜ·vₜ` — no adjugate dictionary appears anywhere.

Also the right-handed class-set decomposition [Buzzard, *Eigenvarieties*, §9 p. 69]:
`f ↦ (f(τ_λ))_λ` identifies the slash-form `L(U,A)` with `∏_λ A^{Γ_λ,∣}`.
-/

open AbstractHeckeOperatorSlash RightSlashAction
open scoped Pointwise QMF

namespace AutomorphicFunction

variable {G : Type*} [Group G] {Γ : Subgroup G} {A : Type*} [AddCommMonoid A]
  {Δ' : Submonoid G} [RightSlashAction Δ' A]
  (R : Type*) [Semiring R] [Module R A] [SMulSlashClass R Δ' A]
  {U : Subgroup G} (hU : (U : Set G) ⊆ Δ')

/-- The transformation law for slash-fixed automorphic functions:
`φ(g·u) = φ(g) ∣ₛ u` — the right-handed counterpart of `apply_mul_coe`. -/
lemma slash_apply_mul {φ : AutomorphicFunction G Γ A}
    (hφ : φ ∈ slashFixedPointsOfLE (U := U) R (AutomorphicFunction G Γ A) hU)
    (u : U) (g : G) :
    φ (g * u) = φ g ∣ₛ (⟨u.1, hU u.2⟩ : Δ') := by
  have h := DFunLike.congr_fun (hφ u) (g * u)
  simpa [mul_inv_cancel_right] using h.symm

/-- **The matrix recipe, thesis form** [Jacobs, Ch. 1 §1.6 pp. 20–21].  Suppose the double
coset `U·η·U` decomposes into the right cosets `U·vₜ`, `t ∈ T` (finite), with each
`vₜ ∈ Δ'`, and suppose each `c·vₜ⁻¹` factors as `c·vₜ⁻¹ = dₜ · cₜ' · uₜ` with `dₜ ∈ Γ`,
`uₜ ∈ U`.  Then for `φ` in the slash-form `L(U, A)`,

  `([UηU]φ)(c) = ∑ₜ φ(cₜ') ∣ₛ (uₜ·vₜ)`

— the thesis's `Σ_t φ(c(i,t))|κ(u(i,t)vₜ)_p` verbatim. -/
theorem heckeOperatorSlash_apply_rep {η : G} (hη : η ∈ Δ')
    (h : (((Quotient.mk'' : G → RightCosets U) '' ({η} * (U : Set G))) :
      Set (RightCosets U)).Finite)
    (φ : slashFixedPointsOfLE (U := U) R (AutomorphicFunction G Γ A) hU)
    {T : Type*} [Fintype T] (vRep : T → G)
    (hvΔ : ∀ t, vRep t ∈ Δ')
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : G → RightCosets U) '' ({η} * (U : Set G))) :
        Set (RightCosets U)))
    (hvinj : Function.Injective vRep)
    (c : G) (c' : T → G) (d : T → G) (hd : ∀ t, d t ∈ Γ) (u : T → U)
    (hfact : ∀ t, c * (vRep t)⁻¹ = d t * c' t * (u t : G))
    (hact : ∀ t, (u t : G) * vRep t ∈ Δ') :
    ((heckeOperatorSlash R hU hU hη h φ :
        slashFixedPointsOfLE (U := U) R (AutomorphicFunction G Γ A) hU) :
        AutomorphicFunction G Γ A) c =
      ∑ t : T, ((φ : AutomorphicFunction G Γ A) (c' t)) ∣ₛ
        (⟨(u t : G) * vRep t, hact t⟩ : Δ') := by
  classical
  obtain ⟨s, hcoe, hmem⟩ : ∃ s : Finset G, (s : Set G) = Set.range vRep ∧
      ∀ t : T, vRep t ∈ s := ⟨Finset.image vRep Finset.univ, by simp, fun t => by simp⟩
  have hsΔ : (s : Set G) ⊆ Δ' := hcoe.subset.trans (Set.range_subset_iff.mpr hvΔ)
  have hsbij : Set.BijOn (Quotient.mk'' : G → RightCosets U) (s : Set G)
      (((Quotient.mk'' : G → RightCosets U) '' ({η} * (U : Set G))) :
        Set (RightCosets U)) := by rwa [hcoe]
  let ev : AutomorphicFunction G Γ A →+ A := ⟨⟨fun ψ => ψ c, rfl⟩, fun _ _ => rfl⟩
  have hev := congrArg ev (heckeOperatorSlash_eq_finsetSum R hU hU hη h φ s hsΔ hsbij)
  rw [map_sum] at hev
  refine hev.trans (Fintype.sum_bijective (fun t : T => (⟨vRep t, hmem t⟩ : {x // x ∈ s}))
    ⟨fun t₁ t₂ h12 => hvinj (congrArg Subtype.val h12), fun y => ?_⟩ _ _ fun t => ?_).symm
  · obtain ⟨t, ht⟩ : (y : G) ∈ Set.range vRep := hcoe.subset y.2
    exact ⟨t, Subtype.ext ht⟩
  · change ((φ : AutomorphicFunction G Γ A) (c' t)) ∣ₛ
        (⟨(u t : G) * vRep t, hact t⟩ : Δ')
      = (((φ : AutomorphicFunction G Γ A) ∣ₛ (⟨vRep t, hsΔ (hmem t)⟩ : Δ')) : _) c
    rw [slash_apply, hfact t, mul_assoc,
      (φ : AutomorphicFunction G Γ A).left_invt' (hd t),
      slash_apply_mul R hU φ.2 (u t) (c' t)]
    exact subtype_slash_mul ((φ : AutomorphicFunction G Γ A) (c' t))
      (hU (u t).2) (hsΔ (hmem t)) (hact t)

/-- Buzzard's `Γ_λ` at a representative `τ` (same subgroup as the left theory's
`stabilizerAt`): `{u ∈ U : τuτ⁻¹ ∈ Γ}`. -/
def stabilizerAtSlash (Γ U : Subgroup G) (τ : G) : Subgroup G :=
  U ⊓ Γ.comap (MulAut.conj τ).toMonoidHom

lemma mem_stabilizerAtSlash_iff {Γ U : Subgroup G} {τ u : G} :
    u ∈ stabilizerAtSlash Γ U τ ↔ u ∈ U ∧ τ * u * τ⁻¹ ∈ Γ := Iff.rfl

lemma stabilizerAtSlash_le (hU : (U : Set G) ⊆ Δ') (Γ : Subgroup G) (τ : G) :
    ((stabilizerAtSlash Γ U τ : Subgroup G) : Set G) ⊆ (Δ' : Set G) :=
  fun _ h => hU h.1

/-- Evaluation of a slash-form level-`U` automorphic function at a family of double-coset
representatives, valued in the slash-`Γ_λ`-invariants.  Right-handed mirror of
`AutomorphicFunction.evalAtReps`. -/
noncomputable def evalAtRepsSlash
    (σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G) :
    slashFixedPointsOfLE (U := U) R (AutomorphicFunction G Γ A) hU →ₗ[R]
      Π q : DoubleCoset.Quotient (Γ : Set G) (U : Set G),
        slashFixedPointsOfLE (U := stabilizerAtSlash Γ U (σ q)) R A
          (stabilizerAtSlash_le hU Γ (σ q)) where
  toFun φ q := ⟨(φ : AutomorphicFunction G Γ A) (σ q), by
    intro w
    obtain ⟨hw1, hw2⟩ := mem_stabilizerAtSlash_iff.mp w.2
    have harg : (φ : AutomorphicFunction G Γ A) (σ q * (w : G))
        = (φ : AutomorphicFunction G Γ A) (σ q) := by
      rw [show σ q * (w : G) = σ q * w * (σ q)⁻¹ * σ q from
        (inv_mul_cancel_right _ _).symm]
      exact (φ : AutomorphicFunction G Γ A).left_invt' hw2 (σ q)
    have hlaw := slash_apply_mul R hU φ.2 ⟨w.1, hw1⟩ (σ q)
    rw [harg] at hlaw
    exact hlaw.symm⟩
  map_add' φ ψ := funext fun q => Subtype.ext rfl
  map_smul' r φ := funext fun q => Subtype.ext rfl

/- Every `g` decomposes as `γ · σ ⟦g⟧ · u` with `γ ∈ Γ` and `u ∈ U`, for `σ` a section of
the double-coset projection. -/
private lemma exists_decomposition
    {σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G}
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q) :
    ∀ g : G, ∃ p : Γ × U, g = p.1 * σ (Quotient.mk'' g) * p.2 := fun g => by
  obtain ⟨γ, hγ, u, hu, hy⟩ :=
    DoubleCoset.rel_iff.mp (Quotient.eq''.mp (hσ (Quotient.mk'' g)))
  exact ⟨(⟨γ, hγ⟩, ⟨u, hu⟩), hy⟩

/- Well-definedness of the inverse of `evalAtRepsSlash`: the value built from a chosen
decomposition `p` agrees with the one read off any other decomposition `g = γ·σq·u`,
because `c q` is slash-`Γ_λ`-invariant. -/
private lemma slash_decomp_eq
    {σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G}
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q)
    (c : Π q : DoubleCoset.Quotient (Γ : Set G) (U : Set G),
      slashFixedPointsOfLE (U := stabilizerAtSlash Γ U (σ q)) R A
        (stabilizerAtSlash_le hU Γ (σ q)))
    (p : G → Γ × U) (hp : ∀ g, g = (p g).1 * σ (Quotient.mk'' g) * (p g).2)
    (q : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) (γ : Γ) (u : U) (g : G)
    (hg : g = γ.1 * σ q * u.1) :
    (c (Quotient.mk'' g)).1 ∣ₛ (⟨((p g).2).1, hU ((p g).2).2⟩ : Δ')
      = (c q).1 ∣ₛ (⟨u.1, hU u.2⟩ : Δ') := by
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
  have hwmem : (((p g).2 * u⁻¹ : U) : G) ∈ stabilizerAtSlash Γ U (σ q) :=
    mem_stabilizerAtSlash_iff.mpr
      ⟨((p g).2 * u⁻¹ : U).2, h2 ▸ Γ.mul_mem (Γ.inv_mem ((p g).1).2) γ.2⟩
  have hsplit : (((p g).2 : U) : G) = (((p g).2 * u⁻¹ : U) : G) * u := by
    push_cast
    group
  simp only [hsplit]
  rw [subtype_slash_mul ((c q).1) (hU ((p g).2 * u⁻¹ : U).2) (hU u.2),
    (c q).2 ⟨_, hwmem⟩]

/-- **Buzzard's decomposition, slash form** [*Eigenvarieties*, §9 p. 69]:
`f ↦ (f(τ_λ))_λ` is bijective onto `∏_λ A^{Γ_λ,∣}` when `σ` is a section of the
double-coset projection. -/
theorem bijective_evalAtRepsSlash
    (σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G)
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q) :
    Function.Bijective (evalAtRepsSlash R hU σ :
      slashFixedPointsOfLE (U := U) R (AutomorphicFunction G Γ A) hU →ₗ[R] _) := by
  constructor
  · intro φ ψ hφψ
    have h : ∀ q, (φ : AutomorphicFunction G Γ A) (σ q)
        = (ψ : AutomorphicFunction G Γ A) (σ q) :=
      fun q => congrArg Subtype.val (congrFun hφψ q)
    refine Subtype.ext (AutomorphicFunction.ext fun g => ?_)
    obtain ⟨⟨γ, u⟩, hy⟩ := exists_decomposition hσ g
    rw [hy, mul_assoc, (φ : AutomorphicFunction G Γ A).left_invt' γ.2,
      (ψ : AutomorphicFunction G Γ A).left_invt' γ.2,
      slash_apply_mul R hU φ.2 u, slash_apply_mul R hU ψ.2 u]
    exact congrArg (· ∣ₛ (⟨u.1, hU u.2⟩ : Δ')) (h _)
  · intro c
    choose p hp using exists_decomposition hσ
    refine ⟨⟨⟨fun g => (c (Quotient.mk'' g)).1 ∣ₛ (⟨((p g).2).1, hU ((p g).2).2⟩ : Δ'),
        fun γ₀ hγ₀ g => ?_⟩, ?_⟩, funext fun q => Subtype.ext ?_⟩
    · -- left `Γ`-invariance
      exact slash_decomp_eq R hU hσ c p hp (Quotient.mk'' g)
        ⟨γ₀ * ((p g).1).1, Γ.mul_mem hγ₀ ((p g).1).2⟩ (p g).2 (γ₀ * g)
        (by (conv_lhs => rw [hp g]); group)
    · -- slash level `U`-fixedness
      intro u₀
      refine AutomorphicFunction.ext fun g => ?_
      show ((c (Quotient.mk'' (g * ((u₀ : U) : G)⁻¹))).1
          ∣ₛ (⟨((p (g * ((u₀ : U) : G)⁻¹)).2).1, hU ((p (g * ((u₀ : U) : G)⁻¹)).2).2⟩ :
            Δ')) ∣ₛ (⟨(u₀ : U).1, hU u₀.2⟩ : Δ')
        = (c (Quotient.mk'' g)).1 ∣ₛ (⟨((p g).2).1, hU ((p g).2).2⟩ : Δ')
      rw [slash_decomp_eq R hU hσ c p hp (Quotient.mk'' g) (p g).1 ((p g).2 * u₀⁻¹)
          (g * ((u₀ : U) : G)⁻¹) (by (conv_lhs => rw [hp g]); push_cast; group),
        ← subtype_slash_mul ((c (Quotient.mk'' g)).1)
          (hU ((p g).2 * u₀⁻¹ : U).2) (hU u₀.2)]
      · congr 1
        refine Subtype.ext ?_
        push_cast
        group
      · exact Δ'.mul_mem (hU (SetLike.coe_mem _)) (hU u₀.2)
    · -- evaluation at the section
      show (c (Quotient.mk'' (σ q))).1
          ∣ₛ (⟨((p (σ q)).2).1, hU ((p (σ q)).2).2⟩ : Δ') = (c q).1
      rw [slash_decomp_eq R hU hσ c p hp q 1 1 (σ q) (by simp),
        show (⟨((1 : U)).1, hU ((1 : U)).2⟩ : Δ') = 1 from Subtype.ext (by simp),
        slash_one]

end AutomorphicFunction
