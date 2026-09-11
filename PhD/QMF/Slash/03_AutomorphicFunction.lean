/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.AutomorphicFunction
import PhD.QMF.Slash.Basic

/-!
# The right slash on automorphic functions, and slash-form level spaces

Buzzard's action on `A`-valued functions [*Eigenvarieties*, §9 p. 69]:

> "If `f : D^×_f → A` and `u ∈ U` then define `f|u : D^×_f → A` by
> `(f|u)(g) := f(gu⁻¹).uₚ`."

Abstractly (`G` a group, `Γ ≤ G`, `Δ' : Submonoid G` the elements whose relevant
component acts on the coefficients on the right): for a coefficient
`RightSlashAction Δ' A` we set `(φ ∣ₛ δ)(g) := φ(g·δ⁻¹) ∣ₛ δ` — the inverse is taken
in the ambient group `G`, so no invertibility in `Δ'` is needed.  This is the literal
Buzzard/Jacobs formula; the library's left action `(δ • φ)(g) = δ • φ(g·δ)`
(`PhD/QMF/AutomorphicFunction.lean`) is its adjugate shadow.

* `AutomorphicFunction` gains a `RightSlashAction Δ'` instance;
* `levelSubmoduleSlash` — Buzzard's `L(U, A) = {f : f∣u = f for u ∈ U}` verbatim;
* `mem_levelSubmoduleSlash_iff'` — the transformation-law form `φ(gu) = φ(g) ∣ₛ u`;
* `levelSubmoduleSlash_eq_levelSubmodule` — **the seam theorem**: under the pointwise
  compatibility hypothesis `hcompat` between the coefficient slash and the coefficient
  left action on `U`-elements, the slash-form level space *equals* the library's
  `levelSubmodule`.  The hypothesis is discharged per-instantiation (for the Jacobs
  κ-modules this is the `adjParams`-vs-`params` computation; any central-character
  residue there is a recorded statement amendment on the instantiation side, never a
  change to this file).
-/

open scoped QMF

namespace AutomorphicFunction

variable {G : Type*} [Group G] {Γ : Subgroup G} {A : Type*} [AddCommMonoid A]
  {Δ' : Submonoid G} [RightSlashAction Δ' A]

/-- Buzzard's right slash on automorphic functions:
`(φ ∣ₛ δ)(g) = φ(g·δ⁻¹) ∣ₛ δ` [*Eigenvarieties*, §9 p. 69, `(f|u)(g) := f(gu⁻¹).uₚ`].
The inverse `δ⁻¹` is formed in the ambient group `G`. -/
noncomputable instance : RightSlashAction Δ' (AutomorphicFunction G Γ A) where
  slash φ δ := ⟨fun g => φ (g * (δ : G)⁻¹) ∣ₛ δ, fun γ' hγ' g => by
    rw [mul_assoc, φ.left_invt' hγ']⟩
  zero_slash δ := ext fun g => by simp
  slash_one φ := ext fun g => by simp
  slash_mul φ δ₁ δ₂ := ext fun g => by
    simp [mul_inv_rev, mul_assoc, RightSlashAction.slash_mul]
  add_slash φ ψ δ := ext fun g => by simp

@[simp]
lemma slash_apply (δ : Δ') (φ : AutomorphicFunction G Γ A) (g : G) :
    (φ ∣ₛ δ) g = φ (g * (δ : G)⁻¹) ∣ₛ δ := rfl

section Level

variable (R : Type*) [Semiring R] [Module R A]
  [RightSlashAction.SMulSlashClass R Δ' A]

/-- The slash on automorphic functions commutes with the scalars whenever the
coefficient slash does (mirror of the library's `SMulCommClass` instance,
`AutomorphicFunction.lean:162`). -/
instance : RightSlashAction.SMulSlashClass R Δ' (AutomorphicFunction G Γ A) where
  smul_slash r φ δ := ext fun g => by
    simp [RightSlashAction.SMulSlashClass.smul_slash]

/-- Buzzard's `L(U, A)` in its original right-handed form [*Eigenvarieties*, §9
p. 69]: automorphic functions with `φ ∣ₛ u = φ` for all `u ∈ U`, for a subgroup
`U ≤ G` with `↑U ⊆ Δ'`. -/
noncomputable def levelSubmoduleSlash (U : Subgroup G) (hU : (U : Set G) ⊆ Δ') :
    Submodule R (AutomorphicFunction G Γ A) where
  carrier := {φ | ∀ u : U, φ ∣ₛ (⟨u.1, hU u.2⟩ : Δ') = φ}
  add_mem' ha hb u := by rw [RightSlashAction.add_slash, ha u, hb u]
  zero_mem' u := RightSlashAction.zero_slash _
  smul_mem' r φ hφ u := by
    rw [RightSlashAction.SMulSlashClass.smul_slash, hφ u]

lemma mem_levelSubmoduleSlash_iff {U : Subgroup G} (hU : (U : Set G) ⊆ Δ')
    {φ : AutomorphicFunction G Γ A} :
    φ ∈ levelSubmoduleSlash R U hU ↔
      ∀ u : U, φ ∣ₛ (⟨u.1, hU u.2⟩ : Δ') = φ := Iff.rfl

/-- The slash-form level condition as a transformation law:
`φ(g·u) = φ(g) ∣ₛ u` — Buzzard's right-handed counterpart of the library's
`apply_mul_coe` (Loeffler Def. 3.3.2). -/
lemma mem_levelSubmoduleSlash_iff' {U : Subgroup G} (hU : (U : Set G) ⊆ Δ')
    {φ : AutomorphicFunction G Γ A} :
    φ ∈ levelSubmoduleSlash R U hU ↔
      ∀ u : U, ∀ g : G, φ (g * u) = φ g ∣ₛ (⟨u.1, hU u.2⟩ : Δ') := by
  constructor
  · intro h u g
    have := DFunLike.congr_fun (h u) (g * u)
    simpa [mul_assoc] using this.symm
  · intro h u
    refine ext fun g => ?_
    have := (h u (g * (u : G)⁻¹)).symm
    simpa [inv_mul_cancel_right] using this

variable {Δ : Submonoid G} [DistribMulAction Δ A] [SMulCommClass Δ R A]

/-- **The seam theorem.**  If on `U`-elements the coefficient slash agrees with the
coefficient left action of the inverse — `a ∣ₛ u = u⁻¹ • a` — then Buzzard's
right-handed `L(U, A)` and the library's left-handed `levelSubmodule` are the *same*
submodule.  The hypothesis is exactly the pointwise dictionary between the two
conventions on the level group, and is discharged (or amended by an explicit central
character) per coefficient instantiation. -/
lemma levelSubmoduleSlash_eq_levelSubmodule {U : Subgroup G}
    (hU' : (U : Set G) ⊆ Δ') (hU : (U : Set G) ⊆ Δ)
    (hcompat : ∀ u : U, ∀ a : A,
      a ∣ₛ (⟨u.1, hU' u.2⟩ : Δ') = (⟨(u⁻¹ : U).1, hU (u⁻¹ : U).2⟩ : Δ) • a) :
    levelSubmoduleSlash R U hU' = levelSubmodule (Γ := Γ) (A := A) R U hU := by
  ext φ
  rw [mem_levelSubmoduleSlash_iff' R hU', mem_levelSubmodule_iff R hU]
  constructor
  · intro h u g
    rw [h u g, hcompat u, ← mul_smul,
      show (⟨u.1, hU u.2⟩ : Δ) * ⟨(u⁻¹ : U).1, hU (u⁻¹ : U).2⟩ = 1 from
        Subtype.ext (by simp), one_smul]
  · intro h u g
    rw [hcompat u, ← h u g, ← mul_smul,
      show (⟨(u⁻¹ : U).1, hU (u⁻¹ : U).2⟩ : Δ) * ⟨u.1, hU u.2⟩ = 1 from
        Subtype.ext (by simp), one_smul]

end Level

end AutomorphicFunction
