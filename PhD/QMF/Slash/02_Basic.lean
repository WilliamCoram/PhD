/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Slash.«01_Sigma0»
import Mathlib.Algebra.Group.Action.Defs

/-!
# The right-slash action class

The classical slash operator `f ∣ γ` of the modular-forms literature is a *right*
monoid action by additive maps.  Mathlib's `SlashAction β G α`
(`Mathlib/NumberTheory/ModularForms/SlashActions.lean`) has exactly this shape but
indexes a family of actions by a weight type `β` on a fixed carrier `α`; in this
project the weight parametrises the *carrier* (`WeightModule R n ν`, the κ-modules),
so we use a weight-free variant with the same axiom names.

`RightSlashAction Δ A` is the statement-level *dialect* of the left-handed theory:
instances are constructed from existing left `DistribMulAction`s (via
`RightSlashAction.ofAntiHom`, transport along an anti-homomorphism such as
`Sigma0'.adj`) or directly from a literature formula (the `WeightModule` instance in
`PhD/QMF/Slash/03_WeightModule.lean` uses Buzzard's own formula).  Proof obligations are
always discharged through the left-handed library; no right-handed theory is
developed on top of this class.
-/

/-- A right action of a monoid `Δ` on an additive monoid `A` by additive maps,
written `a ∣ₛ δ` — the abstract shape of the classical slash operator.  Axiom names
follow mathlib's `SlashAction`. -/
class RightSlashAction (Δ : Type*) (A : Type*) [Monoid Δ] [AddMonoid A] where
  /-- The slash action `a ∣ₛ δ`. -/
  slash : A → Δ → A
  zero_slash : ∀ δ : Δ, slash 0 δ = 0
  slash_one : ∀ a : A, slash a 1 = a
  /-- Right-action law: `a ∣ₛ (δ₁·δ₂) = (a ∣ₛ δ₁) ∣ₛ δ₂`. -/
  slash_mul : ∀ (a : A) (δ₁ δ₂ : Δ), slash a (δ₁ * δ₂) = slash (slash a δ₁) δ₂
  add_slash : ∀ (a b : A) (δ : Δ), slash (a + b) δ = slash a δ + slash b δ

@[inherit_doc] scoped[QMF] notation:73 a:73 " ∣ₛ " δ:74 => RightSlashAction.slash a δ

namespace RightSlashAction

attribute [simp] zero_slash slash_one add_slash

open scoped QMF

variable {Δ' Δ A : Type*}


/-- Transport of a left action along an anti-homomorphism `τ : Δ' → Δ`:
`a ∣ₛ δ := τ δ • a`.  This is the generic dictionary construction — e.g. `τ = Sigma0'.adj`
turns the left `Σ₀`-action of the library into a right `Σ₀'`-slash.  A definition, not
an instance: each concrete carrier chooses its own instance (some, like `WeightModule`,
use a direct literature formula instead and prove agreement with the transport). -/
@[instance_reducible]
def ofAntiHom [Monoid Δ'] [Monoid Δ] [AddMonoid A] [DistribMulAction Δ A]
    (τ : Δ' → Δ) (hone : τ 1 = 1) (hmul : ∀ x y, τ (x * y) = τ y * τ x) :
    RightSlashAction Δ' A where
  slash a δ := τ δ • a
  zero_slash _ := smul_zero _
  slash_one a := by rw [hone, one_smul]
  slash_mul a δ₁ δ₂ := by rw [hmul, mul_smul]
  add_slash a b δ := smul_add _ a b

/-- The slash by a fixed `δ` as an additive monoid homomorphism (packaging
`zero_slash` and `add_slash`; used to push the slash through finite sums). -/
def slashAddHom [Monoid Δ] [AddMonoid A] [RightSlashAction Δ A] (δ : Δ) : A →+ A where
  toFun a := a ∣ₛ δ
  map_zero' := zero_slash δ
  map_add' a b := add_slash a b δ

@[simp] lemma slashAddHom_apply [Monoid Δ] [AddMonoid A] [RightSlashAction Δ A]
    (δ : Δ) (a : A) : slashAddHom δ a = a ∣ₛ δ := rfl

/-- Compatibility mixin: the slash commutes with the scalars `R` (the analogue of
`SMulCommClass` for the left theory; needed for slash-defined submodules). -/
class SMulSlashClass (R : Type*) (Δ : Type*) (A : Type*) [Monoid Δ] [AddMonoid A]
    [SMul R A] [RightSlashAction Δ A] : Prop where
  smul_slash : ∀ (r : R) (a : A) (δ : Δ), (r • a) ∣ₛ δ = r • (a ∣ₛ δ)

attribute [simp] SMulSlashClass.smul_slash

end RightSlashAction
