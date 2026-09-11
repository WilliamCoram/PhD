/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.«00_HeckeMonoid»

/-!
# Abstract automorphic functions with monoid-twisted level action

The abstract shape of Buzzard's space `L(U, A)` [Buzzard, *Eigenvarieties*, §9 p. 69]:

> "Say `t ∈ ℤ^J_{≥1}`, `U` is a compact open of wild level `≥ πᵗ`, and `A` is any right
> `Mₜ`-module, with action written `(a, m) ↦ a.m`.  If `f : D^×_f → A` and `u ∈ U` then
> define `f|u : D^×_f → A` by `(f|u)(g) := f(gu⁻¹).uₚ`.  Now set
> `L(U, A) := {f : D^×\D^×_f → A : f|u = f for all u ∈ U}`."

We work with the left-handed formulation (Loeffler, *Overconvergent algebraic automorphic
forms*, Def. 3.3.2: functions `φ` with `φ(gu) = uₚ⁻¹ ∘ φ(g)`, where the coefficients carry a
*left* action of the monoid), which matches mathlib's action conventions and FLT's
weight-2 architecture (`WeightTwoAutomorphicForm`, `groupSMul`).

Abstractly: `G` a group, `Γ ≤ G` a subgroup (the "global points"), `Δ : Submonoid G` (the
elements whose `p`-component acts on the coefficients), `A` a `Δ`-module.

* `AutomorphicFunction G Γ A` — functions `φ : G → A` with `φ(γg) = φ(g)` for `γ ∈ Γ`.
  No smoothness or level condition is imposed; this keeps the definition topology-free.
* the `Δ`-action `(δ • φ)(g) = δ • φ(g·δ)` — the monoid-twisted right-translation action.
* `AutomorphicFunction.levelSubmodule` — Buzzard's `L(U, A)`: the `U`-fixed points, for
  `U ≤ G` a subgroup with `↑U ⊆ Δ` ("wild level" condition).
* `AutomorphicFunction.heckeOperator` — the Hecke operator `[UgV] : L(V,A) → L(U,A)`.

Weight 2 is the special case where `Δ` acts trivially on `A`; then `levelSubmodule`
is the space of functions on `Γ\G/U`, recovering FLT's weight-2 space of level `U`.
-/

open scoped Pointwise

/-- An `A`-valued automorphic function on `G` relative to a subgroup `Γ`: a function
`G → A` invariant under left translation by `Γ`.  No level or smoothness is imposed. -/
structure AutomorphicFunction (G : Type*) [Group G] (Γ : Subgroup G) (A : Type*) where
  /-- The underlying function `G → A`. -/
  toFun : G → A
  left_invt : ∀ γ ∈ Γ, ∀ g : G, toFun (γ * g) = toFun g

namespace AutomorphicFunction

variable {G : Type*} [Group G] {Γ : Subgroup G} {A : Type*}

instance : FunLike (AutomorphicFunction G Γ A) G A where
  coe := toFun
  coe_injective := by rintro ⟨f, _⟩ ⟨g, _⟩ h; simpa using h

@[ext]
lemma ext {φ ψ : AutomorphicFunction G Γ A} (h : ∀ g, φ g = ψ g) : φ = ψ :=
  DFunLike.ext φ ψ h

@[simp]
lemma coe_mk (f : G → A) (h : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g) :
    ((⟨f, h⟩ : AutomorphicFunction G Γ A) : G → A) = f := rfl

@[simp]
lemma left_invt' (φ : AutomorphicFunction G Γ A) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    φ (γ * g) = φ g := φ.left_invt γ hγ g

section AddCommMonoid

variable [AddCommMonoid A]

instance : Zero (AutomorphicFunction G Γ A) := ⟨⟨0, fun _ _ _ => rfl⟩⟩

@[simp] lemma zero_apply (g : G) : (0 : AutomorphicFunction G Γ A) g = 0 := rfl

instance : Add (AutomorphicFunction G Γ A) :=
  ⟨fun φ ψ => ⟨fun g => φ g + ψ g, fun γ hγ g => by
    rw [φ.left_invt' hγ, ψ.left_invt' hγ]⟩⟩

@[simp] lemma add_apply (φ ψ : AutomorphicFunction G Γ A) (g : G) :
    (φ + ψ) g = φ g + ψ g := rfl

instance : AddCommMonoid (AutomorphicFunction G Γ A) where
  add_assoc a b c := ext fun g => add_assoc _ _ _
  zero_add a := ext fun g => zero_add _
  add_zero a := ext fun g => add_zero _
  add_comm a b := ext fun g => add_comm _ _
  nsmul := nsmulRec

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup A]

instance : Neg (AutomorphicFunction G Γ A) :=
  ⟨fun φ => ⟨fun g => -φ g, fun γ hγ g => by rw [φ.left_invt' hγ]⟩⟩

@[simp] lemma neg_apply (φ : AutomorphicFunction G Γ A) (g : G) : (-φ) g = -φ g := rfl

instance : AddCommGroup (AutomorphicFunction G Γ A) where
  add_assoc _ _ _ := ext fun _ => add_assoc _ _ _
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _
  add_comm _ _ := ext fun _ => add_comm _ _
  neg_add_cancel _ := ext fun _ => neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec

end AddCommGroup

section AddCommMonoid

variable [AddCommMonoid A]

section Module

variable {R : Type*} [Semiring R] [Module R A]

instance : SMul R (AutomorphicFunction G Γ A) :=
  ⟨fun r φ => ⟨fun g => r • φ g, fun γ hγ g => by rw [φ.left_invt' hγ]⟩⟩

@[simp] lemma smul_apply (r : R) (φ : AutomorphicFunction G Γ A) (g : G) :
    (r • φ) g = r • φ g := rfl

instance : Module R (AutomorphicFunction G Γ A) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

end Module

section MonoidAction

variable {Δ : Submonoid G} [DistribMulAction Δ A]

/-- The monoid-twisted translation action of `Δ` on automorphic functions:
`(δ • φ)(g) = δ • φ(g·δ)`.  For trivial coefficients this is FLT's `groupSMul`;
in general it is the left-action form of Buzzard's `f|u` (loc. cit. §9 p. 69).

Convention note: the sources ([Buzzard, *Eigenvarieties*], [Jacobs]) write this as a
*right* action `(f∣u)(g) = f(gu⁻¹)∣κ u_p`, following the classical slash operator; the
left form here is obtained through the adjugate anti-isomorphism on the acting monoid,
which is also what turns Buzzard's `Mₜ` into Pollack–Stevens' `Σ₀(p)`.  The full rationale
— why left (mathlib's `Module`/`DistribMulAction` are left-handed), and why the adjugate
specifically (`g ↦ g⁻¹` is unavailable since `Σ₀` is a monoid, not a group; the transpose
moves the level condition to the wrong entry) — is in `PhD/QMF/00_Sigma0.lean`'s header. -/
instance : SMul Δ (AutomorphicFunction G Γ A) :=
  ⟨fun δ φ => ⟨fun g => δ • φ (g * δ), fun γ hγ g => by
    rw [mul_assoc, φ.left_invt' hγ]⟩⟩

@[simp] lemma monoid_smul_apply (δ : Δ) (φ : AutomorphicFunction G Γ A) (g : G) :
    (δ • φ) g = δ • φ (g * δ) := rfl

instance : DistribMulAction Δ (AutomorphicFunction G Γ A) where
  one_smul _ := ext fun _ => by simp
  mul_smul _ _ _ := ext fun _ => by simp [mul_smul, mul_assoc]
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

instance {R : Type*} [Semiring R] [Module R A] [SMulCommClass Δ R A] :
    SMulCommClass Δ R (AutomorphicFunction G Γ A) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

variable (R : Type*) [Semiring R] [Module R A] [SMulCommClass Δ R A]

/-- Buzzard's `L(U, A)` [*Eigenvarieties*, §9 p. 69]: automorphic functions fixed by a
subgroup `U` with `↑U ⊆ Δ` (the "wild level `≥ πᵗ`" condition), where `U` acts through
the monoid `Δ`. -/
def levelSubmodule (U : Subgroup G) (hU : (U : Set G) ⊆ Δ) :
    Submodule R (AutomorphicFunction G Γ A) :=
  AbstractHeckeOperator.fixedPointsOfLE R (AutomorphicFunction G Γ A) hU

/-- Membership in `levelSubmodule` as a pointwise transformation law:
`⟨u⟩ • φ(g·u) = φ(g)` for all `u ∈ U`. -/
lemma mem_levelSubmodule_iff {U : Subgroup G} (hU : (U : Set G) ⊆ Δ)
    {φ : AutomorphicFunction G Γ A} :
    φ ∈ levelSubmodule R U hU ↔
      ∀ u : U, ∀ g : G, (⟨u.1, hU u.2⟩ : Δ) • φ (g * u) = φ g := by
  constructor
  · intro h u g
    simpa using DFunLike.congr_fun (h u) g
  · intro h u
    exact ext fun g => by simpa using h u g

/-- The transformation law in Loeffler's form [Def. 3.3.2]: `φ(gu) = uₚ⁻¹ • φ(g)`. -/
lemma apply_mul_coe {U : Subgroup G} (hU : (U : Set G) ⊆ Δ)
    {φ : AutomorphicFunction G Γ A} (hφ : φ ∈ levelSubmodule R U hU) (u : U) (g : G) :
    φ (g * u) = (⟨(u⁻¹ : U).1, hU (u⁻¹ : U).2⟩ : Δ) • φ g := by
  have h := (mem_levelSubmodule_iff R hU).mp hφ u⁻¹ (g * u)
  simpa using h.symm

/-- The Hecke operator `[UgV] : L(V, A) → L(U, A)` for `g ∈ Δ`, given the finiteness of
the left-coset decomposition of `UgV`.  Source: Buzzard, *Eigenvarieties*, §9 p. 69
(`f|[UηU] := ∑ᵢ f|xᵢ`). -/
noncomputable def heckeOperator {U V : Subgroup G} (hU : (U : Set G) ⊆ Δ)
    (hV : (V : Set G) ⊆ Δ) {g : G} (hg : g ∈ Δ)
    (h : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)).Finite) :
    levelSubmodule (Γ := Γ) (A := A) R V hV →ₗ[R] levelSubmodule (Γ := Γ) (A := A) R U hU :=
  AbstractHeckeOperator.heckeOperator (A := AutomorphicFunction G Γ A) R hU hV hg h

end MonoidAction

end AddCommMonoid

end AutomorphicFunction
