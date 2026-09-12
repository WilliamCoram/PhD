/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.«02_Decomposition»
import PhD.Main.QMF.«01_WeightModule»
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Quaternionic modular forms of general weight

The instantiation of the abstract theory (`PhD.Main.QMF.«01_AutomorphicFunction»`) for a quaternion
algebra `D` over a number field `F`, following [Buzzard, *Eigenvarieties*, §9]:

> "Now let `D` be a quaternion algebra over `F` ramified at all infinite places.  Let us
> assume that `D` is split at all places above `p`. …
> **Definition.** The space of classical automorphic forms `S^D_{k,w}(U)` of weight `(k,w)`
> and level `U` for `D` is the space `L(U, L_{n,v})`."  (§9 pp. 67–70)

FLT-style mock-up: the definitions below typecheck for any `F`-algebra `D` equipped with a
rigidification at the chosen place `v` (`RigidificationAt`); they are the mathematically
intended objects only when `F` is totally real, `D` is a totally definite quaternion
algebra split at `v`, and `v ∣ p`.  Those hypotheses are only ever assumed on theorems
that need them, mirroring FLT's `WeightTwoAutomorphicForm` design.

* `QMF.Dfx F D` — the unit group `(D ⊗[F] 𝔸_F^∞)ˣ`.
* `QMF.globalUnits F D` — the image of `Dˣ` (the left-invariance subgroup `Γ`).
* `QMF.levelMonoid` — `Δ = {g : gᵥ ∈ Σ₀(γ)}`, Buzzard's "wild level" monoid.
* `QMF.Space` — the space of quaternionic modular forms of weight `(n, ν)` and level `U`.

Finiteness input (used downstream, not here): the class set `Dˣ\(D ⊗ 𝔸_F^∞)ˣ/U` is finite —
Fujisaki's lemma, formalised in FLT as
`NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`
(`FLT/DivisionAlgebra/Finiteness.lean`, Buzzard–Coram); to be ported into
`PhD/Main/QMF/FLTstuff/`.
-/

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

namespace QMF

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [Ring D] [Algebra F D]
-- If `F` is not totally real or `D` is not a totally definite quaternion algebra then the
-- definitions below are mathematically meaningless, but they typecheck.  (FLT convention.)

/-- `Dfx` is the unit group `(D ⊗[F] 𝔸_F^∞)ˣ` of the finite-adelic quaternion algebra. -/
abbrev Dfx := (D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F)ˣ

/-- The inclusion `Dˣ →* (D ⊗[F] 𝔸_F^∞)ˣ`. -/
noncomputable def unitsIncl : Dˣ →* Dfx F D :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := D)).toMonoidHom

/-- The left-invariance subgroup `Γ`: the image of `Dˣ` in `(D ⊗[F] 𝔸_F^∞)ˣ`. -/
noncomputable def globalUnits : Subgroup (Dfx F D) := (unitsIncl F D).range

variable (v : HeightOneSpectrum (RingOfIntegers F))

/-- Evaluation of a finite adele at the place `v`, as an `F`-algebra homomorphism. -/
noncomputable def evalAlgHom :
    FiniteAdeleRing (RingOfIntegers F) F →ₐ[F] v.adicCompletion F where
  toRingHom := RestrictedProduct.evalRingHom _ v
  commutes' _ := rfl

/-- The component of `D ⊗[F] 𝔸_F^∞` at the place `v`. -/
noncomputable def toLocal : (D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) →ₐ[F]
    (D ⊗[F] v.adicCompletion F) :=
  Algebra.TensorProduct.map (AlgHom.id F D) (evalAlgHom F v)

/-- A rigidification of `D` at the place `v`: an identification
`D ⊗[F] F_v ≅ M₂(F_v)`.  This is the "fixed isomorphism" of [Buzzard, *Eigenvarieties*,
§9 pp. 67–68], and exists iff `D` is split at `v`.  Local-at-`v` analogue of FLT's global
`WithRigidification`. -/
class RigidificationAt : Type _ where
  /-- The fixed isomorphism `D ⊗[F] F_v ≅ M₂(F_v)`. -/
  equiv : (D ⊗[F] v.adicCompletion F) ≃ₐ[F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F)

variable [RigidificationAt F D v]

/-- The `v`-component of an adelic unit as a `2×2` matrix over `F_v` (composite of
`toLocal`, the rigidification, and the coercion of units into the matrix monoid). -/
noncomputable def toMatrix : Dfx F D →* Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  (Units.coeHom _).comp <| Units.map <|
    ((RigidificationAt.equiv (F := F) (D := D) (v := v)).toAlgHom.comp (toLocal F D v)).toMonoidHom

variable (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1)

/-- Buzzard's wild-level monoid `Δ`: adelic units whose `v`-component lies in `Σ₀(γ)`
[*Eigenvarieties*, §9 p. 68: "we say that a compact open subgroup `U ⊂ D^×_f` has wild
level `≥ πᵗ` if the projection `U → D^×_p` is contained within `Mₜ`"]. -/
noncomputable def levelMonoid : Submonoid (Dfx F D) :=
  (Sigma0 (v.adicCompletion F) γ hγ).comap (toMatrix F D v)

/-- The corestriction `Δ →* Σ₀(γ)` of the `v`-component map. -/
noncomputable def levelMonoidToSigma0 :
    levelMonoid F D v γ hγ →* Sigma0 (v.adicCompletion F) γ hγ where
  toFun g := ⟨toMatrix F D v g.1, g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

variable {R : Type*} [CommRing R] [Algebra (v.adicCompletion F) R]
-- The weight is the pair `(n, ν)`: `n` is the polynomial degree (`Symⁿ`) and `ν` is a
-- character of `Σ₀(γ)` — a scalar twist, `ν = detChar w` in Buzzard's classical case.
-- The p-adic weights deforming `n` (locally analytic κ) live in `PhD/Main/QMF/Weight/`.
variable (n : ℕ) (ν : Sigma0 (v.adicCompletion F) γ hγ →* Rˣ)

/-- The wild-level monoid acts on the weight module through its `v`-component. -/
noncomputable instance : DistribMulAction (levelMonoid F D v γ hγ) (WeightModule R n ν) :=
  DistribMulAction.compHom _ (levelMonoidToSigma0 F D v γ hγ)

instance : SMulCommClass (levelMonoid F D v γ hγ) R (WeightModule R n ν) where
  smul_comm δ r P := smul_comm (levelMonoidToSigma0 F D v γ hγ δ) r P

/-- The space of quaternionic modular forms of weight `(n, ν)` and level `U`, for `U` a
subgroup of wild level `≥ γ` (i.e. `↑U ⊆ Δ`):  Buzzard's `S^D_{k,w}(U) = L(U, L_{n,v})`
[*Eigenvarieties*, §9 p. 70], in the left-handed one-place formulation.
For `n = 0`, `ν = 1` (and level prime to `v`) this is the weight-2 space of FLT. -/
noncomputable def Space (U : Subgroup (Dfx F D)) (hU : (U : Set (Dfx F D)) ⊆ levelMonoid F D v γ hγ) :
    Submodule R (AutomorphicFunction (Dfx F D) (globalUnits F D) (WeightModule R n ν)) :=
  AutomorphicFunction.levelSubmodule R U hU

/-- The Hecke operator `[UηU]` on quaternionic modular forms, for `η` of wild level `≥ γ`.
[Buzzard, *Eigenvarieties*, §9 p. 69.]  The standard `U_ϖ` operator is the case where the
`v`-component of `η` is `Sigma0.eta`. -/
noncomputable def heckeOperator (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid F D v γ hγ) {η : Dfx F D}
    (hη : η ∈ levelMonoid F D v γ hγ)
    (h : (QuotientGroup.mk '' ((U : Set (Dfx F D)) * {η}) : Set (Dfx F D ⧸ U)).Finite) :
    Space F D v γ hγ n ν U hU →ₗ[R] Space F D v γ hγ n ν U hU :=
  AutomorphicFunction.heckeOperator R hU hU hη h

/-- **Buzzard's decomposition for quaternionic modular forms** [*Eigenvarieties*, §9 p. 69]:
evaluation at a family of double-coset representatives `σ` identifies the space of
quaternionic modular forms of weight `(n, ν)` and level `U` with the product of the
`Γ_λ`-invariants of the weight module, `Γ_λ = σ(λ)⁻¹ Dˣ σ(λ) ∩ U`.

When the class set `Dˣ\(D ⊗ 𝔸_F^∞)ˣ/U` is finite — Fujisaki's lemma, proved in FLT as
`NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset` (port ticket T016) — the
product is a finite direct sum and the space is finite-dimensional over `R` whenever the
invariant submodules are. -/
theorem bijective_space_evalAtReps (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid F D v γ hγ)
    (σ : DoubleCoset.Quotient ((globalUnits F D : Subgroup (Dfx F D)) : Set (Dfx F D))
      (U : Set (Dfx F D)) → Dfx F D)
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient
      ((globalUnits F D : Subgroup (Dfx F D)) : Set (Dfx F D)) (U : Set (Dfx F D))) = q) :
    Function.Bijective (AutomorphicFunction.evalAtReps (A := WeightModule R n ν) R hU σ) :=
  AutomorphicFunction.bijective_evalAtReps R hU σ hσ

end QMF
