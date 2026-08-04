/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Finiteness

/-!
# Finite-dimensionality of the space of quaternionic modular forms

[Buzzard, *Eigenvarieties*, §9 p. 70], immediately after the definition of
`S^D_{k,w}(U) = L(U, L_{n,v})`:

> "This space is a finite-dimensional `K`-vector space."

The proof is the one Buzzard indicates: the class-set decomposition
`L(U, A) ≅ ∏_λ A^{Γ_λ}` (`AutomorphicFunction.bijective_evalAtReps`) has **finitely many**
factors by Fujisaki's lemma (`QMF.finite_classSet`), and each factor is a submodule of the
weight module `L_{n,ν}`, which is finitely generated because it is a homogeneous component
of a polynomial ring in finitely many variables.

## Main results

* `QMF.WeightModule.instFinite` — `L_{n,ν}` is a finite `R`-module.
* `QMF.finite_space` — `S^D(U)` is a finite `R`-module, for `R` noetherian.
* `QMF.finiteDimensional_space` — `S^D(U)` is finite-dimensional, for `R` a field.
-/

open scoped TensorProduct TensorProduct.RightActions
open IsDedekindDomain NumberField MvPolynomial

namespace QMF

section WeightModuleFinite

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀] {γ : Γ₀} {hγ : γ < 1}
variable (R : Type*) [CommRing R] [Algebra K R] (n : ℕ) (ν : Sigma0 K γ hγ →* Rˣ)

/-- The weight module `L_{n,ν}` is a finite `R`-module: it is the degree-`n` homogeneous
component of a polynomial ring in two variables, which is finitely generated (spanned by
the monomials of degree `n`). -/
instance WeightModule.instFinite : Module.Finite R (WeightModule R n ν) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 2) R n)

end WeightModuleFinite

section SpaceFinite

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]
variable (v : HeightOneSpectrum (RingOfIntegers F)) [RigidificationAt F D v]
variable (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1)
variable {R : Type*} [CommRing R] [Algebra (v.adicCompletion F) R]
variable (n : ℕ) (ν : Sigma0 (v.adicCompletion F) γ hγ →* Rˣ)

/-- **The space of quaternionic modular forms is a finite module.**
[Buzzard, *Eigenvarieties*, §9 p. 70.]

For `U` an open subgroup of wild level `≥ γ` and `R` noetherian, the space
`S^D(U) = L(U, L_{n,ν})` of quaternionic modular forms of weight `(n, ν)` and level `U`
is a finite `R`-module.

The two inputs are Fujisaki's lemma (finiteness of the class set `Dˣ＼(D ⊗ 𝔸_F^∞)ˣ／U`,
`QMF.finite_classSet`) and finiteness of the weight module
(`QMF.WeightModule.instFinite`); they are combined through the class-set decomposition
`QMF.bijective_space_evalAtReps`. -/
theorem finite_space [IsNoetherianRing R] {U : Subgroup (Dfx F D)}
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid F D v γ hγ)
    (hUopen : IsOpen (U : Set (Dfx F D))) :
    Module.Finite R (Space F D v γ hγ n ν U hU) := by
  -- Abbreviation for the class set `Dˣ ＼ (D ⊗ 𝔸_F^∞)ˣ ／ U`.
  let Q := DoubleCoset.Quotient
    ((globalUnits F D : Subgroup (Dfx F D)) : Set (Dfx F D)) (U : Set (Dfx F D))
  -- The class set is finite (Fujisaki).
  have : Finite Q := finite_classSet F D hUopen
  -- `Quotient.out` is a section of the double-coset projection.
  have hσ : ∀ q : Q, (Quotient.mk'' q.out : Q) = q := fun q => Quotient.out_eq' q
  -- Each factor of the decomposition is a submodule of the (finite) weight module,
  -- hence finite because `R` is noetherian.
  have : ∀ q : Q, Module.Finite R
      (AbstractHeckeOperator.fixedPointsOfLE
        (V := AutomorphicFunction.stabilizerAt (globalUnits F D) U q.out)
        R (WeightModule R n ν)
        (AutomorphicFunction.stabilizerAt_le hU (globalUnits F D) q.out)) :=
    fun _ => Module.Finite.of_fg (IsNoetherian.noetherian _)
  -- Transport finiteness along the class-set decomposition.
  exact Module.Finite.equiv
    (LinearEquiv.ofBijective (AutomorphicFunction.evalAtReps (A := WeightModule R n ν) R hU _)
      (bijective_space_evalAtReps F D v γ hγ n ν U hU _ hσ)).symm

end SpaceFinite

section SpaceFiniteDimensional

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]
variable (v : HeightOneSpectrum (RingOfIntegers F)) [RigidificationAt F D v]
variable (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1)
variable {R : Type*} [Field R] [Algebra (v.adicCompletion F) R]
variable (n : ℕ) (ν : Sigma0 (v.adicCompletion F) γ hγ →* Rˣ)

/-- **The space of quaternionic modular forms is finite-dimensional.**
[Buzzard, *Eigenvarieties*, §9 p. 70: "This space is a finite-dimensional `K`-vector
space."]  The coefficient-field specialisation of `QMF.finite_space`. -/
theorem finiteDimensional_space {U : Subgroup (Dfx F D)}
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid F D v γ hγ)
    (hUopen : IsOpen (U : Set (Dfx F D))) :
    FiniteDimensional R (Space F D v γ hγ n ν U hU) :=
  finite_space F D v γ hγ n ν hU hUopen

end SpaceFiniteDimensional

end QMF
