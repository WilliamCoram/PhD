/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Quaternionic
import PhD.QMF.FLTstuff.DivisionAlgebra.Finiteness

/-!
# Finiteness of the class set, and of the decomposition of `QMF.Space`

Fujisaki's lemma — the class set `Dˣ \ (D ⊗ 𝔸_F^∞)ˣ / U` is finite for `U` open — is proved
in `PhD/QMF/FLTstuff/DivisionAlgebra/Finiteness.lean` (ported from FLT, by Buzzard–Coram) as
`NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`.  This file records it in the
form the quaternionic-modular-forms library uses, namely for the subgroup
`QMF.globalUnits F D` of `QMF.Dfx F D`.

Combined with `QMF.bijective_space_evalAtReps` this upgrades Buzzard's decomposition
[*Eigenvarieties*, §9 p. 69] from a product to a **finite** product: the space of
quaternionic modular forms of weight `(n, ν)` and level `U` is a finite product of
`Γ_λ`-invariant subspaces of the weight module, indexed by the class set.
-/

open scoped TensorProduct TensorProduct.RightActions
open IsDedekindDomain NumberField

namespace QMF

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]

/-- **Fujisaki's lemma** in the form used by this library: the class set
`Dˣ ＼ (D ⊗ 𝔸_F^∞)ˣ ／ U` is finite for every open subgroup `U`.

This is `NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset` (FLT, ported in
`PhD/QMF/FLTstuff/DivisionAlgebra/Finiteness.lean`) transported along
`QMF.globalUnits F D = (QMF.unitsIncl F D).range`. -/
theorem finite_classSet {U : Subgroup (Dfx F D)} (hU : IsOpen (U : Set (Dfx F D))) :
    Finite (DoubleCoset.Quotient
      ((globalUnits F D : Subgroup (Dfx F D)) : Set (Dfx F D)) (U : Set (Dfx F D))) :=
  NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset F D hU

end QMF
