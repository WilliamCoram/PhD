/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Valuation.Basic
import PhD.TauCeti.Code.NewtonPolygons.AddVal.NegLog

/-!
# Additive valuations attached to multiplicative valuations

Given a multiplicative valuation `v : Valuation R Mᵐ⁰` we build the corresponding *additive*
valuation, an `AddValuation R (WithTop M)` sending `x` to `-log (v x)`, with `∞` at `0`.

Mathlib's `Valuation.toAddValuation` already exhibits the bijection
`Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ`, but its codomain is a type synonym rather than
a usable `M ∪ {∞}`. The point of this file is to land in `WithTop M`, and to pin the architecture
of the whole layer: every concrete additive valuation is `(v.restrict.map φ _).addVal` for a hom
`φ` into `ℤᵐ⁰`, `ℚᵐ⁰` or `ℝᵐ⁰`, converted once, at the end, with `addVal`.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §1.1.3–§1.1.5, coordinated with
mathlib4#43580 (same names and shapes). Tau Ceti home:
`TauCeti/RingTheory/Valuation/AddValuation/Basic.lean`.

## Main definitions

* `Valuation.addVal : Valuation R Mᵐ⁰ → AddValuation R (WithTop M)`; its defining property is
  `Valuation.addVal_eq_coe : v.addVal x = m ↔ v x = exp (-m)`.
* `Valuation.addValValueGroup`, the tautological additive valuation of an *arbitrary* valuation,
  with values in `WithTop` of its own (additively written) value group.

## Main results

* `Valuation.addVal_map`: naturality along `WithZero.mapAddHom'`, which gives the compatibility
  squares `WithTop ℤ → WithTop ℚ → WithTop ℝ` of the later files.
-/

open scoped WithZero

namespace Valuation

open WithZero

variable {R M N : Type*} [Ring R]
  [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
  [AddCommGroup N] [LinearOrder N] [IsOrderedAddMonoid N]

/-- The additive valuation `R → WithTop M = M ∪ {∞}` attached to a valuation with values in
`Mᵐ⁰`: it sends `x` to `-log (v x)`, with the value `∞` at `v x = 0`. -/
def addVal (v : Valuation R Mᵐ⁰) : AddValuation R (WithTop M) :=
  v.toAddValuation.map (orderAddIsoWithTop M).toAddEquiv.toAddMonoidHom rfl
    (orderAddIsoWithTop M).toOrderIso.monotone

lemma addVal_apply (v : Valuation R Mᵐ⁰) (x : R) : v.addVal x = negLog (v x) := rfl

@[simp] lemma addVal_eq_top {v : Valuation R Mᵐ⁰} {x : R} : v.addVal x = ⊤ ↔ v x = 0 := by
  rw [addVal_apply, negLog_eq_top]

/-- The defining property: `v.addVal x = m` if and only if `v x = exp (-m)`. -/
lemma addVal_eq_coe {v : Valuation R Mᵐ⁰} {x : R} {m : M} :
    v.addVal x = (m : WithTop M) ↔ v x = exp (-m) :=
  negLog_eq_coe

/-- The additive valuation reverses the order of the multiplicative one. -/
lemma addVal_le_addVal {v : Valuation R Mᵐ⁰} {x y : R} :
    v.addVal x ≤ v.addVal y ↔ v y ≤ v x :=
  negLog_le_negLog

/-- Pushing a valuation along `mapAddHom' f` pushes its additive valuation along `f`. -/
lemma addVal_map (v : Valuation R Mᵐ⁰) {f : M →+ N} (hf : StrictMono f) (x : R) :
    (v.map (mapAddHom' f) (mapAddHom'_strictMono hf).monotone).addVal x
      = WithTop.map f (v.addVal x) :=
  negLog_mapAddHom' f (v x)

/-! ### The tautological additive valuation -/

section ValueGroup

open MonoidWithZeroHom

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)

/-- The tautological additive valuation attached to an arbitrary valuation `v`: no rank hypothesis
at all, the values live in `WithTop` of the (additively written) value group of `v`. -/
noncomputable def addValValueGroup :
    AddValuation R (WithTop (Additive (valueGroup (.ofClass v)))) :=
  addVal (M := Additive (valueGroup (.ofClass v))) v.restrict

lemma addValValueGroup_apply (x : R) :
    v.addValValueGroup x = negLog (M := Additive (valueGroup (.ofClass v))) (v.restrict x) :=
  rfl

@[simp] lemma addValValueGroup_eq_top {x : R} : v.addValValueGroup x = ⊤ ↔ v x = 0 :=
  (negLog_eq_top (M := Additive (valueGroup (.ofClass v))) (x := v.restrict x)).trans
    v.restrict_eq_zero_iff

end ValueGroup

end Valuation
