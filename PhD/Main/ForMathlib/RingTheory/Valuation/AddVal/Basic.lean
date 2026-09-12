/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Range
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.RingTheory.Valuation.Basic

/-!
# Additive valuations attached to multiplicative valuations

Given a multiplicative valuation `v : Valuation R Γ₀` we build the corresponding *additive*
valuation, i.e. an `AddValuation R (WithTop A)` sending `x` to `-log (v x)`, with `∞` at `0`.

Mathlib's `Valuation.toAddValuation` already exhibits the bijection
`Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ`, but its codomain is a type synonym rather than a
usable `A ∪ {∞}`.  The point of this file is to land in `WithTop A` for `A = ℤ, ℚ, ℝ`, and to check
that the resulting object really is the classical additive valuation.

## Main definitions

* `Valuation.addVal : Valuation R Mᵐ⁰ → AddValuation R (WithTop M)`, the additive valuation of an
  `Mᵐ⁰`-valued valuation.  Its defining property is `Valuation.addVal_eq_coe`:
  `v.addVal x = m ↔ v x = exp (-m)`.
* `Valuation.addValValueGroup`, the tautological additive valuation of an *arbitrary* valuation,
  with values in `WithTop` of its own (additively written) value group.  Every concrete additive
  valuation in this directory is this one pushed along a hom out of the value group.

## Main results

* `Valuation.addVal_map`: naturality along `WithZero.expMap`, which gives the compatibility
  squares `WithTop ℤ → WithTop ℚ → WithTop ℝ` in the downstream files.

## Files in this directory

* `02_Basic.lean` (this file) — `addVal`, `addValValueGroup`;
* `RankOne.lean` — the real additive valuation `x ↦ -log ‖x‖` of a rank-one valuation;
* `Commensurable.lean` — rational rank one normalised at an element, and `addValQ`;
* `Discrete.lean` — the honest `ℤ`-valued additive valuation of a discrete valuation.

The normed-field applications live in `PhD/Main/ForMathlib/Topology/Algebra/Valued/AddVal.lean`, and
the `ℚ_p` verification in `PhD/Main/ForMathlib/NumberTheory/Padics/AddVal.lean`.

Everything here is meant to be redistributed into the relevant `Mathlib` files.
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
  v.toAddValuation.map (negLogOrderAddIso M).toAddEquiv.toAddMonoidHom rfl
    (negLogOrderAddIso M).toOrderIso.monotone

@[simp] lemma addVal_apply (v : Valuation R Mᵐ⁰) (x : R) : v.addVal x = negLog (v x) := rfl

@[simp] lemma addVal_eq_top {v : Valuation R Mᵐ⁰} {x : R} : v.addVal x = ⊤ ↔ v x = 0 := by
  simp

/-- The defining property: `v.addVal x = m` if and only if `v x = exp (-m)`. -/
lemma addVal_eq_coe {v : Valuation R Mᵐ⁰} {x : R} {m : M} :
    v.addVal x = (m : WithTop M) ↔ v x = exp (-m) :=
  negLog_eq_coe

/-- Pushing a valuation along `expMap f` pushes its additive valuation along `f`. -/
lemma addVal_map (v : Valuation R Mᵐ⁰) {f : M →+ N} (hf : StrictMono f) (x : R) :
    (v.map (expMap f) (expMap_strictMono hf).monotone).addVal x
      = WithTop.map f (v.addVal x) :=
  negLog_expMap f (v x)

/-! ### The tautological additive valuation -/

section ValueGroup

open MonoidWithZeroHom

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)

/-- The tautological additive valuation attached to an arbitrary valuation `v`: no rank hypothesis
at all, the values live in `WithTop` of the (additively written) value group of `v`.

All the concrete additive valuations of this directory are obtained from this one by pushing the
value group into `ℤ`, `ℚ` or `ℝ`. -/
noncomputable def addValValueGroup :
    AddValuation R (WithTop (Additive (valueGroup (.ofClass v)))) :=
  addVal (M := Additive (valueGroup (.ofClass v))) v.restrict

@[simp] lemma addValValueGroup_apply (x : R) :
    v.addValValueGroup x = negLog (M := Additive (valueGroup (.ofClass v))) (v.restrict x) := rfl

end ValueGroup

end Valuation
