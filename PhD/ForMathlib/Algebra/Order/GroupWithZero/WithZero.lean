/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.Algebra.Order.Hom.Monoid

/-!
# `negLog : Mᵐ⁰ → WithTop M`

`WithZero.log` in its "additive valuation" reading: instead of the junk value `log 0 = 0` we
record `0` as the genuine `⊤`, and we negate, so that the (reversed) order on `Mᵐ⁰` becomes the
usual order on `WithTop M`.

## Main definitions

* `WithZero.negLog : Mᵐ⁰ → WithTop M`, `0 ↦ ⊤` and `exp m ↦ -m`.
* `WithZero.negLogOrderAddIso : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M`, the order-and-additive
  isomorphism underlying it.  `(Additive Mᵐ⁰)ᵒᵈ` is the codomain of `Valuation.toAddValuation`
  for an `Mᵐ⁰`-valued valuation; this isomorphism turns it into the familiar
  `WithTop M = M ∪ {∞}`.
* `WithZero.expMap : (M →+ N) → (Mᵐ⁰ →*₀ Nᵐ⁰)`, the functoriality of `Mᵐ⁰` in `M`, along
  which `negLog` is natural (`WithZero.negLog_expMap`).

This file is upstream of every additive-valuation construction in `PhD/ForMathlib/RingTheory/
Valuation/AddVal/`; it knows nothing about valuations.

Everything here is meant to be redistributed into the relevant `Mathlib` files.
-/

open scoped WithZero

namespace WithZero

/-! ## `negLog : Mᵐ⁰ → WithTop M` -/

section NegLog

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The map `Mᵐ⁰ → WithTop M` sending `0` to `⊤` and `exp m` to `-m`.

This is `WithZero.log` in its "additive valuation" reading: instead of the junk value `log 0 = 0`
we record `0` as the genuine `⊤`, and we negate, so that the (reversed) order on `Mᵐ⁰` becomes the
usual order on `WithTop M`. -/
def negLog (x : Mᵐ⁰) : WithTop M := expRecOn x ⊤ fun m ↦ ((-m : M) : WithTop M)

@[simp] lemma negLog_zero : negLog (0 : Mᵐ⁰) = ⊤ := rfl

@[simp] lemma negLog_exp (m : M) : negLog (exp m) = ((-m : M) : WithTop M) := rfl

@[simp] lemma negLog_eq_top {x : Mᵐ⁰} : negLog x = ⊤ ↔ x = 0 := by
  induction x using expRecOn <;>
    simp [-WithTop.LinearOrderedAddCommGroup.coe_neg]

@[simp] lemma negLog_one : negLog (1 : Mᵐ⁰) = 0 := by
  rw [← exp_zero, negLog_exp, neg_zero, WithTop.coe_zero]

lemma negLog_eq_coe {x : Mᵐ⁰} {m : M} : negLog x = (m : WithTop M) ↔ x = exp (-m) := by
  induction x using expRecOn with
  | zero => exact ⟨fun h ↦ absurd h (by simp), fun h ↦ absurd h.symm exp_ne_zero⟩
  | exp a => rw [negLog_exp, WithTop.coe_inj, exp_inj, neg_eq_iff_eq_neg]

lemma negLog_mul (x y : Mᵐ⁰) : negLog (x * y) = negLog x + negLog y := by
  induction x using expRecOn with
  | zero => simp
  | exp a =>
    induction y using expRecOn with
    | zero => simp
    | exp b => rw [← exp_add, negLog_exp, negLog_exp, negLog_exp, neg_add, WithTop.coe_add]

variable [LinearOrder M] [IsOrderedAddMonoid M]

lemma negLog_le_negLog {x y : Mᵐ⁰} : negLog x ≤ negLog y ↔ y ≤ x := by
  induction x using expRecOn with
  | zero => simp
  | exp a =>
    induction y using expRecOn with
    | zero => simp
    | exp b => rw [negLog_exp, negLog_exp, WithTop.coe_le_coe, neg_le_neg_iff, exp_le_exp]

variable (M) in
/-- The order-and-additive isomorphism `(Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M` underlying `negLog`.

`(Additive Mᵐ⁰)ᵒᵈ` is the codomain of `Valuation.toAddValuation` for an `Mᵐ⁰`-valued valuation; this
isomorphism turns it into the familiar `WithTop M = M ∪ {∞}`. -/
def negLogOrderAddIso : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M where
  toFun x := negLog x
  invFun y := y.recTopCoe (0 : Mᵐ⁰) fun m ↦ exp (-m)
  left_inv x := by
    induction x using expRecOn with
    | zero => rfl
    | exp a => show exp (- -a) = exp a; rw [neg_neg]
  right_inv y := by
    induction y using WithTop.recTopCoe with
    | top => rfl
    | coe m => show negLog (exp (-m)) = (m : WithTop M); rw [negLog_exp, neg_neg]
  map_add' := negLog_mul
  map_le_map_iff' := negLog_le_negLog

@[simp] lemma negLogOrderAddIso_apply (x : (Additive Mᵐ⁰)ᵒᵈ) :
    negLogOrderAddIso M x = negLog x := rfl

end NegLog

/-! ## Functoriality: `Mᵐ⁰ →*₀ Nᵐ⁰` from `M →+ N` -/

section ExpMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The monoid-with-zero hom `Mᵐ⁰ →*₀ Nᵐ⁰` induced by an additive hom `f : M →+ N`. -/
def expMap (f : M →+ N) : Mᵐ⁰ →*₀ Nᵐ⁰ := map' (AddMonoidHom.toMultiplicative f)

@[simp] lemma expMap_exp (f : M →+ N) (m : M) : expMap f (exp m) = exp (f m) := rfl

lemma expMap_strictMono [Preorder M] [Preorder N] {f : M →+ N} (hf : StrictMono f) :
    StrictMono (expMap f) :=
  map'_strictMono fun _ _ h ↦ hf h

/-- `negLog` is natural in `M`. -/
lemma negLog_expMap (f : M →+ N) (x : Mᵐ⁰) :
    negLog (expMap f x) = WithTop.map f (negLog x) := by
  induction x using expRecOn with
  | zero => rfl
  | exp a => rw [expMap_exp, negLog_exp, negLog_exp, WithTop.map_coe, map_neg]

end ExpMap

end WithZero
