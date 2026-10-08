/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `negLog : Mᵐ⁰ → WithTop M`, and the multiplicative real line `ℝᵐ⁰`

`WithZero.log` in its "additive valuation" reading: instead of the junk value `log 0 = 0` we
record `0` as the genuine `⊤`, and we negate, so that the (reversed) order on `Mᵐ⁰` becomes the
usual order on `WithTop M`. The second half of the file is the real analogue of
`Mathlib/Data/Int/WithZero.lean`: the two monoid-with-zero homs relating `ℝᵐ⁰` to `ℝ≥0`.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §1.1.1–§1.1.2, coordinated with
mathlib4#43578 (same names and shapes). Tau Ceti home:
`TauCeti/Algebra/Order/GroupWithZero/NegLog.lean` and `TauCeti/Data/Real/WithZero.lean`.

## Main definitions

* `WithZero.negLog : Mᵐ⁰ → WithTop M`, `0 ↦ ⊤` and `exp m ↦ -m`.
* `WithZero.orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M`, the order-and-additive
  isomorphism underlying it. `(Additive Mᵐ⁰)ᵒᵈ` is the codomain of `Valuation.toAddValuation`
  for an `Mᵐ⁰`-valued valuation; this isomorphism turns it into the familiar `WithTop M = M ∪ {∞}`.
* `WithZero.mapAddHom' : (M →+ N) → (Mᵐ⁰ →*₀ Nᵐ⁰)`, the functoriality of `Mᵐ⁰` in `M`, along
  which `negLog` is natural (`WithZero.negLog_mapAddHom'`).
* `NNReal.toRealMultZero : ℝ≥0 →*₀ ℝᵐ⁰`, `0 ↦ 0` and `x ↦ exp (log x)`.
* `WithZeroMulReal.toNNReal : ℝᵐ⁰ →*₀ ℝ≥0` for a base `e ≠ 0`, `0 ↦ 0` and `exp t ↦ e ^ t`.
-/

open scoped NNReal WithZero

namespace WithZero

/-! ### `negLog : Mᵐ⁰ → WithTop M` -/

section NegLog

variable {M : Type*} [AddCommGroup M]

/-- The map `Mᵐ⁰ → WithTop M` sending `0` to `⊤` and `exp m` to `-m`: `WithZero.log` in its
"additive valuation" reading, with `0` recorded as a genuine `⊤` and the order reversed. -/
def negLog (x : Mᵐ⁰) : WithTop M := expRecOn x ⊤ fun m ↦ ((-m : M) : WithTop M)

@[simp] lemma negLog_zero : negLog (0 : Mᵐ⁰) = ⊤ := rfl

@[simp] lemma negLog_exp (m : M) : negLog (exp m) = ((-m : M) : WithTop M) := rfl

@[simp] lemma negLog_eq_top {x : Mᵐ⁰} : negLog x = ⊤ ↔ x = 0 := by
  induction x using expRecOn <;> simp [-WithTop.LinearOrderedAddCommGroup.coe_neg]

@[simp] lemma negLog_one : negLog (1 : Mᵐ⁰) = 0 := by
  rw [← exp_zero, negLog_exp, neg_zero, WithTop.coe_zero]

/-- The characterisation of `negLog`: `negLog x = m` if and only if `x = exp (-m)`. -/
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

lemma negLog_lt_negLog {x y : Mᵐ⁰} : negLog x < negLog y ↔ y < x :=
  lt_iff_lt_of_le_iff_le negLog_le_negLog

variable (M) in
/-- The order-and-additive isomorphism `(Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M` underlying `negLog`.
`(Additive Mᵐ⁰)ᵒᵈ` is the codomain of `Valuation.toAddValuation` for an `Mᵐ⁰`-valued valuation;
this isomorphism turns it into the familiar `WithTop M = M ∪ {∞}`. -/
def orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M where
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

@[simp] lemma orderAddIsoWithTop_apply (x : (Additive Mᵐ⁰)ᵒᵈ) :
    orderAddIsoWithTop M x = negLog x := rfl

end NegLog

/-! ### Functoriality: `Mᵐ⁰ →*₀ Nᵐ⁰` from `M →+ N` -/

section MapAddHom

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The monoid-with-zero hom `Mᵐ⁰ →*₀ Nᵐ⁰` induced by an additive hom `f : M →+ N`. -/
def mapAddHom' (f : M →+ N) : Mᵐ⁰ →*₀ Nᵐ⁰ := map' (AddMonoidHom.toMultiplicative f)

@[simp] lemma mapAddHom'_exp (f : M →+ N) (m : M) : mapAddHom' f (exp m) = exp (f m) := rfl

lemma mapAddHom'_strictMono [Preorder M] [Preorder N] {f : M →+ N} (hf : StrictMono f) :
    StrictMono (mapAddHom' f) :=
  map'_strictMono fun _ _ h ↦ hf h

/-- `negLog` is natural in `M`. -/
lemma negLog_mapAddHom' (f : M →+ N) (x : Mᵐ⁰) :
    negLog (mapAddHom' f x) = WithTop.map f (negLog x) := by
  induction x using expRecOn with
  | zero => rfl
  | exp a => rw [mapAddHom'_exp, negLog_exp, negLog_exp, WithTop.map_coe, map_neg]

end MapAddHom

end WithZero

/-! ### The real line: `ℝ≥0` and `ℝᵐ⁰` -/

namespace NNReal

/-- The order-preserving monoid-with-zero hom `ℝ≥0 →*₀ ℝᵐ⁰` sending `0` to `0` and `x` to
`exp (log x)`. It is an isomorphism; only strict monotonicity is used. -/
noncomputable def toRealMultZero : ℝ≥0 →*₀ ℝᵐ⁰ where
  toFun x := if x = 0 then 0 else WithZero.exp (Real.log x)
  map_zero' := if_pos rfl
  map_one' := by rw [if_neg one_ne_zero]; simp
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, ← WithZero.exp_add, NNReal.coe_mul,
      Real.log_mul (by exact_mod_cast hx) (by exact_mod_cast hy)]

lemma toRealMultZero_of_ne_zero {x : ℝ≥0} (hx : x ≠ 0) :
    toRealMultZero x = WithZero.exp (Real.log x) := if_neg hx

lemma toRealMultZero_strictMono : StrictMono toRealMultZero := by
  intro x y hxy
  have hy : y ≠ 0 := (bot_le.trans_lt hxy).ne'
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, toRealMultZero_of_ne_zero hy]
    exact WithZero.exp_pos
  · rw [toRealMultZero_of_ne_zero hx, toRealMultZero_of_ne_zero hy, WithZero.exp_lt_exp]
    exact Real.log_lt_log (by exact_mod_cast hx.bot_lt) (by exact_mod_cast hxy)

end NNReal

namespace WithZeroMulReal

open WithZero

/-- The real analogue of `WithZeroMulInt.toNNReal`: the hom `ℝᵐ⁰ →*₀ ℝ≥0` sending `0` to `0` and
`exp t` to `e ^ t` (an `NNReal.rpow`), for a base `e ≠ 0`. -/
noncomputable def toNNReal {e : ℝ≥0} (he : e ≠ 0) : ℝᵐ⁰ →*₀ ℝ≥0 where
  toFun x := if x = 0 then 0 else e ^ (log x)
  map_zero' := if_pos rfl
  map_one' := by rw [if_neg one_ne_zero, log_one, NNReal.rpow_zero]
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, log_mul hx hy, NNReal.rpow_add he]

@[simp] lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (t : ℝ) : toNNReal he (exp t) = e ^ t := by
  simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg exp_ne_zero, log_exp]

lemma toNNReal_strictMono {e : ℝ≥0} (he : 1 < e) :
    StrictMono (toNNReal (ne_zero_of_lt he)) := by
  intro x y hxy
  have hy : y ≠ 0 := (bot_le.trans_lt hxy).ne'
  rcases eq_or_ne x 0 with rfl | hx
  · lift y to ℝ using hy with t
    rw [map_zero, toNNReal_exp]
    exact NNReal.rpow_pos (zero_lt_one.trans he)
  · lift x to ℝ using hx with s
    lift y to ℝ using hy with t
    rw [toNNReal_exp, toNNReal_exp]
    exact NNReal.rpow_lt_rpow_of_exponent_lt he (exp_lt_exp.mp hxy)

end WithZeroMulReal
