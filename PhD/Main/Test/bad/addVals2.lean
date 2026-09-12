import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued

open scoped NNReal

section AddVal

variable {L Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable [Ring L] (v : Valuation L Γ)

/-- General order-**and**-additive isomorphism
`(Additive (WithZero (Multiplicative G)))ᵒᵈ ≃+o WithTop G` for any linearly ordered additive
commutative group `G`.  Sends `0 ↦ ⊤` and `coe (ofAdd g) ↦ -g`; multiplication on the source
becomes addition on `WithTop G`.  -/
noncomputable def withZeroMultOrderAddIso (G : Type*)
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] :
    (Additive (WithZero (Multiplicative G)))ᵒᵈ ≃+o WithTop G where
  toFun x := WithZero.recZeroCoe (⊤ : WithTop G)
      (fun n => ((-(Multiplicative.toAdd n) : G) : WithTop G)) x
  invFun y := WithTop.recTopCoe (0 : WithZero (Multiplicative G))
      (fun n => ((Multiplicative.ofAdd (-n) : Multiplicative G) : WithZero (Multiplicative G))) y
  left_inv x := by
    induction x using WithZero.recZeroCoe with
    | zero => rfl
    | coe n => simp [WithZero.recZeroCoe, WithTop.recTopCoe, neg_neg,
        -WithTop.LinearOrderedAddCommGroup.coe_neg]
  right_inv y := by
    induction y using WithTop.recTopCoe with
    | top => rfl
    | coe n => simp [WithZero.recZeroCoe, WithTop.recTopCoe, neg_neg, -WithZero.coe_inv,
        -WithTop.LinearOrderedAddCommGroup.coe_neg]
  map_add' a b := by
    induction a using WithZero.recZeroCoe with
    | zero => rfl
    | coe m =>
      induction b using WithZero.recZeroCoe with
      | zero => rfl
      | coe n =>
        show ((-(Multiplicative.toAdd (m * n)) : G) : WithTop G)
          = ((-(Multiplicative.toAdd m) : G) : WithTop G)
            + ((-(Multiplicative.toAdd n) : G) : WithTop G)
        rw [toAdd_mul, neg_add, WithTop.coe_add]
  map_le_map_iff' {a b} := by
    induction a using WithZero.recZeroCoe with
    | zero => induction b using WithZero.recZeroCoe with
      | zero => simp [WithZero.recZeroCoe]
      | coe m =>
        simp only [WithZero.recZeroCoe]
        refine ⟨fun h => absurd (top_le_iff.mp h) (by simp), fun h => ?_⟩
        exact absurd (h : (↑m : WithZero (Multiplicative G)) ≤ 0) (WithZero.not_coe_le_zero m)
    | coe n => induction b using WithZero.recZeroCoe with
      | zero =>
        simp only [WithZero.recZeroCoe]
        exact ⟨fun _ => (WithZero.zero_le (n : WithZero (Multiplicative G))), fun _ => le_top⟩
      | coe m =>
        simp only [WithZero.recZeroCoe]
        rw [WithTop.coe_le_coe, neg_le_neg_iff]
        exact WithZero.coe_le_coe.symm

noncomputable
def AddVal_withTopValGroup : AddValuation L (WithTop (Additive (MonoidWithZeroHom.valueGroup v))) :=
  v.restrict.toAddValuation.map
    (withZeroMultOrderAddIso (Additive (MonoidWithZeroHom.valueGroup v))).toAddEquiv.toAddMonoidHom
    rfl (withZeroMultOrderAddIso (Additive (MonoidWithZeroHom.valueGroup v))).toOrderIso.monotone

@[simp]
lemma AddVal_withTopValGroup_apply (x : L) : AddVal_withTopValGroup v x = withZeroMultOrderAddIso
  (Additive (MonoidWithZeroHom.valueGroup v)) (v.restrict.toAddValuation x) := rfl

end AddVal

/-!
## The real-valued additive valuation on a rank-one valuation: `x ↦ -log (v.norm x)`

Specialisation of the general `AddVal_withTopValGroup` to the rank-one case.  The point is that for a
*rank-one* valuation the value group is "one-dimensional": `Additive (valueGroup v)` embeds
order-and-additively into `(ℝ, +)` via `g ↦ log (RankOne.hom v g)` (`RankOne.valueGroupLog`).
-/

/-- `WithTop.map` of a monotone map is monotone. -/
private lemma monotone_withTop_map {α β : Type*} [Preorder α] [Preorder β] {f : α → β}
    (hf : Monotone f) : Monotone (WithTop.map f) := by
  intro a b hab
  induction b using WithTop.recTopCoe with
  | top => exact le_top
  | coe b' =>
    induction a using WithTop.recTopCoe with
    | top => exact (lt_irrefl _ (lt_of_lt_of_le (WithTop.coe_lt_top b') hab)).elim
    | coe a' =>
      rw [WithTop.map_coe, WithTop.map_coe]
      exact WithTop.coe_le_coe.mpr (hf (WithTop.coe_le_coe.mp hab))

open Valuation

section RankOneAddVal

variable {L Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [Ring L] (v : Valuation L Γ) [RankOne v]

/-- The image under `RankOne.hom v` of a value-group element (a nonzero element of `ValueGroup₀ v`)
is nonzero. -/
private lemma hom_coe_ne_zero (u : MonoidWithZeroHom.valueGroup v) :
    RankOne.hom v (u : MonoidWithZeroHom.ValueGroup₀ v) ≠ 0 :=
  fun h => WithZero.coe_ne_zero (RankOne.zero_of_hom_zero v h)

/-- **The value group of a rank-one valuation, realised inside `(ℝ, +)`.** -/
noncomputable def RankOne.valueGroupLog :
    Additive (MonoidWithZeroHom.valueGroup v) →+ ℝ where
  toFun g := Real.log (RankOne.hom v ((Additive.toMul g : MonoidWithZeroHom.valueGroup v) :
    MonoidWithZeroHom.ValueGroup₀ v))
  map_zero' := by rw [toMul_zero, WithZero.coe_one, map_one, NNReal.coe_one, Real.log_one]
  map_add' g h := by
    rw [toMul_add, WithZero.coe_mul, map_mul, NNReal.coe_mul,
      Real.log_mul (by exact_mod_cast hom_coe_ne_zero v (Additive.toMul g))
        (by exact_mod_cast hom_coe_ne_zero v (Additive.toMul h))]

lemma RankOne.valueGroupLog_strictMono : StrictMono (RankOne.valueGroupLog v) := by
  intro g h hgh
  have hlt : RankOne.hom v ((Additive.toMul g : MonoidWithZeroHom.valueGroup v) :
        MonoidWithZeroHom.ValueGroup₀ v)
      < RankOne.hom v ((Additive.toMul h : MonoidWithZeroHom.valueGroup v) :
        MonoidWithZeroHom.ValueGroup₀ v) :=
    RankOne.strictMono v (WithZero.coe_lt_coe.mpr (Additive.toMul_lt.mpr hgh))
  have hgpos : (0 : ℝ≥0) < RankOne.hom v ((Additive.toMul g : MonoidWithZeroHom.valueGroup v) :
        MonoidWithZeroHom.ValueGroup₀ v) :=
    zero_le'.lt_of_ne (Ne.symm (hom_coe_ne_zero v (Additive.toMul g)))
  simp only [RankOne.valueGroupLog, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact Real.log_lt_log (by exact_mod_cast hgpos) (by exact_mod_cast hlt)

/-- **The real-valued additive valuation `x ↦ -log ‖x‖` on a rank-one valuation**, valued in
`WithTop ℝ` with `⊤` at `0`.  Obtained from the general `AddVal_withTopValGroup` by pushing its
values along the embedding `valueGroupLog`; needs only a `Ring`. -/
noncomputable def RankOne.addVal : AddValuation L (WithTop ℝ) :=
  (AddVal_withTopValGroup v).map (AddMonoidHom.withTopMap (RankOne.valueGroupLog v)) rfl
    (monotone_withTop_map (RankOne.valueGroupLog_strictMono v).monotone)

@[simp]
lemma RankOne.addVal_apply (x : L) :
    RankOne.addVal v x = WithTop.map (RankOne.valueGroupLog v) (AddVal_withTopValGroup v x) := rfl

@[simp]
lemma RankOne.addVal_zero : RankOne.addVal v 0 = ⊤ := AddValuation.map_zero _

end RankOneAddVal

section RankOneAddValField

variable {L Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [Field L] (v : Valuation L Γ) [RankOne v]

/-- On a field, `RankOne.addVal` is `x ↦ -log ‖x‖`. -/
lemma RankOne.addVal_apply_of_ne_zero {x : L} (hx : x ≠ 0) :
    RankOne.addVal v x = ((-Real.log (v.norm x) : ℝ) : WithTop ℝ) := by
  have hne : RankOne.hom v (v.restrict x) ≠ 0 := fun h =>
    hx (v.norm_eq_zero (by show ((RankOne.hom v (v.restrict x) : ℝ≥0) : ℝ) = 0; rw [h]; simp))
  have hr : v.restrict x ≠ 0 := fun h => hne (by rw [h]; exact map_zero _)
  obtain ⟨w, hw⟩ : ∃ w : MonoidWithZeroHom.valueGroup v,
      v.restrict x = ((w : MonoidWithZeroHom.valueGroup v) : MonoidWithZeroHom.ValueGroup₀ v) :=
    ⟨WithZero.unzero hr, (WithZero.coe_unzero hr).symm⟩
  have hA : RankOne.addVal v x
      = ((RankOne.valueGroupLog v (-(Additive.ofMul w)) : ℝ) : WithTop ℝ) := by
    rw [RankOne.addVal_apply, AddVal_withTopValGroup_apply, Valuation.toAddValuation_apply, hw]
    rfl
  rw [hA, show RankOne.valueGroupLog v (-(Additive.ofMul w))
        = -(RankOne.valueGroupLog v (Additive.ofMul w)) from _root_.map_neg _ _]
  simp only [RankOne.valueGroupLog, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul]
  rw [show v.norm x = ((RankOne.hom v (v.restrict x) : ℝ≥0) : ℝ) from rfl, hw]

end RankOneAddValField

/-!
## The rational-rank-one (`ℂ_p`-style) refinement: an honest `ℚ`-valued additive valuation

When `v` has rational rank `≤ 1` (its value group embeds order-preservingly into `ℚ` — e.g. `ℂ_p`,
whose value group is `ℚ`) we get an honest `ℚ`-valued additive valuation.  As with the real case, we
do **not** transport `v` onto `ℚᵐ⁰` and back: we push the general `AddVal_withTopValGroup` along an
embedding `Additive (valueGroup v) →+ ℚ` (`RatRankLeOne.valueGroupRat`), obtained from the
`RatRankLeOne` hom by reading off the exponent of its (nonzero) value on each value-group element.
-/

/-- **Rational-rank-≤-1 hypothesis** on a valuation `v`: its value group `ValueGroup₀ v` embeds,
order-preservingly, into `ℚᵐ⁰ = WithZero (Multiplicative ℚ)`.  The density analogue of
`IsRankOneDiscrete` (whose target is `ℤᵐ⁰`); `ℂ_p` satisfies it, a value group `ℤ + ℤ√2` does not. -/
class Valuation.RatRankLeOne {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) where
  /-- An order-preserving embedding of the value group into `ℚᵐ⁰`. -/
  hom : MonoidWithZeroHom.ValueGroup₀ v →*₀ WithZero (Multiplicative ℚ)
  /-- The embedding is strictly monotone. -/
  strictMono : StrictMono hom

/-!
## Coherence: `IsRankOneDiscrete ⟹ RatRankLeOne ⟹ RankLeOne` (and `RankOne`)

The hypotheses form a genuine hierarchy.  `RatRankLeOne` sits strictly between discreteness
(target `ℤ`) and plain rank ≤ one (target `ℝ≥0`): it embeds the value group into `ℚ`, which then
sits inside `ℝ≥0` via an exponential `x ↦ e^x`.  Together with nontriviality (part of the `RankOne`
class), `RankLeOne` upgrades to `RankOne`.
-/

section Coherence

open Multiplicative WithZero Valuation.IsRankOneDiscrete

variable {L Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [Ring L] (v : Valuation L Γ)

/-- Lift a strictly monotone additive hom `G →+ H` to a monoid-with-zero hom
`WithZero (Multiplicative G) →*₀ WithZero (Multiplicative H)`. -/
noncomputable def withZeroMultMap {G H : Type*} [AddGroup G] [AddGroup H] (f : G →+ H) :
    WithZero (Multiplicative G) →*₀ WithZero (Multiplicative H) :=
  WithZero.map' (AddMonoidHom.toMultiplicative f)

lemma withZeroMultMap_strictMono {G H : Type*} [AddGroup G] [AddGroup H] [Preorder G] [Preorder H]
    {f : G →+ H} (hf : StrictMono f) : StrictMono (withZeroMultMap f) := by
  apply WithZero.map'_strictMono
  intro a b h
  exact hf h

/-- Exponential embedding `ℚᵐ⁰ →*₀ ℝ≥0`, `x ↦ e^(unzero x).toAdd` for a base `e ≠ 0`.  The
`rpow`/`ℚ` analogue of `WithZeroMulInt.toNNReal`. -/
noncomputable def ratToNNReal {e : ℝ≥0} (he : e ≠ 0) :
    WithZero (Multiplicative ℚ) →*₀ ℝ≥0 where
  toFun x := if hx : x = 0 then 0 else e ^ ((WithZero.unzero hx).toAdd : ℝ)
  map_zero' := rfl
  map_one' := by
    have h10 : (1 : WithZero (Multiplicative ℚ)) ≠ 0 := one_ne_zero
    have hu1 : WithZero.unzero h10 = 1 := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero, WithZero.coe_one]
    rw [dif_neg h10, hu1, toAdd_one, Rat.cast_zero, NNReal.rpow_zero]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases mul_eq_zero.mp hxy with hx | hy
      · rw [dif_pos hxy, dif_pos hx, zero_mul]
      · rw [dif_pos hxy, dif_pos hy, mul_zero]
    · obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp hxy
      have hu : WithZero.unzero hxy = WithZero.unzero hx * WithZero.unzero hy := by
        rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero,
          WithZero.coe_unzero]
      rw [dif_neg hxy, dif_neg hx, dif_neg hy, hu, toAdd_mul, Rat.cast_add, NNReal.rpow_add he]

lemma ratToNNReal_strictMono {e : ℝ≥0} (he : 1 < e) :
    StrictMono (ratToNNReal (ne_zero_of_lt he)) := by
  intro x y hxy
  simp only [ratToNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hx hy hy
  · simp only [hy, not_lt_zero'] at hxy
  · exact NNReal.rpow_pos (zero_lt_one.trans he)
  · simp only [hy, not_lt_zero'] at hxy
  · apply NNReal.rpow_lt_rpow_of_exponent_lt he
    rw [Rat.cast_lt, Multiplicative.toAdd_lt, ← WithZero.coe_lt_coe, WithZero.coe_unzero,
      WithZero.coe_unzero]
    exact hxy

/-- **`RatRankLeOne ⟹ RankLeOne`.**  Composing the embedding `ValueGroup₀ v ↪ ℚᵐ⁰` with the
exponential `ℚᵐ⁰ ↪ ℝ≥0` of any base `1 < e` exhibits the value group inside `ℝ≥0`, i.e. rank ≤ one.
(The hypothesis `1 < e` is what makes the exponential strictly monotone: `e = 1` collapses
everything to `1` and `e < 1` reverses the order.) -/
@[reducible]
noncomputable def Valuation.RatRankLeOne.toRankLeOne [v.RatRankLeOne] {e : ℝ≥0} (he : 1 < e) :
    RankLeOne v where
  hom' := (ratToNNReal (ne_zero_of_lt he)).comp (Valuation.RatRankLeOne.hom (v := v))
  strictMono' :=
    (ratToNNReal_strictMono he).comp (Valuation.RatRankLeOne.strictMono (v := v))

/-- **`RatRankLeOne ⟹ RankOne`**, given nontriviality (which is part of the `RankOne` class), for
any exponential base `1 < e`. -/
@[reducible]
noncomputable def Valuation.RatRankLeOne.toRankOne [v.RatRankLeOne] [v.IsNontrivial]
    {e : ℝ≥0} (he : 1 < e) : RankOne v where
  __ := Valuation.RatRankLeOne.toRankLeOne v he
  __ := ‹v.IsNontrivial›

/-- **`IsRankOneDiscrete ⟹ RatRankLeOne`.**  A discrete value group `≅ ℤᵐ⁰` embeds into `ℚᵐ⁰`
via `ℤ ↪ ℚ`, so a discrete valuation automatically has rational rank ≤ 1. -/
noncomputable instance [v.IsRankOneDiscrete] : v.RatRankLeOne where
  hom := (withZeroMultMap (Int.castAddHom ℚ)).comp
    (valueGroup₀_equiv_withZeroMulInt v).toMonoidWithZeroHom
  strictMono := by
    have hf : StrictMono (Int.castAddHom ℚ) := fun a b h => by simpa using Int.cast_lt.mpr h
    exact (withZeroMultMap_strictMono hf).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)

end Coherence

section RatRankAddVal

variable {L Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [Ring L] (v : Valuation L Γ)
  [v.RatRankLeOne]

/-- The image under the `RatRankLeOne` hom of a value-group element (a nonzero element of
`ValueGroup₀ v`) is nonzero. -/
private lemma ratHom_coe_ne_zero (u : MonoidWithZeroHom.valueGroup v) :
    RatRankLeOne.hom (v := v) (u : MonoidWithZeroHom.ValueGroup₀ v) ≠ 0 := fun h =>
  WithZero.coe_ne_zero ((RatRankLeOne.strictMono (v := v)).injective (h.trans (map_zero _).symm))

/-- **The value group of a rational-rank-one valuation, realised inside `(ℚ, +)`.**  The
order-preserving additive embedding `Additive (valueGroup v) →+ ℚ` sending `g` to the exponent of the
(nonzero) value `RatRankLeOne.hom v g ∈ ℚᵐ⁰`.  The `ℚ` analogue of `RankOne.valueGroupLog`. -/
noncomputable def RatRankLeOne.valueGroupRat : Additive (MonoidWithZeroHom.valueGroup v) →+ ℚ where
  toFun g := Multiplicative.toAdd (WithZero.unzero (ratHom_coe_ne_zero v (Additive.toMul g)))
  map_zero' := by
    rw [toAdd_eq_zero, ← WithZero.coe_inj, WithZero.coe_unzero, WithZero.coe_one, toMul_zero,
      WithZero.coe_one, map_one]
  map_add' g h := by
    have key : WithZero.unzero (ratHom_coe_ne_zero v (Additive.toMul (g + h)))
        = WithZero.unzero (ratHom_coe_ne_zero v (Additive.toMul g))
          * WithZero.unzero (ratHom_coe_ne_zero v (Additive.toMul h)) := by
      rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero,
        WithZero.coe_unzero, toMul_add, WithZero.coe_mul, map_mul]
    rw [key, toAdd_mul]

lemma RatRankLeOne.valueGroupRat_strictMono : StrictMono (RatRankLeOne.valueGroupRat v) := by
  intro g h hgh
  simp only [RatRankLeOne.valueGroupRat, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Multiplicative.toAdd_lt, ← WithZero.coe_lt_coe, WithZero.coe_unzero, WithZero.coe_unzero]
  exact (RatRankLeOne.strictMono (v := v)) (WithZero.coe_lt_coe.mpr (Additive.toMul_lt.mpr hgh))

/-- **The rational additive valuation on a rational-rank-one valuation**, valued in `WithTop ℚ`
(`= ℚ ∪ {∞}`) with `⊤` at `0`.  Obtained from the general `AddVal_withTopValGroup` by pushing its
values along the embedding `valueGroupRat`; needs only a `Ring`.  The density analogue of
`RankOne.addVal`. -/
noncomputable def RatRankLeOne.addValQ : AddValuation L (WithTop ℚ) :=
  (AddVal_withTopValGroup v).map (AddMonoidHom.withTopMap (RatRankLeOne.valueGroupRat v)) rfl
    (monotone_withTop_map (RatRankLeOne.valueGroupRat_strictMono v).monotone)

@[simp]
lemma RatRankLeOne.addValQ_apply (x : L) :
    RatRankLeOne.addValQ v x
      = WithTop.map (RatRankLeOne.valueGroupRat v) (AddVal_withTopValGroup v x) := rfl

@[simp]
lemma RatRankLeOne.addValQ_zero : RatRankLeOne.addValQ v 0 = ⊤ := AddValuation.map_zero _

/-!
### Compatibility `ℚ → ℝ`

Since `RatRankLeOne` (with nontriviality) implies `RankOne` via `Valuation.RatRankLeOne.toRankOne`
for any exponential base `1 < e`, the real additive valuation `RankOne.addVal` is available with no
`RankOne` hypothesis, and it is `addValQ` postcomposed with `q ↦ q * log e`: the `ℚ`-valued
valuation and `-log ‖·‖` are literally the same, up to the scale factor `log e` coming from the
choice of base.  (At `e = exp 1` the scaling is plain `Rat.cast`.)
-/

/-- On a nonzero element, `ratToNNReal` is `e ^ (unzero x).toAdd`. -/
lemma ratToNNReal_apply_of_ne_zero {e : ℝ≥0} (he : e ≠ 0)
    {x : WithZero (Multiplicative ℚ)} (hx : x ≠ 0) :
    ratToNNReal he x = e ^ (((WithZero.unzero hx).toAdd : ℚ) : ℝ) := dif_neg hx

/-- **The two value-group realisations agree up to `log e`.**  With the `RankOne` structure induced
by `RatRankLeOne` at exponential base `e`, on the value group the real logarithm `valueGroupLog` is
the rational exponent `valueGroupRat` times `log e`. -/
lemma RankOne.valueGroupLog_eq_valueGroupRat [v.IsNontrivial] {e : ℝ≥0} (he : 1 < e)
    (g : Additive (MonoidWithZeroHom.valueGroup v)) :
    letI := Valuation.RatRankLeOne.toRankOne v he
    RankOne.valueGroupLog v g = ((RatRankLeOne.valueGroupRat v g : ℚ) : ℝ) * Real.log e := by
  letI := Valuation.RatRankLeOne.toRankOne v he
  have he' : (0 : ℝ) < e := by exact_mod_cast zero_lt_one.trans he
  simp only [RankOne.valueGroupLog, RatRankLeOne.valueGroupRat, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  rw [show RankOne.hom v = (ratToNNReal (ne_zero_of_lt he)).comp
      (Valuation.RatRankLeOne.hom (v := v)) from rfl,
    MonoidWithZeroHom.comp_apply,
    ratToNNReal_apply_of_ne_zero (ne_zero_of_lt he) (ratHom_coe_ne_zero v (Additive.toMul g)),
    NNReal.coe_rpow, Real.log_rpow he']

/-- **The compatibility square.**  With the `RankOne` structure induced by `RatRankLeOne` at
exponential base `e`, the real additive valuation is the rational one postcomposed with
`q ↦ q * log e`. -/
theorem RankOne.addVal_eq_map_addValQ [v.IsNontrivial] {e : ℝ≥0} (he : 1 < e) (x : L) :
    letI := Valuation.RatRankLeOne.toRankOne v he
    RankOne.addVal v x
      = WithTop.map (fun q : ℚ => (q : ℝ) * Real.log e) (RatRankLeOne.addValQ v x) := by
  letI := Valuation.RatRankLeOne.toRankOne v he
  rw [RankOne.addVal_apply, RatRankLeOne.addValQ_apply]
  induction AddVal_withTopValGroup v x using WithTop.recTopCoe with
  | top => rfl
  | coe g =>
    rw [WithTop.map_coe, WithTop.map_coe, WithTop.map_coe, WithTop.coe_inj]
    exact RankOne.valueGroupLog_eq_valueGroupRat v he g

/-- **The absolute value is the base to the power of minus the rational additive valuation.**  For a
*given* rank-one structure on the rational-rank-one valuation `v`, if the norm-defining hom factors as
the exponential `ratToNNReal` (base `e`) composed with the `RatRankLeOne` embedding (`hb`), and the
`ℚ`-valued additive valuation of `x` is the rational `q` (`addValQ v x = q`), then the `ℝ≥0`-valued
absolute value `RankOne.hom v (v.restrict x)` equals `e ^ (-q)`.  The `ℂ_p`/`rpow` analogue of the
discrete `hom_eq_base_zpow_neg_addValZ`; stated about the `ℝ≥0`-hom, so it holds over any `Ring`.  Here
the value group is dense (no uniformizer), so this needs the full factorization `hb` rather than a
single scalar. -/
theorem hom_eq_base_rpow_neg_addValQ [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
    (hb : RankOne.hom v = (ratToNNReal he).comp (Valuation.RatRankLeOne.hom (v := v)))
    {x : L} {q : ℚ} (hq : RatRankLeOne.addValQ v x = (q : WithTop ℚ)) :
    RankOne.hom v (v.restrict x) = e ^ (-(q : ℝ)) := by
  have hr : v.restrict x ≠ 0 := by
    intro h
    rw [show RatRankLeOne.addValQ v x = ⊤ by
      rw [RatRankLeOne.addValQ_apply, AddVal_withTopValGroup_apply,
        Valuation.toAddValuation_apply, h]; rfl] at hq
    exact absurd hq (by simp)
  obtain ⟨w, hw⟩ : ∃ w : MonoidWithZeroHom.valueGroup v,
      v.restrict x = ((w : MonoidWithZeroHom.valueGroup v) : MonoidWithZeroHom.ValueGroup₀ v) :=
    ⟨WithZero.unzero hr, (WithZero.coe_unzero hr).symm⟩
  have hq' : RatRankLeOne.valueGroupRat v (Additive.ofMul w) = -q := by
    have hA : RatRankLeOne.addValQ v x
        = ((RatRankLeOne.valueGroupRat v (-(Additive.ofMul w)) : ℚ) : WithTop ℚ) := by
      rw [RatRankLeOne.addValQ_apply, AddVal_withTopValGroup_apply,
        Valuation.toAddValuation_apply, hw]; rfl
    rw [hA, show RatRankLeOne.valueGroupRat v (-(Additive.ofMul w))
          = -(RatRankLeOne.valueGroupRat v (Additive.ofMul w)) from _root_.map_neg _ _,
      WithTop.coe_inj] at hq
    linarith
  rw [hb, MonoidWithZeroHom.comp_apply, hw,
    ratToNNReal_apply_of_ne_zero he (ratHom_coe_ne_zero v w),
    show (WithZero.unzero (ratHom_coe_ne_zero v w)).toAdd
        = RatRankLeOne.valueGroupRat v (Additive.ofMul w) from rfl,
    hq', Rat.cast_neg]

end RatRankAddVal

/-!
## The discrete refinement: an honest `ℤ`-valued additive valuation

When `v` is *discretely* valued (`v.IsRankOneDiscrete`), its value group is infinite cyclic, so
Mathlib's order isomorphism `ValueGroup₀ v ≃* ℤᵐ⁰` realises `Additive (valueGroup v)` inside `(ℤ, +)`.
As before we push the general `AddVal_withTopValGroup` along that embedding
(`IsRankOneDiscrete.valueGroupInt`) to get an honest `ℤ`-valued additive valuation.  It includes into
the rational one of the previous section (`addValQ = map Int.cast addValZ`), which in turn includes
into the real `addVal` — completing the chain `WithTop ℤ → WithTop ℚ → WithTop ℝ`.
-/

section DiscreteAddVal

open Valuation.IsRankOneDiscrete

variable {L Γ : Type*} [LinearOrderedCommGroupWithZero Γ] [Ring L] (v : Valuation L Γ)
  [v.IsRankOneDiscrete]

/-- The image under the discrete isomorphism `ValueGroup₀ v ≃* ℤᵐ⁰` of a value-group element
(a nonzero element of `ValueGroup₀ v`) is nonzero. -/
private lemma zmEquiv_coe_ne_zero (u : MonoidWithZeroHom.valueGroup v) :
    valueGroup₀_equiv_withZeroMulInt v (u : MonoidWithZeroHom.ValueGroup₀ v) ≠ 0 := fun h =>
  WithZero.coe_ne_zero ((valueGroup₀_equiv_withZeroMulInt v).injective
    (h.trans (valueGroup₀_equiv_withZeroMulInt_apply_zero v).symm))

/-- **The value group of a discrete valuation, realised inside `(ℤ, +)`.**  The order-preserving
additive embedding `Additive (valueGroup v) →+ ℤ` reading off the exponent of the (nonzero) value of
the discrete isomorphism `ValueGroup₀ v ≃* ℤᵐ⁰`.  The `ℤ` analogue of `RatRankLeOne.valueGroupRat`. -/
noncomputable def IsRankOneDiscrete.valueGroupInt :
    Additive (MonoidWithZeroHom.valueGroup v) →+ ℤ where
  toFun g := Multiplicative.toAdd (WithZero.unzero (zmEquiv_coe_ne_zero v (Additive.toMul g)))
  map_zero' := by
    rw [toAdd_eq_zero, ← WithZero.coe_inj, WithZero.coe_unzero, WithZero.coe_one, toMul_zero,
      WithZero.coe_one, map_one]
  map_add' g h := by
    have key : WithZero.unzero (zmEquiv_coe_ne_zero v (Additive.toMul (g + h)))
        = WithZero.unzero (zmEquiv_coe_ne_zero v (Additive.toMul g))
          * WithZero.unzero (zmEquiv_coe_ne_zero v (Additive.toMul h)) := by
      rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero,
        WithZero.coe_unzero, toMul_add, WithZero.coe_mul, map_mul]
    rw [key, toAdd_mul]

lemma IsRankOneDiscrete.valueGroupInt_strictMono :
    StrictMono (IsRankOneDiscrete.valueGroupInt v) := by
  intro g h hgh
  simp only [IsRankOneDiscrete.valueGroupInt, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Multiplicative.toAdd_lt, ← WithZero.coe_lt_coe, WithZero.coe_unzero, WithZero.coe_unzero]
  exact (valueGroup₀_equiv_withZeroMulInt_strictMono v)
    (WithZero.coe_lt_coe.mpr (Additive.toMul_lt.mpr hgh))

/-- **The honest `ℤ`-valued additive valuation on a discrete valuation**, valued in `WithTop ℤ`
(`= ℤ ∪ {∞}`) with `⊤` at `0`.  Obtained from the general `AddVal_withTopValGroup` by pushing its
values along the embedding `valueGroupInt`.  The discrete analogue of `RatRankLeOne.addValQ`. -/
noncomputable def IsRankOneDiscrete.addValZ : AddValuation L (WithTop ℤ) :=
  (AddVal_withTopValGroup v).map (AddMonoidHom.withTopMap (IsRankOneDiscrete.valueGroupInt v)) rfl
    (monotone_withTop_map (IsRankOneDiscrete.valueGroupInt_strictMono v).monotone)

@[simp]
lemma IsRankOneDiscrete.addValZ_apply (x : L) :
    IsRankOneDiscrete.addValZ v x
      = WithTop.map (IsRankOneDiscrete.valueGroupInt v) (AddVal_withTopValGroup v x) := rfl

@[simp]
lemma IsRankOneDiscrete.addValZ_zero : IsRankOneDiscrete.addValZ v 0 = ⊤ := AddValuation.map_zero _

/-- On the value group, the rational realisation `valueGroupRat` is the integer realisation
`valueGroupInt` composed with `ℤ ↪ ℚ` (the two agree via `Int.cast`). -/
lemma valueGroupRat_eq_castInt (g : Additive (MonoidWithZeroHom.valueGroup v)) :
    RatRankLeOne.valueGroupRat v g = ((IsRankOneDiscrete.valueGroupInt v g : ℤ) : ℚ) := by
  -- The coe of `ofAdd` of each realisation is the corresponding value-group hom.
  have hR : RatRankLeOne.hom (v := v)
        ((Additive.toMul g : MonoidWithZeroHom.valueGroup v) : MonoidWithZeroHom.ValueGroup₀ v)
      = ↑(Multiplicative.ofAdd (RatRankLeOne.valueGroupRat v g)) := by
    simp only [RatRankLeOne.valueGroupRat, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ofAdd_toAdd,
      WithZero.coe_unzero]
  have hZ : valueGroup₀_equiv_withZeroMulInt v
        ((Additive.toMul g : MonoidWithZeroHom.valueGroup v) : MonoidWithZeroHom.ValueGroup₀ v)
      = ↑(Multiplicative.ofAdd (IsRankOneDiscrete.valueGroupInt v g)) := by
    simp only [IsRankOneDiscrete.valueGroupInt, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ofAdd_toAdd,
      WithZero.coe_unzero]
  -- `RatRankLeOne.hom = withZeroMultMap (Int.cast) ∘ equiv` (the discrete instance), by `rfl`;
  -- rewrite the two realisations into it (entangled terms only appear as replacements).
  have hcomp : RatRankLeOne.hom (v := v)
        ((Additive.toMul g : MonoidWithZeroHom.valueGroup v) : MonoidWithZeroHom.ValueGroup₀ v)
      = withZeroMultMap (Int.castAddHom ℚ) (valueGroup₀_equiv_withZeroMulInt v
          ((Additive.toMul g : MonoidWithZeroHom.valueGroup v) : MonoidWithZeroHom.ValueGroup₀ v)) :=
    rfl
  rw [hR, hZ, withZeroMultMap, WithZero.map'_coe, AddMonoidHom.coe_toMultiplicative] at hcomp
  simp only [Function.comp_apply, toAdd_ofAdd] at hcomp
  have h2 : RatRankLeOne.valueGroupRat v g
      = (Int.castAddHom ℚ) (IsRankOneDiscrete.valueGroupInt v g) :=
    Multiplicative.ofAdd.injective (WithZero.coe_inj.mp hcomp)
  rw [h2, Int.coe_castAddHom]

/-- **Inclusion `WithTop ℤ → WithTop ℚ`.**  For a discrete valuation, the ℚ-valued additive
valuation is the honest ℤ-valued one composed with `WithTop.map (Int.cast)`. -/
theorem addValQ_eq_map_addValZ (x : L) :
    RatRankLeOne.addValQ v x
      = WithTop.map (fun n : ℤ => (n : ℚ)) (IsRankOneDiscrete.addValZ v x) := by
  rw [RatRankLeOne.addValQ_apply, IsRankOneDiscrete.addValZ_apply]
  induction AddVal_withTopValGroup v x using WithTop.recTopCoe with
  | top => rfl
  | coe g =>
    rw [WithTop.map_coe, WithTop.map_coe, WithTop.map_coe, WithTop.coe_inj]
    exact valueGroupRat_eq_castInt v g

/-- `WithZeroMulInt.toNNReal` sends `exp n ↦ eⁿ`. -/
private lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n :=
  WithZeroMulInt.toNNReal_neg_apply he (WithZero.exp_ne_zero (a := n))

/-- **The factorization follows from one scalar.**  On a discrete valuation the value group is
infinite cyclic, so a `→*₀` hom out of it is determined by its value on the generator.  Hence, to
know that a *given* `RankOne.hom v` is "`exp` in base `e`", it suffices that the uniformizer has norm
`e⁻¹`, i.e. `RankOne.hom v (generator') = e⁻¹`. -/
lemma hb_of_norm_generator [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : MonoidWithZeroHom.ValueGroup₀ v) = e⁻¹) :
    RankOne.hom v = (WithZeroMulInt.toNNReal he).comp
      (valueGroup₀_equiv_withZeroMulInt v).toMonoidWithZeroHom := by
  apply MonoidWithZeroHom.ext
  intro γ
  induction γ using WithZero.recZeroCoe with
  | zero => simp
  | coe u =>
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, generator' v ^ k = u := by
      have hu : u ∈ Subgroup.zpowers (generator' v) := by
        rw [generator'_zpowers_eq_top]; exact Subgroup.mem_top u
      exact Subgroup.mem_zpowers_iff.mp hu
    rw [MonoidWithZeroHom.comp_apply, MulEquiv.toMonoidWithZeroHom_apply, WithZero.coe_zpow,
      valueGroup₀_equiv_withZeroMulInt_apply_zpow, toNNReal_exp he, map_zpow₀, hgen,
      inv_zpow, ← zpow_neg]

/-- **The absolute value is the base to the power of minus the ℤ-valued additive valuation.**  For a
*given* rank-one structure on the discrete valuation `v`, if a uniformizer has norm `e⁻¹`
(`RankOne.hom v (generator') = e⁻¹`, which pins the base `e = ‖ϖ‖⁻¹`) and the honest ℤ-valued additive
valuation of `x` is the integer `d` (`addValZ v x = d`), then `RankOne.hom v (v.restrict x) = e ^ (-d)`.
The discrete analogue of `hom_eq_base_rpow_neg_addValQ`: here the value group is cyclic, so the whole
norm is determined by the single scalar `hgen` (`hb_of_norm_generator`), rather than by a chosen base
or full factorization. -/
theorem hom_eq_base_zpow_neg_addValZ [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : MonoidWithZeroHom.ValueGroup₀ v) = e⁻¹)
    {x : L} {d : ℤ} (hd : IsRankOneDiscrete.addValZ v x = (d : WithTop ℤ)) :
    RankOne.hom v (v.restrict x) = e ^ (-d) := by
  have hr : v.restrict x ≠ 0 := by
    intro h
    rw [show IsRankOneDiscrete.addValZ v x = ⊤ by
      rw [IsRankOneDiscrete.addValZ_apply, AddVal_withTopValGroup_apply,
        Valuation.toAddValuation_apply, h]; rfl] at hd
    exact absurd hd (by simp)
  obtain ⟨w, hw⟩ : ∃ w : MonoidWithZeroHom.valueGroup v,
      v.restrict x = ((w : MonoidWithZeroHom.valueGroup v) : MonoidWithZeroHom.ValueGroup₀ v) :=
    ⟨WithZero.unzero hr, (WithZero.coe_unzero hr).symm⟩
  have hd' : IsRankOneDiscrete.valueGroupInt v (Additive.ofMul w) = -d := by
    have hA : IsRankOneDiscrete.addValZ v x
        = ((IsRankOneDiscrete.valueGroupInt v (-(Additive.ofMul w)) : ℤ) : WithTop ℤ) := by
      rw [IsRankOneDiscrete.addValZ_apply, AddVal_withTopValGroup_apply,
        Valuation.toAddValuation_apply, hw]; rfl
    rw [hA, show IsRankOneDiscrete.valueGroupInt v (-(Additive.ofMul w))
          = -(IsRankOneDiscrete.valueGroupInt v (Additive.ofMul w)) from _root_.map_neg _ _,
      WithTop.coe_inj] at hd
    linarith
  rw [hb_of_norm_generator v he hgen, MonoidWithZeroHom.comp_apply,
    MulEquiv.toMonoidWithZeroHom_apply, hw,
    WithZeroMulInt.toNNReal_neg_apply he (zmEquiv_coe_ne_zero v w),
    show (WithZero.unzero (zmEquiv_coe_ne_zero v w)).toAdd
        = IsRankOneDiscrete.valueGroupInt v (Additive.ofMul w) from rfl, hd']

end DiscreteAddVal

/-!
## Application: ultrametric normed fields

Specialising to the canonical valuation `NormedField.valuation = ‖·‖₊` of an ultrametric normed field
(which carries a `RankOne` instance whose hom is the value-group embedding into `ℝ≥0`) turns the
abstract additive valuations into honest `ℤ`- and `ℚ`-valued additive valuations on the field, and the
norm-recovery theorems into `‖x‖ = e ^ (-v(x))`.
-/

section NormedField

open NormedField

variable (R : Type*) [NontriviallyNormedField R] [IsUltrametricDist R]

/-- The real-valued norm attached to `NormedField.valuation` is just `‖·‖`. -/
@[simp]
lemma valuation_norm_eq (x : R) : (NormedField.valuation (K := R)).norm x = ‖x‖ := by
  rw [← coe_nnnorm, ← valuation_apply (K := R) x,
    ← (NormedField.valuation (K := R)).embedding_restrict x]
  rfl

/-- On any ultrametric normed field, `‖x‖ = ↑(RankOne.hom (valuation) (valuation.restrict x))`. -/
private lemma norm_eq_coe_hom (x : R) :
    ‖x‖ = ((RankOne.hom (NormedField.valuation (K := R))
      ((NormedField.valuation (K := R)).restrict x) : ℝ≥0) : ℝ) := by
  rw [← valuation_norm_eq R x]; rfl

/-!
### The discrete (`ℚ_p`-style) case
-/

/-- When the norm is discretely valued, the honest `ℤ`-valued additive valuation on the field, as an
instance of `IsRankOneDiscrete.addValZ`. -/
noncomputable def normAddValZ [(NormedField.valuation (K := R)).IsRankOneDiscrete] :
    AddValuation R (WithTop ℤ) :=
  IsRankOneDiscrete.addValZ (NormedField.valuation (K := R))

@[simp]
lemma normAddValZ_zero [(NormedField.valuation (K := R)).IsRankOneDiscrete] :
    normAddValZ R 0 = ⊤ := AddValuation.map_zero _

/-- **The norm is the base to the power of minus the additive valuation.**  If a uniformizer has norm
`e⁻¹` (`hgen`, which pins `e = ‖ϖ‖⁻¹`) and `x` has integer additive valuation `d` (`normAddValZ R x = d`),
then `‖x‖ = e ^ (-d)`.  For the standard `p`-adic norm `e = p`, so `‖x‖ = p ^ (-vₚ(x))`. -/
theorem norm_eq_base_zpow_neg_normAddValZ
    [(NormedField.valuation (K := R)).IsRankOneDiscrete] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom (NormedField.valuation (K := R))
      (Valuation.IsRankOneDiscrete.generator' (NormedField.valuation (K := R))
        : MonoidWithZeroHom.ValueGroup₀ (NormedField.valuation (K := R))) = e⁻¹)
    {x : R} {d : ℤ} (hd : normAddValZ R x = (d : WithTop ℤ)) :
    ‖x‖ = (e : ℝ) ^ (-d) := by
  rw [norm_eq_coe_hom R x,
    hom_eq_base_zpow_neg_addValZ (NormedField.valuation (K := R)) he hgen hd, NNReal.coe_zpow]

/-!
### The rational-rank-one (`ℂ_p`-style) case
-/

/-- When the norm has rational rank ≤ 1, the honest `ℚ`-valued additive valuation on the field, as an
instance of `RatRankLeOne.addValQ`.  Valued in `ℚ ∪ {∞}` (the `ℂ_p`-style case). -/
noncomputable def normAddValQ [(NormedField.valuation (K := R)).RatRankLeOne] :
    AddValuation R (WithTop ℚ) :=
  RatRankLeOne.addValQ (NormedField.valuation (K := R))

@[simp]
lemma normAddValQ_zero [(NormedField.valuation (K := R)).RatRankLeOne] :
    normAddValQ R 0 = ⊤ := AddValuation.map_zero _

/-- **The norm is the base to the power of minus the additive valuation (rational-rank case).**  If the
norm factors through the `RatRankLeOne` embedding as the exponential of base `e` (`hb`) and `x` has
`ℚ`-valued additive valuation `q` (`normAddValQ R x = q`), then `‖x‖ = e ^ (-q)`.  The `ℚ`/`rpow`
analogue of `norm_eq_base_zpow_neg_normAddValZ`. -/
theorem norm_eq_base_rpow_neg_normAddValQ
    [(NormedField.valuation (K := R)).RatRankLeOne] {e : ℝ≥0} (he : e ≠ 0)
    (hb : RankOne.hom (NormedField.valuation (K := R))
      = (ratToNNReal he).comp (Valuation.RatRankLeOne.hom (v := NormedField.valuation (K := R))))
    {x : R} {q : ℚ} (hq : normAddValQ R x = (q : WithTop ℚ)) :
    ‖x‖ = (e : ℝ) ^ (-(q : ℝ)) := by
  rw [norm_eq_coe_hom R x,
    hom_eq_base_rpow_neg_addValQ (NormedField.valuation (K := R)) he hb hq, NNReal.coe_rpow]

end NormedField

/-!
## `ℚ_p`: our `ℤ`-valued additive valuation is the `p`-adic valuation

The final piece.  We supply the missing `IsRankOneDiscrete` data for the `p`-adic norm (its value
group is the infinite cyclic group generated by `‖p‖₊ = p⁻¹`) and verify that `normAddValZ ℚ_[p]`
— the honest `ℤ`-valued additive valuation produced by the abstract machinery — coincides with
Mathlib's `Padic.addValuationDef` (`vₚ`, with `⊤` at `0`).
-/

section Padic

open NormedField MonoidWithZeroHom Valuation.IsRankOneDiscrete WithZero

variable {p : ℕ} [Fact p.Prime]

private lemma padic_p_ne : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

private lemma padic_nnnorm_p_ne : ‖(p : ℚ_[p])‖₊ ≠ 0 := by simpa using padic_p_ne (p := p)

/-- The generator `‖p‖₊ = p⁻¹` of the value group of the `p`-adic norm. -/
private noncomputable def padicGen : valueGroup (NormedField.valuation (K := ℚ_[p])) :=
  ⟨Units.mk0 ‖(p : ℚ_[p])‖₊ padic_nnnorm_p_ne, mem_valueGroup _ ⟨(p : ℚ_[p]), rfl⟩⟩

private lemma padic_norm_zpow_valuation (x : ℚ_[p]) (hx : x ≠ 0) :
    ‖(p : ℚ_[p])‖₊ ^ x.valuation = ‖x‖₊ := by
  rw [← NNReal.coe_inj]
  push_cast
  rw [Padic.norm_eq_zpow_neg_valuation hx,
    Padic.norm_eq_zpow_neg_valuation (padic_p_ne (p := p)), Padic.valuation_p, ← zpow_mul]
  ring_nf

private lemma padic_zpowers_gen : Subgroup.zpowers (padicGen (p := p)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro y
  rw [Subgroup.mem_zpowers_iff]
  have hy : (y : ℝ≥0ˣ).val ∈ Units.val '' (valueGroup (NormedField.valuation (K := ℚ_[p]))) :=
    ⟨y, y.2, rfl⟩
  rw [valueGroup_eq_range] at hy
  obtain ⟨⟨x, hx⟩, hne⟩ := hy
  simp only [Set.mem_singleton_iff] at hne
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hne (by rw [← hx]; simp [NormedField.valuation])
  refine ⟨x.valuation, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have hg : ((padicGen (p := p)) : ℝ≥0ˣ).val = ‖(p : ℚ_[p])‖₊ := rfl
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val, hg, padic_norm_zpow_valuation x hx0,
    ← hx]
  rfl

instance : IsCyclic (valueGroup (NormedField.valuation (K := ℚ_[p]))) :=
  isCyclic_iff_exists_zpowers_eq_top.mpr ⟨padicGen, padic_zpowers_gen⟩

instance : Nontrivial (valueGroup (NormedField.valuation (K := ℚ_[p]))) := by
  refine ⟨padicGen, 1, ?_⟩
  intro h
  have hval : ‖(p : ℚ_[p])‖₊ = 1 := by
    have := congrArg
      (fun z : valueGroup (NormedField.valuation (K := ℚ_[p])) => ((z : ℝ≥0ˣ) : ℝ≥0)) h
    simpa [padicGen] using this
  have h1 : ‖(p : ℚ_[p])‖ = 1 := by rw [← coe_nnnorm, hval, NNReal.coe_one]
  exact absurd h1 (ne_of_lt Padic.norm_p_lt_one)

private lemma padicGen_lt_one : padicGen (p := p) < 1 := by
  have h : ‖(p : ℚ_[p])‖₊ < 1 := by exact_mod_cast Padic.norm_p_lt_one
  rw [← Subtype.coe_lt_coe]
  exact_mod_cast h

private lemma padic_generator'_eq :
    generator' (NormedField.valuation (K := ℚ_[p])) = padicGen := by
  refine LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq
    (generator'_lt_one _) padicGen_lt_one ?_
  rw [generator'_zpowers_eq_top, padic_zpowers_gen]

/-- The `p`-adic nnnorm of `p` is `p⁻¹`. -/
private lemma padic_nnnorm_p : ‖(p : ℚ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by
  rw [← NNReal.coe_inj]; push_cast; exact Padic.norm_p

/-- The value-group generator of the `p`-adic norm has underlying value `‖p‖₊ = p⁻¹`. -/
private lemma padic_generator_eq :
    (generator (NormedField.valuation (K := ℚ_[p])) : ℝ≥0) = (p : ℝ≥0)⁻¹ := by
  have h := congrArg
    (fun u : valueGroup (NormedField.valuation (K := ℚ_[p])) => ((u : ℝ≥0ˣ) : ℝ≥0))
    padic_generator'_eq
  rw [← padic_nnnorm_p]
  simpa [padicGen] using h

/-- **The scalar hypothesis, discharged for `ℚ_p`**: a uniformizer has norm `p⁻¹`, i.e.
`RankOne.hom (valuation) (generator') = p⁻¹`.  This is essentially `Padic.norm_p`. -/
private lemma hgen_padic :
    RankOne.hom (NormedField.valuation (K := ℚ_[p]))
      (generator' (NormedField.valuation (K := ℚ_[p]))
        : MonoidWithZeroHom.ValueGroup₀ (NormedField.valuation (K := ℚ_[p]))) = (p : ℝ≥0)⁻¹ := by
  rw [show RankOne.hom (NormedField.valuation (K := ℚ_[p]))
        (generator' (NormedField.valuation (K := ℚ_[p]))
          : MonoidWithZeroHom.ValueGroup₀ (NormedField.valuation (K := ℚ_[p])))
        = (generator (NormedField.valuation (K := ℚ_[p])) : ℝ≥0) from embedding_generator' _,
    padic_generator_eq]

/-- **The `p`-adic norm is `p` to the power of minus our additive valuation.**  If
`normAddValZ ℚ_[p] x = d` then `‖x‖ = p ^ (-d)`.  Instance of `norm_eq_base_zpow_neg_normAddValZ` at
`e = p`, with the scalar hypothesis `hgen_padic`. -/
theorem padic_norm_eq_zpow_neg_normAddValZ {x : ℚ_[p]} {d : ℤ}
    (hd : normAddValZ ℚ_[p] x = (d : WithTop ℤ)) : ‖x‖ = (p : ℝ) ^ (-d) := by
  have h := norm_eq_base_zpow_neg_normAddValZ (R := ℚ_[p]) (e := (p : ℝ≥0))
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero) hgen_padic hd
  simpa using h

/-- **The verification.**  On `ℚ_p`, `normAddValZ` (from the abstract machinery) is exactly the
additive `p`-adic valuation `Padic.addValuationDef` (`vₚ`, with `⊤` at `0`).  Deduced from the norm
characterization: `p ^ (-normAddValZ x) = ‖x‖ = p ^ (-vₚ(x))` and `p > 1`. -/
theorem normAddValZ_padic (x : ℚ_[p]) :
    normAddValZ ℚ_[p] x = Padic.addValuationDef x := by
  by_cases hx : x = 0
  · subst hx; rw [normAddValZ_zero, Padic.addValuationDef, if_pos rfl]
  · obtain ⟨d, hd⟩ : ∃ d : ℤ, normAddValZ ℚ_[p] x = (d : WithTop ℤ) := by
      have hr : (NormedField.valuation (K := ℚ_[p])).restrict x ≠ 0 :=
        (NormedField.valuation (K := ℚ_[p])).restrict.ne_zero_iff.mpr hx
      obtain ⟨w, hw⟩ : ∃ w : MonoidWithZeroHom.valueGroup (NormedField.valuation (K := ℚ_[p])),
          (NormedField.valuation (K := ℚ_[p])).restrict x
            = ((w : MonoidWithZeroHom.valueGroup (NormedField.valuation (K := ℚ_[p]))) :
                MonoidWithZeroHom.ValueGroup₀ (NormedField.valuation (K := ℚ_[p]))) :=
        ⟨WithZero.unzero hr, (WithZero.coe_unzero hr).symm⟩
      refine ⟨IsRankOneDiscrete.valueGroupInt (NormedField.valuation (K := ℚ_[p]))
        (-(Additive.ofMul w)), ?_⟩
      show IsRankOneDiscrete.addValZ (NormedField.valuation (K := ℚ_[p])) x = _
      rw [IsRankOneDiscrete.addValZ_apply, AddVal_withTopValGroup_apply,
        Valuation.toAddValuation_apply, hw]
      rfl
    rw [hd, Padic.addValuationDef, if_neg hx]
    congr 1
    have hn1 := padic_norm_eq_zpow_neg_normAddValZ hd
    have hn2 := Padic.norm_eq_zpow_neg_valuation hx
    have hpp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hinj := (zpow_right_strictMono₀ hpp).injective (hn1.symm.trans hn2)
    omega

end Padic

#min_imports
