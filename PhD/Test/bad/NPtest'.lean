import PhD.ToPR.NewtonPolygon
import PhD.ToPR.GaussNorm
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Order.Monoid.ToMulBot
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace NewtonPolygon

open Valuation

open scoped NNReal WithZero


variable {R : Type*} [NormedField R] [IsUltrametricDist R]

noncomputable
abbrev normValuation : Valuation R ℝ≥0 := NormedField.valuation

/-!
## The general (rank one) additive valuation: `-log ‖·‖`, valued in `WithTop ℝ`

This construction only uses that the norm is multiplicative and ultrametric, so it makes sense
for *any* ultrametric normed field, discretely valued or not.  In particular it covers both
`ℚ_p` (value group `p^ℤ`, discrete) and `ℂ_p` (value group `p^ℚ`, dense).  For `x ≠ 0`,
`normAddVal x = -log ‖x‖`, and `normAddVal 0 = ⊤ = +∞`.
-/

open Classical in
/-- The rank-one additive valuation attached to the ultrametric norm, `x ↦ -log ‖x‖`, valued in
`WithTop ℝ` with `⊤` (i.e. `+∞`) at `0`.  Works for `ℚ_p` and `ℂ_p` alike. -/
noncomputable def normAddVal : AddValuation R (WithTop ℝ) :=
  AddValuation.of
    (fun x => if x = 0 then (⊤ : WithTop ℝ) else ((-Real.log ‖x‖ : ℝ) : WithTop ℝ))
    (if_pos rfl)
    (by simp)
    (by
      intro x y
      dsimp only
      by_cases hx : x = 0
      · subst hx; rw [zero_add]; exact min_le_right _ _
      by_cases hy : y = 0
      · subst hy; rw [add_zero]; exact min_le_left _ _
      by_cases hxy : x + y = 0
      · rw [hxy]; simp
      rw [if_neg hx, if_neg hy, if_neg hxy]
      have hpos : 0 < ‖x + y‖ := norm_pos_iff.2 hxy
      have hmax : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
      rcases le_total ‖x‖ ‖y‖ with h | h
      · rw [max_eq_right h] at hmax
        exact (min_le_right _ _).trans (WithTop.coe_le_coe.2 (neg_le_neg (Real.log_le_log hpos hmax)))
      · rw [max_eq_left h] at hmax
        exact (min_le_left _ _).trans (WithTop.coe_le_coe.2 (neg_le_neg (Real.log_le_log hpos hmax))))
    (by
      intro x y
      dsimp only
      by_cases hx : x = 0
      · subst hx; rw [zero_mul]; simp
      by_cases hy : y = 0
      · subst hy; rw [mul_zero]; simp
      rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), neg_add, WithTop.coe_add])

@[simp]
lemma normAddVal_zero : normAddVal (R := R) 0 = ⊤ := if_pos rfl

lemma normAddVal_apply_of_ne_zero {x : R} (hx : x ≠ 0) :
    normAddVal (R := R) x = ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) := if_neg hx

/-!
## The discrete refinement: an honest `ℤ`-valued additive valuation

When (and only when) the norm is *discretely* valued — i.e. `normValuation` is `IsRankOneDiscrete`,
which holds for `ℚ_p` but **not** for `ℂ_p` — the value group is infinite cyclic, so we can push the
valuation onto `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` via Mathlib's order isomorphism of value groups,
and read off a genuine integer valuation.  Under `toAddValuation` this becomes an
`AddValuation R (Additive ℤᵐ⁰)ᵒᵈ`, Mathlib's standard `ℤ ∪ {∞}` additive value group.
-/

/-- Order isomorphism `(Additive ℤᵐ⁰)ᵒᵈ ≃o WithTop ℤ`, Mathlib's native additive value group for a
discrete valuation versus the familiar `ℤ ∪ {∞}`.  It sends `0 ↦ ⊤` and `coe (ofAdd n) ↦ -n`. -/
noncomputable def zmOrderIso : (Additive ℤᵐ⁰)ᵒᵈ ≃o WithTop ℤ where
  toFun x := WithZero.recZeroCoe (⊤ : WithTop ℤ)
      (fun n => ((-(Multiplicative.toAdd n) : ℤ) : WithTop ℤ)) x
  invFun y := WithTop.recTopCoe (0 : ℤᵐ⁰)
      (fun n => ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : ℤᵐ⁰)) y
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
  map_rel_iff' {a b} := by
    induction a using WithZero.recZeroCoe with
    | zero => induction b using WithZero.recZeroCoe with
      | zero => simp [Equiv.coe_fn_mk, WithZero.recZeroCoe, WithTop.recTopCoe]
      | coe m =>
        simp only [Equiv.coe_fn_mk, WithZero.recZeroCoe, WithTop.recTopCoe]
        refine ⟨fun h => absurd (top_le_iff.mp h) (by simp), fun h => ?_⟩
        exact absurd (h : (↑m : ℤᵐ⁰) ≤ 0) (WithZero.not_coe_le_zero m)
    | coe n => induction b using WithZero.recZeroCoe with
      | zero =>
        simp only [Equiv.coe_fn_mk, WithZero.recZeroCoe, WithTop.recTopCoe]
        exact ⟨fun _ => (WithZero.zero_le (n : ℤᵐ⁰)), fun _ => le_top⟩
      | coe m =>
        simp only [Equiv.coe_fn_mk, WithZero.recZeroCoe, WithTop.recTopCoe]
        rw [WithTop.coe_le_coe, neg_le_neg_iff]
        exact WithZero.coe_le_coe.symm

variable [hv : (normValuation (R := R)).IsRankOneDiscrete]

open Valuation.IsRankOneDiscrete in
/-- The discretely-valued norm, transported to a `ℤᵐ⁰`-valued valuation using the order
isomorphism `valueGroup₀ ≃* ℤᵐ⁰`.  Available only in the discrete (`IsRankOneDiscrete`) case. -/
noncomputable def normValZ : Valuation R ℤᵐ⁰ :=
  (normValuation (R := R)).restrict.map
    (valueGroup₀_equiv_withZeroMulInt (normValuation (R := R))).toMonoidWithZeroHom
    (valueGroup₀_equiv_withZeroMulInt_strictMono (normValuation (R := R))).monotone

/-- The additive `ℤ`-valued valuation on a discretely valued ultrametric field, valued in
`(Additive ℤᵐ⁰)ᵒᵈ` (Mathlib's `ℤ ∪ {∞}`).  This is the analogue of `Padic.addValuation`. -/
noncomputable def normAddValZ : AddValuation R (Additive ℤᵐ⁰)ᵒᵈ :=
  (normValZ (R := R)).toAddValuation

/-- The same discrete additive valuation, with its values translated through `zmOrderIso` into the
more familiar `WithTop ℤ` (`= ℤ ∪ {∞}`). -/
noncomputable def normAddValZWithTop : R → WithTop ℤ :=
  fun x => zmOrderIso (normAddValZ (R := R) x)

/-!
## `ℚ_p`: `normAddVal` reproduces `Padic.valuation`

The general real-valued `normAddVal` is defined for every ultrametric normed field, so we can check
it directly on `ℚ_p` (no discreteness hypothesis needed).  It recovers the additive `p`-adic
valuation `Padic.valuation`, scaled by the fixed constant `Real.log p` — exactly the normalization
that only the discrete case lets one divide out to land in `ℤ`.
-/

section Padic

open MonoidWithZeroHom

variable {p : ℕ} [Fact p.Prime]

/-- On `ℚ_p`, for `x ≠ 0`, `normAddVal x = vₚ(x) · log p`, where `vₚ = Padic.valuation`. -/
theorem normAddVal_padic (x : ℚ_[p]) (hx : x ≠ 0) :
    normAddVal x = (((x.valuation : ℝ) * Real.log p : ℝ) : WithTop ℝ) := by
  rw [normAddVal_apply_of_ne_zero hx, Padic.norm_eq_zpow_neg_valuation hx, Real.log_zpow]
  congr 1
  push_cast
  ring

/-!
### `ℚ_p` is discretely valued

Mathlib has no `IsRankOneDiscrete` instance for the `ℚ_p` norm valuation, so we supply it: the value
group of `‖·‖₊` is the infinite cyclic group generated by `‖p‖₊ = p⁻¹`.  This unblocks `normAddValZ`
and `normAddValZWithTop` at `R = ℚ_[p]`.
-/

private lemma padic_p_ne : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

private lemma padic_nnnorm_p_ne : ‖(p : ℚ_[p])‖₊ ≠ 0 := by simpa using padic_p_ne (p := p)

/-- The generator `‖p‖₊ = p⁻¹` of the value group of the `p`-adic norm. -/
private noncomputable def padicGen : valueGroup (normValuation (R := ℚ_[p])) :=
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
  have hy : (y : ℝ≥0ˣ).val ∈ Units.val '' (valueGroup (normValuation (R := ℚ_[p]))) :=
    ⟨y, y.2, rfl⟩
  rw [valueGroup_eq_range] at hy
  obtain ⟨⟨x, hx⟩, hne⟩ := hy
  simp only [Set.mem_singleton_iff] at hne
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hne (by rw [← hx]; simp [normValuation])
  refine ⟨x.valuation, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have hg : ((padicGen (p := p)) : ℝ≥0ˣ).val = ‖(p : ℚ_[p])‖₊ := rfl
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val, hg, padic_norm_zpow_valuation x hx0,
    ← hx]
  rfl

instance : IsCyclic (valueGroup (normValuation (R := ℚ_[p]))) :=
  isCyclic_iff_exists_zpowers_eq_top.mpr ⟨padicGen, padic_zpowers_gen⟩

instance : Nontrivial (valueGroup (normValuation (R := ℚ_[p]))) := by
  refine ⟨padicGen, 1, ?_⟩
  intro h
  have hval : ‖(p : ℚ_[p])‖₊ = 1 := by
    have := congrArg
      (fun z : valueGroup (normValuation (R := ℚ_[p])) => ((z : ℝ≥0ˣ) : ℝ≥0)) h
    simpa [padicGen] using this
  have h1 : ‖(p : ℚ_[p])‖ = 1 := by rw [← coe_nnnorm, hval, NNReal.coe_one]
  exact absurd h1 (ne_of_lt Padic.norm_p_lt_one)

/-- The `p`-adic norm valuation on `ℚ_p` is rank-one discrete. -/
noncomputable instance : (normValuation (R := ℚ_[p])).IsRankOneDiscrete :=
  IsRankOneDiscrete.mk' _

/-!
### `normAddValZ` reproduces `Padic.valuation`

With the instance in place, `normAddValZ`/`normAddValZWithTop` are well-formed on `ℚ_p`, and we
verify `normAddValZWithTop x = Padic.addValuationDef x`, i.e. it equals the honest additive
`p`-adic valuation `vₚ` (with `⊤` at `0`).
-/

open Valuation.IsRankOneDiscrete WithZero

private lemma padicGen_lt_one : padicGen (p := p) < 1 := by
  have h : ‖(p : ℚ_[p])‖₊ < 1 := by exact_mod_cast Padic.norm_p_lt_one
  rw [← Subtype.coe_lt_coe]
  exact_mod_cast h

private lemma padic_generator'_eq : generator' (normValuation (R := ℚ_[p])) = padicGen := by
  refine LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq
    (generator'_lt_one _) padicGen_lt_one ?_
  rw [generator'_zpowers_eq_top, padic_zpowers_gen]

private lemma padicGen_zpow_valuation (x : ℚ_[p]) (hx : x ≠ 0) :
    (padicGen (p := p)) ^ x.valuation
      = ⟨Units.mk0 ‖x‖₊ (nnnorm_ne_zero_iff.mpr hx), mem_valueGroup _ ⟨x, rfl⟩⟩ := by
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]
  exact padic_norm_zpow_valuation x hx

/-- On `ℚ_p`, for `x ≠ 0`, the `ℤᵐ⁰`-valued valuation is `normValZ x = exp(-vₚ(x))`. -/
private lemma normValZ_apply (x : ℚ_[p]) (hx : x ≠ 0) :
    normValZ x = WithZero.exp (-(x.valuation : ℤ)) := by
  have hne : normValuation (R := ℚ_[p]) x ≠ 0 := by simpa [normValuation] using hx
  have h1 : (⟨Units.mk0 (normValuation (R := ℚ_[p]) x) hne, mem_valueGroup _ ⟨x, rfl⟩⟩
      : valueGroup _) = generator' (normValuation (R := ℚ_[p])) ^ x.valuation := by
    rw [padic_generator'_eq, padicGen_zpow_valuation x hx]
    exact Subtype.ext (Units.ext rfl)
  rw [normValZ, Valuation.map_apply, MulEquiv.toMonoidWithZeroHom_apply]
  show (valueGroup₀_equiv_withZeroMulInt (normValuation (R := ℚ_[p])))
    (ValueGroup₀.restrict₀ (normValuation (R := ℚ_[p])) x) = _
  rw [ValueGroup₀.restrict₀_of_ne_zero hne, h1]
  exact valueGroup₀_equiv_withZeroMulInt_apply_zpow (normValuation (R := ℚ_[p])) x.valuation

private lemma zmOrderIso_zero :
    zmOrderIso (OrderDual.toDual (Additive.ofMul (0 : ℤᵐ⁰))) = ⊤ := rfl

private lemma zmOrderIso_exp (n : ℤ) :
    zmOrderIso (OrderDual.toDual (Additive.ofMul (WithZero.exp n))) = ((-n : ℤ) : WithTop ℤ) := rfl

/-- **The verification**: on `ℚ_p`, `normAddValZWithTop` is exactly the additive `p`-adic valuation
`Padic.addValuationDef` (which is `vₚ`, with `⊤` at `0`). -/
theorem normAddValZWithTop_padic (x : ℚ_[p]) :
    normAddValZWithTop x = Padic.addValuationDef x := by
  by_cases hx : x = 0
  · subst hx
    rw [Padic.addValuationDef, if_pos rfl, normAddValZWithTop, normAddValZ,
      Valuation.toAddValuation_apply, _root_.map_zero, zmOrderIso_zero]
  · rw [Padic.addValuationDef, if_neg hx, normAddValZWithTop, normAddValZ,
      Valuation.toAddValuation_apply, normValZ_apply x hx, zmOrderIso_exp, neg_neg]

end Padic


section foo 

variable {F Γ: Type*} [Field F] [LinearOrderedCommMonoidWithZero Γ] (v : Valuation F Γ)



end foo