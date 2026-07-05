import Mathlib

open Filter Set Valuation MonoidWithZeroHom

open scoped NNReal Uniformity Classical WithZero

variable {L Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-!
## The `NormedField` structure from a rank-one valuation (ValuativeRel analogue of `Valued.toNormedField`)

This is the only part that needs the valuative topology (`ValuativeRel`, `UniformSpace`,
`IsUniformAddGroup`, `IsValuativeTopology`, `Compatible`); everything below works with far fewer
hypotheses, so those instances live only in this section.
-/

section Construction

variable [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L] [IsValuativeTopology L]
  (v : Valuation L Γ) [v.Compatible] [hv : RankOne v]

set_option backward.isDefEq.respectTransparency false in
/-- The normed field structure determined by a rank one valuation that is compatible with a
valuative topology on `L`. This is the `ValuativeRel` analogue of `Valued.toNormedField`. -/
@[instance_reducible]
noncomputable def RankOne.toNormedField : NormedField L :=
  { (inferInstance : Field L) with
    norm := v.norm
    dist := fun x y => v.norm (x - y)
    dist_self := fun x => by
      simp only [sub_self, Valuation.norm, Valuation.map_zero, hv.hom.map_zero, NNReal.coe_zero]
    dist_comm := fun x y => by simp only [Valuation.norm]; rw [← neg_sub, Valuation.map_neg]
    dist_triangle := fun x y z => by
      simp only [← sub_add_sub_cancel x y z]
      exact le_trans (v.norm_add_le _ _)
        (max_le_add_of_nonneg (v.norm_nonneg _) (v.norm_nonneg _))
    eq_of_dist_eq_zero := fun hxy => eq_of_sub_eq_zero (v.norm_eq_zero hxy)
    dist_eq := fun x y => by
      simp only [Valuation.norm]
      rw [← v.restrict.map_neg, neg_sub, sub_eq_add_neg, add_comm]
    norm_mul := fun x y => by simp only [Valuation.norm, ← NNReal.coe_mul, map_mul]
    toUniformSpace := ‹UniformSpace L›
    uniformity_dist := by
      haveI : Nonempty { ε : ℝ // ε > 0 } := nonempty_Ioi_subtype
      ext U
      rw [hasBasis_iff.mp v.hasBasis_uniformity, iInf_subtype', mem_iInf_of_directed]
      · simp only [true_and, mem_principal, Subtype.exists, gt_iff_lt, exists_prop]
        refine ⟨fun ⟨ε, hε⟩ => ?_, fun ⟨r, hr_pos, hr⟩ => ?_⟩
        · set δ : ℝ≥0 := hv.hom _ ε with hδ
          have hδ_pos : 0 < δ := by
            rw [hδ, ← map_zero hv.hom]
            exact hv.strictMono _ (Units.zero_lt ε)
          use δ, hδ_pos
          apply subset_trans _ hε
          intro x hx
          simp only [mem_setOf_eq, Valuation.norm, hδ, NNReal.coe_lt_coe] at hx
          rw [mem_setOf, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono v).lt_iff_lt.mp hx
        · haveI : Nontrivial Γˣ := (nontrivial_iff_exists_ne (1 : Γˣ)).mpr
            ⟨RankOne.unit v, RankOne.unit_ne_one v⟩
          obtain ⟨u, hu⟩ := Real.exists_lt_of_strictMono hv.strictMono hr_pos
          use u
          apply subset_trans _ hr
          intro x hx
          simp only [Valuation.norm, mem_setOf_eq]
          apply lt_trans _ hu
          rw [NNReal.coe_lt_coe, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono v).lt_iff_lt.mpr hx
      · simp only [Directed]
        intro x y
        use min x y
        simp only [le_principal_iff, mem_principal, setOf_subset_setOf, Prod.forall]
        exact ⟨fun a b hab => lt_of_lt_of_le hab (min_le_left _ _), fun a b hab =>
            lt_of_lt_of_le hab (min_le_right _ _)⟩ }

end Construction

/-!
## The discrete refinement: an honest `ℤ`-valued additive valuation

When `v` is moreover *discretely* valued (`v.IsRankOneDiscrete`), its value group is infinite
cyclic, so we can transport `v` onto `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` via Mathlib's order
isomorphism of value groups and read off a genuine integer valuation.  Under `toAddValuation`
this becomes an `AddValuation L (Additive ℤᵐ⁰)ᵒᵈ` (Mathlib's `ℤ ∪ {∞}`), which we finally translate
into the familiar `WithTop ℤ`.  This mirrors `NewtonPolygon.normValZ` / `normAddValZ` /
`normAddValZWithTop`, but starting from an abstract discrete valuation `v` rather than `-log ‖·‖`.
-/

section DiscreteAddVal

variable [Ring L] (v : Valuation L Γ)

/-- General order-**and**-additive isomorphism
`(Additive (WithZero (Multiplicative G)))ᵒᵈ ≃+o WithTop G` for any linearly ordered additive
commutative group `G`.  Sends `0 ↦ ⊤` and `coe (ofAdd g) ↦ -g`; multiplication on the source
becomes addition on `WithTop G`.  Instantiated at `G = ℤ` (discrete case, `zmOrderAddIso`) and at
`G = ℚ` (rational-rank-one case, `withZeroMultOrderAddIso ℚ`). -/
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

/-- Order-**and**-additive iso `(Additive ℤᵐ⁰)ᵒᵈ ≃+o WithTop ℤ` (the discrete case). -/
noncomputable def zmOrderAddIso : (Additive ℤᵐ⁰)ᵒᵈ ≃+o WithTop ℤ := withZeroMultOrderAddIso ℤ

/-- The underlying order isomorphism `(Additive ℤᵐ⁰)ᵒᵈ ≃o WithTop ℤ` of `zmOrderAddIso`. -/
noncomputable def zmOrderIso : (Additive ℤᵐ⁰)ᵒᵈ ≃o WithTop ℤ := zmOrderAddIso.toOrderIso

/-- The underlying additive-monoid hom `(Additive ℤᵐ⁰)ᵒᵈ →+ WithTop ℤ` of `zmOrderAddIso`,
used to transport an `AddValuation` along it. -/
noncomputable def zmAddHom : (Additive ℤᵐ⁰)ᵒᵈ →+ WithTop ℤ := zmOrderAddIso.toAddEquiv.toAddMonoidHom

/-- `zmOrderIso` on a coe `↑m` is `-toAdd m` (holds definitionally). -/
@[simp]
lemma zmOrderIso_coe (m : Multiplicative ℤ) :
    zmOrderIso ((m : ℤᵐ⁰)) = ((-(Multiplicative.toAdd m) : ℤ) : WithTop ℤ) := rfl

@[simp]
lemma zmAddHom_apply (x : (Additive ℤᵐ⁰)ᵒᵈ) : zmAddHom x = zmOrderIso x := rfl

lemma zmAddHom_top : zmAddHom ⊤ = ⊤ := rfl

open Valuation.IsRankOneDiscrete

variable [v.IsRankOneDiscrete]

/-- The discretely-valued `v`, transported to a `ℤᵐ⁰`-valued valuation using the order isomorphism
`valueGroup₀ ≃* ℤᵐ⁰`.  Available only in the discrete (`IsRankOneDiscrete`) case. -/
noncomputable def RankOne.valZ : Valuation L ℤᵐ⁰ :=
  v.restrict.map
    (valueGroup₀_equiv_withZeroMulInt v).toMonoidWithZeroHom
    (valueGroup₀_equiv_withZeroMulInt_strictMono v).monotone

/-- The additive `ℤ`-valued valuation attached to a discrete rank-one valuation `v`, valued in
`(Additive ℤᵐ⁰)ᵒᵈ` (Mathlib's `ℤ ∪ {∞}`).  The honest integer refinement of `-log ‖·‖`. -/
noncomputable def RankOne.addValZ : AddValuation L (Additive ℤᵐ⁰)ᵒᵈ :=
  (RankOne.valZ v).toAddValuation

/-- The same discrete additive valuation, with its values translated through `zmOrderIso` into the
more familiar `WithTop ℤ` (`= ℤ ∪ {∞}`).  Bundled as an `AddValuation` so that all the additive
valuation API (`map_add`, `map_mul`, monotonicity, …) is available. -/
noncomputable def RankOne.addValZWithTop : AddValuation L (WithTop ℤ) :=
  (RankOne.addValZ v).map zmAddHom zmAddHom_top zmOrderIso.monotone

@[simp]
lemma RankOne.addValZWithTop_apply (x : L) :
    RankOne.addValZWithTop v x = zmOrderIso (RankOne.addValZ v x) := rfl

end DiscreteAddVal

/-!
## The rational-rank-one refinement: an honest `ℚ`-valued additive valuation

The value group of a rank one valuation is a subgroup of `(ℝ, +)`.  It is `≅ ℤ` exactly in the
discrete case; more generally it embeds into `ℚ` **iff it has rational rank `≤ 1`** (any two elements
commensurable).  This is a *strictly weaker* hypothesis than discreteness and a *strictly stronger*
one than plain rank one:

* `ℚ_p` — value group `ℤ`, discrete, so rational rank one (and lands in `WithTop ℤ`);
* `ℂ_p` — value group `ℚ`, **not** discrete but rational rank one, so it lands in `WithTop ℚ`;
* a valuation with value group `ℤ + ℤ√2` — rank one but rational rank `2`, so it does **not** land
  in `WithTop ℚ` (only the real-valued `-log ‖·‖` is available there).

We record the hypothesis as the existence of an order embedding of the value group into
`ℚᵐ⁰ := WithZero (Multiplicative ℚ)`, mirroring how `IsRankOneDiscrete` packages the iso to `ℤᵐ⁰`.
-/

/-- **Rational-rank-≤-1 hypothesis** on a valuation `v`: its value group `ValueGroup₀ v` embeds,
order-preservingly, into `ℚ`.  Concretely, the data of a strictly monotone `MonoidWithZeroHom` into
`ℚᵐ⁰ = WithZero (Multiplicative ℚ)`.  This is the density analogue of `IsRankOneDiscrete`
(whose target is `ℤᵐ⁰`); `ℂ_p` satisfies it, a value group `ℤ + ℤ√2` does not. -/
class Valuation.RatRankLeOne {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) where
  /-- An order-preserving embedding of the value group into `ℚᵐ⁰`. -/
  hom : MonoidWithZeroHom.ValueGroup₀ v →*₀ WithZero (Multiplicative ℚ)
  /-- The embedding is strictly monotone. -/
  strictMono : StrictMono hom

section RatRankAddVal

variable [Ring L] (v : Valuation L Γ) [v.RatRankLeOne]

/-- The rational-rank-one `v`, transported to a `ℚᵐ⁰`-valued valuation via the order embedding of
value groups.  Density analogue of `RankOne.valZ`. -/
noncomputable def RankOne.valQ : Valuation L (WithZero (Multiplicative ℚ)) :=
  v.restrict.map (Valuation.RatRankLeOne.hom (v := v))
    (Valuation.RatRankLeOne.strictMono (v := v)).monotone

/-- The additive `ℚ`-valued valuation attached to a rational-rank-one `v`, valued in
`(Additive ℚᵐ⁰)ᵒᵈ`.  Density analogue of `RankOne.addValZ`. -/
noncomputable def RankOne.addValQ : AddValuation L (Additive (WithZero (Multiplicative ℚ)))ᵒᵈ :=
  (RankOne.valQ v).toAddValuation

/-- The rational additive valuation translated into the familiar `WithTop ℚ` (`= ℚ ∪ {∞}`), bundled
as an `AddValuation` so all the additive-valuation API is available.  Density analogue of
`RankOne.addValZWithTop`. -/
noncomputable def RankOne.addValQWithTop : AddValuation L (WithTop ℚ) :=
  (RankOne.addValQ v).map (withZeroMultOrderAddIso ℚ).toAddEquiv.toAddMonoidHom rfl
    (withZeroMultOrderAddIso ℚ).toOrderIso.monotone

@[simp]
lemma RankOne.addValQWithTop_apply (x : L) :
    RankOne.addValQWithTop v x = withZeroMultOrderAddIso ℚ (RankOne.addValQ v x) := rfl

end RatRankAddVal

/-!
## Coherence: `IsRankOneDiscrete ⟹ RatRankLeOne ⟹ RankLeOne`

The three hypotheses form a genuine hierarchy.  `RatRankLeOne` sits strictly between discreteness
(target `ℤ`) and plain rank ≤ one (target `ℝ≥0`): it embeds the value group into `ℚ`, which then
sits inside `ℝ≥0` via an exponential `x ↦ e^x`.
-/

section Coherence

open Multiplicative WithZero Valuation.IsRankOneDiscrete

variable [Ring L] (v : Valuation L Γ)

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
exponential `ℚᵐ⁰ ↪ ℝ≥0` (base `2`) exhibits the value group inside `ℝ≥0`, i.e. rank ≤ one. -/
@[reducible]
noncomputable def Valuation.RatRankLeOne.toRankLeOne [v.RatRankLeOne] : RankLeOne v where
  hom' := (ratToNNReal (e := 2) (by norm_num)).comp (Valuation.RatRankLeOne.hom (v := v))
  strictMono' :=
    (ratToNNReal_strictMono (by norm_num)).comp (Valuation.RatRankLeOne.strictMono (v := v))

/-- **`IsRankOneDiscrete ⟹ RatRankLeOne`.**  A discrete value group `≅ ℤᵐ⁰` embeds into `ℚᵐ⁰`
via `ℤ ↪ ℚ`, so a discrete valuation automatically has rational rank ≤ 1. -/
noncomputable instance [v.IsRankOneDiscrete] : v.RatRankLeOne where
  hom := (withZeroMultMap (Int.castAddHom ℚ)).comp
    (valueGroup₀_equiv_withZeroMulInt v).toMonoidWithZeroHom
  strictMono := by
    have hf : StrictMono (Int.castAddHom ℚ) := fun a b h => by simpa using Int.cast_lt.mpr h
    exact (withZeroMultMap_strictMono hf).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)

end Coherence

/-!
## The compatibility square

Fix the ambient rank-one structure on `v` to be the one induced by `RatRankLeOne` with base `e`
satisfying `log e = 1` (i.e. `e = exp 1`).  Then the `ℚ`-valued additive valuation
`addValQWithTop` maps **onto the nose** to the `ℝ`-valued `addVal` under `WithTop.map (Rat.cast)`:
`ℂ_p`'s `ℚ`-valued valuation and its `-log ‖·‖` are literally the same, up to `ℚ ↪ ℝ`.
-/

section Compat

open Multiplicative WithZero

variable [Ring L] (v : Valuation L Γ) [RankOne v]

/-- On a nonzero element, `ratToNNReal` is `e ^ (unzero x).toAdd`. -/
lemma ratToNNReal_apply_of_ne_zero {e : ℝ≥0} (he : e ≠ 0)
    {x : WithZero (Multiplicative ℚ)} (hx : x ≠ 0) :
    ratToNNReal he x = e ^ ((WithZero.unzero hx).toAdd : ℝ) := dif_neg hx

/-- **The absolute value is the base to the power of minus the additive valuation (rational-rank
case).**  If the norm-defining `RankOne` hom of `v` factors as the exponential `ratToNNReal`
(base `e`) composed with the `RatRankLeOne` embedding, and the `ℚ`-valued additive valuation of `x`
is `q` (`addValQWithTop v x = q`), then the `ℝ≥0`-valued absolute value `RankOne.hom v (v.restrict x)`
equals `e ^ (-q)`.  Stated about the `ℝ≥0`-hom rather than `v.norm` (which is `Field`-only), so this
holds over any `Ring`; the `‖·‖` form follows by `v.norm = ↑·`.  The `rpow` analogue of
`hom_eq_base_zpow_neg_addValZ` — the value group here is dense, so this uses the full factorization
`hb` rather than a single scalar. -/
theorem hom_eq_base_rpow_neg_addValQ [v.RatRankLeOne] {e : ℝ≥0} (he : e ≠ 0)
    (hb : RankOne.hom v = (ratToNNReal he).comp (Valuation.RatRankLeOne.hom (v := v)))
    {x : L} {q : ℚ} (hq : RankOne.addValQWithTop v x = (q : WithTop ℚ)) :
    RankOne.hom v (v.restrict x) = e ^ (-(q : ℝ)) := by
  have hvq : RankOne.valQ v x ≠ 0 := by
    intro h
    rw [show RankOne.addValQWithTop v x = ⊤ by
      simp only [RankOne.addValQWithTop_apply, RankOne.addValQ, Valuation.toAddValuation_apply, h]
      rfl] at hq
    exact absurd hq (by simp)
  set m := WithZero.unzero hvq with hm
  have hcoe : RankOne.valQ v x = (m : WithZero (Multiplicative ℚ)) := (WithZero.coe_unzero hvq).symm
  have hlhs : RankOne.addValQWithTop v x = ((-(Multiplicative.toAdd m) : ℚ) : WithTop ℚ) := by
    simp only [RankOne.addValQWithTop_apply, RankOne.addValQ, Valuation.toAddValuation_apply, hcoe]
    rfl
  have hmq : Multiplicative.toAdd m = -q := by
    have h : ((-(Multiplicative.toAdd m) : ℚ) : WithTop ℚ) = ((q : ℚ) : WithTop ℚ) := by
      rw [← hlhs]; exact hq
    rw [WithTop.coe_inj] at h; linarith
  have hh : RankOne.hom v (v.restrict x) = ratToNNReal he (RankOne.valQ v x) :=
    DFunLike.congr_fun hb (v.restrict x)
  rw [hh, ratToNNReal_apply_of_ne_zero he hvq, ← hm, hmq, Rat.cast_neg]

end Compat

section CompatZ

open Multiplicative WithZero Valuation.IsRankOneDiscrete

variable [Ring L] (v : Valuation L Γ) [RankOne v]

/-- `WithZeroMulInt.toNNReal` sends `exp n ↦ eⁿ`. -/
lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n :=
  WithZeroMulInt.toNNReal_neg_apply he (WithZero.exp_ne_zero (a := n))

/-- **The factorization `hb` follows from one scalar.**  On a discrete valuation the value group is
infinite cyclic, so a `→*₀` hom out of it is determined by its value on the generator.  Hence, to
know that `RankOne.hom v` is "`exp` in base `e`", it suffices that `‖ϖ‖ = e⁻¹`, i.e.
`RankOne.hom v (generator') = e⁻¹`. -/
lemma hb_of_norm_generator [v.IsRankOneDiscrete] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : ValueGroup₀ v) = e⁻¹) :
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

/-- **The absolute value is the base to the power of minus the additive valuation.**  If a uniformizer
has norm `e⁻¹` (`RankOne.hom v (generator') = e⁻¹`) and the `ℤ`-valued additive valuation of `x` is
the integer `d` (`addValZWithTop v x = d`), then the `ℝ≥0`-valued absolute value
`RankOne.hom v (v.restrict x)` equals `e ^ (-d)`.  Stated about the `ℝ≥0`-hom rather than `v.norm`
(which is `Field`-only), so this holds over any `Ring`; the `‖·‖` form follows by `v.norm = ↑·`.
Equivalently, with `e⁻¹ = ‖ϖ‖`, this reads `RankOne.hom v (v.restrict x) = ‖ϖ‖ ^ d`. -/
theorem hom_eq_base_zpow_neg_addValZ [v.IsRankOneDiscrete] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : ValueGroup₀ v) = e⁻¹)
    {x : L} {d : ℤ} (hd : RankOne.addValZWithTop v x = (d : WithTop ℤ)) :
    RankOne.hom v (v.restrict x) = e ^ (-d) := by
  have hb := hb_of_norm_generator v he hgen
  have hvz : RankOne.valZ v x ≠ 0 := by
    intro h
    rw [show RankOne.addValZWithTop v x = ⊤ by
      simp only [RankOne.addValZWithTop_apply, RankOne.addValZ, Valuation.toAddValuation_apply, h]
      rfl] at hd
    exact absurd hd (by simp)
  set m := WithZero.unzero hvz with hm
  have hcoe : RankOne.valZ v x = (m : ℤᵐ⁰) := (WithZero.coe_unzero hvz).symm
  have hlhs : RankOne.addValZWithTop v x = ((-(Multiplicative.toAdd m) : ℤ) : WithTop ℤ) := by
    simp only [RankOne.addValZWithTop_apply, RankOne.addValZ, Valuation.toAddValuation_apply, hcoe]
    rfl
  have hmd : Multiplicative.toAdd m = -d := by
    have h : ((-(Multiplicative.toAdd m) : ℤ) : WithTop ℤ) = ((d : ℤ) : WithTop ℤ) := by
      rw [← hlhs]; exact hd
    rw [WithTop.coe_inj] at h; omega
  have hh : RankOne.hom v (v.restrict x) = WithZeroMulInt.toNNReal he (RankOne.valZ v x) :=
    DFunLike.congr_fun hb (v.restrict x)
  rw [hh, WithZeroMulInt.toNNReal_neg_apply he hvz, ← hm, hmd]

end CompatZ

/-!
## Application: ultrametric normed fields

Everything above is stated for an abstract `Valuation`.  Specialising to the canonical valuation
`NormedField.valuation = ‖·‖₊` of an ultrametric normed field recovers the `NewtonPolygon`
construction `normAddValZWithTop` as an instance of the abstract `RankOne.addValZWithTop`, together
with the norm characterization `‖x‖ = e ^ (-v(x))`, now built on all of the machinery in this file.
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

/-- When the norm is discretely valued, the honest `ℤ`-valued additive valuation, as the instance of
`RankOne.addValZWithTop`.  Mirrors `NewtonPolygon.normAddValZWithTop`. -/
noncomputable def normAddValZWithTop [(NormedField.valuation (K := R)).IsRankOneDiscrete] :
    AddValuation R (WithTop ℤ) :=
  RankOne.addValZWithTop (NormedField.valuation (K := R))

@[simp]
lemma normAddValZWithTop_zero [(NormedField.valuation (K := R)).IsRankOneDiscrete] :
    normAddValZWithTop R 0 = ⊤ := AddValuation.map_zero _

/-- **The norm is the base to the power of minus the additive valuation.**  If `x` has integer
additive valuation `d` (`normAddValZWithTop R x = d`), then `‖x‖ = e ^ (-d)`.  For the standard
`p`-adic norm `e = p`, so `‖x‖ = p ^ (-vₚ(x))`; with `e⁻¹ = ‖ϖ‖` the uniformizer norm, equivalently
`‖x‖ = ‖ϖ‖ ^ d`. -/
theorem norm_eq_base_zpow_neg_normAddValZWithTop
    [(NormedField.valuation (K := R)).IsRankOneDiscrete] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom (NormedField.valuation (K := R))
      (Valuation.IsRankOneDiscrete.generator' (NormedField.valuation (K := R))
        : MonoidWithZeroHom.ValueGroup₀ (NormedField.valuation (K := R))) = e⁻¹)
    {x : R} {d : ℤ} (hd : normAddValZWithTop R x = (d : WithTop ℤ)) :
    ‖x‖ = (e : ℝ) ^ (-d) := by
  have hnorm : ‖x‖ = ((RankOne.hom (NormedField.valuation (K := R))
      ((NormedField.valuation (K := R)).restrict x) : ℝ≥0) : ℝ) := by
    rw [← valuation_norm_eq R x]; rfl
  rw [hnorm, hom_eq_base_zpow_neg_addValZ (NormedField.valuation (K := R)) he hgen hd, NNReal.coe_zpow]

/-!
### The rational-rank-one (`ℂ_p`-style) case

When the norm has rational rank ≤ 1 (e.g. `ℂ_p`, value group `ℚ`), we get an honest `ℚ`-valued
additive valuation, specializing `RankOne.addValQWithTop`.
-/

/-- The `ℚ`-valued additive valuation of a rational-rank-one ultrametric normed field, as the
instance of `RankOne.addValQWithTop`.  Mirrors the discrete `normAddValZWithTop`, but valued in
`ℚ ∪ {∞}` (the `ℂ_p`-style case). -/
noncomputable def normAddValQWithTop [(NormedField.valuation (K := R)).RatRankLeOne] :
    AddValuation R (WithTop ℚ) :=
  RankOne.addValQWithTop (NormedField.valuation (K := R))

@[simp]
lemma normAddValQWithTop_zero [(NormedField.valuation (K := R)).RatRankLeOne] :
    normAddValQWithTop R 0 = ⊤ := AddValuation.map_zero _

/-- **The norm is the base to the power of minus the additive valuation (rational-rank case).**  If
`x` has `ℚ`-valued additive valuation `q` (`normAddValQWithTop R x = q`), then `‖x‖ = e ^ (-q)`.
The `ℚ`/`rpow` analogue of `norm_eq_base_zpow_neg_normAddValZWithTop`. -/
theorem norm_eq_base_zpow_neg_normAddValQWithTop
    [(NormedField.valuation (K := R)).RatRankLeOne] {e : ℝ≥0} (he : e ≠ 0)
    (hb : RankOne.hom (NormedField.valuation (K := R))
      = (ratToNNReal he).comp (Valuation.RatRankLeOne.hom (v := NormedField.valuation (K := R))))
    {x : R} {q : ℚ} (hq : normAddValQWithTop R x = (q : WithTop ℚ)) :
    ‖x‖ = (e : ℝ) ^ (-(q : ℝ)) := by
  have hnorm : ‖x‖ = ((RankOne.hom (NormedField.valuation (K := R))
      ((NormedField.valuation (K := R)).restrict x) : ℝ≥0) : ℝ) := by
    rw [← valuation_norm_eq R x]; rfl
  rw [hnorm, hom_eq_base_rpow_neg_addValQ (NormedField.valuation (K := R)) he hb hq, NNReal.coe_rpow]

end NormedField

/-!
## `ℚ_p`: our `ℤ`-valued additive valuation is the `p`-adic valuation

The final piece.  We supply the missing `IsRankOneDiscrete` instance for the `p`-adic norm (its value
group is the infinite cyclic group generated by `‖p‖₊ = p⁻¹`) and verify that `normAddValZWithTop`
— the honest `ℤ`-valued additive valuation produced by the abstract machinery — coincides with
Mathlib's `Padic.addValuationDef` (`vₚ`, with `⊤` at `0`).  Ported from `NewtonPolygon`.
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

/-- The `p`-adic norm valuation on `ℚ_p` is rank-one discrete. -/
noncomputable instance : (NormedField.valuation (K := ℚ_[p])).IsRankOneDiscrete :=
  IsRankOneDiscrete.mk' _

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
`normAddValZWithTop x = d` then `‖x‖ = p ^ (-d)`.  Instance of
`norm_eq_base_zpow_neg_normAddValZWithTop` at `e = p`, with the scalar hypothesis `hgen_padic`. -/
theorem padic_norm_eq_zpow_neg_normAddValZWithTop {x : ℚ_[p]} {d : ℤ}
    (hd : normAddValZWithTop ℚ_[p] x = (d : WithTop ℤ)) : ‖x‖ = (p : ℝ) ^ (-d) := by
  have h := norm_eq_base_zpow_neg_normAddValZWithTop (R := ℚ_[p]) (e := (p : ℝ≥0))
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero) hgen_padic hd
  simpa using h

/-- **The verification.**  On `ℚ_p`, `normAddValZWithTop` (from the abstract machinery) is exactly the
additive `p`-adic valuation `Padic.addValuationDef` (`vₚ`, with `⊤` at `0`).  Deduced from the norm
characterization: `p ^ (-normAddValZWithTop x) = ‖x‖ = p ^ (-vₚ(x))` and `p > 1`. -/
theorem normAddValZWithTop_padic (x : ℚ_[p]) :
    normAddValZWithTop ℚ_[p] x = Padic.addValuationDef x := by
  by_cases hx : x = 0
  · subst hx; rw [normAddValZWithTop_zero, Padic.addValuationDef, if_pos rfl]
  · obtain ⟨d, hd⟩ : ∃ d : ℤ, normAddValZWithTop ℚ_[p] x = (d : WithTop ℤ) := by
      have hvz : RankOne.valZ (NormedField.valuation (K := ℚ_[p])) x ≠ 0 :=
        (RankOne.valZ _).ne_zero_iff.mpr hx
      set m := WithZero.unzero hvz with hm
      have hcoe : RankOne.valZ (NormedField.valuation (K := ℚ_[p])) x = (m : ℤᵐ⁰) :=
        (WithZero.coe_unzero hvz).symm
      refine ⟨-(Multiplicative.toAdd m), ?_⟩
      simp only [normAddValZWithTop, RankOne.addValZWithTop_apply, RankOne.addValZ,
        Valuation.toAddValuation_apply, hcoe]
      rfl
    rw [hd, Padic.addValuationDef, if_neg hx]
    congr 1
    have hn1 := padic_norm_eq_zpow_neg_normAddValZWithTop hd
    have hn2 := Padic.norm_eq_zpow_neg_valuation hx
    have hpp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hinj := (zpow_right_strictMono₀ hpp).injective (hn1.symm.trans hn2)
    omega

end Padic



/-!
## The real-valued additive valuation on any rank-one valuation: `x ↦ -log (v.norm x)`

For an *arbitrary* rank-one valuation `v` — no discreteness or rational-rank hypothesis — we obtain
an additive valuation into `WithTop ℝ`.  This is the universal additive valuation: for a
non-discrete, non-rational-rank value group (an arbitrary subgroup of `ℝ`, e.g. `ℤ + ℤ√2`) it is the
only one available, there being no `ℤ`/`ℚ` refinement.

Mimicking the `ℤ`/`ℚ` constructions, we transport `v` along `RankOne.hom` into `ℝ≥0` and then along
the logarithm `ℝ≥0 →*₀ ℝᵐ⁰` into `ℝᵐ⁰ = WithZero (Multiplicative ℝ)`, and read off `WithTop ℝ` via
`withZeroMultOrderAddIso ℝ`.  Because this goes through `toAddValuation` (which sends the zero of the
value group to `⊤`) rather than taking `-log` pointwise, it needs **no faithfulness/field
hypothesis** — it works over any `Ring`.  On a field it is the familiar `x ↦ -log ‖x‖`
(`RankOne.addVal_apply_of_ne_zero`).
-/

open Multiplicative WithZero in
/-- The order-preserving "logarithm" `ℝ≥0 →*₀ ℝᵐ⁰`, `x ↦ exp (log x)` with `0 ↦ 0`.  It exhibits the
multiplicative monoid `ℝ≥0` as `WithZero (Multiplicative ℝ)`. -/
noncomputable def nnrealLogHom : ℝ≥0 →*₀ WithZero (Multiplicative ℝ) where
  toFun x := if x = 0 then 0 else WithZero.exp (Real.log x)
  map_zero' := if_pos rfl
  map_one' := by rw [if_neg one_ne_zero, NNReal.coe_one, Real.log_one, WithZero.exp_zero]
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, NNReal.coe_mul,
      Real.log_mul (by exact_mod_cast hx) (by exact_mod_cast hy), WithZero.exp_add]

lemma nnrealLogHom_strictMono : StrictMono nnrealLogHom := by
  intro x y hxy
  simp only [nnrealLogHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hx hy hy
  · simp [hx, hy] at hxy
  · exact zero_lt_iff.mpr WithZero.exp_ne_zero
  · simp [hy] at hxy
  · simp only [WithZero.exp_eq_coe_ofAdd, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
    exact Real.log_lt_log (by positivity) (by exact_mod_cast hxy)

section RankOneAddVal

variable [Ring L] (v : Valuation L Γ) [RankOne v]

/-- The `ℝᵐ⁰`-valued valuation attached to a rank one valuation `v`, transporting `v` along
`RankOne.hom` and the logarithm `ℝ≥0 → ℝᵐ⁰`. -/
noncomputable def RankOne.valR : Valuation L (WithZero (Multiplicative ℝ)) :=
  v.restrict.map (nnrealLogHom.comp (RankOne.hom v))
    (nnrealLogHom_strictMono.comp (RankOne.strictMono v)).monotone

/-- The additive `ℝ`-valued valuation attached to `v`, valued in `(Additive ℝᵐ⁰)ᵒᵈ`. -/
noncomputable def RankOne.addValR : AddValuation L (Additive (WithZero (Multiplicative ℝ)))ᵒᵈ :=
  (RankOne.valR v).toAddValuation

/-- **The real-valued additive valuation `x ↦ -log ‖x‖` on any rank-one valuation**, valued in
`WithTop ℝ` with `⊤` at `0`.  Built by transport, so it needs only a `Ring`. -/
noncomputable def RankOne.addVal : AddValuation L (WithTop ℝ) :=
  (RankOne.addValR v).map (withZeroMultOrderAddIso ℝ).toAddEquiv.toAddMonoidHom rfl
    (withZeroMultOrderAddIso ℝ).toOrderIso.monotone

@[simp]
lemma RankOne.addVal_apply (x : L) :
    RankOne.addVal v x = withZeroMultOrderAddIso ℝ (RankOne.addValR v x) := rfl

@[simp]
lemma RankOne.addVal_zero : RankOne.addVal v 0 = ⊤ := AddValuation.map_zero _

end RankOneAddVal

section RankOneAddValField

variable [Field L] (v : Valuation L Γ) [RankOne v]

/-- On a field, `RankOne.addVal` is the familiar `x ↦ -log ‖x‖`. -/
lemma RankOne.addVal_apply_of_ne_zero {x : L} (hx : x ≠ 0) :
    RankOne.addVal v x = ((-Real.log (v.norm x) : ℝ) : WithTop ℝ) := by
  have hne : RankOne.hom v (v.restrict x) ≠ 0 := fun h =>
    hx (v.norm_eq_zero (by show ((RankOne.hom v (v.restrict x) : ℝ≥0) : ℝ) = 0; rw [h]; simp))
  simp only [RankOne.addVal_apply, RankOne.addValR, Valuation.toAddValuation_apply, RankOne.valR,
    Valuation.map_apply, MonoidWithZeroHom.comp_apply, nnrealLogHom, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk]
  split_ifs with h
  · exact absurd h hne
  · rfl

end RankOneAddValField
