/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.Algebra.Order.Group.Commensurable
import PhD.ForMathlib.RingTheory.Valuation.AddVal.RankOne

/-!
# Rational rank one, normalised at an element

`Valuation.IsCommensurable v π` says that `π` has valuation strictly between `0` and `1` and that
every value of `v` is *commensurable* with `v π`: a positive power of it is a power of `v π`.
This is the density analogue of `Valuation.IsRankOneDiscrete`.

It is a `Prop`: the normalisation, which a dense rank-one value group cannot supply on its own,
is carried by the *element* `π` rather than by hidden instance data.  For `ℂ_p` one takes `π = p`.

## Main definitions

* `Valuation.IsCommensurable v π`, rational rank one normalised at `π`;
* `Valuation.ratLog`, the unique `ℚ`-valued logarithm on the value group with `v π ↦ -1`;
* `Valuation.addValQ v π : AddValuation R (WithTop ℚ)`, normalised by `addValQ v π π = 1`.

## Main results

* `Valuation.addValQ_eq_of_zpow`: a witness `v x ^ n = v π ^ m` computes `addValQ v π x = m / n`.
  This is the workhorse; `addValQ_self` and the norm-recovery theorems fall out of it.
* `Valuation.IsCommensurable.toRankOne`: rational rank one implies rank one, for any base
  `1 < e`; the resulting norm satisfies `‖π‖ = e⁻¹`.
* `Valuation.RankOne.addVal_eq_map_addValQ` and `Valuation.RankOne.hom_eq_rpow_addValQ`:
  the compatibility square `ℚ → ℝ`, and `‖x‖ = ‖π‖ ^ (addValQ v π x)`.  Note there is no
  exponential base and no factorisation hypothesis — the normalisation at `π` pins the base to
  `‖π‖⁻¹`.

Everything here is meant to be redistributed into the relevant `Mathlib` files.
-/

open scoped NNReal WithZero

/-- **Rational rank one, normalised at `π`.**  The element `π` has valuation strictly between `0`
and `1`, and every value of `v` is *commensurable* with `v π`: a positive power of it is a power
of `v π`.

This is the density analogue of `Valuation.IsRankOneDiscrete`.  Unlike the discrete case, a dense
rank-one value group has no canonical generator, so the `ℚ`-valued additive valuation only becomes
canonical once a normalising element is chosen — which is exactly what `π` is.  For `ℂ_p` one takes
`π = p`, recovering the usual convention `v p = 1`. -/
class Valuation.IsCommensurable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (π : R) : Prop where
  /-- `π` has nonzero valuation. -/
  val_pos : 0 < v π
  /-- `π` has valuation `< 1`, so that it plays the role of a uniformizer. -/
  val_lt_one : v π < 1
  /-- Every nonzero value of `v` is commensurable with `v π`. -/
  exists_zpow_eq (x : R) (hx : v x ≠ 0) : ∃ m n : ℤ, 0 < n ∧ v x ^ n = v π ^ m

namespace Valuation

open MonoidWithZeroHom WithZero

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)

private lemma ratToReal_strictMono : StrictMono ((Rat.castHom ℝ).toAddMonoidHom) := fun a b h ↦ by
  show (a : ℝ) < (b : ℝ)
  exact_mod_cast h

section IsCommensurable

variable (π : R) [hπ : v.IsCommensurable π]

lemma IsCommensurable.val_ne_zero : v π ≠ 0 := hπ.val_pos.ne'

/-- `v π`, as an element of the value group of `v`; the normalising element. -/
noncomputable def commGen : valueGroup (.ofClass v) :=
  ⟨Units.mk0 (v π) (IsCommensurable.val_ne_zero v π), mem_valueGroup _ ⟨π, rfl⟩⟩

@[simp] lemma coe_commGen : ((commGen v π : Γ₀ˣ) : Γ₀) = v π := rfl

lemma ofMul_commGen_neg : Additive.ofMul (commGen v π) < 0 := by
  show commGen v π < 1
  rw [← Subtype.coe_lt_coe, ← Units.val_lt_val]
  simpa using hπ.val_lt_one

/-- Every element of the value group is commensurable with the normalising element. -/
lemma exists_zpow_eq_commGen (g : valueGroup (.ofClass v)) :
    AddCommGroup.IsCommensurableWith (Additive.ofMul (commGen v π)) (Additive.ofMul g) := by
  obtain ⟨a, ha, x, hax⟩ := (mem_valueGroup_iff_of_comm (f := .ofClass v)).mp g.2
  simp only [MonoidWithZeroHom.coe_ofClass] at ha hax
  have hg0 : ((g : Γ₀ˣ) : Γ₀) ≠ 0 := Units.ne_zero _
  have hx : v x ≠ 0 := by rw [← hax]; exact mul_ne_zero ha hg0
  obtain ⟨m₁, n₁, hn₁, e₁⟩ := hπ.exists_zpow_eq x hx
  obtain ⟨m₂, n₂, hn₂, e₂⟩ := hπ.exists_zpow_eq a ha
  refine ⟨m₁ * n₂ - m₂ * n₁, n₁ * n₂, mul_pos hn₁ hn₂, ?_⟩
  show g ^ (n₁ * n₂) = commGen v π ^ (m₁ * n₂ - m₂ * n₁)
  refine Subtype.ext (Units.ext ?_)
  simp only [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val, coe_commGen]
  have hgx : ((g : Γ₀ˣ) : Γ₀) = v x / v a := by
    rw [← hax]; field_simp
  rw [hgx, div_zpow, zpow_sub₀ (IsCommensurable.val_ne_zero v π),
    show (v x) ^ (n₁ * n₂) = (v π) ^ (m₁ * n₂) by rw [zpow_mul, e₁, ← zpow_mul],
    show (v a) ^ (n₁ * n₂) = (v π) ^ (m₂ * n₁) by
      rw [mul_comm n₁ n₂, zpow_mul, e₂, ← zpow_mul]]

/-- **The `ℚ`-valued logarithm of the value group of `v`, normalised at `π`**: the unique additive
hom sending `v π` to `-1`. -/
noncomputable def ratLog : Additive (valueGroup (.ofClass v)) →+ ℚ :=
  AddCommGroup.ratLog (ofMul_commGen_neg v π) fun a ↦ exists_zpow_eq_commGen v π (Additive.toMul a)

lemma ratLog_strictMono : StrictMono (ratLog v π) := AddCommGroup.ratLog_strictMono _ _

@[simp] lemma ratLog_commGen : ratLog v π (Additive.ofMul (commGen v π)) = -1 :=
  AddCommGroup.ratLog_self _ _

/-- **The `ℚ`-valued additive valuation of `v`, normalised at `π`.**  Valued in
`WithTop ℚ = ℚ ∪ {∞}`, with `∞` at `0` and `addValQ v π π = 1`. -/
noncomputable def addValQ : AddValuation R (WithTop ℚ) :=
  v.addValValueGroup.map (ratLog v π).withTopMap rfl (ratLog_strictMono v π).monotone.withTop_map

@[simp] lemma addValQ_apply (x : R) :
    v.addValQ π x = WithTop.map (ratLog v π) (v.addValValueGroup x) := rfl

@[simp] lemma addValQ_zero : v.addValQ π 0 = ⊤ := AddValuation.map_zero _

private lemma addValValueGroup_of_coe {x : R} {g : valueGroup (.ofClass v)}
    (hg : v.restrict x = (g : ValueGroup₀ (.ofClass v))) :
    v.addValValueGroup x
      = ((-(Additive.ofMul g) : Additive (valueGroup (.ofClass v))) : WithTop _) := by
  rw [addValValueGroup_apply, hg]; rfl

lemma ratLog_eq_of_zsmul {g : valueGroup (.ofClass v)} {m n : ℤ} (hn : 0 < n)
    (hmn : n • Additive.ofMul g = m • Additive.ofMul (commGen v π)) :
    ratLog v π (Additive.ofMul g) = -((m : ℚ) / (n : ℚ)) :=
  AddCommGroup.ratLog_eq _ _ hn hmn

/-- **The workhorse.**  A witness `v x ^ n = v π ^ m` computes the additive valuation. -/
lemma addValQ_eq_of_zpow {x : R} {m n : ℤ} (hx : v x ≠ 0) (hn : 0 < n)
    (hmn : v x ^ n = v π ^ m) : v.addValQ π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by
  have hr : v.restrict x ≠ 0 := by simpa using hx
  obtain ⟨g, hg⟩ : ∃ g : valueGroup (.ofClass v), v.restrict x = (g : ValueGroup₀ (.ofClass v)) :=
    ⟨WithZero.unzero hr, (WithZero.coe_unzero hr).symm⟩
  have hgx : ((g : Γ₀ˣ) : Γ₀) = v x := by
    have h := v.embedding_restrict x
    rw [hg] at h
    exact h
  have hgn : n • Additive.ofMul g = m • Additive.ofMul (commGen v π) := by
    show g ^ n = commGen v π ^ m
    refine Subtype.ext (Units.ext ?_)
    simp only [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val, coe_commGen, hgx]
    exact hmn
  rw [addValQ_apply, addValValueGroup_of_coe v hg, WithTop.map_coe, _root_.map_neg,
    ratLog_eq_of_zsmul v π hn hgn, neg_neg]

@[simp] lemma addValQ_self : v.addValQ π π = 1 := by
  rw [addValQ_eq_of_zpow v π (IsCommensurable.val_ne_zero v π) one_pos rfl]
  norm_num

lemma addValQ_ne_top {x : R} (hx : v x ≠ 0) : v.addValQ π x ≠ ⊤ := by
  obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx
  rw [addValQ_eq_of_zpow v π hx hn e]
  exact WithTop.coe_ne_top

lemma exists_zpow_eq_and_addValQ {x : R} (hx : v x ≠ 0) :
    ∃ m n : ℤ, 0 < n ∧ v x ^ n = v π ^ m ∧
      v.addValQ π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by
  obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx
  exact ⟨m, n, hn, e, addValQ_eq_of_zpow v π hx hn e⟩

include π hπ in
/-- A valuation with a normalising element is nontrivial. -/
lemma IsCommensurable.isNontrivial : v.IsNontrivial :=
  ⟨⟨π, hπ.val_pos.ne', hπ.val_lt_one.ne⟩⟩

/-- **Rational rank one implies rank ≤ one.**  For any base `1 < e`; the resulting norm satisfies
`‖π‖ = e⁻¹`. -/
@[reducible]
noncomputable def IsCommensurable.toRankLeOne {e : ℝ≥0} (he : 1 < e) : RankLeOne v where
  hom' := (WithZeroMulReal.toNNReal (ne_zero_of_lt he)).comp
    (expMap (((Rat.castHom ℝ).toAddMonoidHom).comp (ratLog v π)))
  strictMono' := (WithZeroMulReal.toNNReal_strictMono he).comp
    (expMap_strictMono (ratToReal_strictMono.comp (ratLog_strictMono v π)))

/-- **Rational rank one implies rank one.** -/
@[reducible]
noncomputable def IsCommensurable.toRankOne {e : ℝ≥0} (he : 1 < e) : RankOne v where
  __ := IsCommensurable.toRankLeOne v π he
  __ := IsCommensurable.isNontrivial v π

end IsCommensurable

end Valuation

/-! ## Compatibility `ℚ → ℝ` -/

namespace Valuation

open MonoidWithZeroHom WithZero

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
  [RankOne v] (π : R) [v.IsCommensurable π]

private lemma hom_restrict_pos : (0 : ℝ) < (RankOne.hom v (v.restrict π) : ℝ) := by
  have h : RankOne.hom v (v.restrict π) ≠ 0 := by
    rw [Ne, RankOne.hom_eq_zero_iff, restrict_eq_zero_iff]
    exact IsCommensurable.val_ne_zero v π
  positivity

/-- **The compatibility square `ℚ → ℝ`.**  For a rank-one valuation commensurable at `π`, the real
additive valuation `x ↦ -log ‖x‖` is the `ℚ`-valued one rescaled by `-log ‖π‖`.

No choice of exponential base appears: the base is pinned to `‖π‖⁻¹` by the normalisation. -/
theorem RankOne.addVal_eq_map_addValQ (x : R) :
    RankOne.addVal v x
      = WithTop.map (fun q : ℚ ↦ (q : ℝ) * (-Real.log (RankOne.hom v (v.restrict π))))
          (v.addValQ π x) := by
  rcases eq_or_ne (v x) 0 with hx | hx
  · have h1 : v.addValQ π x = ⊤ := by
      rw [addValQ_apply, addValValueGroup_apply,
        show v.restrict x = 0 from v.restrict_eq_zero_iff.mpr hx]
      rfl
    rw [h1, WithTop.map_top, RankOne.addVal_eq_top]
    exact hx
  · obtain ⟨m, n, hn, e, hq⟩ := exists_zpow_eq_and_addValQ v π hx
    have hsx : RankOne.hom v (v.restrict x) ≠ 0 := by
      rw [Ne, RankOne.hom_eq_zero_iff, restrict_eq_zero_iff]; exact hx
    have hs : (0 : ℝ) < (RankOne.hom v (v.restrict x) : ℝ) := by positivity
    have ht := hom_restrict_pos v π
    have hres : (v.restrict x) ^ n = (v.restrict π) ^ m := by
      apply ValueGroup₀.embedding_injective
      rw [map_zpow₀, map_zpow₀, embedding_restrict, embedding_restrict]
      exact e
    have key := congrArg (RankOne.hom v) hres
    rw [map_zpow₀, map_zpow₀] at key
    have key' : ((RankOne.hom v (v.restrict x) : ℝ)) ^ n
        = ((RankOne.hom v (v.restrict π) : ℝ)) ^ m := by exact_mod_cast congrArg NNReal.toReal key
    have hlog := congrArg Real.log key'
    rw [Real.log_zpow, Real.log_zpow] at hlog
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [RankOne.addVal_apply_of_val_ne_zero v hx, hq, WithTop.map_coe, WithTop.coe_inj]
    push_cast
    field_simp
    linarith

/-- **`‖x‖ = ‖π‖ ^ q`.**  The norm is the normalising element's norm raised to the `ℚ`-valued
additive valuation.  No base, no factorisation hypothesis. -/
theorem RankOne.hom_eq_rpow_addValQ {x : R} {q : ℚ} (hq : v.addValQ π x = (q : WithTop ℚ)) :
    ((RankOne.hom v (v.restrict x) : ℝ)) = ((RankOne.hom v (v.restrict π) : ℝ)) ^ (q : ℝ) := by
  have hx : v x ≠ 0 := by
    intro hx
    rw [show v.addValQ π x = ⊤ by
      rw [addValQ_apply, addValValueGroup_apply,
        show v.restrict x = 0 from v.restrict_eq_zero_iff.mpr hx]; rfl] at hq
    exact absurd hq (by simp)
  have hsx : RankOne.hom v (v.restrict x) ≠ 0 := by
    rw [Ne, RankOne.hom_eq_zero_iff, restrict_eq_zero_iff]; exact hx
  have hs : (0 : ℝ) < (RankOne.hom v (v.restrict x) : ℝ) := by positivity
  have ht := hom_restrict_pos v π
  have h := RankOne.addVal_eq_map_addValQ v π x
  rw [RankOne.addVal_apply_of_val_ne_zero v hx, hq, WithTop.map_coe, WithTop.coe_inj] at h
  rw [Real.rpow_def_of_pos ht, ← Real.exp_log hs]
  congr 1
  linarith

end Valuation
