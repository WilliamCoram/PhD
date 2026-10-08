/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Normed

/-!
# Normed additive valuations

The valuation the Newton polygon of a polynomial or of a power series consumes (roadmap, Layer 2
introduction): an additive valuation `v : AddValuation K (WithTop Γ)` on a normed field `K`, a
strictly monotone additive map `e : Γ →+ ℝ` and a base `b > 1` with `‖x‖ = b ^ (-(e (v x)))` for
`x ≠ 0`, bundled as `NormedField.NormedAddValuation K Γ`. The three members of Layer 1's family
are terms of this structure: `ofNormAddValZ` (`Γ = ℤ`, base `‖π‖⁻¹` at a uniformiser `π`),
`ofNormAddValQ` (`Γ = ℚ`, base `‖π‖⁻¹` at a normalising element `π`) and `ofNormAddVal`
(`Γ = ℝ`, base `exp 1`).

The file also proves the **term dictionary** of roadmap §2.1.2 at the level of a single element:
for the radius `c = b ^ m`, the Gauss-norm term `‖x‖ * c ^ k` is at most `1` exactly when the point
`(k, e (v x))` lies on or above the line of slope `m` through the origin, with the `<`, `=` and
two-term variants; and the scalar relation of §2.2.8 between two normed additive valuations on the
same field.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 2 introduction, §2.1.2, §2.2.8.
Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/NormedAddValuation.lean`.

## Main definitions

* `NormedField.NormedAddValuation K Γ` — the structure, coerced to `K → WithTop Γ`;
* `NormedField.NormedAddValuation.embedTop` — `WithTop.map` of the embedding, the map pushing the
  points of a polygon into `WithTop ℝ` (roadmap convention 4);
* `NormedField.NormedAddValuation.ofNormAddValZ`, `ofNormAddValQ`, `ofNormAddVal` — the three
  instances;
* `NormedField.NormedAddValuation.scale` — the scalar `log b / log b'` of §2.2.8.

## Main results

* `NormedField.NormedAddValuation.norm_mul_rpow_pow_le_one_iff` and its variants — the term
  dictionary (§2.1.2);
* `NormedField.NormedAddValuation.embedTop_apply_eq_map` — two normed additive valuations on the
  same field differ by the positive scalar `scale` (§2.2.8).
-/

open scoped NNReal

namespace NormedField

variable (K : Type*) [NormedField K] (Γ : Type*) [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ]

/-- A **normed additive valuation** on the normed field `K` with values in `WithTop Γ` (roadmap,
Layer 2 introduction): an additive valuation, a strictly monotone additive map `embed : Γ →+ ℝ`
(the rank-one hypothesis in additive form, convention 2) and a base `base > 1` with
`‖x‖ = base ^ (-(embed (v x)))` for `x ≠ 0`. -/
structure NormedAddValuation where
  /-- The additive valuation. -/
  toAddValuation : AddValuation K (WithTop Γ)
  /-- The real embedding of the value group. -/
  embed : Γ →+ ℝ
  /-- The embedding is strictly monotone. -/
  strictMono_embed : StrictMono embed
  /-- The base of the norm. -/
  base : ℝ
  /-- The base exceeds `1`. -/
  one_lt_base : 1 < base
  /-- The norm is the base to the power of minus the embedded valuation. -/
  norm_eq_rpow' : ∀ {x : K} {γ : Γ}, toAddValuation x = (γ : WithTop Γ) → ‖x‖ = base ^ (-embed γ)

namespace NormedAddValuation

variable {K Γ}

section Generic

instance : CoeFun (NormedAddValuation K Γ) fun _ ↦ K → WithTop Γ := ⟨fun v ↦ v.toAddValuation⟩

variable (v : NormedAddValuation K Γ)

lemma coe_apply (x : K) : v x = v.toAddValuation x := rfl

/-! ### The additive valuation -/

lemma map_zero : v 0 = ⊤ := by sorry

lemma map_one : v 1 = 0 := by sorry

lemma map_mul (x y : K) : v (x * y) = v x + v y := by sorry

lemma map_pow (x : K) (n : ℕ) : v (x ^ n) = n • v x := by sorry

lemma map_inv (x : K) : v x⁻¹ = -v x := by sorry

lemma min_le_map_add (x y : K) : min (v x) (v y) ≤ v (x + y) := by sorry

@[simp] lemma eq_top_iff {x : K} : v x = ⊤ ↔ x = 0 := by sorry

lemma ne_top_iff {x : K} : v x ≠ ⊤ ↔ x ≠ 0 := by sorry

lemma exists_eq_coe {x : K} (hx : x ≠ 0) : ∃ γ : Γ, v x = (γ : WithTop Γ) := by sorry

/-! ### The base and the norm -/

lemma base_pos : 0 < v.base := by sorry

lemma log_base_pos : 0 < Real.log v.base := by sorry

/-- The defining relation between the norm and the valuation. -/
lemma norm_eq_rpow {x : K} {γ : Γ} (h : v x = (γ : WithTop Γ)) :
    ‖x‖ = v.base ^ (-v.embed γ) := by sorry

/-- The embedded valuation is `-log_b ‖x‖`. -/
lemma embed_eq_neg_logb {x : K} {γ : Γ} (h : v x = (γ : WithTop Γ)) :
    v.embed γ = -Real.logb v.base ‖x‖ := by sorry

/-- The norm determined by a normed additive valuation is ultrametric. -/
lemma norm_add_le_max (x y : K) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by sorry

/-- Every positive real is a power of the base: the radius `c` is `b ^ (log_b c)`. -/
lemma rpow_logb {c : ℝ} (hc : 0 < c) : v.base ^ Real.logb v.base c = c := by sorry

/-! ### Pushing the values into `WithTop ℝ` -/

/-- The embedding extended by `⊤ ↦ ⊤`: the map pushing the points of a polygon into `WithTop ℝ`
(roadmap convention 4). -/
def embedTop : WithTop Γ → WithTop ℝ := WithTop.map v.embed

lemma embedTop_apply (a : WithTop Γ) : v.embedTop a = WithTop.map v.embed a := rfl

@[simp] lemma embedTop_top : v.embedTop ⊤ = ⊤ := by sorry

@[simp] lemma embedTop_coe (γ : Γ) : v.embedTop (γ : WithTop Γ) = (v.embed γ : WithTop ℝ) := by
  sorry

lemma embedTop_eq_top_iff {a : WithTop Γ} : v.embedTop a = ⊤ ↔ a = ⊤ := by sorry

lemma embedTop_strictMono : StrictMono v.embedTop := by sorry

lemma embedTop_le_embedTop {a b : WithTop Γ} : v.embedTop a ≤ v.embedTop b ↔ a ≤ b := by sorry

lemma embedTop_add (a b : WithTop Γ) : v.embedTop (a + b) = v.embedTop a + v.embedTop b := by
  sorry

lemma embedTop_apply_eq_top_iff {x : K} : v.embedTop (v x) = ⊤ ↔ x = 0 := by sorry

lemma embedTop_map_one : v.embedTop (v 1) = 0 := by sorry

/-! ### The term dictionary (roadmap §2.1.2)

For the radius `c = b ^ m`, the Gauss-norm term `‖x‖ * c ^ k` is `b ^ (m k - e (v x))`; comparing
it with `1`, or with another term, is comparing the point `(k, e (v x))` with a line of slope `m`.
-/

/-- The Gauss-norm term as a power of the base. -/
theorem norm_mul_rpow_pow_eq_rpow {x : K} {γ : Γ} (h : v x = (γ : WithTop Γ)) (m : ℝ) (k : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k = v.base ^ (m * k - v.embed γ) := by sorry

/-- The term is at most `1` exactly when the point lies on or above the line of slope `m` through
the origin. -/
theorem norm_mul_rpow_pow_le_one_iff (x : K) (m : ℝ) (k : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k ≤ 1 ↔ ((m * k : ℝ) : WithTop ℝ) ≤ v.embedTop (v x) := by sorry

/-- The term is less than `1` exactly when the point lies strictly above the line. -/
theorem norm_mul_rpow_pow_lt_one_iff (x : K) (m : ℝ) (k : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k < 1 ↔ ((m * k : ℝ) : WithTop ℝ) < v.embedTop (v x) := by sorry

/-- The term is `1` exactly when the point lies on the line. -/
theorem norm_mul_rpow_pow_eq_one_iff (x : K) (m : ℝ) (k : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k = 1 ↔ v.embedTop (v x) = ((m * k : ℝ) : WithTop ℝ) := by sorry

/-- Comparison of two terms: the term at `(k, x)` is at most the term at `(j, y)` exactly when the
point `(k, e (v x))` lies on or above the line of slope `m` through `(j, e (v y))`. -/
theorem norm_mul_rpow_pow_le_iff (x y : K) (m : ℝ) (k j : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k ≤ ‖y‖ * (v.base ^ m) ^ j ↔
      v.embedTop (v y) + ((m * ((k : ℝ) - j) : ℝ) : WithTop ℝ) ≤ v.embedTop (v x) := by sorry

/-- Strict comparison of two terms. -/
theorem norm_mul_rpow_pow_lt_iff (x y : K) (m : ℝ) (k j : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k < ‖y‖ * (v.base ^ m) ^ j ↔
      v.embedTop (v y) + ((m * ((k : ℝ) - j) : ℝ) : WithTop ℝ) < v.embedTop (v x) := by sorry

/-- Equality of two terms. -/
theorem norm_mul_rpow_pow_eq_iff (x y : K) (m : ℝ) (k j : ℕ) :
    ‖x‖ * (v.base ^ m) ^ k = ‖y‖ * (v.base ^ m) ^ j ↔
      v.embedTop (v x) = v.embedTop (v y) + ((m * ((k : ℝ) - j) : ℝ) : WithTop ℝ) := by sorry

/-! ### Two normed additive valuations on the same field (roadmap §2.2.8) -/

variable {Γ' : Type*} [AddCommGroup Γ'] [LinearOrder Γ'] [IsOrderedAddMonoid Γ']

/-- The positive scalar `log b / log b'` by which the embedded valuations of two normed additive
valuations on the same field differ. -/
noncomputable def scale (w : NormedAddValuation K Γ') : ℝ := Real.log v.base / Real.log w.base

lemma scale_pos (w : NormedAddValuation K Γ') : 0 < v.scale w := by sorry

/-- Both embedded valuations are `-log ‖x‖` up to the scalar. -/
theorem embed_eq_scale_mul_embed (w : NormedAddValuation K Γ') {x : K} {γ : Γ} {γ' : Γ'}
    (hv : v x = (γ : WithTop Γ)) (hw : w x = (γ' : WithTop Γ')) :
    w.embed γ' = v.scale w * v.embed γ := by sorry

/-- The pushed values of `w` are those of `v` scaled by `scale`. -/
theorem embedTop_apply_eq_map (w : NormedAddValuation K Γ') (x : K) :
    w.embedTop (w x) = WithTop.map (fun t : ℝ ↦ v.scale w * t) (v.embedTop (v x)) := by sorry

end Generic

/-! ### The three instances of Layer 1 -/

section Instances

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

open Valuation

/-- The unnormalised member `(normAddVal K, id, exp 1)`. -/
noncomputable def ofNormAddVal : NormedAddValuation K ℝ where
  toAddValuation := normAddVal K
  embed := AddMonoidHom.id ℝ
  strictMono_embed := strictMono_id
  base := Real.exp 1
  one_lt_base := by sorry
  norm_eq_rpow' := by sorry

@[simp] lemma ofNormAddVal_apply (x : K) : ofNormAddVal K x = normAddVal K x := rfl

@[simp] lemma ofNormAddVal_embed : (ofNormAddVal K).embed = AddMonoidHom.id ℝ := rfl

@[simp] lemma ofNormAddVal_base : (ofNormAddVal K).base = Real.exp 1 := rfl

lemma ofNormAddVal_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    ofNormAddVal K x = ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) := by sorry

section Discrete

variable [(valuation (K := K)).IsRankOneDiscrete]

/-- The discrete member `(normAddValZ K, Int.cast, ‖π‖⁻¹)` at a uniformiser `π`. -/
noncomputable def ofNormAddValZ {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    NormedAddValuation K ℤ where
  toAddValuation := normAddValZ K
  embed := Int.castAddHom ℝ
  strictMono_embed := by sorry
  base := ‖π‖⁻¹
  one_lt_base := by sorry
  norm_eq_rpow' := by sorry

@[simp] lemma ofNormAddValZ_apply {π : K} (hπ : IsUniformizer (valuation (K := K)) π) (x : K) :
    ofNormAddValZ K hπ x = normAddValZ K x := rfl

@[simp] lemma ofNormAddValZ_embed {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    (ofNormAddValZ K hπ).embed = Int.castAddHom ℝ := rfl

@[simp] lemma ofNormAddValZ_base {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    (ofNormAddValZ K hπ).base = ‖π‖⁻¹ := rfl

lemma ofNormAddValZ_apply_isUniformizer {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    ofNormAddValZ K hπ π = 1 := by sorry

/-- On a discretely valued field the real member is `-log ‖π‖` times the discrete one. -/
lemma scale_ofNormAddValZ_ofNormAddVal {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    (ofNormAddValZ K hπ).scale (ofNormAddVal K) = -Real.log ‖π‖ := by sorry

end Discrete

section Commensurable

variable (π : K) [(valuation (K := K)).IsCommensurable π]

/-- The rational member `(normAddValQ K π, Rat.cast, ‖π‖⁻¹)` normalised at `π`. -/
noncomputable def ofNormAddValQ : NormedAddValuation K ℚ where
  toAddValuation := normAddValQ K π
  embed := (Rat.castHom ℝ).toAddMonoidHom
  strictMono_embed := by sorry
  base := ‖π‖⁻¹
  one_lt_base := by sorry
  norm_eq_rpow' := by sorry

@[simp] lemma ofNormAddValQ_apply (x : K) : ofNormAddValQ K π x = normAddValQ K π x := rfl

@[simp] lemma ofNormAddValQ_embed :
    (ofNormAddValQ K π).embed = (Rat.castHom ℝ).toAddMonoidHom := rfl

@[simp] lemma ofNormAddValQ_base : (ofNormAddValQ K π).base = ‖π‖⁻¹ := rfl

lemma ofNormAddValQ_self : ofNormAddValQ K π π = 1 := by sorry

end Commensurable

end Instances

end NormedAddValuation

end NormedField
