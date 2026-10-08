/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Multiplicative

/-!
# Tate normed rings

A normed ring is *Tate* if it has a *multiplicative pseudo-uniformiser*: a unit `ϖ` with
`‖ϖ * x‖ = ‖ϖ‖ * ‖x‖` for all `x` and `‖ϖ‖ < 1` (Johansson–Newton, Definition 2.1.2). A
*Banach–Tate ring* is a complete one. The pseudo-uniformiser is data (`PseudoUniformizer R`); the
class `NormedRing.IsTate R` is the Prop that one exists. A pseudo-uniformiser performs every
scaling argument that a ground field performs for Banach spaces: every nonzero vector of a normed
module is moved into the shell `‖ϖ‖ < ‖ϖ ^ n • m‖ ≤ 1` by a unique integer power.

⚠ `NormedRing.IsTate` is a condition on a *norm*. Huber's topological notion of a Tate ring is a
different object; `Huber.lean` and `GaugeNorm.lean` pass between the two.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.4.1–§0.4.4. Tau Ceti home:
`TauCeti/Analysis/Normed/Ring/Ultra/Tate.lean`.

## Main definitions

* `NormedRing.PseudoUniformizer R` — a multiplicative unit of norm less than `1`.
* `NormedRing.IsTate R` — a pseudo-uniformiser exists.
* `NormedRing.PseudoUniformizer.val` — the valuation `v_ϖ`, normalised by `v_ϖ ϖ = 1`.
* `NormedRing.PseudoUniformizer.ofNormedAlgebra` — the pseudo-uniformiser `c • 1` of a normed
  algebra over a field.

## Main results

* `NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc` — the scaling trick.
* `NormedRing.isTate_of_normedAlgebra` — the bridge lemma.
-/

open Filter Topology

namespace NormedRing

/-- A **multiplicative pseudo-uniformiser** of a normed ring: a multiplicative unit of norm less
than `1`. Source: Johansson–Newton, Definition 2.1.2. -/
structure PseudoUniformizer (R : Type*) [NormedRing R] where
  /-- The underlying unit. -/
  unit : Rˣ
  /-- It is multiplicative: `‖ϖ * x‖ = ‖ϖ‖ * ‖x‖`. -/
  isMultiplicative : IsMultiplicative (unit : R)
  /-- Its norm is less than `1`. -/
  norm_lt_one : ‖(unit : R)‖ < 1

/-- A normed ring is **Tate** if it has a multiplicative pseudo-uniformiser. Source:
Johansson–Newton, Definition 2.1.2. -/
class IsTate (R : Type*) [NormedRing R] : Prop where
  /-- There is a multiplicative pseudo-uniformiser. -/
  exists_pseudoUniformizer : Nonempty (PseudoUniformizer R)

namespace PseudoUniformizer

variable {R : Type*} [NormedRing R]

/-- A pseudo-uniformiser coerces to its underlying element: `(ϖ : R)` elaborates to
`((ϖ.unit : Rˣ) : R)`, so no simp lemma relating the two is needed. -/
instance : CoeOut (PseudoUniformizer R) R := ⟨fun ϖ ↦ ϖ.unit⟩

/-- A nontrivial normed ring with a pseudo-uniformiser has `‖1‖ = 1`, since `‖ϖ‖ = ‖ϖ * 1‖ =
‖ϖ‖ * ‖1‖` and `‖ϖ‖ ≠ 0`. So the hypothesis `[NormOneClass R]` of this file says no more than
`[Nontrivial R]`; it is not an instance because it depends on `ϖ`. Source: Johansson–Newton,
Definition 2.1.1(1) (`|1| = 1`). -/
theorem normOneClass_of_nontrivial [Nontrivial R] (ϖ : PseudoUniformizer R) : NormOneClass R := by
  refine ⟨?_⟩
  have h := ϖ.isMultiplicative 1
  rw [mul_one] at h
  have h0 : ‖(ϖ.unit : R)‖ ≠ 0 := norm_ne_zero_iff.2 ϖ.unit.ne_zero
  exact (mul_right_eq_self₀.1 h.symm).resolve_right h0

/-! ### Norms of powers -/

section Norm

variable [NormOneClass R] (ϖ : PseudoUniformizer R)

/-- Source: roadmap §0.4.1. -/
theorem norm_pos : 0 < ‖(ϖ : R)‖ := by
  exact ϖ.isMultiplicative.norm_pos

/-- Source: roadmap §0.4.1 (`‖ϖ⁻¹‖ = ‖ϖ‖⁻¹`); Johansson–Newton, §2.1. -/
theorem norm_inv : ‖((ϖ.unit⁻¹ : Rˣ) : R)‖ = ‖(ϖ : R)‖⁻¹ := by
  exact ϖ.isMultiplicative.norm_inv

/-- Source: roadmap §0.4.1. -/
theorem norm_zpow (n : ℤ) : ‖((ϖ.unit ^ n : Rˣ) : R)‖ = ‖(ϖ : R)‖ ^ n := by
  exact ϖ.isMultiplicative.norm_zpow n

/-- Source: roadmap §0.4.1. -/
theorem log_norm_neg : Real.log ‖(ϖ : R)‖ < 0 := by
  exact Real.log_neg ϖ.norm_pos ϖ.norm_lt_one

variable {M : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- Source: Johansson–Newton, Definition 2.1.4 (the remark on multiplicative units). -/
theorem norm_smul (m : M) : ‖(ϖ : R) • m‖ = ‖(ϖ : R)‖ * ‖m‖ := by
  exact ϖ.isMultiplicative.norm_smul m

/-- Source: roadmap §0.4.2. -/
theorem norm_zpow_smul (n : ℤ) (m : M) :
    ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ = ‖(ϖ : R)‖ ^ n * ‖m‖ := by
  exact ϖ.isMultiplicative.norm_zpow_smul n m

/-! ### The scaling trick -/

/-- **The scaling trick.** Source: roadmap §0.4.2; Buzzard, *Eigenvarieties*, §2 ("one can use `ρ`
to renormalise elements of `M`"); Johansson–Newton, Definition 2.1.5 ("using a multiplicative
pseudo-uniformizer `ϖ` for what Buzzard calls `ρ`"). -/
theorem existsUnique_zpow_norm_smul_mem_Ioc {δ : ℝ} (hδ : 0 < δ) {m : M} (hm : m ≠ 0) :
    ∃! n : ℤ, ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ ∈ Set.Ioc (δ * ‖(ϖ : R)‖) δ := by
  simp only [ϖ.norm_zpow_smul, Set.mem_Ioc]
  obtain ⟨c, hc⟩ : ∃ c, c = ‖(ϖ : R)‖ := ⟨_, rfl⟩
  rw [← hc]
  have hc₀ : 0 < c := hc ▸ ϖ.norm_pos
  have hc₁ : c < 1 := hc ▸ ϖ.norm_lt_one
  have hm' : 0 < ‖m‖ := norm_pos_iff.2 hm
  have hinv : ∀ j : ℤ, c ^ j * c⁻¹ ^ j = 1 := fun j ↦ by
    rw [inv_zpow, mul_inv_cancel₀ (zpow_pos hc₀ j).ne']
  obtain ⟨k, hk₁, hk₂⟩ := exists_mem_Ioc_zpow (div_pos hm' hδ) ((one_lt_inv₀ hc₀).2 hc₁)
  have hk₁' : δ < c ^ k * ‖m‖ := by
    calc δ = c ^ k * (c⁻¹ ^ k * δ) := by rw [← mul_assoc, hinv, one_mul]
      _ < c ^ k * ‖m‖ := mul_lt_mul_of_pos_left ((lt_div_iff₀ hδ).1 hk₁) (zpow_pos hc₀ k)
  have hex₁ : δ * c < c ^ (k + 1) * ‖m‖ := by
    calc δ * c < c ^ k * ‖m‖ * c := mul_lt_mul_of_pos_right hk₁' hc₀
      _ = c ^ (k + 1) * ‖m‖ := by rw [zpow_add_one₀ hc₀.ne']; ring
  have hex₂ : c ^ (k + 1) * ‖m‖ ≤ δ := by
    calc c ^ (k + 1) * ‖m‖ ≤ c ^ (k + 1) * (c⁻¹ ^ (k + 1) * δ) :=
          mul_le_mul_of_nonneg_left ((div_le_iff₀ hδ).1 hk₂) (zpow_pos hc₀ _).le
      _ = δ := by rw [← mul_assoc, hinv, one_mul]
  have key : ∀ n n' : ℤ, n < n' → c ^ n * ‖m‖ ≤ δ → δ * c < c ^ n' * ‖m‖ → False := by
    intro n n' hlt hn hn'
    have hle : c ^ n' ≤ c ^ (n + 1) := zpow_le_zpow_right_of_le_one₀ hc₀ hc₁.le (by omega)
    have : c ^ n' * ‖m‖ ≤ δ * c := by
      calc c ^ n' * ‖m‖ ≤ c ^ (n + 1) * ‖m‖ := mul_le_mul_of_nonneg_right hle hm'.le
        _ = c * (c ^ n * ‖m‖) := by rw [zpow_add_one₀ hc₀.ne']; ring
        _ ≤ c * δ := mul_le_mul_of_nonneg_left hn hc₀.le
        _ = δ * c := mul_comm _ _
    linarith
  refine ⟨k + 1, ⟨hex₁, hex₂⟩, fun n hn ↦ ?_⟩
  rcases lt_trichotomy n (k + 1) with h | h | h
  · exact (key n (k + 1) h hn.2 hex₁).elim
  · exact h
  · exact (key (k + 1) n h hex₂ hn.1).elim

/-- Source: roadmap §0.4.2 (the shell `‖ϖ‖ < ‖ϖ ^ n • m‖ ≤ 1`). -/
theorem existsUnique_zpow_norm_smul_mem_Ioc_one {m : M} (hm : m ≠ 0) :
    ∃! n : ℤ, ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ ∈ Set.Ioc ‖(ϖ : R)‖ 1 := by
  simpa using ϖ.existsUnique_zpow_norm_smul_mem_Ioc one_pos hm

end Norm

/-! ### The valuation `v_ϖ` -/

open Classical in
/-- The valuation of a pseudo-uniformiser: `v_ϖ r = log ‖r‖ / log ‖ϖ‖`, with `v_ϖ 0 = ⊤`, so that
`v_ϖ ϖ = 1`. It is **not** an `AddValuation` unless the norm is multiplicative. Source:
Johansson–Newton, Definition 2.1.2 (`v_ϖ(r) = −log_a |r|`, `a = |ϖ⁻¹|`). -/
noncomputable def val (ϖ : PseudoUniformizer R) (r : R) : WithTop ℝ :=
  if r = 0 then ⊤ else ((Real.log ‖r‖ / Real.log ‖(ϖ : R)‖ : ℝ) : WithTop ℝ)

section Val

variable (ϖ : PseudoUniformizer R) {r s : R}

@[simp]
theorem val_zero : ϖ.val 0 = ⊤ := by
  simp [val]

theorem val_of_ne_zero (hr : r ≠ 0) :
    ϖ.val r = ((Real.log ‖r‖ / Real.log ‖(ϖ : R)‖ : ℝ) : WithTop ℝ) := by
  rw [val, if_neg hr]

@[simp]
theorem val_eq_top_iff : ϖ.val r = ⊤ ↔ r = 0 := by
  by_cases hr : r = 0 <;> simp [val, hr]

variable [NormOneClass R]

/-- Source: roadmap §0.4.3 (`val ϖ ϖ = 1`). -/
@[simp]
theorem val_self : ϖ.val (ϖ : R) = 1 := by
  have : Nontrivial R := NormOneClass.nontrivial
  rw [ϖ.val_of_ne_zero ϖ.unit.ne_zero, div_self ϖ.log_norm_neg.ne, WithTop.coe_one]

@[simp]
theorem val_one : ϖ.val (1 : R) = 0 := by
  have : Nontrivial R := NormOneClass.nontrivial
  rw [ϖ.val_of_ne_zero one_ne_zero, norm_one, Real.log_one, zero_div, WithTop.coe_zero]

/-- Source: roadmap §0.4.3. -/
@[simp]
theorem val_zpow_self (n : ℤ) : ϖ.val ((ϖ.unit ^ n : Rˣ) : R) = ((n : ℝ) : WithTop ℝ) := by
  have : Nontrivial R := NormOneClass.nontrivial
  rw [ϖ.val_of_ne_zero (ϖ.unit ^ n).ne_zero, ϖ.norm_zpow, Real.log_zpow, mul_div_assoc,
    div_self ϖ.log_norm_neg.ne, mul_one]

/-- Source: roadmap §0.4.3 ("order-reversing in the norm"). -/
theorem val_le_val_iff : ϖ.val r ≤ ϖ.val s ↔ ‖s‖ ≤ ‖r‖ := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [val_zero, top_le_iff, val_eq_top_iff, norm_zero, norm_le_zero_iff]
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [val_zero, le_top, norm_zero, norm_nonneg]
  rw [ϖ.val_of_ne_zero hr, ϖ.val_of_ne_zero hs, WithTop.coe_le_coe,
    div_le_div_right_of_neg ϖ.log_norm_neg,
    Real.log_le_log_iff (norm_pos_iff.2 hs) (norm_pos_iff.2 hr)]

theorem val_lt_val_iff : ϖ.val r < ϖ.val s ↔ ‖s‖ < ‖r‖ := by
  simp only [← not_le, ϖ.val_le_val_iff]

theorem val_nonneg_iff : 0 ≤ ϖ.val r ↔ ‖r‖ ≤ 1 := by
  rw [← ϖ.val_one, ϖ.val_le_val_iff, norm_one]

/-- Source: roadmap §0.4.3 (`val ϖ (r * s) ≥ val ϖ r + val ϖ s`). -/
theorem val_add_val_le_val_mul (r s : R) : ϖ.val r + ϖ.val s ≤ ϖ.val (r * s) := by
  rcases eq_or_ne (r * s) 0 with h | h
  · rw [h, val_zero]
    exact le_top
  have hr : r ≠ 0 := left_ne_zero_of_mul h
  have hs : s ≠ 0 := right_ne_zero_of_mul h
  rw [ϖ.val_of_ne_zero hr, ϖ.val_of_ne_zero hs, ϖ.val_of_ne_zero h, ← WithTop.coe_add,
    WithTop.coe_le_coe, ← add_div, div_le_div_right_of_neg ϖ.log_norm_neg,
    ← Real.log_mul (norm_ne_zero_iff.2 hr) (norm_ne_zero_iff.2 hs)]
  exact Real.log_le_log (norm_pos_iff.2 h) (_root_.norm_mul_le r s)

omit [NormOneClass R] in
/-- Source: roadmap §0.4.3 ("with equality when the norm is multiplicative"). -/
theorem val_mul [NormMulClass R] (r s : R) : ϖ.val (r * s) = ϖ.val r + ϖ.val s := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hrs : r * s ≠ 0 := by
    rw [← norm_ne_zero_iff, _root_.norm_mul]
    exact mul_ne_zero (norm_ne_zero_iff.2 hr) (norm_ne_zero_iff.2 hs)
  rw [ϖ.val_of_ne_zero hr, ϖ.val_of_ne_zero hs, ϖ.val_of_ne_zero hrs, _root_.norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 hr) (norm_ne_zero_iff.2 hs), add_div, WithTop.coe_add]

/-- Source: roadmap §0.4.3 (`val ϖ (r + s) ≥ min`). -/
theorem min_val_le_val_add [IsUltrametricDist R] (r s : R) :
    min (ϖ.val r) (ϖ.val s) ≤ ϖ.val (r + s) := by
  rcases le_total ‖r‖ ‖s‖ with h | h
  · exact min_le_of_right_le (ϖ.val_le_val_iff.2
      ((IsUltrametricDist.norm_add_le_max r s).trans (max_le h le_rfl)))
  · exact min_le_of_left_le (ϖ.val_le_val_iff.2
      ((IsUltrametricDist.norm_add_le_max r s).trans (max_le le_rfl h)))

/-- Source: roadmap §0.4.3 (`‖r‖ = ‖ϖ‖ ^ (val ϖ r)`). -/
theorem norm_eq_rpow_of_val_eq {q : ℝ} (h : ϖ.val r = (q : WithTop ℝ)) :
    ‖r‖ = ‖(ϖ : R)‖ ^ q := by
  have hr : r ≠ 0 := by
    rintro rfl
    rw [val_zero] at h
    exact WithTop.top_ne_coe h
  rw [ϖ.val_of_ne_zero hr, WithTop.coe_inj] at h
  have hL := ϖ.log_norm_neg.ne
  have hmul : Real.log ‖(ϖ : R)‖ * (Real.log ‖r‖ / Real.log ‖(ϖ : R)‖) = Real.log ‖r‖ := by
    field_simp
  rw [← h, Real.rpow_def_of_pos ϖ.norm_pos, hmul, Real.exp_log (norm_pos_iff.2 hr)]

end Val

/-! ### The bridge from normed algebras over a field -/

section NormedAlgebra

variable (K : Type*) [NontriviallyNormedField K] [NormedAlgebra K R]

/-- The pseudo-uniformiser `c • 1` of a normed algebra over a field, for a scalar `0 < ‖c‖ < 1`.
Source: roadmap §0.4.4; Wedhorn, Example 6.13. -/
noncomputable def ofNormedAlgebra [NormOneClass R] {c : K} (hc₀ : c ≠ 0) (hc₁ : ‖c‖ < 1) :
    PseudoUniformizer R where
  unit := Units.map (algebraMap K R : K →* R) (Units.mk0 c hc₀)
  isMultiplicative x := by
    change ‖algebraMap K R c * x‖ = ‖algebraMap K R c‖ * ‖x‖
    rw [← Algebra.smul_def, _root_.norm_smul, norm_algebraMap']
  norm_lt_one := by
    change ‖algebraMap K R c‖ < 1
    rw [norm_algebraMap']
    exact hc₁

@[simp]
theorem coe_ofNormedAlgebra [NormOneClass R] {c : K} (hc₀ : c ≠ 0) (hc₁ : ‖c‖ < 1) :
    ((ofNormedAlgebra K hc₀ hc₁ : PseudoUniformizer R) : R) = algebraMap K R c := rfl

end NormedAlgebra

end PseudoUniformizer

/-- **The bridge lemma.** A normed algebra with `‖1‖ = 1` over a nontrivially normed field is a
Tate normed ring. Source: roadmap §0.4.4; Wedhorn, Example 6.13. -/
theorem isTate_of_normedAlgebra (K R : Type*) [NontriviallyNormedField K] [NormedRing R]
    [NormedAlgebra K R] [NormOneClass R] : IsTate R := by
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one K
  exact ⟨⟨PseudoUniformizer.ofNormedAlgebra K (norm_pos_iff.1 hc₀) hc₁⟩⟩

/-- Source: roadmap §0.4.4 ("every nonarchimedean nontrivially normed field is Banach–Tate"). -/
instance (K : Type*) [NontriviallyNormedField K] : IsTate K :=
  isTate_of_normedAlgebra K K

end NormedRing
