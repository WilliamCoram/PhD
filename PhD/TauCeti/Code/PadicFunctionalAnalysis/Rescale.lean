/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Module
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Tate

/-!
# Rescaling a norm to a discrete value set

For `0 < c < 1`, `Real.zpowCeil c x` is the least integer power of `c` that is at least `x`. For a
pseudo-uniformiser `ϖ` of a normed ring `R` and an ultrametric normed `R`-module `M`, the *rescaled
norm* `‖m‖' = zpowCeil ‖ϖ‖ ‖m‖` is an ultrametric norm with values in `‖ϖ‖ ^ ℤ ∪ {0}`,
bounded-equivalent to the original (`‖ϖ‖ * ‖m‖' < ‖m‖ ≤ ‖m‖'`), and `ϖ` still scales it exactly.
It lives on the type synonym `Rescaled ϖ M`. This is Serre's first step towards an orthonormal
basis.

⚠ The rescaled module is a normed module over the *rescaled ring* `Rescaled ϖ R`. It is a normed
module over `R` itself only when the norm of `R` already takes its values in `‖ϖ‖ ^ ℤ ∪ {0}` — over
`ℂ_p` with `ϖ = p`, an `r` of norm `p ^ (-1/2)` has `‖r • 1‖' = 1 > ‖r‖ * ‖1‖'`.

⚠ Ultrametricity of `M` is needed for the triangle inequality: `zpowCeil c` is not subadditive
(`zpowCeil (1/2) 0.51 = 1 > 1/2 + 1/64 = zpowCeil (1/2) 0.5 + zpowCeil (1/2) 0.01`).

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.3.3. Tau Ceti home:
`TauCeti/Analysis/Normed/Module/Ultra/Rescale.lean`.

## Main definitions

* `Real.zpowCeil c x` — the least `c ^ n` (`n : ℤ`) with `x ≤ c ^ n`.
* `NormedRing.PseudoUniformizer.Rescaled ϖ M` — `M` with the rescaled norm.
* `NormedRing.PseudoUniformizer.toRescaled` — the identity, as a linear equivalence.
-/

open Filter Topology

/-! ### The least integer power above a real number -/

namespace Real

/-- The least integer power of `c` that is at least `x`: `inf {c ^ n | n : ℤ, x ≤ c ^ n}`. For
`0 < c < 1` it is `c ^ ⌊logb c x⌋` when `0 < x` and `0` when `x ≤ 0`. Source: Schneider, proof of
Proposition 10.1 (`‖v‖ := inf {s ∈ |K| : s ≥ ‖v‖'}`); Bellaïche, proof of Theorem II.1.13. -/
noncomputable def zpowCeil (c x : ℝ) : ℝ := sInf {y | ∃ n : ℤ, y = c ^ n ∧ x ≤ c ^ n}

variable {c x y : ℝ}

private theorem bddBelow_zpowCeil_set (hc₀ : 0 < c) (x : ℝ) :
    BddBelow {y | ∃ n : ℤ, y = c ^ n ∧ x ≤ c ^ n} :=
  ⟨0, fun _ ⟨n, hy, _⟩ ↦ hy ▸ (zpow_pos hc₀ n).le⟩

/-- For `0 < c < 1` and `0 < x`, `x ≤ c ^ n` exactly when `n ≤ ⌊logb c x⌋`. -/
private theorem le_zpow_iff (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) (n : ℤ) :
    x ≤ c ^ n ↔ n ≤ ⌊logb c x⌋ := by
  rw [Int.le_floor]
  have h := rpow_le_rpow_left_iff_of_base_lt_one hc₀ hc₁ (y := logb c x) (z := (n : ℝ))
  rw [rpow_logb hc₀ hc₁.ne hx, rpow_intCast] at h
  exact h

theorem zpowCeil_nonneg (hc₀ : 0 < c) : 0 ≤ zpowCeil c x := by
  exact sInf_nonneg fun _ ⟨n, hy, _⟩ ↦ hy ▸ (zpow_pos hc₀ n).le

theorem zpowCeil_of_nonpos (hc₀ : 0 < c) (hc₁ : c < 1) (hx : x ≤ 0) : zpowCeil c x = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (zpowCeil_nonneg hc₀)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hc₁
  calc zpowCeil c x ≤ c ^ (k : ℤ) :=
        csInf_le (bddBelow_zpowCeil_set hc₀ x) ⟨(k : ℤ), rfl, hx.trans (zpow_pos hc₀ _).le⟩
    _ = c ^ k := zpow_natCast c k
    _ ≤ 0 + ε := by rw [zero_add]; exact hk.le

theorem zpowCeil_of_pos (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) :
    zpowCeil c x = c ^ ⌊logb c x⌋ := by
  refine IsLeast.csInf_eq ⟨⟨_, rfl, (le_zpow_iff hc₀ hc₁ hx _).2 le_rfl⟩, fun y ⟨n, hy, hn⟩ ↦ ?_⟩
  rw [hy]
  exact zpow_le_zpow_right_of_le_one₀ hc₀ hc₁.le ((le_zpow_iff hc₀ hc₁ hx n).1 hn)

/-- Source: Schneider, proof of Proposition 10.1 (`‖v‖'/‖v‖ ≤ 1`). -/
theorem le_zpowCeil (hc₀ : 0 < c) (hc₁ : c < 1) : x ≤ zpowCeil c x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [zpowCeil_of_nonpos hc₀ hc₁ hx]
    exact hx
  · rw [zpowCeil_of_pos hc₀ hc₁ hx]
    exact (le_zpow_iff hc₀ hc₁ hx _).2 le_rfl

/-- Source: Schneider, proof of Proposition 10.1 (`r ≤ ‖v‖'/‖v‖`). -/
theorem mul_zpowCeil_lt (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) : c * zpowCeil c x < x := by
  rw [zpowCeil_of_pos hc₀ hc₁ hx, ← zpow_one_add₀ hc₀.ne']
  refine lt_of_not_ge fun h ↦ ?_
  have := (le_zpow_iff hc₀ hc₁ hx _).1 h
  omega

theorem zpowCeil_le_of_le_zpow (hc₀ : 0 < c) {n : ℤ} (h : x ≤ c ^ n) : zpowCeil c x ≤ c ^ n := by
  exact csInf_le (bddBelow_zpowCeil_set hc₀ x) ⟨n, rfl, h⟩

theorem exists_zpowCeil_eq_zpow (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) :
    ∃ n : ℤ, zpowCeil c x = c ^ n := by
  exact ⟨_, zpowCeil_of_pos hc₀ hc₁ hx⟩

@[simp]
theorem zpowCeil_zpow (hc₀ : 0 < c) (hc₁ : c < 1) (n : ℤ) : zpowCeil c (c ^ n) = c ^ n := by
  exact le_antisymm (zpowCeil_le_of_le_zpow hc₀ le_rfl) (le_zpowCeil hc₀ hc₁)

theorem zpowCeil_pos (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) : 0 < zpowCeil c x := by
  obtain ⟨n, hn⟩ := exists_zpowCeil_eq_zpow hc₀ hc₁ hx
  rw [hn]
  exact zpow_pos hc₀ n

theorem zpowCeil_eq_zero_iff (hc₀ : 0 < c) (hc₁ : c < 1) : zpowCeil c x = 0 ↔ x ≤ 0 := by
  exact ⟨fun h ↦ not_lt.1 fun hx ↦ (zpowCeil_pos hc₀ hc₁ hx).ne' h, zpowCeil_of_nonpos hc₀ hc₁⟩

theorem zpowCeil_mono (hc₀ : 0 < c) (hc₁ : c < 1) : Monotone (zpowCeil c) := by
  intro x y hxy
  rcases le_or_gt y 0 with hy | hy
  · rw [zpowCeil_of_nonpos hc₀ hc₁ hy, zpowCeil_of_nonpos hc₀ hc₁ (hxy.trans hy)]
  · obtain ⟨n, hn⟩ := exists_zpowCeil_eq_zpow hc₀ hc₁ hy
    rw [hn]
    exact zpowCeil_le_of_le_zpow hc₀ (hxy.trans (hn ▸ le_zpowCeil hc₀ hc₁))

theorem zpowCeil_max (hc₀ : 0 < c) (hc₁ : c < 1) (x y : ℝ) :
    zpowCeil c (max x y) = max (zpowCeil c x) (zpowCeil c y) := by
  exact (zpowCeil_mono hc₀ hc₁).map_max

/-- Source: Bellaïche, proof of Lemma II.1.12 (`|πm| = |π||m|`, read on the rescaled norm). -/
theorem zpowCeil_zpow_mul (hc₀ : 0 < c) (hc₁ : c < 1) (n : ℤ) (x : ℝ) :
    zpowCeil c (c ^ n * x) = c ^ n * zpowCeil c x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [zpowCeil_of_nonpos hc₀ hc₁ hx, mul_zero,
      zpowCeil_of_nonpos hc₀ hc₁ (mul_nonpos_of_nonneg_of_nonpos (zpow_pos hc₀ n).le hx)]
  have key : ∀ (m : ℤ) (y : ℝ), 0 < y → zpowCeil c (c ^ m * y) ≤ c ^ m * zpowCeil c y := by
    intro m y hy
    obtain ⟨k, hk⟩ := exists_zpowCeil_eq_zpow hc₀ hc₁ hy
    rw [hk, ← zpow_add₀ hc₀.ne']
    refine zpowCeil_le_of_le_zpow hc₀ ?_
    rw [zpow_add₀ hc₀.ne', ← hk]
    exact mul_le_mul_of_nonneg_left (le_zpowCeil hc₀ hc₁) (zpow_pos hc₀ m).le
  refine le_antisymm (key n x hx) ?_
  have h := key (-n) (c ^ n * x) (mul_pos (zpow_pos hc₀ n) hx)
  rw [← mul_assoc, ← zpow_add₀ hc₀.ne', neg_add_cancel, zpow_zero, one_mul] at h
  calc c ^ n * zpowCeil c x ≤ c ^ n * (c ^ (-n) * zpowCeil c (c ^ n * x)) :=
        mul_le_mul_of_nonneg_left h (zpow_pos hc₀ n).le
    _ = zpowCeil c (c ^ n * x) := by
      rw [← mul_assoc, ← zpow_add₀ hc₀.ne', add_neg_cancel, zpow_zero, one_mul]

theorem zpowCeil_mul_le (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    zpowCeil c (x * y) ≤ zpowCeil c x * zpowCeil c y := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [zero_mul, zpowCeil_of_nonpos hc₀ hc₁ le_rfl, zero_mul]
  rcases hy.eq_or_lt with rfl | hy
  · rw [mul_zero, zpowCeil_of_nonpos hc₀ hc₁ le_rfl, mul_zero]
  obtain ⟨a, ha⟩ := exists_zpowCeil_eq_zpow hc₀ hc₁ hx
  obtain ⟨b, hb⟩ := exists_zpowCeil_eq_zpow hc₀ hc₁ hy
  rw [ha, hb, ← zpow_add₀ hc₀.ne']
  refine zpowCeil_le_of_le_zpow hc₀ ?_
  rw [zpow_add₀ hc₀.ne', ← ha, ← hb]
  exact mul_le_mul (le_zpowCeil hc₀ hc₁) (le_zpowCeil hc₀ hc₁) hy.le (zpowCeil_nonneg hc₀)

end Real

/-! ### The rescaled module -/

namespace NormedRing.PseudoUniformizer

variable {R : Type*} [NormedRing R]

/-- A normed `R`-module `M` with its norm rescaled to take values in `‖ϖ‖ ^ ℤ ∪ {0}`. A type
synonym; see `toRescaled`. Source: roadmap §0.3.3; Bellaïche, Theorem II.1.13; Schneider,
Proposition 10.1; Colmez, Proposition 1.1.5. -/
@[nolint unusedArguments]
def Rescaled (_ϖ : PseudoUniformizer R) (M : Type*) : Type _ := M

variable (ϖ : PseudoUniformizer R) (M : Type*)

instance [AddCommGroup M] : AddCommGroup (Rescaled ϖ M) := inferInstanceAs (AddCommGroup M)

instance [AddCommGroup M] [Module R M] : Module R (Rescaled ϖ M) := inferInstanceAs (Module R M)

/-- The identity map `M → Rescaled ϖ M`, as an `R`-linear equivalence. -/
def toRescaled [AddCommGroup M] [Module R M] : M ≃ₗ[R] Rescaled ϖ M := LinearEquiv.refl R M

/-- The identity map `Rescaled ϖ M → M`, used to unfold the rescaled norm. -/
private def ofRescaled : Rescaled ϖ M → M := id

section Norm

variable [NormedAddCommGroup M]

/-- The rescaled norm `m ↦ zpowCeil ‖ϖ‖ ‖m‖`, as a group norm on `M`. Source: roadmap §0.3.3. -/
@[nolint unusedArguments]
noncomputable def rescaledNorm [NormOneClass R] [IsUltrametricDist M] : AddGroupNorm M where
  toFun m := Real.zpowCeil ‖(ϖ : R)‖ ‖m‖
  map_zero' := by
    change Real.zpowCeil ‖(ϖ : R)‖ ‖(0 : M)‖ = 0
    rw [norm_zero]
    exact Real.zpowCeil_of_nonpos ϖ.norm_pos ϖ.norm_lt_one le_rfl
  add_le' m n := by
    change Real.zpowCeil ‖(ϖ : R)‖ ‖m + n‖ ≤
      Real.zpowCeil ‖(ϖ : R)‖ ‖m‖ + Real.zpowCeil ‖(ϖ : R)‖ ‖n‖
    calc Real.zpowCeil ‖(ϖ : R)‖ ‖m + n‖ ≤ Real.zpowCeil ‖(ϖ : R)‖ (max ‖m‖ ‖n‖) :=
          Real.zpowCeil_mono ϖ.norm_pos ϖ.norm_lt_one (IsUltrametricDist.norm_add_le_max m n)
      _ = max (Real.zpowCeil ‖(ϖ : R)‖ ‖m‖) (Real.zpowCeil ‖(ϖ : R)‖ ‖n‖) :=
          Real.zpowCeil_max ϖ.norm_pos ϖ.norm_lt_one _ _
      _ ≤ _ := max_le_add_of_nonneg (Real.zpowCeil_nonneg ϖ.norm_pos)
          (Real.zpowCeil_nonneg ϖ.norm_pos)
  neg' m := by
    change Real.zpowCeil ‖(ϖ : R)‖ ‖-m‖ = Real.zpowCeil ‖(ϖ : R)‖ ‖m‖
    rw [norm_neg]
  eq_zero_of_map_eq_zero' m hm :=
    norm_le_zero_iff.1 ((Real.zpowCeil_eq_zero_iff ϖ.norm_pos ϖ.norm_lt_one).1 hm)

noncomputable instance [NormOneClass R] [IsUltrametricDist M] :
    NormedAddCommGroup (Rescaled ϖ M) :=
  @AddGroupNorm.toNormedAddCommGroup (Rescaled ϖ M) _ (rescaledNorm ϖ M)

variable [NormOneClass R] [IsUltrametricDist M] {M}

private theorem norm_rescaled (m : Rescaled ϖ M) :
    ‖m‖ = Real.zpowCeil ‖(ϖ : R)‖ ‖ofRescaled ϖ M m‖ := rfl

theorem norm_toRescaled [Module R M] (m : M) :
    ‖toRescaled ϖ M m‖ = Real.zpowCeil ‖(ϖ : R)‖ ‖m‖ := rfl

/-- Source: roadmap §0.3.3 (`‖m‖ ≤ ‖m‖'`); Schneider, proof of Proposition 10.1. -/
theorem norm_le_norm_toRescaled [Module R M] (m : M) : ‖m‖ ≤ ‖toRescaled ϖ M m‖ := by
  rw [norm_toRescaled]
  exact Real.le_zpowCeil ϖ.norm_pos ϖ.norm_lt_one

/-- Source: roadmap §0.3.3 (`‖π‖ ‖m‖' < ‖m‖`); Schneider, proof of Proposition 10.1. -/
theorem norm_mul_norm_toRescaled_lt [Module R M] {m : M} (hm : m ≠ 0) :
    ‖(ϖ : R)‖ * ‖toRescaled ϖ M m‖ < ‖m‖ := by
  rw [norm_toRescaled]
  exact Real.mul_zpowCeil_lt ϖ.norm_pos ϖ.norm_lt_one (norm_pos_iff.2 hm)

/-- Source: roadmap §0.3.3 ("taking values in `‖π‖ ^ ℤ ∪ {0}`"). -/
theorem exists_norm_rescaled_eq_zpow {m : Rescaled ϖ M} (hm : m ≠ 0) :
    ∃ n : ℤ, ‖m‖ = ‖(ϖ : R)‖ ^ n := by
  have hm' : (0 : ℝ) < ‖(show M from m)‖ := norm_pos_iff.2 hm
  exact Real.exists_zpowCeil_eq_zpow ϖ.norm_pos ϖ.norm_lt_one hm'

/-- The rescaled norm is unchanged when the norm already takes its values in `‖ϖ‖ ^ ℤ ∪ {0}`. -/
theorem norm_toRescaled_eq_of_forall_exists_zpow [Module R M]
    (h : ∀ m : M, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖(ϖ : R)‖ ^ n) (m : M) : ‖toRescaled ϖ M m‖ = ‖m‖ := by
  rw [norm_toRescaled]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [norm_zero]
    exact Real.zpowCeil_of_nonpos ϖ.norm_pos ϖ.norm_lt_one le_rfl
  · obtain ⟨n, hn⟩ := h m hm
    rw [hn]
    exact Real.zpowCeil_zpow ϖ.norm_pos ϖ.norm_lt_one n

variable (M)

/-- Source: roadmap §0.3.3 ("ultrametric"). -/
instance : IsUltrametricDist (Rescaled ϖ M) := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun m n ↦ ?_
  rw [norm_rescaled, norm_rescaled, norm_rescaled, ← Real.zpowCeil_max ϖ.norm_pos ϖ.norm_lt_one]
  exact Real.zpowCeil_mono ϖ.norm_pos ϖ.norm_lt_one
    (IsUltrametricDist.norm_add_le_max (ofRescaled ϖ M m) (ofRescaled ϖ M n))

/-- Source: roadmap §0.3.3 ("complete when the original is"). -/
instance [CompleteSpace M] : CompleteSpace (Rescaled ϖ M) := by
  have hc₀ := ϖ.norm_pos
  have hc₁ := ϖ.norm_lt_one
  refine (AddEquiv.completeSpace_congr_of_bounds (show M ≃+ Rescaled ϖ M from AddEquiv.refl M)
    (C := ‖(ϖ : R)‖⁻¹) (C' := 1) (fun x ↦ ?_) (fun y ↦ ?_)).1 inferInstance
  · change Real.zpowCeil ‖(ϖ : R)‖ ‖x‖ ≤ ‖(ϖ : R)‖⁻¹ * ‖x‖
    rcases eq_or_ne x 0 with rfl | hx
    · rw [norm_zero, mul_zero]
      exact (Real.zpowCeil_of_nonpos hc₀ hc₁ le_rfl).le
    · rw [le_inv_mul_iff₀ hc₀]
      exact (Real.mul_zpowCeil_lt hc₀ hc₁ (norm_pos_iff.2 hx)).le
  · rw [norm_rescaled, one_mul]
    exact Real.le_zpowCeil hc₀ hc₁

variable {M} [Module R M] [IsBoundedSMul R M]

/-- Source: roadmap §0.3.3 (`‖π • m‖' = ‖π‖ ‖m‖'`). -/
theorem norm_smul_rescaled (m : Rescaled ϖ M) : ‖(ϖ : R) • m‖ = ‖(ϖ : R)‖ * ‖m‖ := by
  have h := Real.zpowCeil_zpow_mul ϖ.norm_pos ϖ.norm_lt_one 1 ‖ofRescaled ϖ M m‖
  rw [zpow_one] at h
  have h' : ‖ofRescaled ϖ M ((ϖ : R) • m)‖ = ‖(ϖ : R)‖ * ‖ofRescaled ϖ M m‖ :=
    ϖ.norm_smul (ofRescaled ϖ M m)
  rw [norm_rescaled, norm_rescaled, h']
  exact h

variable (M)

/-- When the norm of `R` takes its values in `‖ϖ‖ ^ ℤ ∪ {0}`, the rescaled module is a normed
`R`-module. Source: Bellaïche, Hypothesis II.1.11 and Theorem II.1.13. -/
theorem isBoundedSMul_rescaled (h : ∀ r : R, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : R)‖ ^ n) :
    IsBoundedSMul R (Rescaled ϖ M) := by
  have hc₀ := ϖ.norm_pos
  have hc₁ := ϖ.norm_lt_one
  have key : ∀ (r : R) (m : M),
      Real.zpowCeil ‖(ϖ : R)‖ ‖r • m‖ ≤ ‖r‖ * Real.zpowCeil ‖(ϖ : R)‖ ‖m‖ := by
    intro r m
    rcases eq_or_ne r 0 with rfl | hr
    · rw [zero_smul, norm_zero, norm_zero, zero_mul, Real.zpowCeil_of_nonpos hc₀ hc₁ le_rfl]
    rcases eq_or_ne m 0 with rfl | hm
    · rw [smul_zero, norm_zero, Real.zpowCeil_of_nonpos hc₀ hc₁ le_rfl, mul_zero]
    obtain ⟨k, hk⟩ := h r hr
    obtain ⟨N, hN⟩ := Real.exists_zpowCeil_eq_zpow hc₀ hc₁ (norm_pos_iff.2 hm)
    rw [hk, hN, ← zpow_add₀ hc₀.ne']
    refine Real.zpowCeil_le_of_le_zpow hc₀ ?_
    rw [zpow_add₀ hc₀.ne', ← hk, ← hN]
    exact (norm_smul_le r m).trans
      (mul_le_mul_of_nonneg_left (Real.le_zpowCeil hc₀ hc₁) (norm_nonneg r))
  exact .of_norm_smul_le fun r m ↦ key r (ofRescaled ϖ M m)

end Norm

end NormedRing.PseudoUniformizer
