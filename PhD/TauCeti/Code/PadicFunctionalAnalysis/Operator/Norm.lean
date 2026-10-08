/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Operator.Basic
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Tate

/-!
# The operator norm over a normed ring

The operator norm on `M →L[R] N` is Mathlib's formula `sInf {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}`
(`ContinuousLinearMap.opNorm`), which Mathlib states for a nontrivially normed field of scalars.
This file states it for a semiring of scalars and seminormed modules, as a *scoped* instance
(roadmap convention 6), proves the lemmas that follow from the formula by order theory alone, and
then, over a Tate normed ring, the lemmas that need the scaling trick: a linear map is continuous
if and only if it is bounded, if and only if it is bounded on a ball, so that `‖u x‖ ≤ ‖u‖ * ‖x‖`
for every continuous `u`, and `‖u‖ = ⨆ x, ‖u x‖ / ‖x‖`.

⚠ Over a general normed ring continuity does not imply boundedness (`Operator/Examples.lean`: the
identity from `ℤ_p` with the squared norm to `ℤ_p`). ⚠ `‖u‖` is **not** the supremum of `‖u x‖` over
the closed unit ball when the norm of `M` is not dense in `ℝ`; the two differ by a factor at most
`‖ϖ‖⁻¹` (`opNorm_le_div_of_forall_norm_le`), and Schneider warns of the same thing after his
Corollary 3.2.

The instances are scoped to `ContinuousLinearMap.Ultra`: `open scoped ContinuousLinearMap.Ultra`
activates them. For a nontrivially normed field of scalars Mathlib's `ContinuousLinearMap.hasOpNorm`
is the only global instance and `norm_eq_opNorm` identifies the two on the nose; do not open the
scope in that setting.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §1.1.1, §1.1.2 and §1.1.6.
Tau Ceti home: `TauCeti/Analysis/Normed/Operator/Ultra/Norm.lean`.

## Main results

* `ContinuousLinearMap.Ultra.instNorm` — the scoped operator norm.
* `ContinuousLinearMap.Ultra.norm_map_le_div_mul_of_forall_norm_le` — the scaling trick: a bound
  on a closed ball is a bound everywhere.
* `ContinuousLinearMap.Ultra.continuous_iff_exists_bound` — over a Tate normed ring, continuity
  is boundedness.
* `ContinuousLinearMap.Ultra.le_opNorm` — `‖u x‖ ≤ ‖u‖ * ‖x‖`.
* `ContinuousLinearMap.Ultra.norm_eq_opNorm` — agreement with Mathlib for field scalars.
-/

open Filter Topology

namespace ContinuousLinearMap.Ultra

open NormedRing

/-! ### The formula, for a semiring of scalars -/

section Semiring

variable {R M N : Type*} [Semiring R] [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N]

/-- The operator norm `sInf {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}`, Mathlib's formula, for a semiring
of scalars. Scoped: `open scoped ContinuousLinearMap.Ultra`. Source: roadmap §1.1.1; Mathlib,
`ContinuousLinearMap.opNorm`. -/
noncomputable scoped instance instNorm : Norm (M →L[R] N) :=
  ⟨fun u ↦ sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}⟩

theorem norm_def (u : M →L[R] N) : ‖u‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖} := rfl

/-- Source: Mathlib, `ContinuousLinearMap.bounds_bddBelow`. -/
theorem bounds_bddBelow {u : M →L[R] N} : BddBelow {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖} :=
  ⟨0, fun _ hc ↦ hc.1⟩

/-- Source: roadmap §1.1.1 (`‖u‖ ≥ 0`). -/
theorem opNorm_nonneg (u : M →L[R] N) : 0 ≤ ‖u‖ :=
  Real.sInf_nonneg fun _ hc ↦ hc.1

/-- Source: roadmap §1.1.1 (`‖u‖ ≤ C` from a uniform bound). -/
theorem opNorm_le_bound (u : M →L[R] N) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖u x‖ ≤ C * ‖x‖) :
    ‖u‖ ≤ C :=
  csInf_le bounds_bddBelow ⟨hC, h⟩

/-- Source: roadmap §1.1.1 (`‖0‖ = 0`). -/
@[simp]
theorem opNorm_zero : ‖(0 : M →L[R] N)‖ = 0 :=
  le_antisymm (opNorm_le_bound _ le_rfl fun x ↦ by simp) (opNorm_nonneg _)

/-- Source: roadmap §1.1.1 (`‖u x‖ ≤ ‖u‖ ‖x‖` for any `u` admitting some uniform bound). -/
theorem le_opNorm_of_bound (u : M →L[R] N) (h : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (x : M) :
    ‖u x‖ ≤ ‖u‖ * ‖x‖ := by
  obtain ⟨C, hC⟩ := h
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · have hux := hC x
    rw [← hx, mul_zero] at hux ⊢
    exact hux
  have hne : {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}.Nonempty :=
    ⟨max C 0, le_max_right C 0, fun y ↦
      (hC y).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg y))⟩
  have hlb : ‖u x‖ / ‖x‖ ≤ ‖u‖ := by
    rw [norm_def]
    exact le_csInf hne fun c hc ↦ (div_le_iff₀ hx).2 (hc.2 x)
  calc ‖u x‖ = ‖u x‖ / ‖x‖ * ‖x‖ := (div_mul_cancel₀ _ hx.ne').symm
    _ ≤ ‖u‖ * ‖x‖ := mul_le_mul_of_nonneg_right hlb hx.le

/-- Source: Mathlib, `ContinuousLinearMap.norm_id_le`. -/
theorem norm_id_le : ‖ContinuousLinearMap.id R M‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x ↦ by simp

end Semiring

section Ring

variable {R M N : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N]

/-- Source: roadmap §1.1.1 (`‖−u‖ = ‖u‖`). -/
@[simp]
theorem opNorm_neg (u : M →L[R] N) : ‖-u‖ = ‖u‖ := by
  simp only [norm_def, _root_.neg_apply, norm_neg]

end Ring

/-! ### Continuity is boundedness over a Tate normed ring -/

section Tate

variable {R M N : Type*} [NormedRing R] [NormOneClass R] [NormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- **The scaling trick for linear maps.** A bound on a closed ball is a bound everywhere: if
`‖f x‖ ≤ C` whenever `‖x‖ ≤ ε`, then `‖f x‖ ≤ C / (ε * ‖ϖ‖) * ‖x‖` for every `x`. Source: Schneider,
Proposition 3.1 ("choose an integer `m` such that `|a|^{m+2} < ‖v‖ ≤ |a|^{m+1}`"); Buzzard,
*Eigenvarieties*, §2 ("one can use `ρ` to renormalise elements of `M`"). -/
theorem norm_map_le_div_mul_of_forall_norm_le (ϖ : PseudoUniformizer R) (f : M →ₗ[R] N)
    {ε C : ℝ} (hε : 0 < ε) (h : ∀ x, ‖x‖ ≤ ε → ‖f x‖ ≤ C) (x : M) :
    ‖f x‖ ≤ C / (ε * ‖(ϖ : R)‖) * ‖x‖ := by
  have hC : 0 ≤ C := by simpa using h 0 (by simpa using hε.le)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨n, ⟨h₁, h₂⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc hε hx
  have hfx := h _ h₂
  rw [map_smul, ϖ.norm_zpow_smul] at hfx
  rw [ϖ.norm_zpow_smul] at h₁
  have ht : 0 < ‖(ϖ : R)‖ ^ n := zpow_pos ϖ.norm_pos n
  have hεϖ : 0 < ε * ‖(ϖ : R)‖ := mul_pos hε ϖ.norm_pos
  have h₃ : ‖f x‖ ≤ C / ‖(ϖ : R)‖ ^ n := (le_div_iff₀ ht).2 (by rw [mul_comm]; exact hfx)
  have h₄ : ε * ‖(ϖ : R)‖ / ‖(ϖ : R)‖ ^ n ≤ ‖x‖ :=
    ((div_lt_iff₀ ht).2 (by rw [mul_comm ‖x‖]; exact h₁)).le
  calc ‖f x‖ ≤ C / ‖(ϖ : R)‖ ^ n := h₃
    _ = C / (ε * ‖(ϖ : R)‖) * (ε * ‖(ϖ : R)‖ / ‖(ϖ : R)‖ ^ n) := by
      rw [div_mul_div_comm, mul_comm C, mul_div_mul_left _ _ hεϖ.ne']
    _ ≤ C / (ε * ‖(ϖ : R)‖) * ‖x‖ := mul_le_mul_of_nonneg_left h₄ (div_nonneg hC hεϖ.le)

/-- Source: Johansson–Newton, Definition 2.1.4 ("continuity of an `R`-linear map `φ` is
equivalent to boundedness"); Schneider, Proposition 3.1. -/
theorem exists_bound [IsTate R] (u : M →L[R] N) : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖ := by
  obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := R)
  obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.1 u.continuous.continuousAt 1 one_pos
  refine ⟨1 / (δ / 2 * ‖(ϖ : R)‖),
    norm_map_le_div_mul_of_forall_norm_le ϖ (u : M →ₗ[R] N) (half_pos hδ) fun y hy ↦ ?_⟩
  have hy' := H (x := y) (by rw [dist_zero_right]; linarith)
  rw [map_zero, dist_zero_right] at hy'
  exact hy'.le

/-- Source: roadmap §1.1.2 ("a linear map is continuous if and only if it is bounded"); Schneider,
Proposition 3.1. -/
theorem continuous_iff_exists_bound [IsTate R] (f : M →ₗ[R] N) :
    Continuous f ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖ :=
  ⟨fun hf ↦ exists_bound ⟨f, hf⟩, fun ⟨C, hC⟩ ↦ AddMonoidHomClass.continuous_of_bound f C hC⟩

/-- Source: roadmap §1.1.2 ("if and only if it is bounded on the unit ball"). -/
theorem continuous_iff_exists_forall_norm_le [IsTate R] (f : M →ₗ[R] N) :
    Continuous f ↔ ∃ C, ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ C := by
  rw [continuous_iff_exists_bound]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, fun x hx ↦ (hC x).trans ?_⟩
    calc C * ‖x‖ ≤ max C 0 * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg x)
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hx (le_max_right C 0)
      _ = max C 0 := mul_one _
  · rintro ⟨C, hC⟩
    obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := R)
    exact ⟨_, norm_map_le_div_mul_of_forall_norm_le ϖ f one_pos hC⟩

/-- Source: roadmap §1.1.2 (`‖u x‖ ≤ ‖u‖ ‖x‖` for every `u : M →L[R] N`). -/
theorem le_opNorm [IsTate R] (u : M →L[R] N) (x : M) : ‖u x‖ ≤ ‖u‖ * ‖x‖ :=
  le_opNorm_of_bound u (exists_bound u) x

/-- Source: roadmap §1.1.2 (the unit-ball bound controls the norm up to `‖ϖ‖⁻¹`). -/
theorem opNorm_le_div_of_forall_norm_le (ϖ : PseudoUniformizer R) (u : M →L[R] N) {ε C : ℝ}
    (hε : 0 < ε) (h : ∀ x, ‖x‖ ≤ ε → ‖u x‖ ≤ C) : ‖u‖ ≤ C / (ε * ‖(ϖ : R)‖) := by
  have hC : 0 ≤ C := by simpa using h 0 (by simpa using hε.le)
  exact opNorm_le_bound u (div_nonneg hC (mul_pos hε ϖ.norm_pos).le)
    (norm_map_le_div_mul_of_forall_norm_le ϖ (u : M →ₗ[R] N) hε h)

/-- Source: roadmap §1.1.2 (the norm controls the unit-ball bound). -/
theorem norm_le_opNorm_of_norm_le_one [IsTate R] (u : M →L[R] N) {x : M} (hx : ‖x‖ ≤ 1) :
    ‖u x‖ ≤ ‖u‖ :=
  (le_opNorm u x).trans (mul_le_of_le_one_right (opNorm_nonneg u) hx)

/-- Source: Schneider, Corollary 3.2 (`‖f‖ = sup {‖f(v)‖ / ‖v‖ : v ≠ 0}`); Johansson–Newton,
Definition 2.1.4 (`|φ| = sup_{m ≠ 0} |φ(m)| |m|⁻¹`). -/
theorem opNorm_eq_iSup_div [IsTate R] (u : M →L[R] N) : ‖u‖ = ⨆ x, ‖u x‖ / ‖x‖ := by
  have hle (x : M) : ‖u x‖ / ‖x‖ ≤ ‖u‖ :=
    div_le_of_le_mul₀ (norm_nonneg x) (opNorm_nonneg u) (le_opNorm u x)
  have hbdd : BddAbove (Set.range fun x ↦ ‖u x‖ / ‖x‖) := ⟨‖u‖, Set.forall_mem_range.2 hle⟩
  refine le_antisymm (opNorm_le_bound u
    (Real.iSup_nonneg fun x ↦ div_nonneg (norm_nonneg _) (norm_nonneg x)) fun x ↦ ?_) (ciSup_le hle)
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · have hux := le_opNorm u x
    rw [← hx, mul_zero] at hux ⊢
    exact hux
  calc ‖u x‖ = ‖u x‖ / ‖x‖ * ‖x‖ := (div_mul_cancel₀ _ hx.ne').symm
    _ ≤ (⨆ y, ‖u y‖ / ‖y‖) * ‖x‖ := mul_le_mul_of_nonneg_right (le_ciSup hbdd x) hx.le

end Tate

/-! ### Agreement with Mathlib -/

section Field

variable {K M N : Type*} [NontriviallyNormedField K] [NormedAddCommGroup M] [NormedSpace K M]
  [NormedAddCommGroup N] [NormedSpace K N]

/-- **Agreement with Mathlib** (roadmap §1.1.6): for field scalars the scoped norm is
`ContinuousLinearMap.opNorm`, on the nose. -/
theorem norm_eq_opNorm (u : M →L[K] N) :
    @norm _ instNorm u = @norm _ ContinuousLinearMap.hasOpNorm u := rfl

end Field

end ContinuousLinearMap.Ultra
