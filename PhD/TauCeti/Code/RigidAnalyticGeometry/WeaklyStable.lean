/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Trace.Basic

/-!
# Weakly stable fields

A nonarchimedean normed field `K`, not assumed complete, is *weakly stable* if every finite
extension `L` of `K`, with its spectral norm, is weakly `K`-cartesian: every `K`-linear functional
on `L` is bounded for the spectral norm, equivalently the spectral norm induces the product
topology of `K ^ [L : K]`. Complete fields and perfect fields are weakly stable; for a perfect
field the trace form supplies enough bounded functionals.

The fraction field of a normed domain with multiplicative norm carries the unique multiplicative
extension of the norm, and this is how the Gauss norm of the Tate algebra becomes a norm on its
fraction field.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.4.1 (BGR 2.2.5/1, 2.3.1/2,
2.3.2/1, 3.2.3/2, 3.5.1/3–4, 3.5.2/1). Tau Ceti home:
`TauCeti/Analysis/Normed/Field/WeaklyStable.lean`.

## Main definitions

* `IsWeaklyStable K` — every finite extension is weakly cartesian for the spectral norm
  (BGR 3.5.2/1).
* `IsFractionRing.normAbsoluteValue A Q`, `IsFractionRing.normedField A Q` — the multiplicative
  extension of the norm of a normed domain to its fraction field.

## Main results

* `Module.Dual.exists_bound_of_forall_exists_ne_zero` — BGR 2.3.1/2.
* `norm_trace_le_spectralNorm` — the trace is a contraction for the spectral norm (BGR 3.2.3/2).
* `exists_bound_of_isSeparable` — finite separable extensions are weakly cartesian (BGR 3.5.1/3).
* `isWeaklyStable_of_perfectField` — BGR 3.5.1/4.
* `isWeaklyStable_of_completeSpace` — BGR 3.5.2 (through 2.3.3/4).
-/

universe u

/-- On a finite-dimensional space, if the functionals bounded with respect to a function `N`
separate the points, then every functional is bounded with respect to `N`.
Source: BGR 2.3.1/2. -/
theorem Module.Dual.exists_bound_of_forall_exists_ne_zero {K : Type*} [NormedField K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (N : V → ℝ)
    (h : ∀ x : V, x ≠ 0 → ∃ φ : V →ₗ[K] K, (∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * N y) ∧ φ x ≠ 0)
    (ψ : V →ₗ[K] K) : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C * N y := by
  let W : Submodule K (Module.Dual K V) :=
    { carrier := {φ | ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * N y}
      add_mem' := by
        rintro φ₁ φ₂ ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
        exact ⟨C₁ + C₂, fun y ↦ (norm_add_le _ _).trans
          (by rw [add_mul]; exact add_le_add (h₁ y) (h₂ y))⟩
      zero_mem' := ⟨0, fun y ↦ by simp⟩
      smul_mem' := by
        rintro a φ ⟨C, hC⟩
        exact ⟨‖a‖ * C, fun y ↦ by
          rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)⟩ }
  have hW : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    obtain ⟨φ, hφW, hφx⟩ := h x hx0
    exact hφx ((Submodule.mem_dualCoannihilator x).1 hx φ hφW)
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW,
      Submodule.dualAnnihilator_bot]
  have hψ : ψ ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  exact hψ

section Trace

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {L : Type*} [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- The trace of a finite extension is a contraction for the spectral norm.
Source: BGR 3.2.3/2. -/
theorem norm_trace_le_spectralNorm (x : L) : ‖Algebra.trace K L x‖ ≤ spectralNorm K L x := by
  have hr : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, norm_mul, norm_neg]
  refine (mul_le_of_le_one_left (norm_nonneg _)
    (IsUltrametricDist.norm_natCast_le_one K _)).trans ?_
  rw [Polynomial.nextCoeff_of_natDegree_pos hr]
  have h := le_ciSup (spectralValueTerms_bddAbove (minpoly K x)) ((minpoly K x).natDegree - 1)
  rw [spectralValueTerms_of_lt_natDegree _ (Nat.sub_lt hr one_pos)] at h
  have hexp : (1 : ℝ) / (((minpoly K x).natDegree : ℝ) -
      (((minpoly K x).natDegree - 1 : ℕ) : ℝ)) = 1 := by
    rw [Nat.cast_sub hr, Nat.cast_one, sub_sub_cancel, div_one]
  rw [hexp, Real.rpow_one] at h
  exact h

/-- **A finite separable extension is weakly cartesian for the spectral norm**: every linear
functional on it is bounded. Source: BGR 3.5.1/3. -/
theorem exists_bound_of_isSeparable [Algebra.IsSeparable K L] (φ : L →ₗ[K] K) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y := by
  refine Module.Dual.exists_bound_of_forall_exists_ne_zero (spectralNorm K L) (fun x hx ↦ ?_) φ
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, Algebra.trace K L (x * y₀) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hx ((traceForm_nondegenerate K L).1 x fun y ↦ by
      rw [Algebra.traceForm_apply]
      exact hcon y)
  refine ⟨(Algebra.trace K L).comp (LinearMap.mulRight K y₀), ⟨spectralNorm K L y₀, fun y ↦ ?_⟩,
    by simpa using hy₀⟩
  refine (norm_trace_le_spectralNorm (y * y₀)).trans ?_
  rw [mul_comm (spectralNorm K L y₀)]
  exact spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic y) (Algebra.IsAlgebraic.isAlgebraic y₀)

end Trace

/-- A nonarchimedean normed field is **weakly stable** if every finite extension is weakly
cartesian for the spectral norm: every linear functional on it is bounded.
Source: BGR 3.5.2/1, with weak cartesianness in the form of BGR 2.3.2/1 (3) and 2.3.1/3. -/
def IsWeaklyStable (K : Type u) [NormedField K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] (φ : L →ₗ[K] K),
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y

/-- **Perfect fields are weakly stable.** Source: BGR 3.5.1/4. -/
theorem isWeaklyStable_of_perfectField (K : Type u) [NormedField K] [IsUltrametricDist K]
    [PerfectField K] : IsWeaklyStable K := by
  intro L _ _ _ φ
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact exists_bound_of_isSeparable φ

/-- **Complete fields are weakly stable.** Source: BGR 3.5.2 ("it follows from Proposition 2.3.3/4
that each complete field `K` is weakly stable"). -/
theorem isWeaklyStable_of_completeSpace (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : IsWeaklyStable K := by
  intro L _ _ _ φ
  letI := spectralNorm.normedField K L
  letI := spectralNorm.normedAlgebra K L
  refine ⟨‖LinearMap.toContinuousLinearMap φ‖, fun y ↦ ?_⟩
  rw [← NormedAlgebra.norm_eq_spectralNorm K y]
  exact (LinearMap.toContinuousLinearMap φ).le_opNorm y

/-! ### The norm of a fraction field -/

namespace IsFractionRing

/-- The value of the norm function of the fraction field on a quotient `a / b`. -/
private lemma raw_div (A : Type*) [NormedCommRing A] [NormMulClass A] [Nontrivial A]
    (Q : Type*) [Field Q] [Algebra A Q] [IsFractionRing A Q] (a : A) {b : A} (hb : b ≠ 0) :
    ‖(IsLocalization.sec (nonZeroDivisors A) (algebraMap A Q a / algebraMap A Q b)).1‖ /
      ‖((IsLocalization.sec (nonZeroDivisors A) (algebraMap A Q a / algebraMap A Q b)).2 : A)‖ =
        ‖a‖ / ‖b‖ := by
  have hspec := IsLocalization.sec_spec (nonZeroDivisors A) (algebraMap A Q a / algebraMap A Q b)
  have hb' : algebraMap A Q b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A Q)).2 hb
  have hs : ((IsLocalization.sec (nonZeroDivisors A)
      (algebraMap A Q a / algebraMap A Q b)).2 : A) ≠ 0 :=
    nonZeroDivisors.ne_zero (IsLocalization.sec (nonZeroDivisors A) _).2.2
  have heq : a * ((IsLocalization.sec (nonZeroDivisors A)
      (algebraMap A Q a / algebraMap A Q b)).2 : A) =
        (IsLocalization.sec (nonZeroDivisors A) (algebraMap A Q a / algebraMap A Q b)).1 * b := by
    apply IsFractionRing.injective A Q
    rw [map_mul, map_mul, ← hspec, div_mul_eq_mul_div, div_mul_cancel₀ _ hb']
  rw [div_eq_div_iff (norm_ne_zero_iff.2 hs) (norm_ne_zero_iff.2 hb), ← norm_mul, ← norm_mul,
    ← heq]

/-- A sum of two quotients as a quotient. -/
private lemma div_add_div_algebraMap (A : Type*) [CommRing A] (Q : Type*) [Field Q] [Algebra A Q]
    [IsFractionRing A Q] (a c : A) {b d : A} (hb : b ≠ 0) (hd : d ≠ 0) :
    algebraMap A Q a / algebraMap A Q b + algebraMap A Q c / algebraMap A Q d =
      algebraMap A Q (a * d + b * c) / algebraMap A Q (b * d) := by
  rw [div_add_div _ _ ((map_ne_zero_iff _ (IsFractionRing.injective A Q)).2 hb)
    ((map_ne_zero_iff _ (IsFractionRing.injective A Q)).2 hd), map_add, map_mul, map_mul, map_mul]

/-- The multiplicative extension of the norm of a normed domain to its fraction field:
`|a / b| = ‖a‖ / ‖b‖`. Source: BGR 3.5.3 ("`K` is the field of fractions of `A`, and the valuation
on `K` extends the valuation on `A`"), 1.5.3. -/
noncomputable def normAbsoluteValue (A : Type*) [NormedCommRing A] [NormMulClass A] [Nontrivial A]
    (Q : Type*) [Field Q] [Algebra A Q] [IsFractionRing A Q] : AbsoluteValue Q ℝ where
  toFun q := ‖(IsLocalization.sec (nonZeroDivisors A) q).1‖ /
    ‖((IsLocalization.sec (nonZeroDivisors A) q).2 : A)‖
  map_mul' := by
    intro q₁ q₂
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A q₁
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective A q₂
    have hb0 := nonZeroDivisors.ne_zero hb
    have hd0 := nonZeroDivisors.ne_zero hd
    rw [div_mul_div_comm, ← map_mul, ← map_mul, raw_div A Q _ (mul_ne_zero hb0 hd0),
      raw_div A Q a hb0, raw_div A Q c hd0, norm_mul, norm_mul, div_mul_div_comm]
  nonneg' _ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  eq_zero' := by
    intro q
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A q
    have hb0 := nonZeroDivisors.ne_zero hb
    rw [raw_div A Q a hb0, div_eq_zero_iff, div_eq_zero_iff, norm_eq_zero, norm_eq_zero,
      map_eq_zero_iff _ (IsFractionRing.injective A Q),
      map_eq_zero_iff _ (IsFractionRing.injective A Q)]
  add_le' := by
    intro q₁ q₂
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A q₁
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective A q₂
    have hb0 := nonZeroDivisors.ne_zero hb
    have hd0 := nonZeroDivisors.ne_zero hd
    rw [div_add_div_algebraMap A Q a c hb0 hd0, raw_div A Q _ (mul_ne_zero hb0 hd0),
      raw_div A Q a hb0, raw_div A Q c hd0,
      div_add_div _ _ (norm_ne_zero_iff.2 hb0) (norm_ne_zero_iff.2 hd0), norm_mul]
    refine div_le_div_of_nonneg_right ((norm_add_le _ _).trans ?_)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [norm_mul, norm_mul]

variable (A : Type*) [NormedCommRing A] [NormMulClass A] [Nontrivial A]
  (Q : Type*) [Field Q] [Algebra A Q] [IsFractionRing A Q]

theorem normAbsoluteValue_algebraMap (a : A) : normAbsoluteValue A Q (algebraMap A Q a) = ‖a‖ := by
  haveI := NormMulClass.toNormOneClass (α := A)
  have h := raw_div A Q a (one_ne_zero (α := A))
  rw [map_one, div_one, norm_one, div_one] at h
  exact h

theorem normAbsoluteValue_div (a : A) {b : A} (hb : b ≠ 0) :
    normAbsoluteValue A Q (algebraMap A Q a / algebraMap A Q b) = ‖a‖ / ‖b‖ :=
  raw_div A Q a hb

theorem isNonarchimedean_normAbsoluteValue [IsUltrametricDist A] :
    IsNonarchimedean (normAbsoluteValue A Q) := by
  intro q₁ q₂
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A q₁
  obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective A q₂
  have hb0 := nonZeroDivisors.ne_zero hb
  have hd0 := nonZeroDivisors.ne_zero hd
  rw [div_add_div_algebraMap A Q a c hb0 hd0, normAbsoluteValue_div A Q _ (mul_ne_zero hb0 hd0),
    normAbsoluteValue_div A Q a hb0, normAbsoluteValue_div A Q c hd0]
  calc ‖a * d + b * c‖ / ‖b * d‖ ≤ max ‖a * d‖ ‖b * c‖ / ‖b * d‖ :=
        div_le_div_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (norm_nonneg _)
    _ = max (‖a * d‖ / ‖b * d‖) (‖b * c‖ / ‖b * d‖) := (max_div_div_right (norm_nonneg _) _ _).symm
    _ = max (‖a‖ / ‖b‖) (‖c‖ / ‖d‖) := by
      rw [norm_mul, norm_mul, norm_mul, mul_div_mul_right _ _ (norm_ne_zero_iff.2 hd0),
        mul_div_mul_left _ _ (norm_ne_zero_iff.2 hb0)]

/-- The fraction field of a normed domain with multiplicative norm, as a normed field. A
reducible definition, not an instance. -/
noncomputable abbrev normedField : NormedField Q :=
  (normAbsoluteValue A Q).toNormedField

theorem isUltrametricDist [IsUltrametricDist A] :
    letI := normedField A Q
    IsUltrametricDist Q := by
  letI := normedField A Q
  exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦
    isNonarchimedean_normAbsoluteValue A Q x y

end IsFractionRing
