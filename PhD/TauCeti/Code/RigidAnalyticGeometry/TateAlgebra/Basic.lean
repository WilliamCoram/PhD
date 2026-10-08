/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Algebra
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Complete

/-!
# The Tate algebra as a Banach algebra

For a nonarchimedean normed field `K`, the ring `MvPowerSeries.Restricted K c` of restricted power
series is a normed `K`-algebra for the Gauss norm, an integral domain, and contains the polynomials
as a dense subring. At the unit polyradius it is the Tate algebra `Tₙ = K⟨X₁, …, Xₙ⟩`, whose Gauss
norm is the maximum of the norms of the coefficients and takes its values in `‖K‖`.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.1.1 (BGR 5.1.1). Tau Ceti
home: `TauCeti/RingTheory/TateAlgebra/Basic.lean`.

## Main definitions

* `Affinoid.TateAlgebra K n` — the Tate algebra `Tₙ`, the restricted power series in `Fin n`
  variables at the unit polyradius.

## Main results

* `MvPowerSeries.Restricted.norm_smul_eq` and the `NormedAlgebra K (Restricted K c)` instance.
* `MvPowerSeries.Restricted.denseRange_toRestricted` — polynomials are dense (BGR 5.1.1/1).
* `MvPowerSeries.Restricted.norm_mem_range_norm` — `|Tₙ| = |K|` (BGR 5.1.1).
* `MvPowerSeries.Restricted.exists_norm_smul_eq_one` — a nonzero series is normalised by a scalar
  (BGR 5.1.1/2).
-/

open Filter Topology

namespace MvPowerSeries.Restricted

/-! ### General polyradius -/

section Ring

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*} (c : σ → ℝ)
  [hc : Fact (∀ i, 0 < c i)]

/-- Each Gauss term is bounded by the Gauss norm. -/
theorem norm_coeff_mul_prod_le (f : Restricted R c) (t : σ →₀ ℕ) :
    ‖coeff t f.1‖ * t.prod (c · ^ ·) ≤ ‖f‖ :=
  (norm_le_iff c f).mp le_rfl t

/-- The Gauss norm is attained at some index. Source: BGR 5.1.1 ("`|f| := max |a_ν|` is
well-defined"). -/
theorem exists_norm_eq_norm_coeff_mul_prod (f : Restricted R c) :
    ∃ t : σ →₀ ℕ, ‖f‖ = ‖coeff t f.1‖ * t.prod (c · ^ ·) := by
  obtain ⟨t, ht⟩ := exists_achievesGaussNorm c f
  exact ⟨t, (norm_def c f).trans ht.symm⟩

/-- The constants embed injectively, so `Restricted R c` is nontrivial when `R` is. -/
instance instNontrivial [Nontrivial R] : Nontrivial (Restricted R c) :=
  ⟨⟨0, 1, fun h ↦ zero_ne_one (α := R) <| by
    simpa using congrArg (fun f : Restricted R c ↦ MvPowerSeries.constantCoeff f.1) h⟩⟩

/-- The constants embed injectively, so `Restricted R c` has characteristic zero when `R` has. -/
instance instCharZero [CharZero R] : CharZero (Restricted R c) :=
  charZero_of_injective_ringHom (f := C c) fun a b h ↦ by
    simpa using congrArg (fun f : Restricted R c ↦ MvPowerSeries.constantCoeff f.1) h

/-- The Gauss norm is multiplicative when the norm of `R` is, so `Restricted R c` has no zero
divisors. Source: BGR 5.1.2/1. -/
instance instIsDomain [NormMulClass R] [Nontrivial R] : IsDomain (Restricted R c) := by
  have : NoZeroDivisors R := NormMulClass.toNoZeroDivisors
  have : NoZeroDivisors (Restricted R c) := ⟨fun {f g} h ↦ by
    have h' : f.1 * g.1 = 0 := congrArg (fun x : Restricted R c ↦ x.1) h
    rcases mul_eq_zero.1 h' with h₁ | h₁
    · exact Or.inl (Restricted.ext h₁)
    · exact Or.inr (Restricted.ext h₁)⟩
  exact NoZeroDivisors.to_isDomain _

/-- A restricted power series is approximated in Gauss norm by its finite truncations. -/
theorem exists_finset_norm_sub_sum_monomial_lt (f : Restricted R c) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (σ →₀ ℕ), ‖f - ∑ t ∈ s, monomial c t (coeff t f.1)‖ < ε := by
  have h : Tendsto (fun s : Finset (σ →₀ ℕ) ↦ ∑ t ∈ s, monomial c t (coeff t f.1)) atTop (𝓝 f) :=
    hasSum_monomial c f
  obtain ⟨s, hs⟩ := (h.eventually (Metric.ball_mem_nhds f hε)).exists
  refine ⟨s, ?_⟩
  rwa [dist_eq_norm, norm_sub_rev] at hs

end Ring

section CommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {σ : Type*} (c : σ → ℝ)
  [hc : Fact (∀ i, 0 < c i)]

/-- Polynomials are dense in the restricted power series. Source: BGR 5.1.1/1. -/
theorem denseRange_toRestricted : DenseRange (MvPolynomial.toRestricted (R := R) c) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨s, hs⟩ := exists_finset_norm_sub_sum_monomial_lt c f hε
  refine ⟨∑ t ∈ s, MvPolynomial.monomial t (coeff t f.1), ?_⟩
  rw [dist_eq_norm, map_sum]
  simpa only [MvPolynomial.toRestricted_monomial] using hs

end CommRing

section NormedAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*} (c : σ → ℝ)
  [hc : Fact (∀ i, 0 < c i)]

/-- Scalar multiplication scales the Gauss norm. -/
theorem norm_smul_eq (a : K) (f : Restricted K c) : ‖a • f‖ = ‖a‖ * ‖f‖ := by
  have key (b : K) (g : Restricted K c) : ‖b • g‖ ≤ ‖b‖ * ‖g‖ := by
    refine (norm_le_iff c _).2 fun t ↦ ?_
    have hcoeff : coeff t (b • g).1 = b * coeff t g.1 := by
      simp only [val_smul, MvPowerSeries.coeff_smul]
    rw [hcoeff, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le c g t) (norm_nonneg b)
  refine le_antisymm (key a f) ?_
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · calc ‖a‖ * ‖f‖ = ‖a‖ * ‖a⁻¹ • a • f‖ := by rw [inv_smul_smul₀ ha]
      _ ≤ ‖a‖ * (‖a⁻¹‖ * ‖a • f‖) := mul_le_mul_of_nonneg_left (key _ _) (norm_nonneg a)
      _ = ‖a • f‖ := by
        rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 ha), one_mul]

/-- The Gauss norm makes `Restricted K c` a normed `K`-algebra. Source: BGR 5.1.1/1. -/
noncomputable instance instNormedAlgebra : NormedAlgebra K (Restricted K c) where
  norm_smul_le a f := (norm_smul_eq c a f).le

end NormedAlgebra

/-! ### The unit polyradius -/

instance {σ : Type*} : Fact (∀ i : σ, (0 : ℝ) < (1 : σ → ℝ) i) := ⟨fun _ ↦ one_pos⟩

section UnitRadius

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*}

private lemma prod_one_pow (t : σ →₀ ℕ) : t.prod ((1 : σ → ℝ) · ^ ·) = 1 := by
  simp [Finsupp.prod]

/-- At the unit polyradius every coefficient is bounded by the Gauss norm. -/
theorem norm_coeff_le (f : Restricted R (1 : σ → ℝ)) (t : σ →₀ ℕ) : ‖coeff t f.1‖ ≤ ‖f‖ := by
  have h := norm_coeff_mul_prod_le 1 f t
  rwa [prod_one_pow, mul_one] at h

/-- At the unit polyradius the Gauss norm is the norm of some coefficient: `|f| = max |a_ν|`.
Source: BGR 5.1.1. -/
theorem exists_norm_coeff_eq (f : Restricted R (1 : σ → ℝ)) :
    ∃ t : σ →₀ ℕ, ‖coeff t f.1‖ = ‖f‖ := by
  obtain ⟨t, ht⟩ := exists_norm_eq_norm_coeff_mul_prod 1 f
  rw [prod_one_pow, mul_one] at ht
  exact ⟨t, ht.symm⟩

theorem norm_le_iff_forall_norm_coeff_le {ε : ℝ} (f : Restricted R (1 : σ → ℝ)) :
    ‖f‖ ≤ ε ↔ ∀ t, ‖coeff t f.1‖ ≤ ε := by
  rw [norm_le_iff 1 f]
  simp only [prod_one_pow, mul_one]

theorem norm_lt_iff_forall_norm_coeff_lt {ε : ℝ} (f : Restricted R (1 : σ → ℝ)) :
    ‖f‖ < ε ↔ ∀ t, ‖coeff t f.1‖ < ε := by
  rw [norm_lt_iff 1 f]
  simp only [prod_one_pow, mul_one]

/-- The coefficients of a restricted power series at the unit polyradius tend to zero. -/
theorem tendsto_norm_coeff_cofinite (f : Restricted R (1 : σ → ℝ)) :
    Tendsto (fun t ↦ ‖coeff t f.1‖) cofinite (𝓝 0) := by
  have h : Tendsto (fun t : σ →₀ ℕ ↦ ‖coeff t f.1‖ * t.prod ((1 : σ → ℝ) · ^ ·)) cofinite
      (𝓝 0) := f.2
  simpa only [prod_one_pow, mul_one] using h

/-- Only finitely many coefficients of a restricted power series are not small. -/
theorem finite_setOf_le_norm_coeff (f : Restricted R (1 : σ → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    {t | ε ≤ ‖coeff t f.1‖}.Finite := by
  have h := Filter.Tendsto.eventually_lt_const hε (tendsto_norm_coeff_cofinite f)
  rw [Filter.eventually_cofinite] at h
  exact h.subset fun t ht ↦ not_lt.2 ht

/-- The Gauss norm takes its values in the norms of the coefficient ring: `|Tₙ| = |K|`.
Source: BGR 5.1.1 ("Using the fact that `|Tₙ| = |k|`"). -/
theorem norm_mem_range_norm (f : Restricted R (1 : σ → ℝ)) :
    ‖f‖ ∈ Set.range (norm : R → ℝ) := by
  obtain ⟨t, ht⟩ := exists_norm_coeff_eq f
  exact ⟨_, ht⟩

end UnitRadius

section UnitRadiusField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}

/-- Every nonzero series can be normed to length `1` by a scalar. Source: BGR 5.1.1/2. -/
theorem exists_norm_smul_eq_one {f : Restricted K (1 : σ → ℝ)} (hf : f ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ‖a • f‖ = 1 := by
  obtain ⟨t, ht⟩ := exists_norm_coeff_eq f
  have hf' : ‖f‖ ≠ 0 := norm_ne_zero_iff.2 hf
  have h0 : coeff t f.1 ≠ 0 := norm_ne_zero_iff.1 (ht ▸ hf')
  refine ⟨(coeff t f.1)⁻¹, inv_ne_zero h0, ?_⟩
  rw [norm_smul_eq, norm_inv, ht, inv_mul_cancel₀ hf']

end UnitRadiusField

end MvPowerSeries.Restricted

namespace Affinoid

/-- The Tate algebra `Tₙ = K⟨X₁, …, Xₙ⟩` of strictly convergent power series in `n` variables: the
restricted power series at the unit polyradius. Source: BGR 5.1.1; roadmap convention 2. -/
abbrev TateAlgebra (K : Type*) [NormedField K] [IsUltrametricDist K] (n : ℕ) : Type _ :=
  MvPowerSeries.Restricted K (1 : Fin n → ℝ)

end Affinoid
