/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.MvPolynomial.Eval
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Sums
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Basic

/-!
# Evaluation of restricted power series

Let `R` be a nonarchimedean normed commutative ring, `B` a complete nonarchimedean normed
commutative ring, `φ : R →+* B` a bounded ring homomorphism (`‖φ r‖ ≤ C ‖r‖`) and `x : σ → B` a
tuple whose monomials are bounded relative to the polyradius `c` (`‖x^ν‖ ≤ M c^ν`), for instance a
tuple with `‖x i‖ ≤ c i`, or at the unit polyradius finitely many power-bounded elements. Then every
restricted power series `f = Σ a_ν X^ν` over `R` at the polyradius `c` can be evaluated at `x`: the
series `Σ φ(a_ν) x^ν` converges in `B`, and `f ↦ f(x)` is a bounded ring homomorphism, contractive
when `φ` is contractive and `‖x i‖ ≤ c i`. It is the unique continuous ring homomorphism extending
`φ` and sending `X i` to `x i` (BGR 6.1.1/4).

For a normed field `K` and a Banach `K`-algebra `B` this gives the substitution homomorphisms of
the Tate algebra: evaluation at a point of the unit ball of a complete extension field, and
substitution of power-bounded series for the variables.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 0 (the adic-spaces roadmap's
§0.5.1 "substitution and evaluation", BGR 5.1.3/5, 5.1.4). Tau Ceti home:
`TauCeti/RingTheory/MvPowerSeries/Restricted/Eval.lean`.

## Main definitions

* `MvPowerSeries.Restricted.eval₂` — evaluation along a bounded ring homomorphism at a tuple
  with bounded monomials.
* `MvPowerSeries.Restricted.aeval` — evaluation in a Banach algebra over a normed field.

## Main results

* `MvPowerSeries.Restricted.norm_eval₂_le_mul` — evaluation is bounded by the product of the
  bounds of `φ` and of the monomials; `norm_eval₂_le` — it is contractive in the contractive case
  (BGR 5.1.4/2).
* `MvPowerSeries.Restricted.exists_forall_norm_prod_pow_le` — the monomials of finitely many
  power-bounded elements are bounded.
* `MvPowerSeries.Restricted.ringHom_ext_of_continuous` — a continuous ring homomorphism out of the
  restricted power series is determined by its values on the constants and the variables
  (BGR 5.1.3/5).
-/

open Filter Topology

namespace MvPowerSeries.Restricted

/-! ### Evaluation along a contractive ring homomorphism -/

section eval₂

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {B : Type*} [NormedCommRing B] [IsUltrametricDist B]
  {σ : Type*} (c : σ → ℝ) (φ : R →+* B) (x : σ → B)

omit [IsUltrametricDist R] [IsUltrametricDist B] in
/-- The monomials of a tuple with `‖x i‖ ≤ c i` are bounded by the monomials of the polyradius,
when `‖1‖ ≤ 1`. -/
theorem norm_prod_pow_le_of_norm_le [NormOneClass B] (hx : ∀ i, ‖x i‖ ≤ c i) (t : σ →₀ ℕ) :
    ‖t.prod fun i k ↦ x i ^ k‖ ≤ 1 * t.prod (c · ^ ·) := by
  rw [one_mul, Finsupp.prod, Finsupp.prod]
  refine (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i _ ↦ ?_)
  exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hx i) _)

omit [IsUltrametricDist R] [IsUltrametricDist B] in
/-- The monomials of finitely many power-bounded elements are bounded: `‖x^ν‖ ≤ M` for all `ν`.
Source: BGR 1.2.5/2 (power-bounded elements form a ring), 6.1.1/4 (the series `Σ φ(a_ν) f^ν`
converges because the `fᵢ` are power-bounded). -/
theorem exists_forall_norm_prod_pow_le [Finite σ] (hx : ∀ i, ∃ Cx, ∀ k, ‖x i ^ k‖ ≤ Cx) :
    ∃ Cx, ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ Cx * t.prod ((1 : σ → ℝ) · ^ ·) := by
  classical
  have := Fintype.ofFinite σ
  choose C hC using hx
  refine ⟨max ‖(1 : B)‖ (∏ i, max 1 (C i)), fun t ↦ ?_⟩
  have h1 : t.prod ((1 : σ → ℝ) · ^ ·) = 1 := by simp [Finsupp.prod]
  rw [h1, mul_one, Finsupp.prod]
  rcases t.support.eq_empty_or_nonempty with h | h
  · rw [h, Finset.prod_empty]
    exact le_max_left _ _
  · refine le_trans ?_ (le_max_right _ _)
    calc ‖∏ i ∈ t.support, x i ^ t i‖ ≤ ∏ i ∈ t.support, ‖x i ^ t i‖ :=
          Finset.norm_prod_le' _ h _
      _ ≤ ∏ i ∈ t.support, max 1 (C i) :=
          Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i _ ↦
            (hC i (t i)).trans (le_max_right _ _)
      _ ≤ ∏ i, max 1 (C i) :=
          Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
            (fun i _ ↦ zero_le_one.trans (le_max_left _ _)) fun i _ _ ↦ le_max_left _ _

variable {Cφ Cx : ℝ}

omit [IsUltrametricDist R] [IsUltrametricDist B] in
/-- Each term of the evaluated series is bounded by the corresponding Gauss term. -/
theorem norm_map_mul_prod_pow_le (hφ : ∀ r, ‖φ r‖ ≤ Cφ * ‖r‖)
    (hx : ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ Cx * t.prod (c · ^ ·)) (a : R)
    (t : σ →₀ ℕ) : ‖φ a * t.prod fun i k ↦ x i ^ k‖ ≤ Cφ * Cx * (‖a‖ * t.prod (c · ^ ·)) := by
  calc ‖φ a * t.prod fun i k ↦ x i ^ k‖ ≤ ‖φ a‖ * ‖t.prod fun i k ↦ x i ^ k‖ := norm_mul_le _ _
    _ ≤ (Cφ * ‖a‖) * (Cx * t.prod (c · ^ ·)) :=
        mul_le_mul (hφ a) (hx t) (norm_nonneg _) ((norm_nonneg _).trans (hφ a))
    _ = Cφ * Cx * (‖a‖ * t.prod (c · ^ ·)) := by ring

omit [IsUltrametricDist B] in
/-- The terms of the evaluated series tend to zero. -/
theorem tendsto_map_coeff_mul_prod_pow (hφ : ∀ r, ‖φ r‖ ≤ Cφ * ‖r‖)
    (hx : ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ Cx * t.prod (c · ^ ·)) (f : Restricted R c) :
    Tendsto (fun t : σ →₀ ℕ ↦ φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k) cofinite (𝓝 0) := by
  have h := Filter.Tendsto.const_mul (Cφ * Cx)
    (show Tendsto (fun t : σ →₀ ℕ ↦ ‖coeff t f.1‖ * t.prod (c · ^ ·)) cofinite (𝓝 0) from f.2)
  rw [mul_zero] at h
  exact squeeze_zero_norm (fun t ↦ norm_map_mul_prod_pow_le c φ x hφ hx _ t) h

/-- The evaluated series converges. Source: BGR 5.1.4 ("Since `a_ν x^ν` is a zero-sequence in `L`,
the series `Σ a_ν x^ν` must converge"); 6.1.1/4. -/
theorem summable_map_coeff_mul_prod_pow [CompleteSpace B] (hφ : ∀ r, ‖φ r‖ ≤ Cφ * ‖r‖)
    (hx : ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ Cx * t.prod (c · ^ ·)) (f : Restricted R c) :
    Summable fun t : σ →₀ ℕ ↦ φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_map_coeff_mul_prod_pow c φ x hφ hx f)

/-- The value `Σ φ(a_ν) x^ν` of a restricted power series at the tuple `x`. -/
noncomputable def eval₂Fun (f : Restricted R c) : B :=
  ∑' t : σ →₀ ℕ, φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k

omit [IsUltrametricDist B] in
theorem eval₂Fun_zero : eval₂Fun c φ x 0 = 0 := by
  simp [eval₂Fun]

omit [IsUltrametricDist B] in
theorem eval₂Fun_one : eval₂Fun c φ x 1 = 1 := by
  classical
  unfold eval₂Fun
  rw [tsum_eq_single 0]
  · simp [MvPowerSeries.coeff_one]
  · intro t ht
    simp [MvPowerSeries.coeff_one, ht]

theorem eval₂Fun_add [CompleteSpace B] (hφ : ∀ r, ‖φ r‖ ≤ Cφ * ‖r‖)
    (hx : ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ Cx * t.prod (c · ^ ·))
    (f g : Restricted R c) : eval₂Fun c φ x (f + g) = eval₂Fun c φ x f + eval₂Fun c φ x g := by
  unfold eval₂Fun
  rw [← (summable_map_coeff_mul_prod_pow c φ x hφ hx f).tsum_add
    (summable_map_coeff_mul_prod_pow c φ x hφ hx g)]
  congr 1
  ext t
  rw [val_add, map_add, map_add, add_mul]

/-- Evaluation is multiplicative: the Cauchy product of two evaluated series. -/
theorem eval₂Fun_mul [CompleteSpace B] (hφ : ∀ r, ‖φ r‖ ≤ Cφ * ‖r‖)
    (hx : ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ Cx * t.prod (c · ^ ·))
    (f g : Restricted R c) : eval₂Fun c φ x (f * g) = eval₂Fun c φ x f * eval₂Fun c φ x g := by
  classical
  have hf := summable_map_coeff_mul_prod_pow c φ x hφ hx f
  have hg := summable_map_coeff_mul_prod_pow c φ x hφ hx g
  have hfg := IsUltrametricDist.summable_prod_map₂ (b := fun a b : B ↦ a * b)
    (fun a b ↦ norm_mul_le a b) hf hg
  unfold eval₂Fun
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg]
  congr 1
  ext t
  simp only [val_mul, MvPowerSeries.coeff_mul, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [← hp, Finsupp.prod_add_index' (fun i ↦ pow_zero _) (fun i a b ↦ pow_add _ a b)]
  ring

variable [CompleteSpace B]

/-- Evaluation of restricted power series at a tuple `x` whose monomials are bounded relative to
the polyradius `c`, along a bounded ring homomorphism `φ` of the coefficients.
Source: BGR 5.1.3/5, 5.1.4, 6.1.1/4. -/
noncomputable def eval₂ (hφ : ∀ r, ‖φ r‖ ≤ Cφ * ‖r‖)
    (hx : ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ Cx * t.prod (c · ^ ·)) :
    Restricted R c →+* B where
  toFun := eval₂Fun c φ x
  map_one' := eval₂Fun_one c φ x
  map_mul' := eval₂Fun_mul c φ x hφ hx
  map_zero' := eval₂Fun_zero c φ x
  map_add' := eval₂Fun_add c φ x hφ hx

variable {c φ x} (hφ : ∀ r, ‖φ r‖ ≤ Cφ * ‖r‖)
  (hx : ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ Cx * t.prod (c · ^ ·))

theorem eval₂_apply (f : Restricted R c) :
    eval₂ c φ x hφ hx f = ∑' t : σ →₀ ℕ, φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k := rfl

theorem hasSum_eval₂ (f : Restricted R c) :
    HasSum (fun t : σ →₀ ℕ ↦ φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k) (eval₂ c φ x hφ hx f) :=
  (summable_map_coeff_mul_prod_pow c φ x hφ hx f).hasSum

@[simp]
theorem eval₂_monomial (t : σ →₀ ℕ) (a : R) :
    eval₂ c φ x hφ hx (monomial c t a) = φ a * t.prod fun i k ↦ x i ^ k := by
  classical
  rw [eval₂_apply, tsum_eq_single t]
  · simp
  · intro u hu
    simp [MvPowerSeries.coeff_monomial, hu]

@[simp]
theorem eval₂_C (a : R) : eval₂ c φ x hφ hx (C c a) = φ a := by
  classical
  rw [eval₂_apply, tsum_eq_single 0]
  · simp [MvPowerSeries.coeff_C]
  · intro u hu
    simp [MvPowerSeries.coeff_C, hu]

@[simp]
theorem eval₂_X (i : σ) : eval₂ c φ x hφ hx (X R c i) = x i := by
  classical
  rw [eval₂_apply, tsum_eq_single (Finsupp.single i 1)]
  · simp [MvPowerSeries.coeff_X]
  · intro u hu
    simp [MvPowerSeries.coeff_X, hu]

/-- On polynomials, evaluation is polynomial evaluation. -/
theorem eval₂_toRestricted (p : MvPolynomial σ R) :
    eval₂ c φ x hφ hx (MvPolynomial.toRestricted c p) = MvPolynomial.eval₂ φ x p := by
  have h : (eval₂ c φ x hφ hx).comp (MvPolynomial.toRestricted c) =
      MvPolynomial.eval₂Hom φ x :=
    MvPolynomial.ringHom_ext (fun a ↦ by simp) (fun i ↦ by simp)
  exact RingHom.congr_fun h p

/-- Evaluation is bounded by the product of the bounds (in absolute value: the bounds can be
negative only over the zero ring, where the right-hand side would otherwise be negative).
Source: BGR 5.1.4/2, 6.1.1/4. -/
theorem norm_eval₂_le_mul [Fact (∀ i, 0 < c i)] (f : Restricted R c) :
    ‖eval₂ c φ x hφ hx f‖ ≤ |Cφ * Cx| * ‖f‖ := by
  rw [eval₂_apply]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (abs_nonneg _) (norm_nonneg f)) fun t ↦ ?_
  have hy : 0 ≤ ‖coeff t f.1‖ * t.prod (c · ^ ·) := by
    rw [Finsupp.prod]
    exact mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun i _ ↦ pow_nonneg (Fact.out (p := ∀ i, 0 < c i) i).le _)
  calc ‖φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k‖
      ≤ Cφ * Cx * (‖coeff t f.1‖ * t.prod (c · ^ ·)) := norm_map_mul_prod_pow_le c φ x hφ hx _ t
    _ ≤ |Cφ * Cx| * (‖coeff t f.1‖ * t.prod (c · ^ ·)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hy
    _ ≤ |Cφ * Cx| * ‖f‖ := mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le c f t) (abs_nonneg _)

/-- Evaluation along a contractive homomorphism at a tuple with contractive monomials is
contractive. Source: BGR 5.1.4/2. -/
theorem norm_eval₂_le [Fact (∀ i, 0 < c i)] (hφ : ∀ r, ‖φ r‖ ≤ 1 * ‖r‖)
    (hx : ∀ t : σ →₀ ℕ, ‖t.prod fun i k ↦ x i ^ k‖ ≤ 1 * t.prod (c · ^ ·))
    (f : Restricted R c) : ‖eval₂ c φ x hφ hx f‖ ≤ ‖f‖ := by
  simpa using norm_eval₂_le_mul hφ hx f

theorem continuous_eval₂ [Fact (∀ i, 0 < c i)] : Continuous (eval₂ c φ x hφ hx) :=
  AddMonoidHomClass.continuous_of_bound (eval₂ c φ x hφ hx) |Cφ * Cx| fun f ↦
    norm_eval₂_le_mul hφ hx f

end eval₂

section Ext

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {σ : Type*} {c : σ → ℝ}
  [hc : Fact (∀ i, 0 < c i)] {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B]

/-- A continuous ring homomorphism out of the restricted power series is determined by its values
on the constants and on the variables. Source: BGR 5.1.3/5 ("`φ` is uniquely determined by the
tuple `(φ(X₁), …, φ(Xₙ))`"). -/
theorem ringHom_ext_of_continuous {ψ₁ ψ₂ : Restricted R c →+* B} (h₁ : Continuous ψ₁)
    (h₂ : Continuous ψ₂) (hC : ∀ a, ψ₁ (C c a) = ψ₂ (C c a))
    (hX : ∀ i, ψ₁ (X R c i) = ψ₂ (X R c i)) : ψ₁ = ψ₂ := by
  have hpoly : ψ₁.comp (MvPolynomial.toRestricted c) = ψ₂.comp (MvPolynomial.toRestricted c) :=
    MvPolynomial.ringHom_ext (fun a ↦ by simpa using hC a) (fun i ↦ by simpa using hX i)
  have h := (denseRange_toRestricted c).equalizer h₁ h₂
    (funext fun p ↦ RingHom.congr_fun hpoly p)
  exact RingHom.ext (congrFun h)

end Ext

/-! ### Evaluation in a Banach algebra over a normed field -/

section aeval

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [NormOneClass B] [IsUltrametricDist B]
  [CompleteSpace B] {σ : Type*} (c : σ → ℝ) (x : σ → B)

omit [IsUltrametricDist K] [IsUltrametricDist B] [CompleteSpace B] in
theorem norm_algebraMap_le_one_mul (r : K) : ‖algebraMap K B r‖ ≤ 1 * ‖r‖ := by
  rw [one_mul]
  exact (norm_algebraMap' B r).le

/-- Evaluation of restricted power series over a normed field `K` at a tuple `x` with
`‖x i‖ ≤ c i` of a Banach `K`-algebra, as a `K`-algebra homomorphism. Source: BGR 5.1.3/5 (the
substitution homomorphism), 5.1.4 (evaluation at a point of the unit ball). -/
noncomputable def aeval (hx : ∀ i, ‖x i‖ ≤ c i) : Restricted K c →ₐ[K] B :=
  { eval₂ c (algebraMap K B) x (norm_algebraMap_le_one_mul (B := B))
      (norm_prod_pow_le_of_norm_le c x hx) with
    commutes' := fun r ↦ by
      rw [algebraMap_apply]
      exact eval₂_C (norm_algebraMap_le_one_mul (B := B)) (norm_prod_pow_le_of_norm_le c x hx) r }

variable {c x} (hx : ∀ i, ‖x i‖ ≤ c i)

theorem aeval_apply (f : Restricted K c) :
    aeval c x hx f = ∑' t : σ →₀ ℕ, algebraMap K B (coeff t f.1) * t.prod fun i k ↦ x i ^ k :=
  rfl

@[simp]
theorem aeval_X (i : σ) : aeval c x hx (X K c i) = x i :=
  eval₂_X (norm_algebraMap_le_one_mul (B := B)) (norm_prod_pow_le_of_norm_le c x hx) i

/-- On polynomials, evaluation is polynomial evaluation. -/
theorem aeval_toRestricted (p : MvPolynomial σ K) :
    aeval c x hx (MvPolynomial.toRestricted c p) = MvPolynomial.aeval x p :=
  (eval₂_toRestricted (norm_algebraMap_le_one_mul (B := B))
    (norm_prod_pow_le_of_norm_le c x hx) p).trans (MvPolynomial.aeval_def x p).symm

/-- Evaluation is contractive: `|f(x)| ≤ |f|`. Source: BGR 5.1.4/2. -/
theorem norm_aeval_le [Fact (∀ i, 0 < c i)] (f : Restricted K c) : ‖aeval c x hx f‖ ≤ ‖f‖ :=
  norm_eval₂_le (norm_algebraMap_le_one_mul (B := B)) (norm_prod_pow_le_of_norm_le c x hx) f

theorem continuous_aeval [Fact (∀ i, 0 < c i)] : Continuous (aeval (K := K) c x hx) :=
  continuous_eval₂ (norm_algebraMap_le_one_mul (B := B)) (norm_prod_pow_le_of_norm_le c x hx)

end aeval

section AlgHomExt

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*} {c : σ → ℝ}
  [hc : Fact (∀ i, 0 < c i)] {B : Type*} [Semiring B] [Algebra K B] [TopologicalSpace B]
  [T2Space B]

/-- A continuous `K`-algebra homomorphism out of the restricted power series is determined by its
values on the variables. Source: BGR 5.1.3/5. -/
theorem algHom_ext_of_continuous {ψ₁ ψ₂ : Restricted K c →ₐ[K] B} (h₁ : Continuous ψ₁)
    (h₂ : Continuous ψ₂) (hX : ∀ i, ψ₁ (X K c i) = ψ₂ (X K c i)) : ψ₁ = ψ₂ := by
  refine AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous h₁ h₂ (fun a ↦ ?_) hX)
  simp only [RingHom.coe_coe]
  rw [← algebraMap_apply, ψ₁.commutes, ψ₂.commutes]

end AlgHomExt

end MvPowerSeries.Restricted
