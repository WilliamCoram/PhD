/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Reduction
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Tower

/-!
# Distinguished series and Weierstrass polynomials in the Tate algebra

A series `g` of the Tate algebra `T_{n+1}` is `X 0`-distinguished of order `s` when its `s`-th
coefficient `coeffX0 g s` is a unit of Gauss norm `‖g‖` that strictly dominates all later
coefficients; for a series of Gauss norm one this is read off the reduction. A Weierstrass
polynomial is a monic polynomial in `X 0` over `Tₙ` of Gauss norm one, and by the Weierstrass
preparation theorem every distinguished series is a unit times a unique Weierstrass polynomial.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.2.1 (BGR 5.2.1/1, 5.2.2/1,
5.2.3/1–2; Bosch 1.2/6, 1.2/9). Tau Ceti home: `TauCeti/RingTheory/TateAlgebra/Weierstrass.lean`.

## Main definitions

* `Affinoid.TateAlgebra.IsWeierstrassPolynomial` — BGR's Definition 5.2.3/1.

## Main results

* `Affinoid.TateAlgebra.norm_le_iff_forall_norm_coeffX0_le` — the Gauss norm of `g = Σ g_ν X 0 ^ ν`
  is the maximum of the Gauss norms of the `g_ν`.
* `Affinoid.TateAlgebra.isMulDistinguishedX0_iff_reduction` — the criterion through the reduction.
* `Affinoid.TateAlgebra.IsWeierstrassPolynomial.of_mul` — BGR 5.2.3/2.
* `Affinoid.TateAlgebra.exists_isWeierstrassPolynomial_of_isMulDistinguishedX0` — Weierstrass
  preparation on Weierstrass polynomials (BGR 5.2.2/1).
-/

open Filter Topology Subring NormedRing IsLocalRing MvPowerSeries MvPowerSeries.Restricted

namespace Affinoid.TateAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {n : ℕ}

/-! ### The coefficients in `X 0` -/

theorem coeffX0_add (g h : TateAlgebra K (n + 1)) (ν : ℕ) :
    coeffX0 (g + h) ν = coeffX0 g ν + coeffX0 h ν :=
  Restricted.ext (MvPowerSeries.ext fun t ↦ by simp only [coeff_coeffX0, val_add, map_add])

theorem coeffX0_smul (a : K) (g : TateAlgebra K (n + 1)) (ν : ℕ) :
    coeffX0 (a • g) ν = a • coeffX0 g ν :=
  Restricted.ext (MvPowerSeries.ext fun t ↦ by
    simp only [coeff_coeffX0, val_smul, MvPowerSeries.coeff_smul])

theorem norm_coeffX0_le (g : TateAlgebra K (n + 1)) (ν : ℕ) : ‖coeffX0 g ν‖ ≤ ‖g‖ :=
  (norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ by
    rw [coeff_coeffX0]
    exact norm_coeff_le g _

/-- The Gauss norm of `g = Σ g_ν X 0 ^ ν` is the maximum of the Gauss norms of the `g_ν`. -/
theorem norm_le_iff_forall_norm_coeffX0_le {ε : ℝ} (g : TateAlgebra K (n + 1)) :
    ‖g‖ ≤ ε ↔ ∀ ν, ‖coeffX0 g ν‖ ≤ ε := by
  refine ⟨fun h ν ↦ (norm_coeffX0_le g ν).trans h, fun h ↦ ?_⟩
  refine (norm_le_iff_forall_norm_coeff_le g).2 fun t ↦ ?_
  rw [← Finsupp.cons_tail t, ← coeff_coeffX0]
  exact (norm_coeff_le _ _).trans (h (t 0))

/-- The coefficients in `X 0` of a series of the Tate algebra tend to zero. Source: BGR 5.1.1
("`Tₙ(k) = Tₙ₋₁(k)⟨Xₙ⟩`"). -/
theorem tendsto_norm_coeffX0 (g : TateAlgebra K (n + 1)) :
    Tendsto (fun ν ↦ ‖coeffX0 g ν‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hfin := finite_setOf_le_norm_coeff g hε
  refine ⟨hfin.toFinset.sup (fun t ↦ t 0) + 1, fun ν hν ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine (norm_lt_iff_forall_norm_coeff_lt _).2 fun t ↦ ?_
  rw [coeff_coeffX0]
  refine lt_of_not_ge fun hle ↦ ?_
  have hmem : Finsupp.cons ν t ∈ hfin.toFinset := (Set.Finite.mem_toFinset _).2 hle
  have h := Finset.le_sup (f := fun t : Fin (n + 1) →₀ ℕ ↦ t 0) hmem
  simp only [Finsupp.cons_zero] at h
  omega

/-! ### Polynomials in `X 0` -/

theorem ofTail_injective : Function.Injective (ofTail K n) :=
  ofPolynomial_injective.comp Polynomial.C_injective

theorem ofTail_apply (f : TateAlgebra K n) : ofTail K n f = ofPolynomial K n (Polynomial.C f) :=
  rfl

omit [IsUltrametricDist K] in
private lemma eq_cons_iff {t : Fin (n + 1) →₀ ℕ} {a : ℕ} {u : Fin n →₀ ℕ} :
    t = Finsupp.cons a u ↔ t 0 = a ∧ Finsupp.tail t = u := by
  constructor
  · rintro rfl
    exact ⟨Finsupp.cons_zero a u, Finsupp.tail_cons a u⟩
  · rintro ⟨h0, ht⟩
    rw [← Finsupp.cons_tail t, h0, ht]

omit [IsUltrametricDist K] in
private lemma single_zero_eq_cons : (Finsupp.single 0 1 : Fin (n + 1) →₀ ℕ) = Finsupp.cons 1 0 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

omit [IsUltrametricDist K] in
private lemma single_succ_eq_cons (i : Fin n) :
    (Finsupp.single i.succ 1 : Fin (n + 1) →₀ ℕ) = Finsupp.cons 0 (Finsupp.single i 1) := by
  ext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [(Fin.succ_ne_zero i).symm]
  · simp [Finsupp.single_apply, Fin.succ_inj]

@[simp]
theorem ofPolynomial_X :
    ofPolynomial K n Polynomial.X = Restricted.X K (1 : Fin (n + 1) → ℝ) 0 := by
  classical
  refine Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)
  rw [coeff_ofPolynomial, Polynomial.coeff_X, val_X, MvPowerSeries.coeff_X, single_zero_eq_cons]
  simp only [eq_cons_iff]
  by_cases h0 : t 0 = 1
  · simp [h0, MvPowerSeries.coeff_one]
  · simp [h0, Ne.symm h0]

@[simp]
theorem ofTail_X (i : Fin n) :
    ofTail K n (Restricted.X K (1 : Fin n → ℝ) i) =
      Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ := by
  classical
  refine Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)
  rw [ofTail_apply, coeff_ofPolynomial, Polynomial.coeff_C, val_X, MvPowerSeries.coeff_X,
    single_succ_eq_cons]
  simp only [eq_cons_iff]
  by_cases h0 : t 0 = 0
  · simp [h0, MvPowerSeries.coeff_X]
  · simp [h0]

@[simp]
theorem ofTail_C (a : K) :
    ofTail K n (Restricted.C (1 : Fin n → ℝ) a) = Restricted.C (1 : Fin (n + 1) → ℝ) a := by
  classical
  refine Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)
  rw [ofTail_apply, coeff_ofPolynomial, Polynomial.coeff_C, val_C, MvPowerSeries.coeff_C,
    ← Finsupp.cons_zero_zero]
  simp only [eq_cons_iff]
  by_cases h0 : t 0 = 0
  · simp [h0, MvPowerSeries.coeff_C]
  · simp [h0]

/-- The Gauss norm of a polynomial in `X 0` is the maximum of the norms of its coefficients. -/
theorem norm_ofPolynomial_le_iff {ε : ℝ} (p : Polynomial (TateAlgebra K n)) :
    ‖ofPolynomial K n p‖ ≤ ε ↔ ∀ i, ‖p.coeff i‖ ≤ ε := by
  simp only [norm_le_iff_forall_norm_coeffX0_le, coeffX0_ofPolynomial]

theorem norm_ofTail (f : TateAlgebra K n) : ‖ofTail K n f‖ = ‖f‖ := by
  refine le_antisymm ((norm_ofPolynomial_le_iff _).2 fun i ↦ ?_) ?_
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg f
  · have h := norm_coeffX0_le (ofTail K n f) 0
    rwa [ofTail_apply, coeffX0_ofPolynomial, Polynomial.coeff_C_zero] at h

/-! ### Distinguished series -/

/-- A distinguished series is nonzero. -/
theorem ne_zero_of_isMulDistinguishedX0 {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) : g ≠ 0 := by
  rintro rfl
  have hu := (isMulDistinguishedX0_iff.1 hg).1
  have h0 : coeffX0 (0 : TateAlgebra K (n + 1)) s = 0 :=
    Restricted.ext (MvPowerSeries.ext fun t ↦ by simp [coeff_coeffX0])
  rw [h0] at hu
  exact not_isUnit_zero hu

/-- Distinguishedness is invariant under multiplication by a nonzero scalar. -/
theorem isMulDistinguishedX0_smul_iff {a : K} (ha : a ≠ 0) {g : TateAlgebra K (n + 1)} {s : ℕ} :
    IsMulDistinguishedX0 (a • g) s ↔ IsMulDistinguishedX0 g s := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hunit : IsUnit (Restricted.C (1 : Fin n → ℝ) a) := (isUnit_iff_ne_zero.2 ha).map _
  have hsmul (h : TateAlgebra K n) : a • h = Restricted.C (1 : Fin n → ℝ) a * h := by
    rw [Algebra.smul_def, algebraMap_apply]
  simp only [isMulDistinguishedX0_iff, coeffX0_smul, norm_smul_eq]
  constructor
  · rintro ⟨hu, hn, hlt⟩
    refine ⟨?_, mul_left_cancel₀ hapos.ne' hn, fun ν hν ↦ lt_of_mul_lt_mul_left (hlt ν hν)
      hapos.le⟩
    rw [hsmul] at hu
    exact (IsUnit.mul_iff.1 hu).2
  · rintro ⟨hu, hn, hlt⟩
    refine ⟨?_, by rw [hn], fun ν hν ↦ mul_lt_mul_of_pos_left (hlt ν hν) hapos⟩
    rw [hsmul]
    exact hunit.mul hu

/-- A series whose constant coefficient dominates has the norm of its constant coefficient. -/
private lemma norm_eq_norm_coeff_zero {m : ℕ} {h : TateAlgebra K m}
    (hlt : ∀ t ≠ 0, ‖coeff t h.1‖ < ‖coeff 0 h.1‖) : ‖h‖ = ‖coeff 0 h.1‖ :=
  le_antisymm ((norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ by
    rcases eq_or_ne t 0 with rfl | ht
    exacts [le_rfl, (hlt t ht).le]) (norm_coeff_le _ 0)

/-- A series is `X 0`-distinguished of order `0` if and only if it is a unit.
Source: Bosch 1.2/6 ("an arbitrary series `g ∈ Tₙ` is `ζₙ`-distinguished of order `0` if and only
if it is a unit"). -/
theorem isMulDistinguishedX0_zero_iff [CompleteSpace K] {g : TateAlgebra K (n + 1)} :
    IsMulDistinguishedX0 g 0 ↔ IsUnit g := by
  rw [isMulDistinguishedX0_iff, isUnit_iff_norm_coeff_lt, isUnit_iff_norm_coeff_lt]
  have hc0 : coeff 0 (coeffX0 g 0).1 = coeff 0 g.1 := by
    rw [coeff_coeffX0, Finsupp.cons_zero_zero]
  rw [hc0]
  constructor
  · rintro ⟨⟨h0, hlt0⟩, -, hlt⟩
    have hnorm0 : ‖coeffX0 g 0‖ = ‖coeff 0 g.1‖ := by
      rw [← hc0]
      exact norm_eq_norm_coeff_zero (by rwa [hc0])
    refine ⟨h0, fun t ht ↦ ?_⟩
    by_cases ht0 : t 0 = 0
    · have htail : Finsupp.tail t ≠ 0 := fun h ↦
        ht (by rw [← Finsupp.cons_tail t, ht0, h, Finsupp.cons_zero_zero])
      have h1 := hlt0 (Finsupp.tail t) htail
      rwa [coeff_coeffX0, ← ht0, Finsupp.cons_tail] at h1
    · calc ‖coeff t g.1‖ = ‖coeff (Finsupp.tail t) (coeffX0 g (t 0)).1‖ := by
            rw [coeff_coeffX0, Finsupp.cons_tail]
        _ ≤ ‖coeffX0 g (t 0)‖ := norm_coeff_le _ _
        _ < ‖coeffX0 g 0‖ := hlt (t 0) (Nat.pos_of_ne_zero ht0)
        _ = ‖coeff 0 g.1‖ := hnorm0
  · rintro ⟨h0, hlt⟩
    have hlt0 (t : Fin n →₀ ℕ) (ht : t ≠ 0) : ‖coeff t (coeffX0 g 0).1‖ < ‖coeff 0 g.1‖ := by
      rw [coeff_coeffX0]
      exact hlt _ (Finsupp.cons_ne_zero_iff.2 (Or.inr ht))
    have hnorm0 : ‖coeffX0 g 0‖ = ‖coeff 0 g.1‖ := by
      rw [← hc0]
      exact norm_eq_norm_coeff_zero (by rwa [hc0])
    refine ⟨⟨h0, hlt0⟩, by rw [hnorm0, norm_eq_norm_coeff_zero hlt], fun ν hν ↦ ?_⟩
    rw [hnorm0]
    refine (norm_lt_iff_forall_norm_coeff_lt _).2 fun t ↦ ?_
    rw [coeff_coeffX0]
    exact hlt _ (Finsupp.cons_ne_zero_iff.2 (Or.inl hν.ne'))

/-- The coefficients in `X 0` of the reduction are the reductions of the coefficients in `X 0`.
Source: BGR 5.2.1 (reading `g̃` in `k̃[X₁, …, X_{n−1}][Xₙ]`). -/
theorem coeff_finSuccEquiv_reduction (g : unitClosedBall (TateAlgebra K (n + 1))) (ν : ℕ) :
    (MvPolynomial.finSuccEquiv _ n (reduction g)).coeff ν =
      reduction ⟨coeffX0 (g : TateAlgebra K (n + 1)) ν,
        mem_unitClosedBall.2 ((norm_coeffX0_le _ ν).trans (Subring.norm_le_one g))⟩ := by
  refine MvPolynomial.ext _ _ fun t ↦ ?_
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, coeff_reduction, coeff_reduction]
  congr 1
  exact Subtype.ext (coeff_coeffX0 _ ν t).symm

/-- A series of Gauss norm one is `X 0`-distinguished of order `s` if and only if its reduction,
as a polynomial in `X 0`, has degree `s` and a unit as leading coefficient. Source: BGR 5.2.1
("`g` with `|g| = 1` is `Xₙ`-distinguished of degree `s` if and only if `g̃` is a unitary polynomial
of degree `s`"); Bosch 1.2/6. -/
theorem isMulDistinguishedX0_iff_reduction [CompleteSpace K]
    {g : unitClosedBall (TateAlgebra K (n + 1))} (hg : ‖(g : TateAlgebra K (n + 1))‖ = 1)
    {s : ℕ} :
    IsMulDistinguishedX0 (g : TateAlgebra K (n + 1)) s ↔
      (MvPolynomial.finSuccEquiv _ n (reduction g)).natDegree = s ∧
        IsUnit (MvPolynomial.finSuccEquiv _ n (reduction g)).leadingCoeff := by
  set P := MvPolynomial.finSuccEquiv _ n (reduction g)
  have hmem (ν : ℕ) : coeffX0 (g : TateAlgebra K (n + 1)) ν ∈ unitClosedBall (TateAlgebra K n) :=
    mem_unitClosedBall.2 ((norm_coeffX0_le _ ν).trans (Subring.norm_le_one g))
  have hcoeff (ν : ℕ) : P.coeff ν = reduction ⟨_, hmem ν⟩ := coeff_finSuccEquiv_reduction g ν
  rw [isMulDistinguishedX0_iff, hg]
  constructor
  · rintro ⟨hu, hn, hlt⟩
    have hs : IsUnit (P.coeff s) := by
      rw [hcoeff]
      exact (isUnit_coe_iff_isUnit_reduction (f := ⟨_, hmem s⟩) hn).1 hu
    have hzero (ν : ℕ) (hν : s < ν) : P.coeff ν = 0 := by
      rw [hcoeff, reduction_eq_zero_iff]
      exact (hlt ν hν).trans_eq hn
    have hdeg : P.natDegree = s :=
      le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.2 hzero)
        (Polynomial.le_natDegree_of_ne_zero hs.ne_zero)
    refine ⟨hdeg, ?_⟩
    rw [Polynomial.leadingCoeff, hdeg]
    exact hs
  · rintro ⟨hdeg, hlc⟩
    rw [Polynomial.leadingCoeff, hdeg, hcoeff] at hlc
    have hn : ‖coeffX0 (g : TateAlgebra K (n + 1)) s‖ = 1 :=
      norm_eq_one_of_reduction_ne_zero hlc.ne_zero
    refine ⟨(isUnit_coe_iff_isUnit_reduction (f := ⟨_, hmem s⟩) hn).2 hlc, hn, fun ν hν ↦ ?_⟩
    rw [hn]
    have h := Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (n := ν) (by omega)
    rw [hcoeff, reduction_eq_zero_iff] at h
    exact h

/-! ### Weierstrass polynomials -/

variable (K n) in
/-- A **Weierstrass polynomial** in `X 0`: a monic polynomial over the Tate algebra in the
remaining variables, of Gauss norm one. Source: BGR 5.2.3/1; Bosch 1.2 (after Corollary 9). -/
structure IsWeierstrassPolynomial (ω : Polynomial (TateAlgebra K n)) : Prop where
  monic : ω.Monic
  norm_eq_one : ‖ofPolynomial K n ω‖ = 1

/-- A monic polynomial in `X 0` has Gauss norm at least one. -/
private lemma one_le_norm_ofPolynomial {ω : Polynomial (TateAlgebra K n)} (h : ω.Monic) :
    1 ≤ ‖ofPolynomial K n ω‖ := by
  have h1 := norm_coeffX0_le (ofPolynomial K n ω) ω.natDegree
  rwa [coeffX0_ofPolynomial, h.coeff_natDegree, norm_one] at h1

/-- A monic polynomial is a Weierstrass polynomial if and only if its coefficients lie in the
unit ball. -/
theorem isWeierstrassPolynomial_iff {ω : Polynomial (TateAlgebra K n)} :
    IsWeierstrassPolynomial K n ω ↔ ω.Monic ∧ ∀ i, ‖ω.coeff i‖ ≤ 1 :=
  ⟨fun h ↦ ⟨h.monic, (norm_ofPolynomial_le_iff ω).1 h.norm_eq_one.le⟩,
    fun ⟨hm, hc⟩ ↦ ⟨hm, le_antisymm ((norm_ofPolynomial_le_iff ω).2 hc)
      (one_le_norm_ofPolynomial hm)⟩⟩

/-- The powers of the variable `X 0` are Weierstrass polynomials. -/
theorem isWeierstrassPolynomial_X_pow (s : ℕ) :
    IsWeierstrassPolynomial K n (Polynomial.X ^ s) := by
  refine isWeierstrassPolynomial_iff.2 ⟨Polynomial.monic_X_pow s, fun i ↦ ?_⟩
  rw [Polynomial.coeff_X_pow]
  split_ifs
  · rw [norm_one]
  · rw [norm_zero]
    exact zero_le_one

/-- If a product of two monic polynomials is a Weierstrass polynomial, so is the left factor.
Source: BGR 5.2.3/2. -/
theorem IsWeierstrassPolynomial.of_mul_left {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    (h₁ : ω₁.Monic) (h₂ : ω₂.Monic) (h : IsWeierstrassPolynomial K n (ω₁ * ω₂)) :
    IsWeierstrassPolynomial K n ω₁ := by
  have hmul : ‖ofPolynomial K n ω₁‖ * ‖ofPolynomial K n ω₂‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    exact h.norm_eq_one
  refine ⟨h₁, le_antisymm ?_ (one_le_norm_ofPolynomial h₁)⟩
  calc ‖ofPolynomial K n ω₁‖ ≤ ‖ofPolynomial K n ω₁‖ * ‖ofPolynomial K n ω₂‖ :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_norm_ofPolynomial h₂)
    _ = 1 := hmul

/-- If a product of two monic polynomials is a Weierstrass polynomial, so is the right factor.
Source: BGR 5.2.3/2. -/
theorem IsWeierstrassPolynomial.of_mul_right {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    (h₁ : ω₁.Monic) (h₂ : ω₂.Monic) (h : IsWeierstrassPolynomial K n (ω₁ * ω₂)) :
    IsWeierstrassPolynomial K n ω₂ := by
  have hmul : ‖ofPolynomial K n ω₁‖ * ‖ofPolynomial K n ω₂‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    exact h.norm_eq_one
  refine ⟨h₂, le_antisymm ?_ (one_le_norm_ofPolynomial h₂)⟩
  calc ‖ofPolynomial K n ω₂‖ ≤ ‖ofPolynomial K n ω₁‖ * ‖ofPolynomial K n ω₂‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (one_le_norm_ofPolynomial h₁)
    _ = 1 := hmul

/-- If a product of two monic polynomials is a Weierstrass polynomial, so are the factors.
Source: BGR 5.2.3/2. -/
theorem IsWeierstrassPolynomial.of_mul {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    (h₁ : ω₁.Monic) (h₂ : ω₂.Monic) (h : IsWeierstrassPolynomial K n (ω₁ * ω₂)) :
    IsWeierstrassPolynomial K n ω₁ ∧ IsWeierstrassPolynomial K n ω₂ :=
  ⟨h.of_mul_left h₁ h₂, h.of_mul_right h₁ h₂⟩

/-- A Weierstrass polynomial of degree `s` is `X 0`-distinguished of order `s`.
Source: BGR 5.2.2/1 ("`|ω| = 1` so that `ω` is `Xₙ`-distinguished of degree `s`"). -/
theorem IsWeierstrassPolynomial.isMulDistinguishedX0 {ω : Polynomial (TateAlgebra K n)}
    (hω : IsWeierstrassPolynomial K n ω) :
    IsMulDistinguishedX0 (ofPolynomial K n ω) ω.natDegree := by
  have hc : coeffX0 (ofPolynomial K n ω) ω.natDegree = 1 := by
    rw [coeffX0_ofPolynomial, hω.monic.coeff_natDegree]
  refine isMulDistinguishedX0_iff.2 ⟨by rw [hc]; exact isUnit_one,
    by rw [hc, norm_one, hω.norm_eq_one], fun ν hν ↦ ?_⟩
  rw [hc, norm_one, coeffX0_ofPolynomial, Polynomial.coeff_eq_zero_of_natDegree_lt hν, norm_zero]
  exact zero_lt_one

/-- **Weierstrass preparation on Weierstrass polynomials**: a series that is `X 0`-distinguished
of order `s` is a unit times a Weierstrass polynomial of degree `s`. Source: BGR 5.2.2/1;
Bosch 1.2/9. -/
theorem exists_isWeierstrassPolynomial_of_isMulDistinguishedX0 [CompleteSpace K]
    {g : TateAlgebra K (n + 1)} {s : ℕ} (hg : IsMulDistinguishedX0 g s) :
    ∃ (ω : Polynomial (TateAlgebra K n)) (e : (TateAlgebra K (n + 1))ˣ),
      IsWeierstrassPolynomial K n ω ∧ ω.natDegree = s ∧ g = e * ofPolynomial K n ω := by
  obtain ⟨ω, e, hm, hd, hn, he, hge⟩ := weierstrassPreparation_exists hg
  refine ⟨ω, he.unit, ⟨hm, hn⟩, Polynomial.natDegree_eq_of_degree_eq_some hd, ?_⟩
  rw [IsUnit.unit_spec]
  exact hge

/-- Two Weierstrass polynomials that differ by a unit factor have the same degree: their
reductions differ by a unit of the polynomial ring over the residue field. -/
private lemma natDegree_eq_of_eq_mul [CompleteSpace K] {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    (h₁ : IsWeierstrassPolynomial K n ω₁) (h₂ : IsWeierstrassPolynomial K n ω₂)
    {u : TateAlgebra K (n + 1)} (hu : IsUnit u)
    (h : ofPolynomial K n ω₁ = u * ofPolynomial K n ω₂) : ω₁.natDegree = ω₂.natDegree := by
  have hnu : ‖u‖ = 1 := by
    have h' := congrArg norm h
    rw [norm_mul, h₁.norm_eq_one, h₂.norm_eq_one, mul_one] at h'
    exact h'.symm
  let p₁ : unitClosedBall (TateAlgebra K (n + 1)) :=
    ⟨_, mem_unitClosedBall.2 h₁.norm_eq_one.le⟩
  let p₂ : unitClosedBall (TateAlgebra K (n + 1)) :=
    ⟨_, mem_unitClosedBall.2 h₂.norm_eq_one.le⟩
  let v : unitClosedBall (TateAlgebra K (n + 1)) := ⟨u, mem_unitClosedBall.2 hnu.le⟩
  have hpv : p₁ = v * p₂ := Subtype.ext h
  have hv : IsUnit (reduction v) := (isUnit_coe_iff_isUnit_reduction (f := v) hnu).1 hu
  have hd₁ := (isMulDistinguishedX0_iff_reduction (g := p₁) h₁.norm_eq_one).1
    h₁.isMulDistinguishedX0
  have hd₂ := (isMulDistinguishedX0_iff_reduction (g := p₂) h₂.norm_eq_one).1
    h₂.isMulDistinguishedX0
  have hQ : MvPolynomial.finSuccEquiv _ n (reduction p₁) =
      MvPolynomial.finSuccEquiv _ n (reduction v) *
        MvPolynomial.finSuccEquiv _ n (reduction p₂) := by
    rw [hpv, map_mul, map_mul]
  have hU : IsUnit (MvPolynomial.finSuccEquiv _ n (reduction v)) :=
    hv.map (MvPolynomial.finSuccEquiv _ n)
  have hQ₂ : MvPolynomial.finSuccEquiv _ n (reduction p₂) ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.1 hd₂.2.ne_zero
  rw [← hd₁.1, ← hd₂.1, hQ, Polynomial.natDegree_mul hU.ne_zero hQ₂,
    Polynomial.natDegree_eq_zero_of_isUnit hU, zero_add]

/-- The Weierstrass polynomial of a distinguished series is unique. Source: BGR 5.2.2/1. -/
theorem IsWeierstrassPolynomial.eq_of_mul_eq_mul [CompleteSpace K]
    {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    (h₁ : IsWeierstrassPolynomial K n ω₁) (h₂ : IsWeierstrassPolynomial K n ω₂)
    {e₁ e₂ : (TateAlgebra K (n + 1))ˣ}
    (h : (e₁ : TateAlgebra K (n + 1)) * ofPolynomial K n ω₁ = e₂ * ofPolynomial K n ω₂) :
    ω₁ = ω₂ := by
  have hu : ofPolynomial K n ω₁ = ↑(e₁⁻¹ * e₂) * ofPolynomial K n ω₂ := by
    rw [Units.val_mul, mul_assoc, ← h, ← mul_assoc, Units.inv_mul, one_mul]
  have hdeg := natDegree_eq_of_eq_mul h₁ h₂ (e₁⁻¹ * e₂).isUnit hu
  exact weierstrassPreparation_omega_unique h₁.isMulDistinguishedX0 h₁.monic
    (Polynomial.degree_eq_natDegree h₁.monic.ne_zero) isUnit_one (one_mul _).symm h₂.monic
    (by rw [Polynomial.degree_eq_natDegree h₂.monic.ne_zero, hdeg]) (e₁⁻¹ * e₂).isUnit hu

end Affinoid.TateAlgebra
