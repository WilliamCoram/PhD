/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import PhD.Main.NewtonPolygons.SpecConstruction
import PhD.Main.ForMathlib.Analysis.Normed.Ring.NegLogNorm
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.GaussNorm

/-!
# Coefficient valuations of a power series over an ultrametric field

The valuation bridge between the norm on a nontrivially-normed ultrametric field `K` and the
Newton-polygon machinery of this directory (blueprint §5.2–§5.4 setup; refactor of the
corresponding layer of `Test/test.lean` onto `negLogNorm`):

* `coeffVal f` — the coefficient-valuation sequence `i ↦ negLogNorm (coeff i f) = -log ‖aᵢ‖`
  (with `⊤` at vanishing coefficients), i.e. `coeffSeq negLogNorm f`. The canonical base is
  `e`: the norm is recovered as `‖a‖ = exp (-(coeffVal f i))`.
* the term dictionary `norm_mul_exp_pow_*_iff` — Gauss-norm terms `‖a‖ (eᵐ)ᵏ` compared to `1`
  (or to a reference coefficient) translate to point-vs-line comparisons for the polygon.
* admissibility — polynomials and restricted power series have admissible coefficient
  sequences, so the constructed polygon satisfies the geometric specification
  (`isNewtonPolygonOf_coeffVal_coe`, `isNewtonPolygonOf_coeffVal_of_isRestricted`).
* the blueprint's standing normalisation `a₀ = 1` anchors the polygon at the origin
  (`newtonPolygon₀_starting_point_of_coeff_zero_eq_one`).
-/

variable {K : Type*} [NontriviallyNormedField K]

/-- The coefficient-valuation sequence of `f`: the input the Newton-polygon machinery consumes,
`i ↦ -log ‖aᵢ‖` with `⊤` at vanishing coefficients. -/
noncomputable def coeffVal (f : PowerSeries K) : ℕ → WithTop ℝ :=
  coeffSeq negLogNorm f

@[simp] lemma coeffVal_apply (f : PowerSeries K) (i : ℕ) :
    coeffVal f i = negLogNorm (PowerSeries.coeff i f) := rfl

lemma coeffVal_eq_top_iff {f : PowerSeries K} {i : ℕ} :
    coeffVal f i = ⊤ ↔ PowerSeries.coeff i f = 0 := negLogNorm_eq_top

lemma coeffVal_of_ne_zero {f : PowerSeries K} {i : ℕ} (h : PowerSeries.coeff i f ≠ 0) :
    coeffVal f i = ((-Real.log ‖PowerSeries.coeff i f‖ : ℝ) : WithTop ℝ) :=
  negLogNorm_of_ne_zero h

lemma coeffVal_zero_of_coeff_zero_eq_one {f : PowerSeries K} (h : PowerSeries.coeff 0 f = 1) :
    coeffVal f 0 = (0 : ℝ) := by
  rw [coeffVal_apply, h, negLogNorm_one, WithTop.coe_zero]

lemma exists_coeffVal_ne_top {f : PowerSeries K} (hf : f ≠ 0) : ∃ i, coeffVal f i ≠ ⊤ :=
  (PowerSeries.exists_coeff_ne_zero_iff_ne_zero.mpr hf).imp fun _ => mt coeffVal_eq_top_iff.mp

/-! ### The term dictionary

Gauss-norm terms at radius `c = exp m` against heights of polygon points: `‖a‖ (eᵐ)ᵏ ≤ 1` iff
the point `(k, -log ‖a‖)` lies on/above the line `y = mx`, etc. These are the public forms of
the `term_*` dictionary of `Test/test.lean` (lines 435–452, 661–684), consumed by §5.6–§5.11. -/

/-- `‖a‖ (eᵐ)ᵏ = exp (log ‖a‖ + mk)`: the basic dictionary between Gauss-norm terms at
`c = exp m` and heights of polygon points. -/
lemma norm_mul_exp_pow_eq_exp {a : K} (ha : a ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k = Real.exp (Real.log ‖a‖ + m * k) := by
  rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr ha), ← Real.exp_nat_mul, mul_comm m (k : ℝ)]

/-- The term at `k` is `≤ 1` iff the point `(k, -log ‖a‖)` lies on/above the line `y = mx`. -/
lemma norm_mul_exp_pow_le_one_iff {a : K} (ha : a ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k ≤ 1 ↔ m * k ≤ -Real.log ‖a‖ := by
  rw [norm_mul_exp_pow_eq_exp ha m k, Real.exp_le_one_iff, le_neg_iff_add_nonpos_left]

/-- The term at `k` is `= 1` iff the point `(k, -log ‖a‖)` lies on the line `y = mx`. -/
lemma norm_mul_exp_pow_eq_one_iff {a : K} (ha : a ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k = 1 ↔ -Real.log ‖a‖ = m * k := by
  rw [norm_mul_exp_pow_eq_exp ha m k, Real.exp_eq_one_iff, add_eq_zero_iff_neg_eq]

/-- The term at `k` is `< 1` iff the point `(k, -log ‖a‖)` lies strictly above the line
`y = mx`. -/
lemma norm_mul_exp_pow_lt_one_iff {a : K} (ha : a ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k < 1 ↔ m * k < -Real.log ‖a‖ := by
  rw [norm_mul_exp_pow_eq_exp ha m k, Real.exp_lt_one_iff, lt_neg_iff_add_neg']

/-- Comparison with a reference coefficient: `‖a‖ (eᵐ)ᵏ ≤ ‖b‖` iff `(k, -log ‖a‖)` lies on/above
the line of slope `m` through `(0, -log ‖b‖)`. -/
lemma norm_mul_exp_pow_le_norm_iff {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k ≤ ‖b‖ ↔ m * k ≤ -Real.log ‖a‖ - -Real.log ‖b‖ := by
  rw [norm_mul_exp_pow_eq_exp ha m k, ← Real.le_log_iff_exp_le (norm_pos_iff.mpr hb),
    neg_sub_neg, le_sub_iff_add_le']

/-- Comparison with a reference coefficient, with equality: `‖a‖ (eᵐ)ᵏ = ‖b‖` iff
`(k, -log ‖a‖)` lies on the line of slope `m` through `(0, -log ‖b‖)`. -/
lemma norm_mul_exp_pow_eq_norm_iff {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℝ) (k : ℕ) :
    ‖a‖ * Real.exp m ^ k = ‖b‖ ↔ -Real.log ‖a‖ - -Real.log ‖b‖ = m * k := by
  rw [norm_mul_exp_pow_eq_exp ha m k, ← Real.exp_log (norm_pos_iff.mpr hb), Real.exp_eq_exp,
    Real.log_exp, neg_sub_neg, sub_eq_iff_eq_add', eq_comm]

/-! ### Admissibility and the geometric specification -/

/-- Polynomials have admissible coefficient sequences: finitely many points admit an affine
floor. -/
lemma isAdmissible_coeffVal_coe (f : Polynomial K) :
    IsAdmissible (coeffVal (f : PowerSeries K)) := by
  intro i₀ i₁ _
  -- the slope set is contained in the image of the finitely many indices `k ≤ natDegree f`
  refine Set.Finite.bddBelow (Set.Finite.subset ((Set.finite_Iic f.natDegree).image
    (fun k : ℕ => slopeReal i₀ k i₁ (-Real.log ‖f.coeff k‖))) ?_)
  rintro x ⟨j₀, hj₀, hfin, j₁, hj₁, rfl⟩
  have hcoeff : f.coeff j₀ ≠ 0 := fun hc =>
    hfin (coeffVal_eq_top_iff.mpr (by rw [Polynomial.coeff_coe, hc]))
  have hj₁' : j₁ = -Real.log ‖f.coeff j₀‖ :=
    WithTop.coe_inj.mp (hj₁.symm.trans (by
      rw [coeffVal_of_ne_zero (by rwa [Polynomial.coeff_coe]), Polynomial.coeff_coe]))
  exact ⟨j₀, Polynomial.le_natDegree_of_ne_zero hcoeff, by rw [hj₁']⟩

/-- Restricted power series have admissible coefficient sequences: the Gauss-norm bound
`‖aₖ‖ cᵏ ≤ B` is an affine floor `k log c - log B ≤ -log ‖aₖ‖`. -/
lemma isAdmissible_coeffVal_of_isRestricted {f : PowerSeries K} {c : ℝ} (hc : 0 < c)
    (hf : PowerSeries.IsRestricted c f) : IsAdmissible (coeffVal f) := by
  have hterm : ∀ k : ℕ, ‖PowerSeries.coeff k f‖ * c ^ k ≤ PowerSeries.gaussNorm norm c f :=
    fun k => PowerSeries.le_gaussNorm norm c f hf.hasGaussNorm k
  intro i₀ i₁ hvi
  refine isAdmissible_of_affine_bound (coeffVal f) (m := Real.log c)
    (b := -Real.log (PowerSeries.gaussNorm norm c f)) ?_ i₀ i₁ hvi
  intro k a hva
  have hak : PowerSeries.coeff k f ≠ 0 := fun hcz =>
    WithTop.coe_ne_top (hva.symm.trans (coeffVal_eq_top_iff.mpr hcz))
  have hnorm : 0 < ‖PowerSeries.coeff k f‖ := norm_pos_iff.mpr hak
  have haeq : a = -Real.log ‖PowerSeries.coeff k f‖ :=
    WithTop.coe_inj.mp (hva.symm.trans (coeffVal_of_ne_zero hak))
  -- the Gauss-norm bound `‖aₖ‖ cᵏ ≤ B` is the affine floor `k log c - log B ≤ -log ‖aₖ‖`
  have hlog : Real.log ‖PowerSeries.coeff k f‖ + k * Real.log c ≤
      Real.log (PowerSeries.gaussNorm norm c f) := by
    have h1 := Real.log_le_log (mul_pos hnorm (pow_pos hc k)) (hterm k)
    rwa [Real.log_mul hnorm.ne' (pow_pos hc k).ne', Real.log_pow] at h1
  simp only [Algebra.algebraMap_self, RingHom.id_apply, haeq]
  linarith

/-- **The Newton polygon of a nonzero polynomial satisfies the geometric specification.** -/
theorem isNewtonPolygonOf_coeffVal_coe (f : Polynomial K) (hf : f ≠ 0) :
    IsNewtonPolygonOf (coeffVal (f : PowerSeries K))
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)) :=
  isNewtonPolygonOf_powerSeries negLogNorm (f : PowerSeries K)
    (exists_coeffVal_ne_top fun h => hf (Polynomial.coe_eq_zero_iff.mp h))
    (isAdmissible_coeffVal_coe f)

/-- **The Newton polygon of a nonzero restricted power series satisfies the geometric
specification.** -/
theorem isNewtonPolygonOf_coeffVal_of_isRestricted {f : PowerSeries K} {c : ℝ} (hc : 0 < c)
    (hf : PowerSeries.IsRestricted c f) (hne : f ≠ 0) :
    IsNewtonPolygonOf (coeffVal f) (newtonPolygon₀OfPowerSeries negLogNorm f) :=
  isNewtonPolygonOf_powerSeries negLogNorm f (exists_coeffVal_ne_top hne)
    (isAdmissible_coeffVal_of_isRestricted hc hf)

/-- Under the blueprint's standing normalisation `a₀ = 1`, the constructed polygon is anchored
at the origin. -/
lemma newtonPolygon₀_starting_point_of_coeff_zero_eq_one {f : PowerSeries K}
    (h : PowerSeries.coeff 0 f = 1) :
    (newtonPolygon₀OfPowerSeries negLogNorm f).starting_point = ((0 : ℤ), (0 : ℝ)) := by
  have hzero : coeffVal f 0 = ((0 : ℝ) : WithTop ℝ) := coeffVal_zero_of_coeff_zero_eq_one h
  have h1 : ∃ i, coeffVal f i ≠ ⊤ := ⟨0, hzero.trans_ne WithTop.coe_ne_top⟩
  obtain ⟨k, hk1, hk2⟩ := newtonPolygon₀OfSeq_start_mem (coeffVal f) h1
  have hle := newtonPolygon₀OfSeq_start_le (coeffVal f) h1
  -- the polygon of `f` is by definition the polygon of its coefficient-valuation sequence
  show (newtonPolygon₀OfSeq (coeffVal f)).starting_point = _
  -- the anchor is at `x = 0`: it is a point index (so `≥ 0`), and no point lies left of it,
  -- while `0` is a point
  have hx : (newtonPolygon₀OfSeq (coeffVal f)).starting_point.1 = 0 := by
    rcases eq_or_lt_of_le (show (0 : ℤ) ≤ (newtonPolygon₀OfSeq (coeffVal f)).starting_point.1 from
      hk1 ▸ Int.natCast_nonneg k) with h' | h'
    · exact h'.symm
    · exact absurd (hle 0 (by exact_mod_cast h')) (hzero.trans_ne WithTop.coe_ne_top)
  have hk0 : k = 0 := by omega
  rw [hk0, hzero] at hk2
  exact Prod.ext hx (WithTop.coe_inj.mp hk2).symm
