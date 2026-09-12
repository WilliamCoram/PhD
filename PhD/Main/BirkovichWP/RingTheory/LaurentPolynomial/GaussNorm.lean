/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Normed.Ring.Ultra
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.DivisibleRadius

/-! # The Gauss norm on Laurent polynomials

The Gauss norm at radius `r > 0` on Laurent polynomials, `‖p‖ = sup_m ‖p.coeff m‖ * r^m`
(a finite supremum), and its algebra: ultrametric, attained, and **multiplicative whenever
`r` lies outside the divisible closure of the value group** — distinct exponents then have
distinct Gauss terms (a tie `‖a‖ r^i = ‖b‖ r^j` would exhibit a power of `r` as a realised
norm), so products have a strictly dominant term.

`GaussLaurent K r` is the type synonym carrying the resulting normed-ring structure; its
completion is the Gauss-point field (see `GaussExtension`).
-/

namespace LaurentPolynomial

section Def

variable {R : Type*} [NormedCommRing R] (r : ℝ)

/-- The **Gauss norm at radius `r`** of a Laurent polynomial: the supremum of the weighted
coefficient norms `‖p.coeff m‖ * r^m` (finitely many nonzero). -/
noncomputable def gaussNorm (p : R[T;T⁻¹]) : ℝ :=
  ⨆ m : ℤ, ‖p.coeff m‖ * r ^ m

variable [Fact (0 < r)]

omit [Fact (0 < r)] in
private lemma bddAbove_range_gaussTerm (p : R[T;T⁻¹]) :
    BddAbove (Set.range fun m : ℤ ↦ ‖p.coeff m‖ * r ^ m) := by
  refine BddAbove.mono ?_
    (((p.coeff.support.image fun m ↦ ‖p.coeff m‖ * r ^ m).finite_toSet.insert 0).bddAbove)
  rintro x ⟨m, rfl⟩
  by_cases hm : p.coeff m = 0
  · simp only [hm, norm_zero, zero_mul]
    exact Set.mem_insert 0 _
  · exact Set.mem_insert_of_mem _
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hm)))

lemma gaussNorm_nonneg (p : R[T;T⁻¹]) : 0 ≤ gaussNorm r p :=
  Real.iSup_nonneg fun m ↦
    mul_nonneg (norm_nonneg _) (zpow_pos (Fact.out : (0 : ℝ) < r) m).le

omit [Fact (0 < r)] in
lemma le_gaussNorm (p : R[T;T⁻¹]) (m : ℤ) : ‖p.coeff m‖ * r ^ m ≤ gaussNorm r p :=
  le_ciSup (bddAbove_range_gaussTerm r p) m

omit [Fact (0 < r)] in
private lemma coeff_support_nonempty {p : R[T;T⁻¹]} (hp : p ≠ 0) : p.coeff.support.Nonempty :=
  Finsupp.support_nonempty_iff.mpr fun h0 ↦
    hp (LaurentPolynomial.ext fun a ↦ by simp [h0, AddMonoidAlgebra.coeff_zero])

/-- The Gauss norm of a nonzero Laurent polynomial is attained. -/
lemma exists_gaussNorm_eq {p : R[T;T⁻¹]} (hp : p ≠ 0) :
    ∃ m : ℤ, gaussNorm r p = ‖p.coeff m‖ * r ^ m := by
  obtain ⟨m₀, -, hmax⟩ :=
    p.coeff.support.exists_max_image (fun m ↦ ‖p.coeff m‖ * r ^ m) (coeff_support_nonempty hp)
  refine ⟨m₀, le_antisymm (ciSup_le fun m ↦ ?_) (le_gaussNorm r p m₀)⟩
  by_cases hm : p.coeff m = 0
  · rw [hm, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (zpow_pos (Fact.out : (0 : ℝ) < r) m₀).le
  · exact hmax m (Finsupp.mem_support_iff.mpr hm)

omit [Fact (0 < r)] in
lemma gaussNorm_neg (p : R[T;T⁻¹]) : gaussNorm r (-p) = gaussNorm r p := by
  unfold gaussNorm
  exact iSup_congr fun m ↦ by rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, norm_neg]

omit [Fact (0 < r)] in
lemma coeff_add_apply (p q : R[T;T⁻¹]) (m : ℤ) :
    (p + q).coeff m = p.coeff m + q.coeff m := rfl

omit [Fact (0 < r)] in
lemma coeff_sub_apply (p q : R[T;T⁻¹]) (m : ℤ) :
    (p - q).coeff m = p.coeff m - q.coeff m := rfl

omit [Fact (0 < r)] in
@[simp]
lemma gaussNorm_zero : gaussNorm r (0 : R[T;T⁻¹]) = 0 := by
  unfold gaussNorm
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, norm_zero, zero_mul]
  exact ciSup_const

lemma gaussNorm_eq_zero_iff {p : R[T;T⁻¹]} : gaussNorm r p = 0 ↔ p = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ gaussNorm_zero r⟩
  by_contra hp
  obtain ⟨m, hm⟩ := coeff_support_nonempty hp
  have h1 := le_gaussNorm r p m
  rw [h] at h1
  have h2 := mul_pos (norm_pos_iff.mpr (Finsupp.mem_support_iff.mp hm))
    (zpow_pos (Fact.out : (0 : ℝ) < r) m)
  linarith

omit [Fact (0 < r)] in
lemma gaussNorm_C (a : R) : gaussNorm r (C a) = ‖a‖ := by
  refine le_antisymm (ciSup_le fun m ↦ ?_) ?_
  · rcases eq_or_ne m 0 with rfl | hm
    · rw [C_apply, if_pos rfl, zpow_zero, mul_one]
    · rw [C_apply, if_neg hm, norm_zero, zero_mul]
      exact norm_nonneg a
  · have h := le_gaussNorm r (C a) 0
    rwa [C_apply, if_pos rfl, zpow_zero, mul_one] at h

lemma gaussNorm_T [NormOneClass R] (m : ℤ) : gaussNorm r (T m : R[T;T⁻¹]) = r ^ m := by
  refine le_antisymm (ciSup_le fun k ↦ ?_) ?_
  · rcases eq_or_ne m k with rfl | hk
    · simp [T_apply]
    · simp only [T_apply]
      rw [if_neg hk, norm_zero, zero_mul]
      exact (zpow_pos (Fact.out : (0 : ℝ) < r) m).le
  · have h := le_gaussNorm r (T m : R[T;T⁻¹]) m
    simpa [T_apply] using h

lemma gaussNorm_add_le [IsUltrametricDist R] (p q : R[T;T⁻¹]) :
    gaussNorm r (p + q) ≤ max (gaussNorm r p) (gaussNorm r q) := by
  refine ciSup_le fun m ↦ ?_
  have hrm : (0 : ℝ) ≤ r ^ m := (zpow_pos (Fact.out : (0 : ℝ) < r) m).le
  have h1 : ‖(p + q).coeff m‖ ≤ max ‖p.coeff m‖ ‖q.coeff m‖ := by
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact IsUltrametricDist.norm_add_le_max _ _
  calc ‖(p + q).coeff m‖ * r ^ m
      ≤ max ‖p.coeff m‖ ‖q.coeff m‖ * r ^ m := mul_le_mul_of_nonneg_right h1 hrm
    _ = max (‖p.coeff m‖ * r ^ m) (‖q.coeff m‖ * r ^ m) := max_mul_of_nonneg _ _ hrm
    _ ≤ max (gaussNorm r p) (gaussNorm r q) :=
        max_le_max (le_gaussNorm r p m) (le_gaussNorm r q m)

omit [Fact (0 < r)] in
private lemma coeff_mul_eq_sum (p q : R[T;T⁻¹]) (m : ℤ) :
    (p * q).coeff m = ∑ ij ∈ p.coeff.support ×ˢ q.coeff.support,
      if ij.1 + ij.2 = m then p.coeff ij.1 * q.coeff ij.2 else 0 := by
  rw [AddMonoidAlgebra.coeff_mul, Finset.sum_product]
  rfl

lemma gaussNorm_mul_le [IsUltrametricDist R] (p q : R[T;T⁻¹]) :
    gaussNorm r (p * q) ≤ gaussNorm r p * gaussNorm r q := by
  have hr0 : (0 : ℝ) < r := Fact.out
  refine Real.iSup_le (fun m ↦ ?_)
    (mul_nonneg (gaussNorm_nonneg r p) (gaussNorm_nonneg r q))
  have hcoeff := coeff_mul_eq_sum p q m
  obtain ⟨k, -, hsum⟩ := IsNonarchimedean.finset_image_add norm_zero
    (fun a ↦ norm_nonneg a) IsUltrametricDist.isNonarchimedean_norm
    (fun ij : ℤ × ℤ ↦ if ij.1 + ij.2 = m then p.coeff ij.1 * q.coeff ij.2 else 0)
    (p.coeff.support ×ˢ q.coeff.support)
  rw [hcoeff]
  refine le_trans (mul_le_mul_of_nonneg_right hsum (zpow_pos hr0 m).le) ?_
  rcases eq_or_ne (k.1 + k.2) m with hk | hk
  · rw [if_pos hk]
    calc ‖p.coeff k.1 * q.coeff k.2‖ * r ^ m
        ≤ ‖p.coeff k.1‖ * ‖q.coeff k.2‖ * r ^ m :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (zpow_pos hr0 m).le
      _ = (‖p.coeff k.1‖ * r ^ k.1) * (‖q.coeff k.2‖ * r ^ k.2) := by
          rw [← hk, zpow_add₀ hr0.ne']
          ring
      _ ≤ gaussNorm r p * gaussNorm r q :=
          mul_le_mul (le_gaussNorm r p k.1) (le_gaussNorm r q k.2)
            (mul_nonneg (norm_nonneg _) (zpow_pos hr0 _).le) (gaussNorm_nonneg r p)
  · rw [if_neg hk, norm_zero, zero_mul]
    exact mul_nonneg (gaussNorm_nonneg r p) (gaussNorm_nonneg r q)

end Def

section NoTie

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {r : ℝ} [Fact (0 < r)]

omit [IsUltrametricDist K] in
/-- Off the divisible closure of the value group, distinct exponents have distinct Gauss
terms: a tie `‖a‖ r^i = ‖b‖ r^j` with `i ≠ j` would exhibit `r^|i-j|` as the realised norm
`‖b * a⁻¹‖`. -/
lemma gaussTerm_injOn_of_not_memDivisibleValueGroup (hr : ¬MemDivisibleValueGroup K r)
    {p : K[T;T⁻¹]} {i j : ℤ} (hi : p.coeff i ≠ 0) (hj : p.coeff j ≠ 0)
    (h : ‖p.coeff i‖ * r ^ i = ‖p.coeff j‖ * r ^ j) : i = j := by
  have hr0 : (0 : ℝ) < r := Fact.out
  have hni : ‖p.coeff i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
  have hnj : ‖p.coeff j‖ ≠ 0 := norm_ne_zero_iff.mpr hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine hr ⟨(j - i).toNat, by omega, p.coeff i * (p.coeff j)⁻¹, ?_⟩
    have hcast : r ^ (j - i).toNat = r ^ (j - i : ℤ) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    rw [norm_mul, norm_inv, hcast, zpow_sub₀ hr0.ne']
    field_simp [hnj, (zpow_pos hr0 i).ne']
    linear_combination h
  · refine hr ⟨(i - j).toNat, by omega, p.coeff j * (p.coeff i)⁻¹, ?_⟩
    have hcast : r ^ (i - j).toNat = r ^ (i - j : ℤ) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    rw [norm_mul, norm_inv, hcast, zpow_sub₀ hr0.ne']
    field_simp [hni, (zpow_pos hr0 j).ne']
    linear_combination -h

/-- **Multiplicativity of the Gauss norm off the divisible closure**: products have a
strictly dominant term (the product of the two unique dominant terms). -/
lemma gaussNorm_mul (hr : ¬MemDivisibleValueGroup K r) (p q : K[T;T⁻¹]) :
    gaussNorm r (p * q) = gaussNorm r p * gaussNorm r q := by
  have hr0 : (0 : ℝ) < r := Fact.out
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine le_antisymm (gaussNorm_mul_le r p q) ?_
  obtain ⟨i₀, hi₀⟩ := exists_gaussNorm_eq r hp
  obtain ⟨j₀, hj₀⟩ := exists_gaussNorm_eq r hq
  have hpi₀ : p.coeff i₀ ≠ 0 := fun h0 ↦ hp ((gaussNorm_eq_zero_iff r).mp
    (by rw [hi₀, h0, norm_zero, zero_mul]))
  have hqj₀ : q.coeff j₀ ≠ 0 := fun h0 ↦ hq ((gaussNorm_eq_zero_iff r).mp
    (by rw [hj₀, h0, norm_zero, zero_mul]))
  have hmem : (i₀, j₀) ∈ p.coeff.support ×ˢ q.coeff.support :=
    Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr hpi₀, Finsupp.mem_support_iff.mpr hqj₀⟩
  have hcoeff := coeff_mul_eq_sum p q (i₀ + j₀)
  have hstrict : ∀ ij ∈ p.coeff.support ×ˢ q.coeff.support, ij ≠ (i₀, j₀) →
      ‖if ij.1 + ij.2 = i₀ + j₀ then p.coeff ij.1 * q.coeff ij.2 else 0‖
        < ‖if i₀ + j₀ = i₀ + j₀ then p.coeff i₀ * q.coeff j₀ else 0‖ := by
    rintro ⟨i, j⟩ hijS hne
    rw [if_pos rfl, norm_mul]
    obtain ⟨hiS, hjS⟩ := Finset.mem_product.mp hijS
    have hpi := Finsupp.mem_support_iff.mp hiS
    have hqj := Finsupp.mem_support_iff.mp hjS
    have hpos : 0 < ‖p.coeff i₀‖ * ‖q.coeff j₀‖ :=
      mul_pos (norm_pos_iff.mpr hpi₀) (norm_pos_iff.mpr hqj₀)
    by_cases hm : i + j = i₀ + j₀
    · have hii₀ : i ≠ i₀ := by
        rintro rfl
        exact hne (Prod.ext rfl (by omega))
      have h1 : ‖p.coeff i‖ * r ^ i < gaussNorm r p :=
        lt_of_le_of_ne (le_gaussNorm r p i) fun heq ↦ hii₀
          (gaussTerm_injOn_of_not_memDivisibleValueGroup hr hpi hpi₀ (heq.trans hi₀))
      rw [if_pos hm, norm_mul]
      have hw : ‖p.coeff i‖ * ‖q.coeff j‖ * r ^ (i₀ + j₀)
          < ‖p.coeff i₀‖ * ‖q.coeff j₀‖ * r ^ (i₀ + j₀) := by
        calc ‖p.coeff i‖ * ‖q.coeff j‖ * r ^ (i₀ + j₀)
            = (‖p.coeff i‖ * r ^ i) * (‖q.coeff j‖ * r ^ j) := by
              rw [← hm, zpow_add₀ hr0.ne']
              ring
          _ < gaussNorm r p * gaussNorm r q := by
              refine mul_lt_mul h1 (le_gaussNorm r q j) ?_ ?_
              · exact mul_pos (norm_pos_iff.mpr hqj) (zpow_pos hr0 j)
              · exact le_of_lt (lt_of_le_of_lt (by positivity) h1)
          _ = ‖p.coeff i₀‖ * ‖q.coeff j₀‖ * r ^ (i₀ + j₀) := by
              rw [hi₀, hj₀, zpow_add₀ hr0.ne']
              ring
      exact lt_of_mul_lt_mul_right hw (zpow_pos hr0 _).le
    · rw [if_neg hm, norm_zero]
      exact hpos
  have hcoeff_norm : ‖(p * q).coeff (i₀ + j₀)‖ = ‖p.coeff i₀‖ * ‖q.coeff j₀‖ := by
    have hsum := IsNonarchimedean.apply_sum_eq_of_lt IsUltrametricDist.isNonarchimedean_norm
      (fun a ↦ (norm_neg a).symm) hmem hstrict
    rw [hcoeff, hsum, if_pos rfl, norm_mul]
  have hfinal := le_gaussNorm r (p * q) (i₀ + j₀)
  rw [hcoeff_norm] at hfinal
  calc gaussNorm r p * gaussNorm r q
      = ‖p.coeff i₀‖ * ‖q.coeff j₀‖ * r ^ (i₀ + j₀) := by
        rw [hi₀, hj₀, zpow_add₀ hr0.ne']
        ring
    _ ≤ gaussNorm r (p * q) := hfinal

end NoTie

end LaurentPolynomial

/-! ## The normed Laurent-polynomial algebra -/

/-- Type synonym for `LaurentPolynomial K` carrying the Gauss norm at radius `r` as a
normed-ring structure — the dense subring whose completion is the Gauss-point field
`GaussExtension K r`. -/
@[nolint unusedArguments]
def GaussLaurent (K : Type*) [NormedCommRing K] (_r : ℝ) := LaurentPolynomial K

namespace GaussLaurent

variable {K : Type*} [NormedCommRing K] {r : ℝ}

noncomputable instance : CommRing (GaussLaurent K r) :=
  inferInstanceAs (CommRing (LaurentPolynomial K))

/-- Interpret a Laurent polynomial in the Gauss-normed synonym. -/
def of (p : LaurentPolynomial K) : GaussLaurent K r := p

variable [IsUltrametricDist K] [Fact (0 < r)]

/-- The Gauss norm as a ring norm on the synonym. -/
noncomputable def gaussRingNorm : RingNorm (GaussLaurent K r) where
  toFun p := LaurentPolynomial.gaussNorm r (p : LaurentPolynomial K)
  map_zero' := LaurentPolynomial.gaussNorm_zero r
  add_le' p q := (LaurentPolynomial.gaussNorm_add_le r p q).trans
    (max_le_add_of_nonneg (LaurentPolynomial.gaussNorm_nonneg r _)
      (LaurentPolynomial.gaussNorm_nonneg r _))
  neg' p := LaurentPolynomial.gaussNorm_neg r (p : LaurentPolynomial K)
  mul_le' p q := LaurentPolynomial.gaussNorm_mul_le r p q
  eq_zero_of_map_eq_zero' _ h := (LaurentPolynomial.gaussNorm_eq_zero_iff r).mp h

noncomputable instance : NormedCommRing (GaussLaurent K r) :=
  { RingNorm.toNormedRing (gaussRingNorm (K := K) (r := r)) with
    mul_comm := mul_comm }

lemma norm_def (p : GaussLaurent K r) :
    ‖p‖ = LaurentPolynomial.gaussNorm r (p : LaurentPolynomial K) := rfl

instance : IsUltrametricDist (GaussLaurent K r) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun p q ↦
    LaurentPolynomial.gaussNorm_add_le r p q

/-- Constants, as a ring homomorphism into the Gauss-normed Laurent algebra. -/
noncomputable def C : K →+* GaussLaurent K r :=
  LaurentPolynomial.C

@[simp]
lemma norm_C (a : K) : ‖(C a : GaussLaurent K r)‖ = ‖a‖ := by
  rw [norm_def]
  exact LaurentPolynomial.gaussNorm_C r a

instance [NormOneClass K] : NormOneClass (GaussLaurent K r) where
  norm_one := by
    rw [show (1 : GaussLaurent K r) = C 1 from (map_one (C (K := K) (r := r))).symm, norm_C,
      norm_one]

noncomputable instance : Algebra K (GaussLaurent K r) :=
  (C (K := K) (r := r)).toAlgebra

/-- The variable `T`, of Gauss norm `r`, invertible already at the Laurent level. -/
noncomputable def T : GaussLaurent K r := LaurentPolynomial.T 1

lemma norm_T [NormOneClass K] : ‖(T : GaussLaurent K r)‖ = r := by
  rw [norm_def]
  have h := LaurentPolynomial.gaussNorm_T (R := K) r 1
  rwa [zpow_one] at h

omit [IsUltrametricDist K] [Fact (0 < r)] in
lemma isUnit_T : IsUnit (T : GaussLaurent K r) :=
  LaurentPolynomial.isUnit_T 1

/-- The `T⁰`-coefficient, as a `K`-linear functional — the seed of the descent retraction
of the Gauss extension. -/
noncomputable def coeffZero : GaussLaurent K r →ₗ[K] K where
  toFun p := (p : LaurentPolynomial K).coeff 0
  map_add' p q :=
    LaurentPolynomial.coeff_add_apply (p : LaurentPolynomial K) (q : LaurentPolynomial K) 0
  map_smul' a p := by
    rw [RingHom.id_apply, smul_eq_mul,
      ← AddMonoidAlgebra.coeff_single_zero_mul (p : LaurentPolynomial K) a 0]
    rfl

omit [IsUltrametricDist K] [Fact (0 < r)] in
lemma coeffZero_C (a : K) : coeffZero (C a : GaussLaurent K r) = a := by
  show (LaurentPolynomial.C a).coeff 0 = a
  rw [LaurentPolynomial.C_apply, if_pos rfl]

lemma norm_coeffZero_le (p : GaussLaurent K r) : ‖coeffZero p‖ ≤ ‖p‖ := by
  have h := LaurentPolynomial.le_gaussNorm r (p : LaurentPolynomial K) 0
  rwa [zpow_zero, mul_one, ← norm_def] at h

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {r : ℝ}
  [Fact (0 < r)] [Fact (¬MemDivisibleValueGroup K r)]

instance : NormMulClass (GaussLaurent K r) where
  norm_mul p q := LaurentPolynomial.gaussNorm_mul Fact.out p q

/-- The tail left after subtracting the dominant monomial has strictly smaller Gauss norm:
if `q` agrees coefficient-wise with `single m (p.coeff m)` at the norm-attaining index `m`,
then `‖p - q‖ < ‖p‖`, because off the divisible closure every other exponent contributes a
strictly smaller Gauss term. -/
private lemma norm_sub_lt_of_coeff_eq_single {p q : GaussLaurent K r} {m : ℤ}
    (ham : (p : LaurentPolynomial K).coeff m ≠ 0)
    (hm : LaurentPolynomial.gaussNorm r (p : LaurentPolynomial K)
      = ‖(p : LaurentPolynomial K).coeff m‖ * r ^ m)
    (hqc : ∀ j, (q : LaurentPolynomial K).coeff j
      = Finsupp.single m ((p : LaurentPolynomial K).coeff m) j) :
    ‖(p - q : GaussLaurent K r)‖ < ‖(p : GaussLaurent K r)‖ := by
  have hppos : 0 < ‖(p : GaussLaurent K r)‖ := by
    rw [norm_def, hm]
    exact mul_pos (norm_pos_iff.mpr ham) (zpow_pos Fact.out m)
  rcases eq_or_ne (p - q : GaussLaurent K r) 0 with h0 | h0
  · rwa [h0, norm_zero]
  have h0' : ((p - q : GaussLaurent K r) : LaurentPolynomial K) ≠ 0 := h0
  obtain ⟨k, hk⟩ := LaurentPolynomial.exists_gaussNorm_eq r h0'
  have hcoeffk : ((p - q : GaussLaurent K r) : LaurentPolynomial K).coeff k
      = (p : LaurentPolynomial K).coeff k
        - Finsupp.single m ((p : LaurentPolynomial K).coeff m) k := by
    have h3 := LaurentPolynomial.coeff_sub_apply (p : LaurentPolynomial K)
      (q : LaurentPolynomial K) k
    rwa [hqc k] at h3
  have hkm : k ≠ m := by
    rintro rfl
    rw [hcoeffk, Finsupp.single_eq_same, sub_self, norm_zero, zero_mul] at hk
    exact h0 ((LaurentPolynomial.gaussNorm_eq_zero_iff r).mp hk)
  have hck : ((p - q : GaussLaurent K r) : LaurentPolynomial K).coeff k
      = (p : LaurentPolynomial K).coeff k := by
    rw [hcoeffk, Finsupp.single_apply, if_neg (fun h : m = k ↦ hkm h.symm), sub_zero]
  rw [norm_def, hk, hck, norm_def]
  rcases eq_or_ne ((p : LaurentPolynomial K).coeff k) 0 with hc0 | hc0
  · rw [hc0, norm_zero, zero_mul, ← norm_def]
    exact hppos
  · refine lt_of_le_of_ne (LaurentPolynomial.le_gaussNorm r _ k) fun heq ↦ hkm ?_
    exact LaurentPolynomial.gaussTerm_injOn_of_not_memDivisibleValueGroup Fact.out hc0 ham
      (heq.trans hm)

/-- Off the divisible closure, every nonzero element of the Gauss-normed Laurent algebra is
within its own norm of a unit — its dominant monomial `q = single m (p.coeff m)`, which
satisfies `‖q‖ = ‖p‖` and `‖p - q‖ < ‖p‖`. This is the algebraic input to the completeness
argument that makes the Gauss extension (the completion) a field. -/
lemma exists_isUnit_norm_sub_lt {p : GaussLaurent K r} (hp : p ≠ 0) :
    ∃ q : GaussLaurent K r, IsUnit q ∧ ‖q‖ = ‖p‖ ∧ ‖p - q‖ < ‖p‖ := by
  have hp0 : (p : LaurentPolynomial K) ≠ 0 := hp
  obtain ⟨m, hm⟩ := LaurentPolynomial.exists_gaussNorm_eq r hp0
  have ham : (p : LaurentPolynomial K).coeff m ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hm
    exact hp0 ((LaurentPolynomial.gaussNorm_eq_zero_iff r).mp hm)
  set q : GaussLaurent K r :=
    (AddMonoidAlgebra.single m ((p : LaurentPolynomial K).coeff m) : LaurentPolynomial K)
    with hqdef
  have hqu : IsUnit q := by
    have h1 : IsUnit (LaurentPolynomial.C ((p : LaurentPolynomial K).coeff m)
        * LaurentPolynomial.T m) :=
      ((LaurentPolynomial.C).isUnit_map (isUnit_iff_ne_zero.mpr ham)).mul
        (LaurentPolynomial.isUnit_T m)
    have h2 : (q : LaurentPolynomial K)
        = LaurentPolynomial.C ((p : LaurentPolynomial K).coeff m) * LaurentPolynomial.T m :=
      LaurentPolynomial.single_eq_C_mul_T _ _
    exact (h2.symm ▸ h1 : IsUnit (q : LaurentPolynomial K))
  have hqn : ‖q‖ = ‖p‖ := by
    rw [norm_def, hqdef]
    have hsingle : LaurentPolynomial.gaussNorm r
        (AddMonoidAlgebra.single m ((p : LaurentPolynomial K).coeff m) : LaurentPolynomial K)
        = ‖(p : LaurentPolynomial K).coeff m‖ * r ^ m := by
      rw [LaurentPolynomial.single_eq_C_mul_T _ _,
        LaurentPolynomial.gaussNorm_mul Fact.out, LaurentPolynomial.gaussNorm_C,
        LaurentPolynomial.gaussNorm_T]
    rw [hsingle, ← hm, ← norm_def]
  exact ⟨q, hqu, hqn, norm_sub_lt_of_coeff_eq_single ham hm fun j ↦ by rw [hqdef]; rfl⟩

end Field

end GaussLaurent
