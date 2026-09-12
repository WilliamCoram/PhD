/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.MvPolynomial.Nilpotent
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Complete
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Residue

/-! # Units of restricted multivariate power series

Let `R` be a complete normed commutative ring with ultrametric distance and multiplicative
norm.  This file characterises the units of `MvPowerSeries.Restricted R c` by the dominance of
the constant coefficient.

For arbitrary strictly positive radii `c`:

* `MvPowerSeries.Restricted.constantCoeff`: the constant coefficient, as a ring homomorphism
  `Restricted R c →+* R`.
* `MvPowerSeries.Restricted.norm_constantCoeff_of_isUnit`: the constant coefficient of a unit
  achieves the Gauss norm.
* `MvPowerSeries.Restricted.isUnit_of_norm_lt_norm_constantCoeff`: if the constant coefficient
  is a unit of `R` and strictly dominates all other weighted coefficients, the series is a
  unit — its inverse is the geometric series.

The dominance condition is also necessary, at any radii: by the lex-maximality clause of
`exists_achievesGaussNorm_dominant` applied to `f` and `f⁻¹`, every index achieving the Gauss
norm of a unit is `0` (`eq_zero_of_achievesGaussNorm_of_isUnit`), whence:

* `MvPowerSeries.Restricted.isUnit_iff`: a restricted power series is a unit if and only if
  its constant coefficient is a unit of `R` and strictly dominates all other weighted
  coefficients.

For the Tate algebra radii `c = 1` (with `‖1‖ = 1` and non-isolated origin) the power-bounded
subring has its own criterion:

* `MvPowerSeries.Restricted.isUnit_powerBounded_iff`: an element of the power-bounded subring
  `T°` is a unit if and only if its constant coefficient is a unit of `R°` and all its other
  coefficients are topologically nilpotent.  The proof reduces modulo the topological
  nilradical along `topologicalNilradicalResidueEquiv` and applies `MvPolynomial.isUnit_iff`
  over the (reduced) residue ring.
-/

open Filter PowerBounded
open scoped Topology

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {σ : Type*}

section ConstantCoeff

variable (c : σ → ℝ)

/-- The constant coefficient of a restricted power series, as a ring homomorphism. -/
noncomputable def constantCoeff : Restricted R c →+* R :=
  (MvPowerSeries.constantCoeff (σ := σ) (R := R)).comp (IsRestricted.subring c).subtype

omit [NormMulClass R] in
@[simp]
lemma constantCoeff_apply (f : Restricted R c) :
    constantCoeff c f = MvPowerSeries.constantCoeff f.1 := rfl

omit [NormMulClass R] in
lemma constantCoeff_eq_coeff_zero (f : Restricted R c) :
    constantCoeff c f = MvPowerSeries.coeff 0 f.1 := by
  simp [MvPowerSeries.coeff_zero_eq_constantCoeff]

variable [hc : Fact (∀ i, 0 < c i)]

omit [NormMulClass R] in
/-- The constant coefficient is bounded by the Gauss norm. -/
lemma norm_constantCoeff_le (f : Restricted R c) : ‖constantCoeff c f‖ ≤ ‖f‖ := by
  have h := (norm_le_iff c f).mp le_rfl 0
  rwa [Finsupp.prod_zero_index, mul_one, ← constantCoeff_eq_coeff_zero] at h

variable [NormOneClass R]

/-- The constant coefficient of a unit achieves the Gauss norm. -/
theorem norm_constantCoeff_of_isUnit {f : Restricted R c} (hf : IsUnit f) :
    ‖constantCoeff c f‖ = ‖f‖ := by
  obtain ⟨u, rfl⟩ := hf
  set v : Restricted R c := ↑u⁻¹ with hv
  have h1 : ‖(u : Restricted R c)‖ * ‖v‖ = 1 := by rw [hv, ← norm_mul, u.mul_inv, norm_one]
  have h2 : ‖constantCoeff c (u : Restricted R c)‖ * ‖constantCoeff c v‖ = 1 := by
    rw [hv, ← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
  have hg0 : (0 : ℝ) < ‖v‖ :=
    (norm_nonneg _).lt_of_ne fun h ↦ by rw [← h, mul_zero] at h1; exact zero_ne_one h1
  refine le_antisymm (norm_constantCoeff_le c _) (le_of_mul_le_mul_right ?_ hg0)
  calc ‖(u : Restricted R c)‖ * ‖v‖
      = ‖constantCoeff c (u : Restricted R c)‖ * ‖constantCoeff c v‖ := h1.trans h2.symm
    _ ≤ ‖constantCoeff c (u : Restricted R c)‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_left (norm_constantCoeff_le c _) (norm_nonneg _)

omit [NormMulClass R] [NormOneClass R] in
/-- The tail `f - C (constantCoeff f)` has Gauss norm strictly below `‖constantCoeff f‖`,
provided the constant coefficient has positive norm and strictly dominates every other
weighted coefficient. -/
lemma norm_sub_C_constantCoeff_lt {f : Restricted R c} (ha0 : 0 < ‖constantCoeff c f‖)
    (hlt : ∀ t ≠ 0, ‖coeff t f.1‖ * t.prod (c · ^ ·) < ‖constantCoeff c f‖) :
    ‖f - C c (constantCoeff c f)‖ < ‖constantCoeff c f‖ := by
  classical
  rw [norm_lt_iff]
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [val_sub, map_sub, val_C, ← constantCoeff_eq_coeff_zero,
      MvPowerSeries.coeff_zero_C, sub_self, norm_zero, zero_mul]
    exact ha0
  · rw [val_sub, map_sub, val_C, MvPowerSeries.coeff_C, if_neg ht, sub_zero]
    exact hlt t ht

/-- If the constant coefficient `a` of `f` is a unit and the tail `f - C a` has Gauss norm
strictly below `‖a‖`, then `f` is a unit: it factors as `C a * (C a⁻¹ * f)` with
`C a⁻¹ * f = 1 + g` for a topologically nilpotent `g`. -/
theorem isUnit_of_norm_sub_C_constantCoeff_lt [CompleteSpace R] {f : Restricted R c}
    (hu : IsUnit (constantCoeff c f))
    (hfa : ‖f - C c (constantCoeff c f)‖ < ‖constantCoeff c f‖) : IsUnit f := by
  obtain ⟨u, hua⟩ := hu
  set b : R := ((u⁻¹ : Rˣ) : R)
  have h1 : ‖constantCoeff c f‖ * ‖b‖ = 1 := by rw [← hua, ← norm_mul, u.mul_inv, norm_one]
  have hb0 : (0 : ℝ) < ‖b‖ :=
    (norm_nonneg _).lt_of_ne fun h ↦ by rw [← h, mul_zero] at h1; exact zero_ne_one h1
  have hg : ‖C c b * (f - C c (constantCoeff c f))‖ < 1 := by
    have h1' : ‖b‖ * ‖constantCoeff c f‖ = 1 := by rw [mul_comm]; exact h1
    rw [norm_mul, norm_C, ← h1']
    exact mul_lt_mul_of_pos_left hfa hb0
  have hCb : C c (constantCoeff c f) * C c b = 1 := by rw [← map_mul, ← hua, u.mul_inv, map_one]
  have hCbf : C c b * f = 1 + C c b * (f - C c (constantCoeff c f)) := by
    rw [mul_sub, mul_comm (C c b) (C c (constantCoeff c f)), hCb]; ring
  have hunit : IsUnit (C c b * f) := by
    rw [hCbf, ← sub_neg_eq_add]
    exact (IsTopologicallyNilpotent.of_norm_lt_one (by rwa [norm_neg])).isUnit_one_sub
  have hf : f = C c (constantCoeff c f) * (C c b * f) := by rw [← mul_assoc, hCb, one_mul]
  rw [hf]
  exact ((u.isUnit.map (C c)).mul hunit).imp fun _ h ↦ hua ▸ h

/-- If the constant coefficient of `f` is a unit of `R` and strictly dominates all other
weighted coefficients, then `f` is a unit: `f` factors as its constant coefficient times a
`1 + g` with `g` topologically nilpotent. -/
theorem isUnit_of_norm_lt_norm_constantCoeff [CompleteSpace R] {f : Restricted R c}
    (hu : IsUnit (constantCoeff c f))
    (hlt : ∀ t ≠ 0, ‖coeff t f.1‖ * t.prod (c · ^ ·) < ‖constantCoeff c f‖) : IsUnit f := by
  obtain ⟨u, hua⟩ := hu
  have h1 : ‖constantCoeff c f‖ * ‖((u⁻¹ : Rˣ) : R)‖ = 1 := by
    rw [← hua, ← norm_mul, u.mul_inv, norm_one]
  have ha0 : (0 : ℝ) < ‖constantCoeff c f‖ :=
    (norm_nonneg _).lt_of_ne fun h ↦ by rw [← h, zero_mul] at h1; exact zero_ne_one h1
  exact isUnit_of_norm_sub_C_constantCoeff_lt c ⟨u, hua⟩ (norm_sub_C_constantCoeff_lt c ha0 hlt)

/-- Every index achieving the Gauss norm of a unit is `0`: for the lex-maximal dominant pair
`(i, j)` of `f` and `f⁻¹` produced by `exists_achievesGaussNorm_dominant`, the coefficient of
`f * f⁻¹ = 1` at `i + j` has norm `‖coeff i f.1‖ * ‖coeff j f⁻¹.1‖ ≠ 0`, so `i + j = 0` and
maximality collapses all achieving indices to `0`. -/
theorem eq_zero_of_achievesGaussNorm_of_isUnit {f : Restricted R c} (hf : IsUnit f)
    {t : σ →₀ ℕ} (ht : AchievesGaussNorm norm c f.1 t) : t = 0 := by
  classical
  obtain ⟨u, rfl⟩ := hf
  set v : Restricted R c := ↑u⁻¹ with hv
  have h1 : ‖(u : Restricted R c)‖ * ‖v‖ = 1 := by rw [hv, ← norm_mul, u.mul_inv, norm_one]
  have hu0 : ‖(u : Restricted R c)‖ ≠ 0 := fun h ↦ by rw [h, zero_mul] at h1; exact zero_ne_one h1
  have hv0 : ‖v‖ ≠ 0 := fun h ↦ by rw [h, mul_zero] at h1; exact zero_ne_one h1
  obtain ⟨i, j, hi, hj, hdom, hzero⟩ :=
    exists_achievesGaussNorm_dominant c (StrongLT.le hc.out) (u : Restricted R c) v hu0 hv0
  have hkey : ‖coeff (i + j) ((↑u : Restricted R c).1 * v.1)‖
      = ‖coeff i (↑u : Restricted R c).1 * coeff j v.1‖ :=
    MvPowerSeries.antidiagonal_dominant norm _ _ i j IsUltrametricDist.isNonarchimedean_norm
      norm_mul (fun a ↦ (norm_neg a).symm) hdom
  rw [hv, ← val_mul, u.mul_inv, val_one] at hkey
  have hi0 : ‖coeff i (↑u : Restricted R c).1‖ ≠ 0 := fun h ↦
    hu0 (by rw [norm_def, ← hi, h, zero_mul])
  have hj0 : ‖coeff j v.1‖ ≠ 0 := fun h ↦ hv0 (by rw [norm_def, ← hj, h, zero_mul])
  have hij : i + j = 0 := by
    by_contra h
    rw [MvPowerSeries.coeff_one, if_neg h, norm_zero, norm_mul] at hkey
    exact mul_ne_zero hi0 hj0 hkey.symm
  exact (hzero hij).1 t ht

/-- The constant coefficient of a unit strictly dominates every other weighted coefficient. -/
theorem norm_coeff_lt_norm_constantCoeff_of_isUnit {f : Restricted R c} (hf : IsUnit f)
    {t : σ →₀ ℕ} (ht : t ≠ 0) :
    ‖coeff t f.1‖ * t.prod (c · ^ ·) < ‖constantCoeff c f‖ := by
  rw [norm_constantCoeff_of_isUnit c hf]
  exact lt_of_le_of_ne ((norm_le_iff c f).mp le_rfl t) fun h ↦
    ht (eq_zero_of_achievesGaussNorm_of_isUnit c hf h)

/-- **Units of restricted power series**, at arbitrary radii: `f` is a unit if and only if its
constant coefficient is a unit of `R` and strictly dominates all other weighted
coefficients. -/
theorem isUnit_iff [CompleteSpace R] {f : Restricted R c} :
    IsUnit f ↔ IsUnit (constantCoeff c f) ∧
      ∀ t ≠ 0, ‖coeff t f.1‖ * t.prod (c · ^ ·) < ‖constantCoeff c f‖ :=
  ⟨fun hf ↦ ⟨hf.map _, fun _ ht ↦ norm_coeff_lt_norm_constantCoeff_of_isUnit c hf ht⟩,
    fun ⟨hu, hlt⟩ ↦ isUnit_of_norm_lt_norm_constantCoeff c hu hlt⟩

end ConstantCoeff

section TateAlgebra

variable [NormOneClass R] [NeBot (𝓝[≠] (0 : R))] [DecidableEq σ] [CompleteSpace R]

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (MvPowerSeries.Restricted R (1 : σ → ℝ)) (S := ℤ)

/-- **Units of the power-bounded subring of the Tate algebra**: `f ∈ T°` is a unit if and only
if its constant coefficient is a unit of `R°` and all its other coefficients are topologically
nilpotent.  Reduce modulo the topological nilradical along `topologicalNilradicalResidueEquiv`
and use the polynomial criterion over the reduced residue ring. -/
theorem isUnit_powerBounded_iff (f : ↥T°) :
    IsUnit f ↔ IsUnit (powerBoundedCoeff f 0) ∧
      ∀ t ≠ 0, IsTopologicallyNilpotent (coeff t f.1.1) := by
  refine (isUnit_iff_isUnit_mk_topologicalNilradical f).trans ?_
  refine (MulEquiv.isUnit_map
    (f := topologicalNilradicalResidueEquiv (R := R) (σ := σ))).symm.trans ?_
  rw [topologicalNilradicalResidueEquiv_mk, MvPolynomial.isUnit_iff]
  refine and_congr ?_ (forall_congr' fun t ↦ imp_congr Iff.rfl ?_)
  · rw [coeff_residueRingHom]
    exact (isUnit_iff_isUnit_mk_topologicalNilradical _).symm
  · rw [coeff_residueRingHom, isNilpotent_iff_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
      mem_topologicalNilradical_iff, powerBoundedCoeff_coe]

end TateAlgebra

end MvPowerSeries.Restricted
