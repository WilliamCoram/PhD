/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Lifts
import PhD.BirkovichWP.RingTheory.PowerSeries.Restricted.WeierstrassDivision
import PhD.BirkovichWP.RingTheory.PowerSeries.Restricted.Rescale
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Residue

/-! # Weierstrass division existence: the radius-`1` residue engine (legacy)

The **existence** half of univariate Weierstrass division, proved by the residue-field
reduction: normalise the divisor to norm one, reduce modulo a closed-ball ideal to a monic
polynomial over `R° ⧸ ball` where Euclidean division is available, lift `ε`-approximately,
and conclude by density + closedness of `divisionSet` (the closedness, bounds and quotient
uniqueness live in the shared core `PhD.ForMathlib.…PowerSeries.Restricted.WeierstrassDivision`).

This engine is **subsumed** by the extension-free Martin proof
`PhD.ForMathlib.…PowerSeries.Restricted.MulWeierstrassDivision.weierstrassDivision_exists_of_isMulDistinguished`
(any complete ultrametric normed commutative ring, no norm-one/scaling hypotheses). It is
retained here, verbatim, as the engine behind the Berkovich (Gauss-extension) endpoints in
`PhD.BirkovichWP`, and is not part of the mathlib-bound canonical development.
-/

open Filter PowerBounded
open scoped Topology

namespace PowerSeries.Restricted

/-! ## The radius-`1` engine

Everything in this section is the implementation layer behind the general-radius existence
theorem: it is stated at radius `1` because the reduction of `T°` modulo a ball ideal is a
*polynomial* ring only there.  Consumers should use the general-radius theorems below. -/

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormMulClass R] [NormOneClass R] [NeBot (𝓝[≠] (0 : R))]

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)

section Engine

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] in
/-- For a distinguished `g` with leading-coefficient norm `1`, there is `ε ∈ (0, 1)`
dominating every strictly-higher coefficient norm. -/
lemma exists_lt_one_forall_norm_coeff_le {g : Restricted R 1} {s : ℕ}
    (hg : IsDistinguished norm 1 g.1 s) (hg1 : ‖coeff s g.1‖ = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ t, s < t → ‖coeff t g.1‖ ≤ ε := by
  have htend := (isRestricted_iff' 1 g.1).mp g.2
  simp only [one_pow, mul_one] at htend
  exact exists_pos_lt_forall_le_of_tendsto_zero htend (fun t ↦ norm_nonneg _) one_pos
    fun t ht ↦ by simpa [hg1] using hg.gaussTerm_lt t ht

omit [CompleteSpace R] in
/-- For `0 < ε < 1` the residue ring `R° ⧸ closedBall ε` is nontrivial. -/
lemma nontrivial_quotient_closedBall_ideal {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Nontrivial (↥R° ⧸ closedBall_ideal (R := R) hε0.le) := by
  refine Ideal.Quotient.nontrivial_iff.mpr fun h ↦ absurd hε1 (not_lt.mpr ?_)
  have h1 : (1 : ↥R°) ∈ closedBall_ideal (R := R) hε0.le := h ▸ Submodule.mem_top
  rwa [mem_closedBall_ideal, OneMemClass.coe_one, norm_one] at h1

omit [CompleteSpace R] in
/-- When `g ∈ T°` has degree-`s` coefficient equal to `1` and `ε ∈ (0, 1)` dominates every
strictly-higher coefficient norm, the reduction of `g` modulo the closed ball of radius `ε` is
a monic polynomial of degree `s`. -/
lemma monic_residueRingHom_of_isDistinguished {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {s : ℕ}
    (g : ↥T°) (hcs : coeff s g.1.1 = 1) (hgt : ∀ t, s < t → ‖coeff t g.1.1‖ ≤ ε) :
    (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).Monic ∧
    (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).degree = s := by
  have := nontrivial_quotient_closedBall_ideal (R := R) hε0 hε1
  have hs : (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).coeff s
      = 1 := by
    rw [coeff_residueRingHom, show powerBoundedCoeff g s = 1 from Subtype.ext hcs, map_one]
  have hzero : ∀ v, s < v →
      (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).coeff v = 0 := by
    intro v hv
    rw [coeff_residueRingHom, Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal]
    exact hgt v hv
  have hdeg := le_antisymm
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm ↦ hzero m (mod_cast hm))
    (Polynomial.le_degree_of_ne_zero (by rw [hs]; exact one_ne_zero))
  exact ⟨Polynomial.monic_of_degree_le s hdeg.le hs, hdeg⟩

omit [CompleteSpace R] in
/-- If the reduction of `g` modulo the closed ball of radius `ε` is monic, every `f ∈ T°`
admits an `ε`-approximate Euclidean division by `g`: there are `q ∈ T°` and a polynomial `r`
over `R` with `deg r < deg (residue g)` and `‖f - g q - r‖ ≤ ε`. -/
lemma exists_approx_div_of_monic_residue {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (g f : ↥T°)
    (hτg : (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).Monic) :
    ∃ (q : ↥T°) (r : Polynomial R),
      r.degree < (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0)
        g).degree ∧ ‖f.1 - g.1 * q.1 - Polynomial.toRestricted 1 r‖ ≤ ε := by
  have hnt := nontrivial_quotient_closedBall_ideal (R := R) hε0 hε1
  set τ := residueRingHom (closedBall_ideal (R := R) hε0.le) (isOpen_closedBall_ideal hε0)
    with hτdef
  have hrdeg := Polynomial.degree_modByMonic_lt (τ f) hτg
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective (τ f /ₘ τ g)
  have hmem : (τ f %ₘ τ g)
      ∈ Polynomial.lifts (Ideal.Quotient.mk (closedBall_ideal (R := R) hε0.le)) :=
    Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective _
  obtain ⟨P, hP_map, hP_deg⟩ := Polynomial.exists_degree_eq_of_mem_lifts hmem
  have hres : τ (f - g * toPowerBounded Q - toPowerBounded P) = 0 := by
    rw [map_sub, map_sub, map_mul, hτdef, residueRingHom_toPowerBounded,
      residueRingHom_toPowerBounded, ← hτdef, hQ, hP_map]
    linear_combination -Polynomial.modByMonic_add_div (τ f) (τ g)
  refine ⟨toPowerBounded Q, P.map (PowerBounded.subring R (S := ℤ)).subtype,
    Polynomial.degree_map_le.trans_lt (hP_deg.trans_lt hrdeg), ?_⟩
  simpa [sub_sub] using (residueRingHom_closedBall_ideal_eq_zero_iff hε0 _).mp hres

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] in
/-- The algebraic core of transporting an approximate division back to the original data:
scaling the normalised Weierstrass residual `C α * f - (C u * g) * qT - r` by `C αinv`, with
`αinv * α = 1`, yields the un-normalised residual for the original `f` and `g`. -/
private lemma C_mul_normalised_residual_eq {f g qT : Restricted R 1} {α αinv u : R}
    (hαinv_α : αinv * α = 1) (r : Polynomial R) :
    C 1 αinv * (C 1 α * f - C 1 u * g * qT - Polynomial.toRestricted 1 r)
      = f - g * (C 1 (αinv * u) * qT) - Polynomial.toRestricted 1 (Polynomial.C αinv * r) := by
  rw [mul_sub, mul_sub,
    show C 1 αinv * Polynomial.toRestricted 1 r
        = Polynomial.toRestricted 1 (Polynomial.C αinv * r) from by
      rw [map_mul, Polynomial.toRestricted_C],
    show C 1 αinv * (C 1 α * f) = f from by
      rw [← mul_assoc, ← map_mul, hαinv_α, map_one, one_mul],
    show C 1 αinv * (C 1 u * g * qT) = g * (C 1 (αinv * u) * qT) from by
      rw [map_mul (C 1) αinv u]; ring]

omit [CompleteSpace R] in
/-- **The `ε`-approximation step**: for a distinguished `g` of norm `1` and every `f` whose
norm is realised by a unit, there is `b ∈ divisionSet g s` with `‖-f + b‖ ≤ ε * ‖f‖`. -/
lemma exists_mem_divisionSet_norm_le {g : Restricted R 1} (hgn : ‖g‖ = 1) {s : ℕ}
    (hg : IsDistinguished norm 1 g.1 s) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hε_bd : ∀ t, s < t → ‖coeff t g.1‖ ≤ ε) (f : Restricted R 1)
    (hf : ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ b ∈ divisionSet g s, ‖-f + b‖ ≤ ε * ‖f‖ := by
  have hcoeff_C : ∀ (a : R) (h : Restricted R 1) (k : ℕ),
      coeff k (C 1 a * h).1 = a * coeff k h.1 := fun a h k ↦ coeff_C_mul k h.1 a
  have hntR : Nontrivial R := hg.nontrivial
  obtain ⟨α, hα_norm, hα_unit⟩ := hf
  have hf_pos : 0 < ‖f‖ := inv_pos.mp (hα_norm ▸ norm_pos_iff.mpr hα_unit.ne_zero)
  obtain ⟨A, hA⟩ := hα_unit
  set αinv : R := ((A⁻¹ : Rˣ) : R) with hαinv_def
  have hαinv_α : αinv * α = 1 := by rw [hαinv_def, ← hA]; exact A.inv_mul
  have hαinv_norm : ‖αinv‖ = ‖f‖ := by rw [hαinv_def, norm_units_inv, hA, hα_norm, inv_inv]
  have hg1 : ‖coeff s g.1‖ = 1 := by simpa [hgn] using hg.norm_coeff_mul_pow_eq
  obtain ⟨U, hU⟩ := hg.isUnit_coeff
  set u : R := ((U⁻¹ : Rˣ) : R) with hu_def
  have hu_cs : u * coeff s g.1 = 1 := by rw [hu_def, ← hU]; exact U.inv_mul
  have hu_norm : ‖u‖ = 1 := by rw [hu_def, norm_units_inv, hU, hg1, inv_one]
  set g' : Restricted R 1 := C 1 u * g with hg'_def
  set f' : Restricted R 1 := C 1 α * f with hf'_def
  have hg'_cs : coeff s g'.1 = 1 := by rw [hg'_def, hcoeff_C, hu_cs]
  have hg'_norm : ‖g'‖ = 1 := by rw [hg'_def, norm_mul, norm_C, hu_norm, hgn, one_mul]
  have hf'_norm : ‖f'‖ = 1 := by
    rw [hf'_def, norm_mul, norm_C, hα_norm, inv_mul_cancel₀ hf_pos.ne']
  have hg'_bd : ∀ t, s < t → ‖coeff t g'.1‖ ≤ ε := fun t ht ↦ by
    simpa only [hg'_def, hcoeff_C, norm_mul, hu_norm, one_mul] using hε_bd t ht
  have hg'_pb : g' ∈ PowerBounded.subring (Restricted R 1) (S := ℤ) :=
    isPowerBounded_of_norm_le_one hg'_norm.le
  have hf'_pb : f' ∈ PowerBounded.subring (Restricted R 1) (S := ℤ) :=
    isPowerBounded_of_norm_le_one hf'_norm.le
  have hnt := nontrivial_quotient_closedBall_ideal (R := R) hε0 hε1
  have hmonic := monic_residueRingHom_of_isDistinguished hε0 hε1 ⟨g', hg'_pb⟩ hg'_cs hg'_bd
  obtain ⟨qpb, r, hr_deg, hbound⟩ :=
    exists_approx_div_of_monic_residue hε0 hε1 ⟨g', hg'_pb⟩ ⟨f', hf'_pb⟩ hmonic.1
  rw [hmonic.2] at hr_deg
  set qT : Restricted R 1 := qpb.1
  have hX : ‖f' - g' * qT - Polynomial.toRestricted 1 r‖ ≤ ε := by
    simpa [sub_sub] using hbound
  set q : Restricted R 1 := C 1 (αinv * u) * qT
  set r' : Polynomial R := Polynomial.C αinv * r with hr'_def
  have key : C 1 αinv * (f' - g' * qT - Polynomial.toRestricted 1 r)
      = f - g * q - Polynomial.toRestricted 1 r' :=
    C_mul_normalised_residual_eq hαinv_α r
  refine ⟨g * q + Polynomial.toRestricted 1 r', ⟨q, r', ?_, rfl⟩, ?_⟩
  · rw [hr'_def, ← Polynomial.smul_eq_C_mul αinv]
    exact (Polynomial.degree_smul_le αinv r).trans_lt hr_deg
  · rw [show -f + (g * q + Polynomial.toRestricted 1 r')
        = -(C 1 αinv * (f' - g' * qT - Polynomial.toRestricted 1 r)) from by rw [key]; ring,
      norm_neg, norm_mul, norm_C, hαinv_norm, mul_comm ε]
    exact mul_le_mul_of_nonneg_left hX (norm_nonneg f)

omit [CompleteSpace R] in
/-- The division set of a norm-one distinguished series is dense, by
`AddSubgroup.dense_of_infDist_le` applied to the `ε`-approximation. -/
lemma dense_divisionSet {g : Restricted R 1} (hgn : ‖g‖ = 1) {s : ℕ}
    (hg : IsDistinguished norm 1 g.1 s)
    (hunit : ∀ f : Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    Dense (divisionSet g s) := by
  have hg1 : ‖coeff s g.1‖ = 1 := by simpa [hgn] using hg.norm_coeff_mul_pow_eq
  obtain ⟨ε, hε0, hε1, hε_bd⟩ := exists_lt_one_forall_norm_coeff_le hg hg1
  exact dense_divisionSet_of_forall_exists_norm_le hε0 hε1
    fun f hf ↦ exists_mem_divisionSet_norm_le hgn hg hε0 hε1 hε_bd f (hunit f hf)

/-- **Weierstrass division at radius `1`, normalised case `‖g‖ = 1`**: the division set is
closed and dense, hence everything. -/
theorem weierstrassDivision_exists_of_norm_eq_one {g : Restricted R 1} (hgn : ‖g‖ = 1) {s : ℕ}
    (hg : IsDistinguished norm 1 g.1 s) (f : Restricted R 1)
    (hunit : ∀ f : Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (q : Restricted R 1) (r : Polynomial R), r.degree < s ∧
      f = g * q + Polynomial.toRestricted 1 r := by
  change f ∈ divisionSet g s
  rw [← (isClosed_divisionSet hg).closure_eq]
  exact dense_divisionSet hgn hg hunit f

end Engine

/-! ## Weierstrass division, at an arbitrary radius -/

section Existence

variable {c : ℝ} [Fact (0 < c)]

omit [CompleteSpace R] [(𝓝[≠] (0 : R)).NeBot] in
/-- The scaling hypothesis of Weierstrass division realises the radius by a unit of `R`:
apply it to the variable `X` (of norm `c`) and invert the realising unit.  In particular
`hunit` can only hold when `c` lies in the value group `‖Rˣ‖`; over a normed field this is
exactly when it holds. -/
lemma exists_units_norm_eq
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ u : Rˣ, ‖(u : R)‖ = c := by
  have hXnorm : ‖X R c‖ = c := by rw [norm_X, norm_one, one_mul]
  have hX0 : X R c ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_eq (Fact.out : (0 : ℝ) < c) hXnorm.symm)
  obtain ⟨a, ha_norm, ha_unit⟩ := hunit _ hX0
  obtain ⟨A, rfl⟩ := ha_unit
  exact ⟨A⁻¹, by rw [norm_units_inv, ha_norm, hXnorm, inv_inv]⟩

/-- **Weierstrass division, existence**: for `g` distinguished of degree `s`, under the
scaling hypothesis `hunit` (every nonzero norm value is realised by a unit of `R`; over a
normed field this holds if and only if `c` lies in the value group `‖Rˣ‖`, cf.
`exists_units_norm_eq`), every `f` divides as `f = g * q + r` with `deg r < s`.  Proven by
rescaling to the radius-`1` engine along a unit realising the radius. -/
theorem weierstrassDivision_exists {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) (f : Restricted R c)
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r := by
  have hntR : Nontrivial R := hg.nontrivial
  obtain ⟨u, hu⟩ := exists_units_norm_eq hunit
  have hu' : ‖(u : R)‖ * 1 = c := (mul_one _).trans hu
  have hg₁ : IsDistinguished norm 1 (rescaleEquiv u hu' g).1 s :=
    (isDistinguished_rescaleEquiv_iff u hu' g s).mpr hg
  obtain ⟨a, ha1, ha2⟩ : ∃ a : R, ‖a‖ = ‖rescaleEquiv u hu' g‖⁻¹ ∧ IsUnit a := by
    rw [norm_rescaleEquiv u hu' g]
    exact hunit g fun h0 ↦ hg.ne_zero (congrArg Subtype.val h0)
  have hga : ‖C 1 a * rescaleEquiv u hu' g‖ = 1 := by
    rw [norm_mul, norm_C, ha1, inv_mul_cancel₀ hg₁.norm_pos.ne']
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_exists_of_norm_eq_one hga (hg₁.C_mul ha2)
    (rescaleEquiv u hu' f) (hunit_transport u hu' hunit)
  have hf₁ : rescaleEquiv u hu' f
      = rescaleEquiv u hu' g * (C 1 a * q₀) + Polynomial.toRestricted 1 r₀ := by
    linear_combination hf₀
  have h2 := congrArg (rescaleEquiv u hu').symm hf₁
  rw [RingEquiv.symm_apply_apply, map_add, map_mul, RingEquiv.symm_apply_apply,
    rescaleEquiv_symm_toRestricted] at h2
  exact ⟨(rescaleEquiv u hu').symm (C 1 a * q₀),
    r₀.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X),
    Polynomial.degree_comp_C_mul_X_lt hr₀ _, h2⟩

/-- **Weierstrass division**: existence and uniqueness of the division `f = g * q + r`,
`deg r < s`, under the scaling hypothesis.  (The nested `∃!` shares the witness pair; the
parts are recovered by `weierstrassDivision_exists` and `weierstrassDivision_q_unique`.) -/
theorem weierstrassDivision_uniqueness {g : Restricted R c}
    {s : ℕ} (hg : IsDistinguished norm c g.1 s) (f : Restricted R c)
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! q : Restricted R c, ∃! r : Polynomial R, r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r :=
  weierstrassDivision_uniqueness_of_exists hg (weierstrassDivision_exists hg f hunit)

end Existence

end PowerSeries.Restricted
