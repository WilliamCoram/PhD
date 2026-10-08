/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import PhD.TauCeti.Code.PadicFunctionalAnalysis.PowerBounded
import PhD.TauCeti.Code.PadicFunctionalAnalysis.UnitBall
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Units
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Basic

/-!
# The reduction of the Tate algebra

Let `K` be a nonarchimedean normed field with unit ball `K⁰` and residue field `k = K⁰ / K⁰⁰`, and
let `T` be the ring of restricted power series over `K` at the unit polyradius. The unit ball
`T⁰ = {‖f‖ ≤ 1}` consists of the series with coefficients in `K⁰`, the open unit ball
`T⁰⁰ = {‖f‖ < 1}` of those with coefficients in `K⁰⁰`, and reduction of the coefficients is a
surjective ring homomorphism `T⁰ → k[X]` with kernel `T⁰⁰`. Units are detected by the reduction.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.1.2 (BGR 5.1.2, 5.1.3;
Bosch 1.2/4). Tau Ceti home: `TauCeti/RingTheory/TateAlgebra/Reduction.lean`.

## Main definitions

* `MvPowerSeries.Restricted.reduction` — the reduction map `T⁰ →+* MvPolynomial σ k`.
* `MvPowerSeries.Restricted.reductionEquiv` — the isomorphism `T⁰ ⧸ T⁰⁰ ≃+* MvPolynomial σ k`
  (BGR 5.1.2/2).
* `MvPowerSeries.Restricted.ofUnitBallPolynomial` — polynomials over `K⁰` inside `T⁰`.

## Main results

* `MvPowerSeries.Restricted.ker_reduction`, `reduction_surjective`.
* `MvPowerSeries.Restricted.isUnit_iff_norm_coeff_lt` — the units of the Tate algebra
  (BGR 5.1.3/1; Bosch 1.2/4).
* `MvPowerSeries.Restricted.isUnit_iff_isUnit_reduction` — units of `T⁰` are detected by the
  reduction (BGR 5.1.3/1).
* `MvPowerSeries.Restricted.jacobson_bot` — the Jacobson radical of the Tate algebra is zero
  (BGR 5.1.3/3).
-/

open Subring NormedRing IsLocalRing Filter Topology

namespace MvPowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}

/-! ### The reduction map -/

/-- The coefficient of a series in the unit ball of the Tate algebra, as an element of the unit
ball of `K`. -/
def unitBallCoeff (f : unitClosedBall (Restricted K (1 : σ → ℝ))) (t : σ →₀ ℕ) :
    unitClosedBall K :=
  ⟨coeff t f.1.1, mem_unitClosedBall.2 ((norm_coeff_le f.1 t).trans (Subring.norm_le_one f))⟩

@[simp]
theorem coe_unitBallCoeff (f : unitClosedBall (Restricted K (1 : σ → ℝ))) (t : σ →₀ ℕ) :
    (unitBallCoeff f t : K) = coeff t f.1.1 := rfl

private lemma residue_unitBallCoeff_eq_zero_iff (f : unitClosedBall (Restricted K (1 : σ → ℝ)))
    (t : σ →₀ ℕ) : residue (unitClosedBall K) (unitBallCoeff f t) = 0 ↔ ‖coeff t f.1.1‖ < 1 := by
  rw [residue_eq_zero_iff, maximalIdeal_unitClosedBall, mem_openUnitBallIdeal, coe_unitBallCoeff]

/-- All but finitely many coefficients of a series in the unit ball reduce to zero. -/
theorem finite_support_residue_unitBallCoeff (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    (Function.support fun t ↦ residue (unitClosedBall K) (unitBallCoeff f t)).Finite :=
  (finite_setOf_le_norm_coeff f.1 one_pos).subset fun t ht ↦
    not_lt.1 fun h ↦ ht ((residue_unitBallCoeff_eq_zero_iff f t).2 h)

/-- The reduction of a series in the unit ball: reduce every coefficient to the residue field.
Source: BGR 5.1.2 ("`(Σ a_ν X^ν)~ := Σ ã_ν X^ν`"). -/
noncomputable def reductionFun (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    MvPolynomial σ (ResidueField (unitClosedBall K)) :=
  ⟨Finsupp.ofSupportFinite _ (finite_support_residue_unitBallCoeff f)⟩

theorem coeff_reductionFun (f : unitClosedBall (Restricted K (1 : σ → ℝ))) (t : σ →₀ ℕ) :
    (reductionFun f).coeff t = residue (unitClosedBall K) (unitBallCoeff f t) := rfl

theorem reductionFun_one :
    reductionFun (1 : unitClosedBall (Restricted K (1 : σ → ℝ))) = 1 := by
  classical
  ext t
  rw [coeff_reductionFun, MvPolynomial.coeff_one]
  by_cases ht : t = 0
  · subst ht
    have h1 : unitBallCoeff (1 : unitClosedBall (Restricted K (1 : σ → ℝ))) 0 = 1 :=
      Subtype.ext (by simp [MvPowerSeries.coeff_one])
    simp [h1]
  · have h0 : unitBallCoeff (1 : unitClosedBall (Restricted K (1 : σ → ℝ))) t = 0 :=
      Subtype.ext (by simp [MvPowerSeries.coeff_one, ht])
    simp [h0, Ne.symm ht]

theorem reductionFun_mul (f g : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reductionFun (f * g) = reductionFun f * reductionFun g := by
  classical
  ext t
  have h : unitBallCoeff (f * g) t =
      ∑ p ∈ Finset.antidiagonal t, unitBallCoeff f p.1 * unitBallCoeff g p.2 :=
    Subtype.ext (by simp [MvPowerSeries.coeff_mul])
  rw [MvPolynomial.coeff_mul, coeff_reductionFun, h, map_sum]
  simp only [map_mul, coeff_reductionFun]

theorem reductionFun_zero :
    reductionFun (0 : unitClosedBall (Restricted K (1 : σ → ℝ))) = 0 := by
  ext t
  have h0 : unitBallCoeff (0 : unitClosedBall (Restricted K (1 : σ → ℝ))) t = 0 :=
    Subtype.ext (by simp)
  rw [coeff_reductionFun, h0, map_zero, MvPolynomial.coeff_zero]

theorem reductionFun_add (f g : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reductionFun (f + g) = reductionFun f + reductionFun g := by
  ext t
  have h : unitBallCoeff (f + g) t = unitBallCoeff f t + unitBallCoeff g t :=
    Subtype.ext (by simp)
  rw [MvPolynomial.coeff_add, coeff_reductionFun, coeff_reductionFun, coeff_reductionFun, h,
    map_add]

/-- The reduction map `T⁰ → k[X]`, coefficientwise reduction to the residue field.
Source: BGR 5.1.2; Bosch 1.2 (the epimorphism `π`). -/
noncomputable def reduction :
    unitClosedBall (Restricted K (1 : σ → ℝ)) →+*
      MvPolynomial σ (ResidueField (unitClosedBall K)) where
  toFun := reductionFun
  map_one' := reductionFun_one
  map_mul' := reductionFun_mul
  map_zero' := reductionFun_zero
  map_add' := reductionFun_add

@[simp]
theorem coeff_reduction (f : unitClosedBall (Restricted K (1 : σ → ℝ))) (t : σ →₀ ℕ) :
    (reduction f).coeff t = residue (unitClosedBall K) (unitBallCoeff f t) := rfl

/-- The reduction vanishes exactly on the series of Gauss norm less than one. Source: BGR 5.1.2
("Obviously the kernel of this map is `Tₙˇ`"); Bosch 1.2 ("`f̃ = 0` if and only if `|f| < 1`"). -/
theorem reduction_eq_zero_iff (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reduction f = 0 ↔ ‖(f : Restricted K (1 : σ → ℝ))‖ < 1 := by
  rw [MvPolynomial.ext_iff, norm_lt_iff_forall_norm_coeff_lt]
  simp only [coeff_reduction, MvPolynomial.coeff_zero, residue_unitBallCoeff_eq_zero_iff]

/-- A series of the unit ball with nonzero reduction has Gauss norm one. -/
theorem norm_eq_one_of_reduction_ne_zero {f : unitClosedBall (Restricted K (1 : σ → ℝ))}
    (hf : reduction f ≠ 0) : ‖(f : Restricted K (1 : σ → ℝ))‖ = 1 :=
  le_antisymm (Subring.norm_le_one f) (not_lt.1 fun h ↦ hf ((reduction_eq_zero_iff f).2 h))

/-- The kernel of the reduction map is the open unit ball. Source: BGR 5.1.2. -/
theorem ker_reduction :
    RingHom.ker (reduction (K := K) (σ := σ)) = openUnitBallIdeal (Restricted K (1 : σ → ℝ)) := by
  ext f
  rw [RingHom.mem_ker, reduction_eq_zero_iff, mem_openUnitBallIdeal]

private lemma coeff_toRestricted_map_subtype (p : MvPolynomial σ (unitClosedBall K))
    (t : σ →₀ ℕ) :
    coeff t (MvPolynomial.toRestricted (1 : σ → ℝ)
      (MvPolynomial.map (unitClosedBall K).subtype p)).1 = (↑(p.coeff t) : K) := by
  rw [MvPolynomial.val_toRestricted, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]
  rfl

/-- A polynomial with coefficients in the unit ball of `K` has Gauss norm at most one. -/
theorem norm_toRestricted_map_subtype_le_one (p : MvPolynomial σ (unitClosedBall K)) :
    ‖MvPolynomial.toRestricted (1 : σ → ℝ)
      (MvPolynomial.map (unitClosedBall K).subtype p)‖ ≤ 1 :=
  (norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ by
    rw [coeff_toRestricted_map_subtype]
    exact Subring.norm_le_one (p.coeff t)

/-- Polynomials over the unit ball of `K`, inside the unit ball of the Tate algebra. -/
noncomputable def ofUnitBallPolynomial :
    MvPolynomial σ (unitClosedBall K) →+* unitClosedBall (Restricted K (1 : σ → ℝ)) :=
  ((MvPolynomial.toRestricted (1 : σ → ℝ)).comp
    (MvPolynomial.map (unitClosedBall K).subtype)).codRestrict _
      fun p ↦ mem_unitClosedBall.2 (norm_toRestricted_map_subtype_le_one p)

@[simp]
theorem coe_ofUnitBallPolynomial (p : MvPolynomial σ (unitClosedBall K)) :
    (ofUnitBallPolynomial p : Restricted K (1 : σ → ℝ)) =
      MvPolynomial.toRestricted (1 : σ → ℝ) (MvPolynomial.map (unitClosedBall K).subtype p) :=
  rfl

/-- The reduction of a polynomial over the unit ball is its coefficientwise reduction. -/
theorem reduction_ofUnitBallPolynomial (p : MvPolynomial σ (unitClosedBall K)) :
    reduction (ofUnitBallPolynomial p) = MvPolynomial.map (residue (unitClosedBall K)) p := by
  ext t
  rw [coeff_reduction, MvPolynomial.coeff_map]
  congr 1

/-- The reduction of a constant of the unit ball is its residue class. -/
theorem reduction_C (a : unitClosedBall K)
    (h : C (1 : σ → ℝ) (a : K) ∈ unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reduction ⟨C (1 : σ → ℝ) (a : K), h⟩ = MvPolynomial.C (residue (unitClosedBall K) a) := by
  have e : (⟨C (1 : σ → ℝ) (a : K), h⟩ : unitClosedBall (Restricted K (1 : σ → ℝ))) =
      ofUnitBallPolynomial (MvPolynomial.C a) :=
    Subtype.ext (by rw [coe_ofUnitBallPolynomial, MvPolynomial.map_C,
      MvPolynomial.toRestricted_C]; rfl)
  rw [e, reduction_ofUnitBallPolynomial, MvPolynomial.map_C]

/-- The reduction of a variable is the variable. -/
theorem reduction_X (i : σ) (h : X K (1 : σ → ℝ) i ∈ unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reduction ⟨X K (1 : σ → ℝ) i, h⟩ = MvPolynomial.X i := by
  have e : (⟨X K (1 : σ → ℝ) i, h⟩ : unitClosedBall (Restricted K (1 : σ → ℝ))) =
      ofUnitBallPolynomial (MvPolynomial.X i) :=
    Subtype.ext (by rw [coe_ofUnitBallPolynomial, MvPolynomial.map_X,
      MvPolynomial.toRestricted_X])
  rw [e, reduction_ofUnitBallPolynomial, MvPolynomial.map_X]

/-- Every series of the unit ball is a polynomial over the unit ball of `K` up to a series of Gauss
norm less than one. -/
theorem exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal
    (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    ∃ p : MvPolynomial σ (unitClosedBall K),
      f - ofUnitBallPolynomial p ∈ openUnitBallIdeal (Restricted K (1 : σ → ℝ)) := by
  classical
  set s := (finite_setOf_le_norm_coeff f.1 one_pos).toFinset
  set p := ∑ u ∈ s, MvPolynomial.monomial u (unitBallCoeff f u)
  refine ⟨p, ?_⟩
  rw [mem_openUnitBallIdeal, norm_lt_iff_forall_norm_coeff_lt]
  intro t
  have hp : (↑(p.coeff t) : K) = if t ∈ s then coeff t f.1.1 else 0 := by
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', apply_ite Subtype.val,
      coe_unitBallCoeff, ZeroMemClass.coe_zero]
  have hcoeff : coeff t ((f - ofUnitBallPolynomial p : unitClosedBall _) :
      Restricted K (1 : σ → ℝ)).1 = coeff t f.1.1 - (↑(p.coeff t) : K) := by
    rw [AddSubgroupClass.coe_sub, val_sub, map_sub, coe_ofUnitBallPolynomial,
      coeff_toRestricted_map_subtype]
  rw [hcoeff, hp]
  split_ifs with ht
  · simp
  · rw [sub_zero]
    exact not_le.1 fun h ↦ ht ((Set.Finite.mem_toFinset _).2 h)

/-- The reduction map is surjective. Source: BGR 5.1.2 ("the map is surjective"). -/
theorem reduction_surjective : Function.Surjective (reduction (K := K) (σ := σ)) := by
  intro q
  obtain ⟨p, rfl⟩ :=
    MvPolynomial.map_surjective (f := residue (unitClosedBall K)) residue_surjective q
  exact ⟨ofUnitBallPolynomial p, reduction_ofUnitBallPolynomial p⟩

/-- **The reduction of the Tate algebra is a polynomial ring**: `T⁰ / T⁰⁰ ≅ k[X]`.
Source: BGR 5.1.2/2. -/
noncomputable def reductionEquiv :
    (unitClosedBall (Restricted K (1 : σ → ℝ)) ⧸ openUnitBallIdeal (Restricted K (1 : σ → ℝ))) ≃+*
      MvPolynomial σ (ResidueField (unitClosedBall K)) :=
  (Ideal.quotEquivOfEq ker_reduction.symm).trans
    (RingHom.quotientKerEquivOfSurjective reduction_surjective)

theorem reductionEquiv_mk (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    reductionEquiv (Ideal.Quotient.mk _ f) = reduction f :=
  rfl

/-! ### Power-bounded and topologically nilpotent elements -/

section PowerBounded

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜]

/-- The power-bounded elements of the Tate algebra are the series with coefficients in the unit
ball. Source: BGR 5.1.2 ("`T̊ₙ = Tₙ°`"). -/
theorem isPowerBounded_iff_forall_norm_coeff_le_one {f : Restricted 𝕜 (1 : σ → ℝ)} :
    PowerBounded.IsPowerBounded f ↔ ∀ t, ‖coeff t f.1‖ ≤ 1 :=
  PowerBounded.isPowerBounded_iff_norm_le_one.trans (norm_le_iff_forall_norm_coeff_le f)

end PowerBounded

/-- The topologically nilpotent elements of the Tate algebra are the series with coefficients in
the open unit ball. Source: BGR 5.1.2 ("`Ťₙ = Tₙˇ`"). -/
theorem isTopologicallyNilpotent_iff_forall_norm_coeff_lt_one {f : Restricted K (1 : σ → ℝ)} :
    IsTopologicallyNilpotent f ↔ ∀ t, ‖coeff t f.1‖ < 1 :=
  isTopologicallyNilpotent_iff_norm_lt_one.trans (norm_lt_iff_forall_norm_coeff_lt f)

/-! ### Going up and down between the Tate algebra and its reduction -/

section Units

variable [CompleteSpace K]

/-- **The units of the Tate algebra**: a series is a unit if and only if its constant coefficient
strictly dominates every other coefficient. Source: BGR 5.1.3/1; Bosch 1.2/4. -/
theorem isUnit_iff_norm_coeff_lt {f : Restricted K (1 : σ → ℝ)} :
    IsUnit f ↔ coeff 0 f.1 ≠ 0 ∧ ∀ t ≠ 0, ‖coeff t f.1‖ < ‖coeff 0 f.1‖ := by
  rw [isUnit_iff 1, constantCoeff_eq_coeff_zero, isUnit_iff_ne_zero]
  simp only [Finsupp.prod, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one]

/-- An element of the unit ball of the Tate algebra is a unit there if and only if its reduction
is a unit. Source: BGR 5.1.3/1. -/
theorem isUnit_iff_isUnit_reduction (f : unitClosedBall (Restricted K (1 : σ → ℝ))) :
    IsUnit f ↔ IsUnit (reduction f) := by
  rw [NormedRing.isUnit_iff_isUnit_mk f, ← reductionEquiv_mk]
  exact (isUnit_map_iff reductionEquiv _).symm

/-- A series of Gauss norm one is a unit of the Tate algebra if and only if its reduction is a
unit. Source: BGR 5.1.3/1 ("`f` is a unit if and only if `f̃` is a unit in `T̃ₙ`"). -/
theorem isUnit_coe_iff_isUnit_reduction {f : unitClosedBall (Restricted K (1 : σ → ℝ))}
    (hf : ‖(f : Restricted K (1 : σ → ℝ))‖ = 1) :
    IsUnit (f : Restricted K (1 : σ → ℝ)) ↔ IsUnit (reduction f) := by
  rw [← isUnit_iff_isUnit_reduction]
  refine ⟨fun h ↦ ?_, ?_⟩
  swap
  · rintro ⟨u, rfl⟩
    let v : (Restricted K (1 : σ → ℝ))ˣ :=
      { val := Subtype.val (u : unitClosedBall (Restricted K (1 : σ → ℝ)))
        inv := Subtype.val ((u⁻¹ : (unitClosedBall (Restricted K (1 : σ → ℝ)))ˣ) :
          unitClosedBall (Restricted K (1 : σ → ℝ)))
        val_inv := by rw [← Subring.coe_mul, u.mul_inv, Subring.coe_one]
        inv_val := by rw [← Subring.coe_mul, u.inv_mul, Subring.coe_one] }
    exact ⟨v, rfl⟩
  obtain ⟨u, hu⟩ := h
  have hnorm : ‖(↑u⁻¹ : Restricted K (1 : σ → ℝ))‖ = 1 := by
    have h1 : ‖(u : Restricted K (1 : σ → ℝ))‖ * ‖(↑u⁻¹ : Restricted K (1 : σ → ℝ))‖ = 1 := by
      rw [← norm_mul, Units.mul_inv, norm_one]
    rwa [hu, hf, one_mul] at h1
  refine ⟨⟨f, ⟨(↑u⁻¹ : Restricted K (1 : σ → ℝ)), mem_unitClosedBall.2 hnorm.le⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (by simp [← hu])
  · exact Subtype.ext (by simp [← hu])

/-- For a series of Gauss norm one there is a constant of norm one whose sum with it is not a
unit. Source: BGR 5.1.3/2. -/
theorem exists_norm_eq_one_not_isUnit_C_add {f : Restricted K (1 : σ → ℝ)} (hf : ‖f‖ = 1) :
    ∃ a : K, ‖a‖ = 1 ∧ ¬ IsUnit (C (1 : σ → ℝ) a + f) := by
  classical
  have hcoeffC (a : K) (t : σ →₀ ℕ) :
      coeff t (C (1 : σ → ℝ) a + f).1 = (if t = 0 then a else 0) + coeff t f.1 := by
    rw [val_add, val_C, map_add, MvPowerSeries.coeff_C]
  have h00 : ‖coeff 0 f.1‖ ≤ 1 := hf ▸ norm_coeff_le f 0
  rcases h00.lt_or_eq with hlt | heq
  · obtain ⟨t, ht⟩ := exists_norm_coeff_eq f
    rw [hf] at ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hlt.ne ht
    refine ⟨1, norm_one, fun hu ↦ ?_⟩
    have h := (isUnit_iff_norm_coeff_lt.1 hu).2 t ht0
    rw [hcoeffC, hcoeffC, if_neg ht0, zero_add, if_pos rfl, ht] at h
    have h1 : ‖(1 : K) + coeff 0 f.1‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'),
        norm_one, max_eq_left hlt.le]
    linarith
  · refine ⟨-coeff 0 f.1, by rw [norm_neg, heq], fun hu ↦ ?_⟩
    have h := (isUnit_iff_norm_coeff_lt.1 hu).1
    rw [hcoeffC, if_pos rfl, neg_add_cancel] at h
    exact h rfl

/-- **The Jacobson radical of the Tate algebra is zero**: the intersection of all maximal ideals
is `0`. Source: BGR 5.1.3/3. -/
theorem jacobson_bot : Ideal.jacobson (⊥ : Ideal (Restricted K (1 : σ → ℝ))) = ⊥ := by
  refine eq_bot_iff.2 fun f hf ↦ ?_
  rw [Ideal.mem_bot]
  by_contra hf0
  obtain ⟨a, -, haf⟩ := exists_norm_smul_eq_one hf0
  obtain ⟨c, hc, hnu⟩ := exists_norm_eq_one_not_isUnit_C_add haf
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hmem : C (1 : σ → ℝ) a * f ∈ Ideal.jacobson ⊥ := Ideal.mul_mem_left _ _ hf
  have hu := Ideal.mem_jacobson_bot.1 hmem (C (1 : σ → ℝ) c⁻¹)
  have hcc : C (1 : σ → ℝ) c⁻¹ * C (1 : σ → ℝ) c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have heq : C (1 : σ → ℝ) a * f * C (1 : σ → ℝ) c⁻¹ + 1 =
      C (1 : σ → ℝ) c⁻¹ * (C (1 : σ → ℝ) c + a • f) := by
    rw [Algebra.smul_def, algebraMap_apply]
    linear_combination -hcc
  rw [heq] at hu
  exact hnu (IsUnit.mul_iff.1 hu).2

end Units

end MvPowerSeries.Restricted
