/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.ProperSpace
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.MaxModulus
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Rueckert
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Stable
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.StrictlyClosed

/-!
# Examples for the Tate algebra

The acceptance examples of Layer 0 of the rigid analytic geometry roadmap: the Tate algebra in no
variables is the ground field; the Gauss norm and the reduction of explicit series over `ℚ_[p]`; a
series that is not distinguished and becomes distinguished after a shear; an explicit Weierstrass
polynomial; the maximal ideal of a rational point; and a maximal ideal of `T₁` with a quadratic
residue field.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 0, Examples. Tau Ceti home:
`TauCetiTest/RingTheory/TateAlgebra.lean`.
-/

open MvPowerSeries MvPowerSeries.Restricted Affinoid Affinoid.TateAlgebra Subring NormedRing
  IsLocalRing

namespace Affinoid.TateAlgebra.Examples

section General

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- `T₀ = K`. Source: BGR 5.1.1 ("we write `T₀(k) := k`"). -/
noncomputable example : TateAlgebra K 0 ≃+* K :=
  Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)

/-- The variables of the Tate algebra have Gauss norm one. -/
theorem norm_X (n : ℕ) (i : Fin n) : ‖Restricted.X K (1 : Fin n → ℝ) i‖ = 1 := by
  rw [Restricted.norm_X, norm_one, one_mul]
  rfl

/-- The variable `X 1` of `T₂` is not `X 0`-distinguished of any order. -/
theorem not_isMulDistinguishedX0_X_one (s : ℕ) :
    ¬ IsMulDistinguishedX0 (Restricted.X K (1 : Fin 2 → ℝ) 1) s := by
  intro h
  have hX : Restricted.X K (1 : Fin 2 → ℝ) 1 =
      ofTail K 1 (Restricted.X K (1 : Fin 1 → ℝ) 0) := (ofTail_X 0).symm
  rw [hX, isMulDistinguishedX0_iff, ofTail_apply, coeffX0_ofPolynomial, Polynomial.coeff_C] at h
  obtain ⟨hu, -, -⟩ := h
  split_ifs at hu with hs
  · have h0 := hu.map (Restricted.constantCoeff (R := K) (1 : Fin 1 → ℝ))
    have hc : Restricted.constantCoeff (R := K) (1 : Fin 1 → ℝ)
        (Restricted.X K (1 : Fin 1 → ℝ) 0) = 0 := MvPowerSeries.constantCoeff_X 0
    rw [hc] at h0
    exact not_isUnit_zero h0
  · exact not_isUnit_zero hu

variable [CompleteSpace K]

/-- After the shear `X 1 ↦ X 1 + X 0` the variable `X 1` of `T₂` is `X 0`-distinguished of
order one. -/
theorem isMulDistinguishedX0_shear_X_one :
    IsMulDistinguishedX0 (shear K 1 (fun _ ↦ 1) (Restricted.X K (1 : Fin 2 → ℝ) 1)) 1 := by
  have h1 : shear K 1 (fun _ ↦ 1) (Restricted.X K (1 : Fin 2 → ℝ) 1) =
      ofPolynomial K 1 (Polynomial.X + Polynomial.C (Restricted.X K (1 : Fin 1 → ℝ) 0)) := by
    rw [map_add, ofPolynomial_X, ← ofTail_apply, ofTail_X]
    exact (shear_X_succ (fun _ ↦ 1) 0).trans (by rw [pow_one]; exact add_comm _ _)
  have hω : IsWeierstrassPolynomial K 1
      (Polynomial.X + Polynomial.C (Restricted.X K (1 : Fin 1 → ℝ) 0)) := by
    refine isWeierstrassPolynomial_iff.2 ⟨Polynomial.monic_X_add_C _, fun i ↦ ?_⟩
    rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
    rcases i with _ | _ | i <;> simp
  have h2 := hω.isMulDistinguishedX0
  rw [Polynomial.natDegree_X_add_C] at h2
  rw [h1]
  exact h2

/-- The kernel of the evaluation at a `K`-rational point of the unit ball is a maximal ideal. -/
theorem isMaximal_ker_aeval {n : ℕ} (x : Fin n → K) (hx : ∀ i, ‖x i‖ ≤ 1) :
    (RingHom.ker (aeval (K := K) (1 : Fin n → ℝ) x hx)).IsMaximal :=
  isMaximal_ker_of_isAlgebraic _

end General

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- The prime `p` has norm less than one in `ℚ_[p]`. -/
private lemma norm_p_lt_one : ‖(p : ℚ_[p])‖ < 1 := by
  rw [Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- The Gauss norm of `1 + p X` over `ℚ_[p]` is one. -/
theorem norm_one_add_p_mul_X :
    ‖(1 + Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 :
      TateAlgebra ℚ_[p] 1)‖ = 1 := by
  have hu : ‖(Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 :
      TateAlgebra ℚ_[p] 1)‖ < 1 := by
    rw [norm_mul, Restricted.norm_C, norm_X, mul_one]
    exact norm_p_lt_one p
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hu.ne'),
    norm_one, max_eq_left hu.le]

/-- The series `1 + p X` is a unit of `T₁` over `ℚ_[p]`. -/
theorem isUnit_one_add_p_mul_X :
    IsUnit (1 + Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 :
      TateAlgebra ℚ_[p] 1) := by
  have hu : ‖(Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 :
      TateAlgebra ℚ_[p] 1)‖ < 1 := by
    rw [norm_mul, Restricted.norm_C, norm_X, mul_one]
    exact norm_p_lt_one p
  rw [← sub_neg_eq_add]
  exact isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])

/-- The reduction of `p + X + p X²` over `ℚ_[p]` is `X`. -/
theorem reduction_p_add_X_add_p_mul_X_sq
    (h : ‖(Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) + Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 +
      Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 ^ 2 :
        TateAlgebra ℚ_[p] 1)‖ ≤ 1) :
    reduction ⟨Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) + Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 +
      Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 ^ 2,
        mem_unitClosedBall.2 h⟩ = MvPolynomial.X 0 := by
  have hC : Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) ∈ unitClosedBall (TateAlgebra ℚ_[p] 1) :=
    mem_unitClosedBall.2 (by rw [Restricted.norm_C]; exact (norm_p_lt_one p).le)
  have hX : Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 ∈ unitClosedBall (TateAlgebra ℚ_[p] 1) :=
    mem_unitClosedBall.2 (norm_X ℚ_[p] 1 0).le
  have heq : (⟨_, mem_unitClosedBall.2 h⟩ : unitClosedBall (TateAlgebra ℚ_[p] 1)) =
      ⟨_, hC⟩ + ⟨_, hX⟩ + ⟨_, hC⟩ * ⟨_, hX⟩ ^ 2 := Subtype.ext rfl
  have hC0 : reduction (⟨_, hC⟩ : unitClosedBall (TateAlgebra ℚ_[p] 1)) = 0 :=
    (reduction_eq_zero_iff _).2 (by
      change ‖Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p])‖ < 1
      rw [Restricted.norm_C]
      exact norm_p_lt_one p)
  rw [heq, map_add, map_add, map_mul, map_pow, hC0, reduction_X, zero_add, zero_mul, add_zero]

/-- The polynomial `X² - p X₁ X - p` over `T₁ = ℚ_[p]⟨X₁⟩` is a Weierstrass polynomial. -/
theorem isWeierstrassPolynomial_example :
    IsWeierstrassPolynomial ℚ_[p] 1
      (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) *
        Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0) * Polynomial.X -
          Polynomial.C (Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]))) := by
  have ha : ‖(Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * Restricted.X ℚ_[p] (1 : Fin 1 → ℝ) 0 :
      TateAlgebra ℚ_[p] 1)‖ ≤ 1 := by
    rw [norm_mul, Restricted.norm_C, norm_X, mul_one]
    exact (norm_p_lt_one p).le
  have hb : ‖(Restricted.C (1 : Fin 1 → ℝ) (p : ℚ_[p]) : TateAlgebra ℚ_[p] 1)‖ ≤ 1 := by
    rw [Restricted.norm_C]
    exact (norm_p_lt_one p).le
  have hpT : ‖(p : TateAlgebra ℚ_[p] 1)‖ ≤ 1 := by
    rw [← map_natCast (Restricted.C (1 : Fin 1 → ℝ)) p, Restricted.norm_C]
    exact (norm_p_lt_one p).le
  refine isWeierstrassPolynomial_iff.2 ⟨?_, fun i ↦ ?_⟩
  · rw [sub_sub]
    exact Polynomial.monic_X_pow_sub (Polynomial.degree_linear_le.trans_lt (by norm_num))
  · rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    rcases i with _ | _ | _ | i <;> simp [hpT]

/-- The ideal `(X² - p)` of `T₁` over `ℚ_[p]` is maximal, with residue field the quadratic
extension `ℚ_[p](√p)`. -/
theorem isMaximal_span_X_sq_sub_p :
    (Ideal.span {ofPolynomial ℚ_[p] 0
      (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) (p : ℚ_[p])))}).IsMaximal := by
  have hω : IsWeierstrassPolynomial ℚ_[p] 0
      (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) (p : ℚ_[p]))) := by
    have hpT : ‖(p : TateAlgebra ℚ_[p] 0)‖ ≤ 1 := by
      rw [← map_natCast (Restricted.C (1 : Fin 0 → ℝ)) p, Restricted.norm_C]
      exact (norm_p_lt_one p).le
    refine isWeierstrassPolynomial_iff.2 ⟨Polynomial.monic_X_pow_sub_C _ two_ne_zero, fun i ↦ ?_⟩
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rcases i with _ | _ | _ | i <;> simp [hpT]
  have hEω : Polynomial.mapEquiv (Restricted.isEmptyEquiv ℚ_[p] (1 : Fin 0 → ℝ))
      (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) (p : ℚ_[p]))) =
        Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p]) := by
    rw [Polynomial.mapEquiv_apply, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    rfl
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p])) := by
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [Polynomial.natDegree_X_pow_sub_C]) (by rw [Polynomial.natDegree_X_pow_sub_C]; omega)]
    refine Multiset.eq_zero_of_forall_notMem fun a ha ↦ ?_
    rw [Polynomial.mem_roots (Polynomial.monic_X_pow_sub_C _ two_ne_zero).ne_zero,
      Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at ha
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at ha
      exact hp0 ha.symm
    have h1 := congrArg norm ha
    rw [norm_pow, Padic.norm_eq_zpow_neg_valuation ha0, Padic.norm_p, ← zpow_natCast,
      ← zpow_mul, ← zpow_neg_one] at h1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have h2 := zpow_right_injective₀ (by positivity) hp1.ne' h1
    omega
  haveI := PrincipalIdealRing.isMaximal_of_irreducible hirr
  have hmax : (Ideal.span {Polynomial.X ^ 2 -
      Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) (p : ℚ_[p]))}).IsMaximal := by
    have h := Ideal.map_isMaximal_of_equiv
      (Polynomial.mapEquiv (Restricted.isEmptyEquiv ℚ_[p] (1 : Fin 0 → ℝ))).symm
      (p := Ideal.span {Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p])})
    rwa [Ideal.map_span, Set.image_singleton, ← hEω, RingEquiv.symm_apply_apply] at h
  have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hfield' := MulEquiv.isField hfield
    (RingEquiv.ofBijective _ hω.bijective_quotientMap).symm.toMulEquiv
  have hI : (Ideal.span {Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ)
      (p : ℚ_[p]))}).map (ofPolynomial ℚ_[p] 0) = Ideal.span {ofPolynomial ℚ_[p] 0
        (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) (p : ℚ_[p])))} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hI] at hfield'
  exact Ideal.Quotient.maximal_of_isField _ hfield'

end Padic

end Affinoid.TateAlgebra.Examples
