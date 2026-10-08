/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Distinguished
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.EvalReduction

/-!
# Distinguished charts

For exponents `e : Fin n → ℕ` the *shear* `X 0 ↦ X 0`, `X (i + 1) ↦ X (i + 1) + X 0 ^ e i` is an
isometric `K`-algebra automorphism of the Tate algebra `T_{n+1}`, and every nonzero series becomes
`X 0`-distinguished after a suitable shear. On reductions the shear is the corresponding
automorphism of the polynomial ring over the residue field, and the statement comes down to the
classical fact that it makes the leading coefficient in `X 0` of a nonzero polynomial over a field
a unit, as soon as the exponents `e i = t ^ (i + 1)` are powers of a number `t` exceeding every
exponent of the polynomial.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.2.3 (BGR 5.1.3 (Example),
5.2.4/1–2; Bosch 1.2/7). Tau Ceti home: `TauCeti/RingTheory/TateAlgebra/Chart.lean`.

## Main definitions

* `MvPolynomial.shear R e` — the shear automorphism of a polynomial ring.
* `Affinoid.TateAlgebra.shear K n e` — the shear automorphism of the Tate algebra.

## Main results

* `MvPolynomial.isUnit_leadingCoeff_finSuccEquiv_shear` — the polynomial statement.
* `Affinoid.TateAlgebra.norm_shear` — the shear is an isometry (BGR 5.1.3, Example).
* `Affinoid.TateAlgebra.exists_isMulDistinguishedX0_shear` — BGR 5.2.4/2.
* `Affinoid.TateAlgebra.exists_shear_isMulDistinguishedX0` — BGR 5.2.4/1.
* `Affinoid.TateAlgebra.exists_shear_forall_isMulDistinguishedX0` — Bosch 1.2/7.
-/

open Subring NormedRing IsLocalRing MvPowerSeries MvPowerSeries.Restricted

/-! ### The shear of a polynomial ring -/

namespace MvPolynomial

section CommRing

variable (R : Type*) [CommRing R] {n : ℕ}

/-- The `R`-algebra endomorphism `X 0 ↦ X 0`, `X (i + 1) ↦ X (i + 1) + a * X 0 ^ e i` of the
polynomial ring in `n + 1` variables. -/
noncomputable def shearAlgHom (e : Fin n → ℕ) (a : R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  aeval (Fin.cases (X 0) fun i ↦ X i.succ + C a * X 0 ^ e i)

theorem shearAlgHom_comp_shearAlgHom (e : Fin n → ℕ) {a b : R} (hab : a + b = 0) :
    (shearAlgHom R e a).comp (shearAlgHom R e b) = AlgHom.id R _ := by
  refine algHom_ext fun j ↦ ?_
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp [shearAlgHom]
  · simp only [shearAlgHom, AlgHom.comp_apply, aeval_X, Fin.cases_succ, Fin.cases_zero, map_add,
      map_mul, map_pow, aeval_C, AlgHom.id_apply, algebraMap_eq]
    rw [add_assoc, ← add_mul, ← C_add, hab, C_0, zero_mul, add_zero]

/-- The shear `X 0 ↦ X 0`, `X (i + 1) ↦ X (i + 1) + X 0 ^ e i`, an `R`-algebra automorphism of
the polynomial ring in `n + 1` variables. Source: BGR 5.1.3 (Example), on reductions. -/
noncomputable def shear (e : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom (shearAlgHom R e 1) (shearAlgHom R e (-1))
    (shearAlgHom_comp_shearAlgHom R e (add_neg_cancel 1))
    (shearAlgHom_comp_shearAlgHom R e (neg_add_cancel 1))

variable {R}

@[simp]
theorem shear_X_zero (e : Fin n → ℕ) : shear R e (X 0) = X 0 := by
  change shearAlgHom R e 1 (X 0) = X 0
  simp [shearAlgHom]

@[simp]
theorem shear_X_succ (e : Fin n → ℕ) (i : Fin n) :
    shear R e (X i.succ) = X i.succ + X 0 ^ e i := by
  change shearAlgHom R e 1 (X i.succ) = _
  simp [shearAlgHom]

end CommRing

section Field

variable {k : Type*} [Field k] {n : ℕ}

/-- Base-`t` expansions are unique, for functions. -/
private lemma eq_of_sum_pow_mul_eq {t : ℕ} :
    ∀ {m : ℕ} {v w : Fin (m + 1) → ℕ}, (∀ i, v i < t) → (∀ i, w i < t) →
      ∑ i : Fin (m + 1), t ^ i.val * v i = ∑ i : Fin (m + 1), t ^ i.val * w i → v = w
  | 0, v, w, _, _, h => by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simpa using h
  | m + 1, v, w, hv, hw, h => by
    have ht : 0 < t := (Nat.zero_le _).trans_lt (hv 0)
    have hsum (u : Fin (m + 1 + 1) → ℕ) : ∑ i : Fin (m + 1 + 1), t ^ i.val * u i =
        u 0 + t * ∑ i : Fin (m + 1), t ^ i.val * u i.succ := by
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hsum v, hsum w] at h
    have h0 : v 0 = w 0 := by
      have h' := congrArg (· % t) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hv 0), Nat.mod_eq_of_lt (hw 0)] at h'
      exact h'
    rw [h0, Nat.add_left_cancel_iff] at h
    have htail := eq_of_sum_pow_mul_eq (fun i ↦ hv i.succ) (fun i ↦ hw i.succ)
      (Nat.eq_of_mul_eq_mul_left ht h)
    funext i
    exact Fin.cases h0 (fun j ↦ congrFun htail j) i

/-- Distinct exponent vectors with entries below `t` have distinct weighted degrees
`Σ t ^ i * v i`: the base-`t` expansion is unique. -/
theorem sum_pow_mul_ne_of_lt {t : ℕ} {v w : Fin (n + 1) →₀ ℕ} (hv : ∀ i, v i < t)
    (hw : ∀ i, w i < t) (hvw : v ≠ w) :
    ∑ i : Fin (n + 1), t ^ i.val * v i ≠ ∑ i : Fin (n + 1), t ^ i.val * w i := fun h ↦
  hvw (DFunLike.coe_injective (eq_of_sum_pow_mul_eq hv hw h))

/-- The shear of a monomial, as a polynomial in `X 0`. -/
private lemma finSuccEquiv_shear_monomial (e : Fin n → ℕ) (v : Fin (n + 1) →₀ ℕ) (a : k) :
    finSuccEquiv k n (shear k e (monomial v a)) =
      Polynomial.C (C a) * Polynomial.X ^ v 0 *
        ∏ i : Fin n, (Polynomial.C (X i) + Polynomial.X ^ e i) ^ v i.succ := by
  have hC : shear k e (C a) = C a := (shear k e).commutes a
  have hC' : finSuccEquiv k n (C a) = Polynomial.C (C a) := by simp [finSuccEquiv_apply]
  rw [monomial_eq, Finsupp.prod_pow, Fin.prod_univ_succ, map_mul, map_mul, hC, map_mul, hC',
    mul_assoc]
  simp only [map_mul, map_prod, map_pow, shear_X_zero, shear_X_succ, map_add, finSuccEquiv_X_zero,
    finSuccEquiv_X_succ]

/-- The factors `C (X i) + X ^ m` of the shear of a monomial are nonzero. -/
private lemma C_X_add_X_pow_ne_zero (i : Fin n) (m : ℕ) :
    (Polynomial.C (X i) + Polynomial.X ^ m : Polynomial (MvPolynomial (Fin n) k)) ≠ 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [pow_zero, ← Polynomial.C_1, ← Polynomial.C_add, Polynomial.C_ne_zero]
    intro h
    have h' := congrArg (MvPolynomial.coeff 0) h
    simp at h'
  · rw [add_comm]
    exact Polynomial.X_pow_add_C_ne_zero hm _

/-- The degree in `X 0` of the shear of a monomial. -/
theorem degreeOf_zero_shear_monomial (e : Fin n → ℕ) (v : Fin (n + 1) →₀ ℕ) {a : k}
    (ha : a ≠ 0) :
    ((shear k e) (monomial v a)).degreeOf 0 = v 0 + ∑ i : Fin n, e i * v i.succ := by
  have h₁ : (Polynomial.C (C a) * Polynomial.X ^ v 0 : Polynomial (MvPolynomial (Fin n) k)) ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.2 (C_ne_zero.2 ha)) (pow_ne_zero _ Polynomial.X_ne_zero)
  have h₂ : ∏ i : Fin n, (Polynomial.C (X i) + Polynomial.X ^ e i : Polynomial (MvPolynomial
      (Fin n) k)) ^ v i.succ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (C_X_add_X_pow_ne_zero i (e i))
  rw [← natDegree_finSuccEquiv, finSuccEquiv_shear_monomial, Polynomial.natDegree_mul h₁ h₂,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.2 (C_ne_zero.2 ha))
      (pow_ne_zero _ Polynomial.X_ne_zero), Polynomial.natDegree_C, Polynomial.natDegree_X_pow,
    Polynomial.natDegree_prod _ _ fun i _ ↦ pow_ne_zero _ (C_X_add_X_pow_ne_zero i (e i)),
    zero_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.natDegree_pow, add_comm (Polynomial.C (X i)), Polynomial.natDegree_X_pow_add_C,
    mul_comm]

/-- For positive exponents, the leading coefficient in `X 0` of the shear of a monomial is its
coefficient. -/
theorem leadingCoeff_finSuccEquiv_shear_monomial {e : Fin n → ℕ} (he : ∀ i, 0 < e i)
    (v : Fin (n + 1) →₀ ℕ) (a : k) :
    (finSuccEquiv k n ((shear k e) (monomial v a))).leadingCoeff = C a := by
  rw [finSuccEquiv_shear_monomial, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X_pow, Polynomial.leadingCoeff_prod, mul_one,
    Finset.prod_eq_one fun i _ ↦ by
      rw [Polynomial.leadingCoeff_pow, add_comm (Polynomial.C (X i)),
        Polynomial.leadingCoeff_X_pow_add_C (he i),
        one_pow], mul_one]

/-- After the shear with exponents `t ^ (i + 1)`, for `t` exceeding every exponent of a nonzero
polynomial `f` over a field, the leading coefficient of `f` in `X 0` is a unit.
Source: BGR 5.2.4/1 (the computation of `σ̃(f̃)`); Bosch 1.2/7. -/
theorem isUnit_leadingCoeff_finSuccEquiv_shear {f : MvPolynomial (Fin (n + 1)) k} (hf : f ≠ 0)
    {t : ℕ} (ht : ∀ v ∈ f.support, ∀ i, v i < t) :
    IsUnit (finSuccEquiv k n (shear k (fun i : Fin n ↦ t ^ (i.val + 1)) f)).leadingCoeff := by
  obtain ⟨v₀, hv₀⟩ := support_nonempty.2 hf
  have htpos : 0 < t := (Nat.zero_le _).trans_lt (ht v₀ hv₀ 0)
  have he (i : Fin n) : 0 < t ^ (i.val + 1) := pow_pos htpos _
  let D : (Fin (n + 1) →₀ ℕ) → ℕ := fun v ↦ ∑ j : Fin (n + 1), t ^ j.val * v j
  have hD (v : Fin (n + 1) →₀ ℕ) : D v = v 0 + ∑ i : Fin n, t ^ (i.val + 1) * v i.succ := by
    simp only [D, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
  let P : (Fin (n + 1) →₀ ℕ) → Polynomial (MvPolynomial (Fin n) k) := fun v ↦
    finSuccEquiv k n (shear k (fun i : Fin n ↦ t ^ (i.val + 1)) (monomial v (f.coeff v)))
  have hP : finSuccEquiv k n (shear k (fun i : Fin n ↦ t ^ (i.val + 1)) f) =
      ∑ v ∈ f.support, P v := by
    conv_lhs => rw [f.as_sum]
    simp only [map_sum, P]
  have hPdeg (v : Fin (n + 1) →₀ ℕ) (hv : v ∈ f.support) : (P v).natDegree = D v := by
    rw [natDegree_finSuccEquiv, degreeOf_zero_shear_monomial _ v (mem_support_iff.1 hv), hD]
  have hPlc (v : Fin (n + 1) →₀ ℕ) : (P v).leadingCoeff = C (f.coeff v) :=
    leadingCoeff_finSuccEquiv_shear_monomial he v _
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image f.support D ⟨v₀, hv₀⟩
  have hPm : P m ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.1 (by rw [hPlc]; exact C_ne_zero.2 (mem_support_iff.1 hm))
  have hdeg : (∑ v ∈ f.support.erase m, P v).degree < (P m).degree := by
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    rw [Polynomial.degree_eq_natDegree hPm, hPdeg m hm]
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun v hv ↦ ?_
    obtain ⟨hvm, hv⟩ := Finset.mem_erase.1 hv
    have hlt : D v < D m :=
      lt_of_le_of_ne (hmax v hv) (sum_pow_mul_ne_of_lt (ht v hv) (ht m hm) hvm)
    refine Polynomial.degree_le_natDegree.trans_lt ?_
    rw [hPdeg v hv]
    exact_mod_cast hlt
  rw [hP, ← Finset.add_sum_erase _ _ hm, Polynomial.leadingCoeff_add_of_degree_lt' hdeg, hPlc]
  exact (isUnit_iff_ne_zero.2 (mem_support_iff.1 hm)).map C

end Field

end MvPolynomial

/-! ### The shear of the Tate algebra -/

namespace Affinoid.TateAlgebra

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (n : ℕ)

/-- The tuple `X 0`, `X (i + 1) + a * X 0 ^ e i` of the Tate algebra. -/
noncomputable def shearTuple (e : Fin n → ℕ) (a : K) : Fin (n + 1) → TateAlgebra K (n + 1) :=
  Fin.cases (Restricted.X K (1 : Fin (n + 1) → ℝ) 0) fun i ↦
    Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ +
      Restricted.C (1 : Fin (n + 1) → ℝ) a * Restricted.X K (1 : Fin (n + 1) → ℝ) 0 ^ e i

omit [CompleteSpace K] in
@[simp]
theorem shearTuple_zero (e : Fin n → ℕ) (a : K) :
    shearTuple K n e a 0 = Restricted.X K (1 : Fin (n + 1) → ℝ) 0 :=
  rfl

omit [CompleteSpace K] in
@[simp]
theorem shearTuple_succ (e : Fin n → ℕ) (a : K) (i : Fin n) :
    shearTuple K n e a i.succ = Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ +
      Restricted.C (1 : Fin (n + 1) → ℝ) a * Restricted.X K (1 : Fin (n + 1) → ℝ) 0 ^ e i :=
  rfl

omit [CompleteSpace K] in
theorem norm_shearTuple_le_one (e : Fin n → ℕ) {a : K} (ha : ‖a‖ ≤ 1) (i : Fin (n + 1)) :
    ‖shearTuple K n e a i‖ ≤ 1 := by
  have hX (j : Fin (n + 1)) : ‖Restricted.X K (1 : Fin (n + 1) → ℝ) j‖ ≤ 1 := by
    simp [Restricted.norm_X]
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · exact hX 0
  · rw [shearTuple_succ]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX _) ?_)
    refine (_root_.norm_mul_le _ _).trans ?_
    rw [Restricted.norm_C, norm_pow]
    exact mul_le_one₀ ha (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) (hX 0))

/-- The continuous `K`-algebra endomorphism `X 0 ↦ X 0`, `X (i + 1) ↦ X (i + 1) + a * X 0 ^ e i`
of the Tate algebra, for `‖a‖ ≤ 1`. -/
noncomputable def shearAlgHom (e : Fin n → ℕ) (a : K) (ha : ‖a‖ ≤ 1) :
    TateAlgebra K (n + 1) →ₐ[K] TateAlgebra K (n + 1) :=
  aeval (1 : Fin (n + 1) → ℝ) (shearTuple K n e a) (norm_shearTuple_le_one K n e ha)

theorem shearAlgHom_comp_shearAlgHom (e : Fin n → ℕ) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hab : a + b = 0) :
    (shearAlgHom K n e a ha).comp (shearAlgHom K n e b hb) = AlgHom.id K _ := by
  have hc (c : K) (hc : ‖c‖ ≤ 1) : Continuous (shearAlgHom K n e c hc) :=
    Restricted.continuous_aeval (norm_shearTuple_le_one K n e hc)
  have hcomp : Continuous ((shearAlgHom K n e a ha).comp (shearAlgHom K n e b hb)) := by
    rw [AlgHom.coe_comp]
    exact (hc a ha).comp (hc b hb)
  have hid : Continuous (AlgHom.id K (TateAlgebra K (n + 1))) := by
    rw [AlgHom.coe_id]
    exact continuous_id
  refine algHom_ext_of_continuous hcomp hid fun j ↦ ?_
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp [shearAlgHom]
  · have hCb : aeval (1 : Fin (n + 1) → ℝ) (shearTuple K n e a) (norm_shearTuple_le_one K n e ha)
        (Restricted.C (1 : Fin (n + 1) → ℝ) b) = Restricted.C (1 : Fin (n + 1) → ℝ) b := by
      rw [← Restricted.algebraMap_apply, AlgHom.commutes]
    simp only [AlgHom.comp_apply, AlgHom.id_apply, shearAlgHom, aeval_X, shearTuple_succ,
      shearTuple_zero, map_add, map_mul, map_pow, hCb]
    rw [add_assoc, ← add_mul, ← map_add (Restricted.C (1 : Fin (n + 1) → ℝ)) a b, hab, map_zero,
      zero_mul, add_zero]

/-- The shear `X 0 ↦ X 0`, `X (i + 1) ↦ X (i + 1) + X 0 ^ e i`, a `K`-algebra automorphism of the
Tate algebra. Source: BGR 5.1.3 (Example); Bosch 1.2/7. -/
noncomputable def shear (e : Fin n → ℕ) : TateAlgebra K (n + 1) ≃ₐ[K] TateAlgebra K (n + 1) :=
  AlgEquiv.ofAlgHom (shearAlgHom K n e 1 norm_one.le)
    (shearAlgHom K n e (-1) (by rw [norm_neg, norm_one]))
    (shearAlgHom_comp_shearAlgHom K n e _ _ (add_neg_cancel 1))
    (shearAlgHom_comp_shearAlgHom K n e _ _ (neg_add_cancel 1))

variable {K n}

@[simp]
theorem shear_X_zero (e : Fin n → ℕ) :
    shear K n e (Restricted.X K (1 : Fin (n + 1) → ℝ) 0) =
      Restricted.X K (1 : Fin (n + 1) → ℝ) 0 := by
  change shearAlgHom K n e 1 norm_one.le (Restricted.X K (1 : Fin (n + 1) → ℝ) 0) = _
  simp [shearAlgHom, shearTuple]

@[simp]
theorem shear_X_succ (e : Fin n → ℕ) (i : Fin n) :
    shear K n e (Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ) =
      Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ +
        Restricted.X K (1 : Fin (n + 1) → ℝ) 0 ^ e i := by
  change shearAlgHom K n e 1 norm_one.le (Restricted.X K (1 : Fin (n + 1) → ℝ) i.succ) = _
  simp [shearAlgHom, shearTuple]

/-- The shear is an isometry for the Gauss norm. Source: BGR 5.1.3 (Example: "`φ` is an isometric
automorphism of `Tₙ`"); Bosch 1.2/7 ("`|σ(f)| = |f|` for all `f ∈ Tₙ`"). -/
theorem norm_shear (e : Fin n → ℕ) (f : TateAlgebra K (n + 1)) : ‖shear K n e f‖ = ‖f‖ := by
  have h₁ (g : TateAlgebra K (n + 1)) : ‖shear K n e g‖ ≤ ‖g‖ :=
    norm_aeval_le (norm_shearTuple_le_one K n e norm_one.le) g
  have h₂ (g : TateAlgebra K (n + 1)) : ‖(shear K n e).symm g‖ ≤ ‖g‖ :=
    norm_aeval_le (norm_shearTuple_le_one K n e (by rw [norm_neg, norm_one])) g
  refine le_antisymm (h₁ f) ?_
  calc ‖f‖ = ‖(shear K n e).symm (shear K n e f)‖ := by rw [AlgEquiv.symm_apply_apply]
    _ ≤ ‖shear K n e f‖ := h₂ _

/-- The reduction of the shear is the shear of the reduction. Source: BGR 5.2.4/1
("`(σ(f))~ = σ̃(f̃)`"). -/
theorem reduction_shear (e : Fin n → ℕ) (f : unitClosedBall (TateAlgebra K (n + 1))) :
    reduction ⟨shear K n e (f : TateAlgebra K (n + 1)),
        mem_unitClosedBall.2 ((norm_shear e _).trans_le (Subring.norm_le_one f))⟩ =
      MvPolynomial.shear _ e (reduction f) := by
  have hX (j : Fin (n + 1)) :
      Restricted.X K (1 : Fin (n + 1) → ℝ) j ∈ unitClosedBall (TateAlgebra K (n + 1)) :=
    mem_unitClosedBall.2 (by simp [Restricted.norm_X])
  have h := reduction_aeval (norm_shearTuple_le_one K n e (norm_one.le : ‖(1 : K)‖ ≤ 1)) f
  refine h.trans ?_
  change _ = MvPolynomial.aeval _ (reduction f)
  congr 2
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact reduction_X _ (hX 0)
  · have heq : (⟨shearTuple K n e 1 i.succ, mem_unitClosedBall.2
        (norm_shearTuple_le_one K n e norm_one.le i.succ)⟩ :
          unitClosedBall (TateAlgebra K (n + 1))) = ⟨_, hX i.succ⟩ + ⟨_, hX 0⟩ ^ e i :=
      Subtype.ext (by simp [shearTuple])
    simp only [Fin.cases_succ]
    rw [heq, map_add, map_pow, reduction_X, reduction_X, map_one, one_mul]

/-- **Distinguished charts, explicit form**: for `t` exceeding every exponent occurring at a
coefficient of `f` of maximal norm, the shear with exponents `t ^ (i + 1)` makes `f`
`X 0`-distinguished. Source: BGR 5.2.4/2; Bosch 1.2/7. -/
theorem exists_isMulDistinguishedX0_shear {f : TateAlgebra K (n + 1)} (hf : f ≠ 0) {t : ℕ}
    (ht : ∀ ν : Fin (n + 1) →₀ ℕ, ‖MvPowerSeries.coeff ν f.1‖ = ‖f‖ → ∀ i, ν i < t) :
    ∃ s, IsMulDistinguishedX0 (shear K n (fun i : Fin n ↦ t ^ (i.val + 1)) f) s := by
  obtain ⟨a, ha, hnorm⟩ := exists_norm_smul_eq_one hf
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha
  let g : unitClosedBall (TateAlgebra K (n + 1)) := ⟨a • f, mem_unitClosedBall.2 hnorm.le⟩
  have hq : reduction g ≠ 0 := fun h ↦ ((reduction_eq_zero_iff g).1 h).ne hnorm
  have hsupp : ∀ v ∈ (reduction g).support, ∀ i, v i < t := by
    intro v hv
    refine ht v ?_
    have hres := MvPolynomial.mem_support_iff.1 hv
    rw [coeff_reduction, Ne, residue_eq_zero_iff, maximalIdeal_unitClosedBall,
      mem_openUnitBallIdeal, coe_unitBallCoeff, not_lt] at hres
    have hle : ‖MvPowerSeries.coeff v (a • f).1‖ ≤ 1 := hnorm ▸ norm_coeff_le (a • f) v
    have hcoeff : ‖MvPowerSeries.coeff v (a • f).1‖ = ‖a‖ * ‖MvPowerSeries.coeff v f.1‖ := by
      simp only [val_smul, MvPowerSeries.coeff_smul, norm_mul]
    have h1 : ‖a‖ * ‖MvPowerSeries.coeff v f.1‖ = ‖a‖ * ‖f‖ := by
      rw [← hcoeff, ← norm_smul_eq, hnorm]
      exact le_antisymm hle hres
    exact mul_left_cancel₀ hapos.ne' h1
  have hunit := MvPolynomial.isUnit_leadingCoeff_finSuccEquiv_shear hq hsupp
  have hnorm' : ‖shear K n (fun i : Fin n ↦ t ^ (i.val + 1)) (a • f)‖ = 1 := by
    rw [norm_shear]
    exact hnorm
  have hred : reduction ⟨shear K n (fun i : Fin n ↦ t ^ (i.val + 1)) (a • f),
      mem_unitClosedBall.2 hnorm'.le⟩ =
        MvPolynomial.shear _ (fun i : Fin n ↦ t ^ (i.val + 1)) (reduction g) :=
    reduction_shear _ g
  have hd := (isMulDistinguishedX0_iff_reduction (g := ⟨_, mem_unitClosedBall.2 hnorm'.le⟩)
    hnorm').2 ⟨rfl, by rw [hred]; exact hunit⟩
  obtain ⟨s, hs⟩ : ∃ s,
      IsMulDistinguishedX0 (shear K n (fun i : Fin n ↦ t ^ (i.val + 1)) (a • f)) s :=
    ⟨_, hd⟩
  rw [map_smul] at hs
  exact ⟨s, (isMulDistinguishedX0_smul_iff ha).1 hs⟩

omit [CompleteSpace K] in
/-- A bound on the exponents of the coefficients of maximal norm of a nonzero series. -/
private lemma exists_bound_of_ne_zero {f : TateAlgebra K (n + 1)} (hf : f ≠ 0) :
    ∃ t : ℕ, ∀ ν : Fin (n + 1) →₀ ℕ, ‖MvPowerSeries.coeff ν f.1‖ = ‖f‖ → ∀ i, ν i < t := by
  have hfin := finite_setOf_le_norm_coeff f (norm_pos_iff.2 hf)
  refine ⟨(hfin.toFinset.sup fun ν ↦ Finset.univ.sup fun i ↦ ν i) + 1,
    fun ν hν i ↦ Nat.lt_succ_of_le ?_⟩
  have hmem : ν ∈ hfin.toFinset := hfin.mem_toFinset.2 hν.ge
  exact (Finset.le_sup (f := fun i ↦ ν i) (Finset.mem_univ i)).trans
    (Finset.le_sup (f := fun ν : Fin (n + 1) →₀ ℕ ↦ Finset.univ.sup fun i ↦ ν i) hmem)

/-- **Distinguished charts**: every nonzero series becomes `X 0`-distinguished after a shear.
Source: BGR 5.2.4/1. -/
theorem exists_shear_isMulDistinguishedX0 {f : TateAlgebra K (n + 1)} (hf : f ≠ 0) :
    ∃ (e : Fin n → ℕ) (s : ℕ), IsMulDistinguishedX0 (shear K n e f) s := by
  obtain ⟨t, ht⟩ := exists_bound_of_ne_zero hf
  exact ⟨_, exists_isMulDistinguishedX0_shear hf ht⟩

/-- Finitely many nonzero series become `X 0`-distinguished after one and the same shear.
Source: Bosch 1.2/7. -/
theorem exists_shear_forall_isMulDistinguishedX0 (F : Finset (TateAlgebra K (n + 1)))
    (hF : ∀ f ∈ F, f ≠ 0) :
    ∃ e : Fin n → ℕ, ∀ f ∈ F, ∃ s, IsMulDistinguishedX0 (shear K n e f) s := by
  choose! T hT using fun f (hf : f ∈ F) ↦ exists_bound_of_ne_zero (hF f hf)
  exact ⟨fun i : Fin n ↦ F.sup T ^ (i.val + 1), fun f hf ↦ exists_isMulDistinguishedX0_shear
    (hF f hf) fun ν hν i ↦ (hT f hf ν hν i).trans_le (Finset.le_sup hf)⟩

end Affinoid.TateAlgebra
