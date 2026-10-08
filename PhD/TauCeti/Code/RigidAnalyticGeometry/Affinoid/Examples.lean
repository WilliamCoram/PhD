/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.BaseChange
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Fractions
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Polydisc
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Tensor
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples

/-!
# Examples of affinoid algebras

The acceptance examples of Layer 1 of the rigid analytic geometry roadmap: `K⟨X⟩ ⧸ (X² − a)` for
`‖a‖ < 1` is two-dimensional over `K`; `K⟨X⟩ ⧸ (X − a)` for `‖a‖ ≤ 1` is `K`; `K⟨X⟩ ⧸ (aX − 1) = 0`
for `‖a‖ < 1`, in particular `ℚ_p⟨X⟩ ⧸ (pX − 1) = 0`; `A⟨f⟩ = A` for `f = X` in `A = K⟨X⟩`;
`K⟨X, Y⟩ ⧸ (XY − 1) = K⟨X, X⁻¹⟩`; Noether normalisation of `K⟨X, Y⟩ ⧸ (Y² − X³)` by `T₁`; the
two presentations `K⟨X⟩ ⧸ (X)` and `K` of the same affinoid algebra have equal residue norms; and
`ℚ_p⟨X⟩ ⊗ K' = K'⟨X⟩` for a finite extension `K'` of `ℚ_p`.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 1, "Examples".
-/

open MvPowerSeries MvPowerSeries.Restricted TensorProduct Affinoid.TateAlgebra

namespace Affinoid.Examples

section General

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- `K⟨X⟩ ⧸ (X² − a)` is affinoid. -/
theorem isAffinoidAlgebra_quotient_X_sq_sub (a : K) :
    IsAffinoidAlgebra K (TateAlgebra K 1 ⧸
      Ideal.span {X K (1 : Fin 1 → ℝ) 0 ^ 2 - C (1 : Fin 1 → ℝ) a}) :=
  IsAffinoidAlgebra.tateAlgebra_quotient 1 _

/-- `T₀ = K` as `K`-algebras. -/
private noncomputable def tateZeroAlgEquiv : TateAlgebra K 0 ≃ₐ[K] K :=
  AlgEquiv.ofRingEquiv (f := Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)) fun k ↦ by
    rw [algebraMap_apply, Restricted.isEmptyEquiv_apply, val_C, MvPowerSeries.constantCoeff_C]
    rfl

omit [CompleteSpace K] in
/-- Every element of `T₀` is a constant. -/
private theorem eq_C_isEmptyEquiv (r : TateAlgebra K 0) :
    r = Restricted.C (1 : Fin 0 → ℝ) (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ) r) :=
  (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)).injective (by
    simp only [Restricted.isEmptyEquiv_apply, val_C, MvPowerSeries.constantCoeff_C])

/-- `K⟨X⟩ ⧸ (X² − a)` for `‖a‖ < 1` is a two-dimensional `K`-vector space with basis `1, X̄`: the
polynomial `X² − a` is a Weierstrass polynomial, so every series has a unique remainder of degree
less than two. Source: Layer 0, `IsWeierstrassPolynomial.existsUnique_remainder`. -/
theorem finrank_quotient_X_sq_sub {a : K} (ha : ‖a‖ < 1) :
    Module.finrank K (TateAlgebra K 1 ⧸
      Ideal.span {X K (1 : Fin 1 → ℝ) 0 ^ 2 - C (1 : Fin 1 → ℝ) a}) = 2 := by
  have hω : IsWeierstrassPolynomial K 0
      (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) a)) := by
    refine isWeierstrassPolynomial_iff.2 ⟨Polynomial.monic_X_pow_sub_C _ two_ne_zero, fun i ↦ ?_⟩
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rcases i with _ | _ | _ | i <;> simp [Restricted.norm_C, ha.le]
  have hωeq : ofPolynomial K 0
      (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) a)) =
        X K (1 : Fin 1 → ℝ) 0 ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a := by
    rw [map_sub, map_pow, ofPolynomial_X, ← ofTail_apply, ofTail_C]
  have hI : (Ideal.span {Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) a)}).map
      (ofPolynomial K 0) =
        Ideal.span {X K (1 : Fin 1 → ℝ) 0 ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a} := by
    rw [Ideal.map_span, Set.image_singleton, hωeq]
  let e : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) a)) ≃+*
      (TateAlgebra K 1 ⧸ Ideal.span {X K (1 : Fin 1 → ℝ) 0 ^ 2 - Restricted.C (1 : Fin 1 → ℝ) a}) :=
    (RingEquiv.ofBijective _ hω.bijective_quotientMap).trans (Ideal.quotEquivOfEq hI)
  have he : ∀ k : K, e (algebraMap K _ k) = algebraMap K _ k := fun k ↦ by
    have h : ofPolynomial K 0 (Polynomial.C (algebraMap K (TateAlgebra K 0) k)) =
        algebraMap K (TateAlgebra K 1) k := by
      rw [← ofTail_apply, algebraMap_apply, algebraMap_apply, ofTail_C]
    exact congrArg (Ideal.Quotient.mk _) h
  have h1 : Module.finrank K (TateAlgebra K 0) = 1 :=
    tateZeroAlgEquiv.toLinearEquiv.finrank_eq.trans (Module.finrank_self K)
  have h2 : Module.finrank (TateAlgebra K 0)
      (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) a))) = 2 := by
    rw [(AdjoinRoot.powerBasis' hω.monic).finrank, AdjoinRoot.powerBasis'_dim,
      Polynomial.natDegree_X_pow_sub_C]
  haveI : Module.Free (TateAlgebra K 0)
      (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) a))) :=
    hω.monic.free_adjoinRoot
  haveI : Module.Free K (TateAlgebra K 0) :=
    Module.Free.of_equiv tateZeroAlgEquiv.symm.toLinearEquiv
  rw [← (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv.finrank_eq,
    ← Module.finrank_mul_finrank K (TateAlgebra K 0), h1, h2, one_mul]

/-- The kernel of evaluation at a point `a` of the closed unit disc is `(X − a)`: Weierstrass
division by the Weierstrass polynomial `X − a`. -/
theorem ker_aeval_eq_span {a : K} (ha : ‖a‖ ≤ 1) :
    RingHom.ker (aeval (1 : Fin 1 → ℝ) (fun _ ↦ a) fun _ ↦ by simpa using ha) =
      Ideal.span {X K (1 : Fin 1 → ℝ) 0 - C (1 : Fin 1 → ℝ) a} := by
  set ev := aeval (K := K) (B := K) (1 : Fin 1 → ℝ) (fun _ ↦ a) (fun _ ↦ by simpa using ha)
  have hevC : ∀ k, ev (Restricted.C (1 : Fin 1 → ℝ) k) = k := fun k ↦
    (congrArg ev (algebraMap_apply _ k).symm).trans (ev.commutes k)
  have hevT : ∀ r₀ : TateAlgebra K 0,
      ev (ofTail K 0 r₀) = Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ) r₀ := fun r₀ ↦ by
    conv_lhs => rw [eq_C_isEmptyEquiv r₀]
    exact (congrArg ev (ofTail_C _)).trans (hevC _)
  have hmem : X K (1 : Fin 1 → ℝ) 0 - Restricted.C (1 : Fin 1 → ℝ) a ∈ RingHom.ker ev := by
    rw [RingHom.mem_ker, map_sub, aeval_X, hevC, sub_self]
  have hspan : Ideal.span {X K (1 : Fin 1 → ℝ) 0 - Restricted.C (1 : Fin 1 → ℝ) a} ≤
      RingHom.ker ev := Ideal.span_le.2 (Set.singleton_subset_iff.2 hmem)
  refine le_antisymm (fun f hf ↦ ?_) hspan
  have hω : IsWeierstrassPolynomial K 0
      (Polynomial.X - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) a)) := by
    refine isWeierstrassPolynomial_iff.2 ⟨Polynomial.monic_X_sub_C _, fun i ↦ ?_⟩
    rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    rcases i with _ | _ | i <;> simp [Restricted.norm_C, ha]
  have hωeq : ofPolynomial K 0 (Polynomial.X - Polynomial.C (Restricted.C (1 : Fin 0 → ℝ) a)) =
      X K (1 : Fin 1 → ℝ) 0 - Restricted.C (1 : Fin 1 → ℝ) a := by
    rw [map_sub, ofPolynomial_X, ← ofTail_apply, ofTail_C]
  obtain ⟨r, ⟨hr, hrmem⟩, -⟩ := hω.existsUnique_remainder f
  rw [Polynomial.degree_X_sub_C, Nat.WithBot.lt_one_iff_le_zero] at hr
  rw [Polynomial.eq_C_of_degree_le_zero hr, ← ofTail_apply, hωeq] at hrmem
  have h0 := RingHom.mem_ker.1 (hspan hrmem)
  rw [map_sub, RingHom.mem_ker.1 hf, zero_sub, neg_eq_zero, hevT] at h0
  have hr0 : ofTail K 0 (r.coeff 0) = 0 := by
    rw [eq_C_isEmptyEquiv (r.coeff 0), h0, map_zero, map_zero]
  rw [hr0, sub_zero] at hrmem
  exact hrmem

/-- `K⟨X⟩ ⧸ (X − a) ≅ K` for `‖a‖ ≤ 1`, by evaluation at `a`. -/
theorem nonempty_algEquiv_quotient_X_sub {a : K} (ha : ‖a‖ ≤ 1) :
    Nonempty ((TateAlgebra K 1 ⧸ Ideal.span {X K (1 : Fin 1 → ℝ) 0 - C (1 : Fin 1 → ℝ) a}) ≃ₐ[K]
      K) := by
  have hsurj : Function.Surjective
      (aeval (K := K) (B := K) (1 : Fin 1 → ℝ) (fun _ ↦ a) (fun _ ↦ by simpa using ha)) :=
    fun k ↦ ⟨Restricted.C (1 : Fin 1 → ℝ) k, (congrArg _ (algebraMap_apply _ k).symm).trans
      (AlgHom.commutes _ k)⟩
  exact ⟨(Ideal.quotientEquivAlgOfEq K (ker_aeval_eq_span ha)).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)⟩

/-- `aX − 1` is a unit of `K⟨X⟩` for `‖a‖ < 1`, so `K⟨X⟩ ⧸ (aX − 1) = 0`. -/
theorem isUnit_C_mul_X_sub_one {a : K} (ha : ‖a‖ < 1) :
    IsUnit (C (1 : Fin 1 → ℝ) a * X K (1 : Fin 1 → ℝ) 0 - 1) := by
  have h : ‖Restricted.C (1 : Fin 1 → ℝ) a * X K (1 : Fin 1 → ℝ) 0‖ < 1 := by
    rw [norm_mul, Restricted.norm_C, Affinoid.TateAlgebra.Examples.norm_X K 1 0, mul_one]
    exact ha
  rw [← neg_sub, IsUnit.neg_iff]
  exact isUnit_one_sub_of_norm_lt_one h

theorem subsingleton_quotient_C_mul_X_sub_one {a : K} (ha : ‖a‖ < 1) :
    Subsingleton (TateAlgebra K 1 ⧸
      Ideal.span {C (1 : Fin 1 → ℝ) a * X K (1 : Fin 1 → ℝ) 0 - 1}) :=
  Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 (isUnit_C_mul_X_sub_one ha))

omit [CompleteSpace K] in
/-- `A⟨f⟩ = A` for `f = X` in `A = K⟨X⟩`: `X` is already power-bounded, so the identity has the
universal property of `A⟨X⟩`. Source: roadmap, Layer 1 examples. -/
theorem isGeneralisedFractions_id_X :
    IsGeneralisedFractions.{u_1} (AlgHom.id K (TateAlgebra K 1))
      (fun _ : Fin 1 ↦ X K (1 : Fin 1 → ℝ) 0) (Fin.elim0 : Fin 0 → TateAlgebra K 1) :=
  IsGeneralisedFractions.of_isUnit (fun j ↦ j.elim0) (fun _ ↦ isPowerBounded_X _) fun j ↦ j.elim0

/-- `K⟨X⟩⟨X⁻¹⟩ = K⟨X, Y⟩ ⧸ (XY − 1)`: the generalised ring of fractions `T₁⟨X⁻¹⟩` is the quotient
of `T₂`. Source: roadmap, Layer 1 examples; BGR 6.1.4 ("the algebra `A⟨X⟩⟨X⁻¹⟩` is canonically
isomorphic to the algebra `A⟨X, X⁻¹⟩`"). -/
theorem nonempty_algEquiv_generalisedFractions_X :
    Nonempty (GeneralisedFractions (TateAlgebra K 1) (Fin.elim0 : Fin 0 → TateAlgebra K 1)
      (fun _ : Fin 1 ↦ X K (1 : Fin 1 → ℝ) 0) ≃ₐ[K]
      TateAlgebra K 2 ⧸ Ideal.span {X K (1 : Fin 2 → ℝ) 0 * X K (1 : Fin 2 → ℝ) 1 - 1}) := by
  let e₁ : Restricted (TateAlgebra K 1) (1 : Fin 0 ⊕ Fin 1 → ℝ) ≃ₐ[K]
      Restricted (TateAlgebra K 1) (1 : Fin 1 → ℝ) :=
    AlgEquiv.ofRingEquiv (f := renameEquiv (TateAlgebra K 1) (Equiv.emptySum (Fin 0) (Fin 1)))
      fun k ↦ by
        rw [algebraMap_eq_C_comp (1 : Fin 0 ⊕ Fin 1 → ℝ) (S := TateAlgebra K 1),
          algebraMap_eq_C_comp (1 : Fin 1 → ℝ) (S := TateAlgebra K 1), RingHom.comp_apply,
          RingHom.comp_apply, renameEquiv_C]
  let e := e₁.trans (TateAlgebra.sumEquiv K 1 1)
  have hY : e (X (TateAlgebra K 1) (1 : Fin 0 ⊕ Fin 1 → ℝ) (Sum.inr 0)) =
      X K (1 : Fin 2 → ℝ) 0 := by
    change TateAlgebra.sumEquiv K 1 1 (renameEquiv (TateAlgebra K 1)
      (Equiv.emptySum (Fin 0) (Fin 1)) (X _ _ (Sum.inr 0))) = _
    rw [renameEquiv_X, sumEquiv_X]
    rfl
  have hC : e (Restricted.C (1 : Fin 0 ⊕ Fin 1 → ℝ) (X K (1 : Fin 1 → ℝ) 0)) =
      X K (1 : Fin 2 → ℝ) 1 := by
    change TateAlgebra.sumEquiv K 1 1 (renameEquiv (TateAlgebra K 1)
      (Equiv.emptySum (Fin 0) (Fin 1)) (Restricted.C _ (X K (1 : Fin 1 → ℝ) 0))) = _
    rw [renameEquiv_C, sumEquiv_C, Restricted.eval₂_X]
    rfl
  refine ⟨Ideal.quotientEquivAlg _ _ e ?_⟩
  rw [fractionIdeal, Ideal.map_span, Set.range_eq_empty, Set.empty_union, Set.range_unique,
    Set.image_singleton, map_sub, map_mul, map_one]
  change Ideal.span {X K (1 : Fin 2 → ℝ) 0 * X K (1 : Fin 2 → ℝ) 1 - 1} =
    Ideal.span {e (Restricted.C (1 : Fin 0 ⊕ Fin 1 → ℝ) (X K (1 : Fin 1 → ℝ) 0)) *
      e (X (TateAlgebra K 1) (1 : Fin 0 ⊕ Fin 1 → ℝ) (Sum.inr 0)) - 1}
  rw [hC, hY, mul_comm]

omit [CompleteSpace K] in
/-- The cusp `Y² − X³` (here `X 0 ^ 2 − X 1 ^ 3`, since `X 0` is the distinguished variable) is
`X 0`-distinguished of order two. -/
theorem isMulDistinguishedX0_cusp :
    IsMulDistinguishedX0 (X K (1 : Fin 2 → ℝ) 0 ^ 2 - X K (1 : Fin 2 → ℝ) 1 ^ 3) 2 := by
  have h1 : ofPolynomial K 1 (Polynomial.X ^ 2 - Polynomial.C (X K (1 : Fin 1 → ℝ) 0 ^ 3)) =
      X K (1 : Fin 2 → ℝ) 0 ^ 2 - X K (1 : Fin 2 → ℝ) 1 ^ 3 := by
    rw [map_sub, map_pow, ofPolynomial_X, ← ofTail_apply, map_pow, ofTail_X]
    rfl
  have hω : IsWeierstrassPolynomial K 1
      (Polynomial.X ^ 2 - Polynomial.C (X K (1 : Fin 1 → ℝ) 0 ^ 3)) := by
    refine isWeierstrassPolynomial_iff.2 ⟨Polynomial.monic_X_pow_sub_C _ two_ne_zero, fun i ↦ ?_⟩
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rcases i with _ | _ | _ | i <;> simp [norm_pow]
  have h2 := hω.isMulDistinguishedX0
  rw [Polynomial.natDegree_X_pow_sub_C, h1] at h2
  exact h2

/-- **Noether normalisation of the cusp**: `T₁ → K⟨X, Y⟩ ⧸ (Y² − X³)` is finite and injective.
Source: roadmap, Layer 1 examples; BGR 6.1.2/1. -/
theorem finite_injective_cusp :
    ((Ideal.Quotient.mk (Ideal.span
        {X K (1 : Fin 2 → ℝ) 0 ^ 2 - X K (1 : Fin 2 → ℝ) 1 ^ 3})).comp (ofTail K 1)).Finite ∧
      Function.Injective ((Ideal.Quotient.mk (Ideal.span
        {X K (1 : Fin 2 → ℝ) 0 ^ 2 - X K (1 : Fin 2 → ℝ) 1 ^ 3})).comp (ofTail K 1)) :=
  ⟨finite_mk_comp_ofTail_of_isMulDistinguishedX0 isMulDistinguishedX0_cusp,
    injective_mk_comp_ofTail_of_isMulDistinguishedX0 isMulDistinguishedX0_cusp two_ne_zero⟩

/-- The two presentations `K⟨X⟩ ⧸ (X)` and `K` of the affinoid algebra `K`: evaluation at `0`
induces an isometric isomorphism for the residue norm, since the nearest point of `(X)` to `f` is
`f − f(0)`. Source: roadmap, Layer 1 examples. -/
theorem exists_algEquiv_quotient_X_norm_eq :
    ∃ e : (TateAlgebra K 1 ⧸ Ideal.span {X K (1 : Fin 1 → ℝ) 0}) ≃ₐ[K] K, ∀ f, ‖e f‖ = ‖f‖ := by
  have h0 : ‖(0 : K)‖ ≤ 1 := by simp
  set ev := aeval (K := K) (B := K) (1 : Fin 1 → ℝ) (fun _ ↦ (0 : K)) (fun _ ↦ by simp)
  have hker : RingHom.ker ev = Ideal.span {X K (1 : Fin 1 → ℝ) 0} := by
    rw [ker_aeval_eq_span h0, map_zero, sub_zero]
  have hevC : ∀ k, ev (Restricted.C (1 : Fin 1 → ℝ) k) = k := fun k ↦
    (congrArg ev (algebraMap_apply _ k).symm).trans (ev.commutes k)
  have hsurj : Function.Surjective ev := fun k ↦ ⟨Restricted.C (1 : Fin 1 → ℝ) k, hevC k⟩
  let e := (Ideal.quotientEquivAlgOfEq K hker).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  refine ⟨e, fun x ↦ ?_⟩
  have hx : x = Ideal.Quotient.mk _ (Restricted.C (1 : Fin 1 → ℝ) (e x)) :=
    e.injective (hevC (e x)).symm
  -- the constant `e x` is the representative of least norm
  have hle : ∀ a ∈ Ideal.span {X K (1 : Fin 1 → ℝ) 0},
      ‖Restricted.C (1 : Fin 1 → ℝ) (e x)‖ ≤ ‖Restricted.C (1 : Fin 1 → ℝ) (e x) - a‖ := by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have hc : MvPowerSeries.coeff 0
        (Restricted.C (1 : Fin 1 → ℝ) (e x) - q * X K (1 : Fin 1 → ℝ) 0).1 = e x := by
      rw [val_sub, val_mul, val_C, val_X, map_sub, MvPowerSeries.coeff_zero_mul_X, sub_zero,
        MvPowerSeries.coeff_zero_C]
    rw [Restricted.norm_C]
    exact (congrArg norm hc.symm).trans_le (norm_coeff_le _ 0)
  conv_rhs => rw [hx]
  rw [Ideal.Quotient.norm_mk_eq_norm_of_forall_le (Ideal.span {X K (1 : Fin 1 → ℝ) 0}) hle,
    Restricted.norm_C]

/-- The polydisc algebra `T_{1,ρ}` is affinoid for `ρ = ‖c‖^{1/s}`. Source: BGR 6.1.5/4. -/
theorem isAffinoidAlgebra_polydisc {ρ : ℝ} (hρ : 0 < ρ) {s : ℕ} {c : K} (hs : s ≠ 0) (hc : c ≠ 0)
    (h : ρ ^ s = ‖c‖) :
    haveI : Fact (∀ i : Fin 1, 0 < (fun _ ↦ ρ) i) := ⟨fun _ ↦ hρ⟩
    IsAffinoidAlgebra K (Restricted K (fun _ : Fin 1 ↦ ρ)) :=
  haveI : Fact (∀ i : Fin 1, 0 < (fun _ ↦ ρ) i) := ⟨fun _ ↦ hρ⟩
  isAffinoidAlgebra_of_forall_exists_pow_eq_norm (ρ := fun _ : Fin 1 ↦ ρ) fun _ ↦ ⟨s, c, hs, hc, h⟩

end General

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- `ℚ_p⟨X⟩ ⧸ (pX − 1) = 0`, since `pX − 1` is a unit. Source: roadmap, Layer 1 examples. -/
theorem subsingleton_quotient_p_mul_X_sub_one :
    Subsingleton (TateAlgebra ℚ_[p] 1 ⧸
      Ideal.span {C (1 : Fin 1 → ℝ) (p : ℚ_[p]) * X ℚ_[p] (1 : Fin 1 → ℝ) 0 - 1}) :=
  subsingleton_quotient_C_mul_X_sub_one (Padic.norm_p_lt_one (p := p))

/-- `ℚ_p⟨X⟩ ⧸ (X² − p)` is the quadratic extension `ℚ_p(√p)`: two-dimensional over `ℚ_p` and a
field (Layer 0, `isMaximal_span_X_sq_sub_p`). -/
theorem finrank_quotient_X_sq_sub_p :
    Module.finrank ℚ_[p] (TateAlgebra ℚ_[p] 1 ⧸
      Ideal.span {X ℚ_[p] (1 : Fin 1 → ℝ) 0 ^ 2 - C (1 : Fin 1 → ℝ) (p : ℚ_[p])}) = 2 :=
  finrank_quotient_X_sq_sub (Padic.norm_p_lt_one (p := p))

/-- `ℚ_p⟨X⟩ ⊗_{ℚ_p} K' = K'⟨X⟩` for a finite extension `K'` of `ℚ_p` with a norm extending the
`p`-adic norm (its spectral norm). Source: BGR 6.1.1/8; roadmap, Layer 1 examples
(`ℚ_p⟨X⟩ ⊗_{ℚ_p} ℚ_p(√p) = ℚ_p(√p)⟨X⟩`). -/
noncomputable example (K' : Type*) [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra ℚ_[p] K']
    [NormOneClass K'] [FiniteDimensional ℚ_[p] K'] :
    K' ⊗[ℚ_[p]] TateAlgebra ℚ_[p] 1 ≃ₐ[K'] TateAlgebra K' 1 :=
  TateAlgebra.baseChangeEquiv ℚ_[p] K' 1

end Padic

end Affinoid.Examples
