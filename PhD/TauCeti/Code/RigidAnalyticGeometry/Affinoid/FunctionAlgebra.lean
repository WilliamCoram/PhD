/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.PowerBounded
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm.FunctionAlgebra

/-!
# Reduced affinoid algebras are Banach function algebras

Layer 2, §2.4.1, §2.3.5 (second half) and §2.4.3 (BGR 6.2.4/1). For a reduced affinoid algebra
`A` with any complete `K`-algebra norm, `|·|_sup` is equivalent to the norm: `‖f‖ ≤ C * |f|_sup`.
Domain case: Noether normalisation `T_d ↪ A` and BGR 3.8.3/7 with the weak stability of `Q(T_d)`
(Layer 0, characteristic `0`: plan D2). General case: `A ↪ ⊕ A ⧸ 𝔭ᵢ` over the minimal primes with
the maximum of the residue norms, closed by BGR 3.7.3/1, and the open mapping theorem.

## Main declarations

* `IsAffinoidAlgebra.isBanachFunctionAlgebra_of_isDomain`: BGR 6.2.4/1 for domains.
* `Ideal.Quotient.continuousSMul_pi`, `IsAffinoidAlgebra.isClosed_range_pi_quotient_mk`,
  `IsAffinoidAlgebra.exists_norm_le_mul_norm_pi_quotient_mk`: the diagonal map `A → ∏ A ⧸ 𝔭ᵢ`.
* `IsAffinoidAlgebra.isBanachFunctionAlgebra_of_isReduced`: BGR 6.2.4/1 (M4).
* `IsAffinoidAlgebra.isBounded_powerBounded_of_isReduced`: §2.3.5, reduced ⇒ `Å` bounded.
* `IsAffinoidAlgebra.exists_norm_map_le_mul_supSeminorm`: §2.4.3, continuous homomorphisms are
  bounded for `|·|_sup`.
-/

open Affinoid

universe u

namespace IsAffinoidAlgebra

-- `A` lives in the universe of `K`: the domain case applies BGR 3.8.3/7 with `B = T_d`, whose weak
-- stability (Layer 0) quantifies over finite extensions of `Q(T_d)` in the universe of `K`.
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A]

/-- **BGR 6.2.4/1 for an affinoid domain** (`[CharZero K]`, plan D2): choose a finite
normalisation `φ : T_d ↪ A`; `φ` is continuous (Layer 1), `T_d` is a valued integrally closed
noetherian Banach function algebra (`|·|_sup = ‖·‖`, Layer 0) with weakly stable fraction field
(Layer 0, `isWeaklyStable_fractionRing`), so BGR 3.8.3/7 applies. -/
theorem isBanachFunctionAlgebra_of_isDomain [CharZero K] (hA : IsAffinoidAlgebra K A)
    [IsDomain A] : IsBanachFunctionAlgebra K A := by
  obtain ⟨d, φ, hφ, hinj⟩ := hA.exists_finite_injective
  letI : Algebra (TateAlgebra K d) A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (TateAlgebra K d) A :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (φ.commutes k).symm
  haveI : Module.Finite (TateAlgebra K d) A := hφ
  haveI : FaithfulSMul (TateAlgebra K d) A := (faithfulSMul_iff_algebraMap_injective _ A).2 hinj
  -- `T_d` is a valued integrally closed noetherian Banach function algebra with `|·|_sup = ‖·‖`
  -- and weakly stable fraction field (Layer 0); `φ` is continuous (Layer 1)
  exact IsBanachFunctionAlgebra.of_finite_domain (B := TateAlgebra K d)
    (fun t ↦ MvPowerSeries.Restricted.supSeminorm_eq_norm t)
    (TateAlgebra.isWeaklyStable_fractionRing K d) (hA.continuous_presentation φ)

section Quotient

variable {R : Type*} [SeminormedCommRing R] {ι : Type*} (𝔭 : ι → Ideal R)

/-- The product `∏ R ⧸ 𝔭ᵢ` of residue (semi)normed rings has continuous scalar multiplication by
`R`: `a • x = (mk a * xᵢ)ᵢ` and each `mk` is a contraction. -/
theorem _root_.Ideal.Quotient.continuousSMul_pi : ContinuousSMul R (∀ i, R ⧸ 𝔭 i) := by
  refine ⟨continuous_pi fun i ↦ ?_⟩
  have hmk : Continuous (Ideal.Quotient.mk (𝔭 i)) :=
    AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mk (𝔭 i)) 1 fun r ↦ by
      rw [one_mul]
      exact Ideal.Quotient.norm_mk_le (𝔭 i) r
  have h : (fun p : R × (∀ i, R ⧸ 𝔭 i) ↦ (p.1 • p.2) i) =
      fun p ↦ Ideal.Quotient.mk (𝔭 i) p.1 * p.2 i :=
    funext fun p ↦ Algebra.smul_def p.1 (p.2 i)
  rw [h]
  exact (hmk.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

end Quotient

section MinimalPrimes

variable {ι : Type*} [Fintype ι] (𝔭 : ι → Ideal A)

/-- The diagonal map `A → ∏ A ⧸ 𝔭ᵢ` is injective when `⋂ 𝔭ᵢ = ⊥`, continuous, and has closed range
(BGR 3.7.3/1: `A` is a submodule of the finite `A`-module `A'`). -/
theorem isClosed_range_pi_quotient_mk (hA : IsAffinoidAlgebra K A) :
    haveI : ∀ i, IsClosed ((𝔭 i : Ideal A) : Set A) := fun i ↦ hA.isClosed_ideal (𝔭 i)
    IsClosed (Set.range (RingHom.pi fun i ↦ Ideal.Quotient.mk (𝔭 i))) := by
  haveI : ∀ i, IsClosed ((𝔭 i : Ideal A) : Set A) := fun i ↦ hA.isClosed_ideal (𝔭 i)
  haveI := hA.isNoetherianRing
  haveI := Ideal.Quotient.continuousSMul_pi 𝔭
  -- the range is the `A`-submodule `A · 1` of the finite `A`-module `∏ A ⧸ 𝔭ᵢ` (BGR 3.7.3/1)
  have h := Submodule.isClosed_of_isNoetherianRing_of_finite K (A := A) (M := ∀ i, A ⧸ 𝔭 i)
    (LinearMap.range (Algebra.linearMap A (∀ i, A ⧸ 𝔭 i)))
  rw [LinearMap.coe_range] at h
  exact h

/-- Open mapping for the diagonal map: `‖f‖ ≤ C * max_i ‖f mod 𝔭ᵢ‖` when `⋂ 𝔭ᵢ = ⊥`. -/
theorem exists_norm_le_mul_norm_pi_quotient_mk (hA : IsAffinoidAlgebra K A)
    (h : ⨅ i, 𝔭 i = ⊥) :
    haveI : ∀ i, IsClosed ((𝔭 i : Ideal A) : Set A) := fun i ↦ hA.isClosed_ideal (𝔭 i)
    ∃ C : ℝ, ∀ f : A, ‖f‖ ≤ C * ‖(RingHom.pi fun i ↦ Ideal.Quotient.mk (𝔭 i)) f‖ := by
  haveI : ∀ i, IsClosed ((𝔭 i : Ideal A) : Set A) := fun i ↦ hA.isClosed_ideal (𝔭 i)
  have hcont : Continuous fun f : A ↦ fun i ↦ Ideal.Quotient.mk (𝔭 i) f := continuous_pi fun i ↦
    AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mk (𝔭 i)) 1 fun r ↦ by
      rw [one_mul]
      exact Ideal.Quotient.norm_mk_le (𝔭 i) r
  have hinj : Function.Injective (RingHom.pi fun i ↦ Ideal.Quotient.mk (𝔭 i)) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have hmem : f ∈ ⨅ i, 𝔭 i := (Submodule.mem_iInf _).2 fun i ↦
      Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hf i)
    rwa [h, Submodule.mem_bot] at hmem
  -- a continuous injective `K`-linear map with closed range is anti-Lipschitz (open mapping)
  let π : A →L[K] (∀ i, A ⧸ 𝔭 i) :=
    ⟨LinearMap.pi fun i ↦ (Ideal.Quotient.mkₐ K (𝔭 i)).toLinearMap, hcont⟩
  obtain ⟨c, hc⟩ :=
    π.antilipschitz_of_injective_of_isClosed_range hinj (hA.isClosed_range_pi_quotient_mk 𝔭)
  refine ⟨c, fun f ↦ ?_⟩
  have hle := hc.le_mul_dist f 0
  rw [dist_zero_right, map_zero, dist_zero_right] at hle
  exact hle

end MinimalPrimes

/-- **BGR 6.2.4/1** (M4; `[CharZero K]`, plan D2): every reduced affinoid algebra is a Banach
function algebra, i.e. `‖f‖ ≤ C * |f|_sup` for every complete `K`-algebra norm. Through the
diagonal map into `∏ A ⧸ 𝔭ᵢ` (minimal primes, `⋂ 𝔭ᵢ = nilradical = ⊥`), the domain case on each
factor, 6.2.1/3 (`|f mod 𝔭ᵢ|_sup ≤ |f|_sup`) and the open mapping bound. -/
theorem isBanachFunctionAlgebra_of_isReduced [CharZero K] (hA : IsAffinoidAlgebra K A)
    [IsReduced A] : IsBanachFunctionAlgebra K A := by
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · exact ⟨0, fun f ↦ by rw [Subsingleton.elim f 0, norm_zero, zero_mul]⟩
  haveI := hA.hasSupSeminorm
  haveI := hA.isNoetherianRing
  haveI : Fintype (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  let 𝔭 : minimalPrimes A → Ideal A := fun P ↦ P
  haveI : ∀ i, IsClosed ((𝔭 i : Ideal A) : Set A) := fun i ↦ hA.isClosed_ideal (𝔭 i)
  -- `⋂ 𝔭ᵢ = nilradical A = ⊥` (`A` reduced)
  have hinf : ⨅ i, 𝔭 i = ⊥ := by
    refine eq_bot_iff.2 fun f hf ↦ ?_
    have hrad : f ∈ (⊥ : Ideal A).radical := by
      rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro P hP
      exact (Submodule.mem_iInf _).1 hf ⟨P, hP⟩
    exact Ideal.mem_bot.2 (mem_nilradical.1 hrad).eq_zero
  obtain ⟨C, hC⟩ := hA.exists_norm_le_mul_norm_pi_quotient_mk 𝔭 hinf
  -- each `A ⧸ 𝔭ᵢ` with its residue norm is a Banach function algebra (the domain case)
  have hdom : ∀ i, ∃ D : ℝ, ∀ g : A ⧸ 𝔭 i, ‖g‖ ≤ D * supSeminorm K g := fun i ↦ by
    haveI : (𝔭 i).IsPrime := IsMinimalPrime.isPrime i.2
    haveI : NormOneClass (A ⧸ 𝔭 i) :=
      Ideal.Quotient.normOneClass_of_ne_top (𝔭 i) (Ideal.IsPrime.ne_top ‹_›)
    exact (hA.quotient (𝔭 i)).isBanachFunctionAlgebra_of_isDomain
  choose D hD using hdom
  -- `‖f‖ ≤ C max ‖f mod 𝔭ᵢ‖ ≤ C max Dᵢ |f mod 𝔭ᵢ|_sup ≤ C (Σ max Dᵢ 0) |f|_sup`
  have hD0 : 0 ≤ ∑ i, max (D i) 0 := Finset.sum_nonneg fun i _ ↦ le_max_right _ _
  refine ⟨max C 0 * ∑ i, max (D i) 0, fun f ↦ ?_⟩
  have hs := supSeminorm_nonneg K f
  have hπ : ‖(RingHom.pi fun i ↦ Ideal.Quotient.mk (𝔭 i)) f‖ ≤
      (∑ i, max (D i) 0) * supSeminorm K f := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hD0 hs)).2 fun i ↦ ?_
    calc ‖Ideal.Quotient.mk (𝔭 i) f‖ ≤ D i * supSeminorm K (Ideal.Quotient.mk (𝔭 i) f) := hD i _
      _ ≤ max (D i) 0 * supSeminorm K (Ideal.Quotient.mk (𝔭 i) f) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (supSeminorm_nonneg K _)
      _ ≤ max (D i) 0 * supSeminorm K f :=
          mul_le_mul_of_nonneg_left (supSeminorm_mk_le K (𝔭 i) f) (le_max_right _ _)
      _ ≤ (∑ j, max (D j) 0) * supSeminorm K f :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j ↦ max (D j) 0)
            (fun j _ ↦ le_max_right _ _) (Finset.mem_univ i)) hs
  calc ‖f‖ ≤ C * ‖(RingHom.pi fun i ↦ Ideal.Quotient.mk (𝔭 i)) f‖ := hC f
    _ ≤ max C 0 * ‖(RingHom.pi fun i ↦ Ideal.Quotient.mk (𝔭 i)) f‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max C 0 * ((∑ i, max (D i) 0) * supSeminorm K f) :=
        mul_le_mul_of_nonneg_left hπ (le_max_right _ _)
    _ = (max C 0 * ∑ i, max (D i) 0) * supSeminorm K f := (mul_assoc _ _ _).symm

/-- **§2.3.5**: a reduced affinoid algebra has bounded `Å` (is "uniform" in the norm sense). -/
theorem isBounded_powerBounded_of_isReduced [CharZero K] (hA : IsAffinoidAlgebra K A)
    [IsReduced A] :
    haveI := hA.hasSupSeminorm
    TopologicalRing.IsBounded (powerBounded K A : Set A) :=
  hA.exists_norm_le_mul_supSeminorm_iff_isBounded_powerBounded.1
    hA.isBanachFunctionAlgebra_of_isReduced

/-- **§2.4.3**: on a reduced affinoid algebra every continuous algebra homomorphism into a Banach
algebra is bounded for `|·|_sup` (`‖φ f‖ ≤ C * |f|_sup`), the form in which the Banach function
algebra property is used downstream. -/
theorem exists_norm_map_le_mul_supSeminorm [CharZero K] (hA : IsAffinoidAlgebra K A) [IsReduced A]
    {B : Type*} [NormedCommRing B] [NormedAlgebra K B] (φ : A →ₐ[K] B) (hφ : Continuous φ) :
    ∃ C : ℝ, ∀ f : A, ‖φ f‖ ≤ C * supSeminorm K f := by
  obtain ⟨C, hC⟩ := hA.isBanachFunctionAlgebra_of_isReduced
  obtain ⟨C', hC'0, hC'⟩ := SemilinearMapClass.bound_of_continuous φ.toLinearMap hφ
  refine ⟨C' * C, fun f ↦ ?_⟩
  calc ‖φ f‖ ≤ C' * ‖f‖ := hC' f
    _ ≤ C' * (C * supSeminorm K f) := mul_le_mul_of_nonneg_left (hC f) hC'0.le
    _ = C' * C * supSeminorm K f := (mul_assoc _ _ _).symm

end IsAffinoidAlgebra
