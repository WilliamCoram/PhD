/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Noether
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm.Banach
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.MaxModulus

/-!
# The supremum seminorm of an affinoid algebra

Layer 2, §2.1 (instance) and §2.2 (BGR 6.2.1/1, 6.2.1/4–5, 6.2.2/1–2, 6.2.2/4). An affinoid
algebra has a supremum seminorm (all residue fields are finite over `K`, Layer 1, and the point
evaluations are bounded by the Gauss norm through a presentation). The **maximum modulus
principle** holds (6.2.1/4 (i)): for a domain by Noether normalisation `T_d ↪ A` and BGR 3.8.1/7 (b)
from the maximum modulus principle on `T_d` (Layer 0), in general through the minimal primes
(6.2.1/3). The values of `|·|_sup` have a power in `‖K‖` (6.2.1/4 (ii)), `|f|_sup = 0` exactly for
nilpotent `f` (6.2.1/4 (iii)), and every homomorphism of a Banach algebra into a reduced affinoid
algebra is continuous (6.2.1/5). Integral homomorphisms are isometries (6.2.2/1) and `|f|_sup` is
the spectral value of an integral equation (6.2.2/2, 6.2.2/4).

## Main declarations

* `IsAffinoidAlgebra.hasSupSeminorm`, `IsAffinoidAlgebra.supSeminorm_le_norm_of_eq`: BGR 6.2.1/1.
* `IsAffinoidAlgebra.exists_evalNorm_eq_supSeminorm`: BGR 6.2.1/4 (i) (M2), from the domain case
  `IsAffinoidAlgebra.exists_evalNorm_eq_supSeminorm_of_isDomain`.
* `IsAffinoidAlgebra.exists_forall_pow_supSeminorm_mem_range_norm_of_isDomain`,
  `IsAffinoidAlgebra.exists_forall_exists_smul_pow_supSeminorm_eq_one`,
  `IsAffinoidAlgebra.exists_smul_pow_supSeminorm_eq_one`: BGR 6.2.1/4 (ii), with a uniform exponent.
* `IsAffinoidAlgebra.supSeminorm_eq_zero_iff_isNilpotent`,
  `IsAffinoidAlgebra.eq_zero_of_supSeminorm_eq_zero`,
  `IsAffinoidAlgebra.isReduced_of_forall_supSeminorm_eq_zero_imp`: BGR 6.2.1/4 (iii).
* `AlgHom.continuous_of_isReduced_of_isAffinoidAlgebra`: BGR 6.2.1/5.
* `IsAffinoidAlgebra.supSeminorm_map_eq_of_isIntegral`: BGR 6.2.2/1.
* `IsAffinoidAlgebra.supSeminorm_eq_supSpectralValue_minpoly_tateAlgebra`,
  `IsAffinoidAlgebra.supSeminorm_algebraMap_tateAlgebra_mul`: BGR 6.2.2/2.
* `IsAffinoidAlgebra.exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue`: BGR 6.2.2/4, from
  the domain case `…_of_isDomain`.
-/

open Polynomial Affinoid

namespace IsAffinoidAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- **BGR 6.2.1/1.** An affinoid algebra has a supremum seminorm: the residue fields are finite
over `K` (Corollary 6.1.2/3, Layer 1) and `|f(x)| ≤ ‖g‖` for any preimage `g ∈ Tₙ` of `f`
(Corollary 3.8.2/2 through the presentation). -/
theorem hasSupSeminorm (hA : IsAffinoidAlgebra K A) : HasSupSeminorm K A := by
  refine ⟨fun x ↦ ?_, fun f ↦ ?_⟩
  · haveI := x.isMaximal
    haveI := hA.finiteDimensional_quotient_of_isMaximal x.asIdeal
    exact Algebra.IsAlgebraic.of_finite K _
  · obtain ⟨n, α, hα⟩ := hA
    obtain ⟨g, rfl⟩ := hα f
    exact ⟨‖g‖, by
      rintro _ ⟨x, rfl⟩
      exact evalNorm_map_le_norm α x g⟩

/-- The supremum seminorm of the Tate algebra is the Gauss norm (Layer 0 `supSeminorm_eq_norm`),
restated with `HasSupSeminorm` available. -/
instance _root_.Affinoid.TateAlgebra.instHasSupSeminorm (n : ℕ) :
    HasSupSeminorm K (TateAlgebra K n) :=
  (tateAlgebra n).hasSupSeminorm

/-- Through a presentation `α : Tₙ ↠ A`, `|f|_sup ≤ ‖g‖` for every preimage `g` of `f`
(BGR p. 236, "`|f|_sup ≤ |f|_α for all f ∈ A and all epimorphisms α: Tₙ → A`"). -/
theorem supSeminorm_le_norm_of_eq {n : ℕ} (α : TateAlgebra K n →ₐ[K] A) {g : TateAlgebra K n}
    {f : A} (hg : α g = f) : supSeminorm K f ≤ ‖g‖ := by
  subst hg
  exact supSeminorm_map_le_norm α g

section MaximumModulus

/-- **The maximum modulus principle for affinoid domains** (BGR 6.2.1/4 (i), the special case):
Noether normalisation `T_d ↪ A` (finite, injective), `T_d` integrally closed with the maximum
modulus principle (Layer 0), and BGR 3.8.1/7 (b). -/
theorem exists_evalNorm_eq_supSeminorm_of_isDomain (hA : IsAffinoidAlgebra K A) [IsDomain A]
    (f : A) : ∃ x : MaximalSpectrum A, evalNorm K x f = supSeminorm K f := by
  obtain ⟨d, φ, hφ, hinj⟩ := hA.exists_finite_injective
  letI : Algebra (TateAlgebra K d) A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (TateAlgebra K d) A :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (φ.commutes k).symm
  haveI : Algebra.IsIntegral (TateAlgebra K d) A := ⟨hφ.to_isIntegral⟩
  haveI : FaithfulSMul (TateAlgebra K d) A := (faithfulSMul_iff_algebraMap_injective _ A).2 hinj
  haveI := hA.hasSupSeminorm
  -- the maximum modulus principle on `T_d` (Layer 0) transfers to `A` (BGR 3.8.1/7 (b))
  refine exists_evalNorm_eq_supSeminorm_of_forall_exists K (B := TateAlgebra K d) (fun t ↦ ?_) f
  obtain ⟨y, -, hy⟩ := MvPowerSeries.Restricted.exists_evalNorm_eq_norm t
  exact ⟨y, hy.trans (MvPowerSeries.Restricted.supSeminorm_eq_norm t).symm⟩

/-- **The maximum modulus principle** (BGR 6.2.1/4 (i); Bosch 1.4/14): for a nonzero affinoid
algebra `A` and `f ∈ A` there is a point `x` with `|f(x)| = |f|_sup`. Through the minimal primes
(BGR 6.2.1/3) from the domain case. -/
theorem exists_evalNorm_eq_supSeminorm (hA : IsAffinoidAlgebra K A) [Nontrivial A] (f : A) :
    ∃ x : MaximalSpectrum A, evalNorm K x f = supSeminorm K f := by
  haveI := hA.hasSupSeminorm
  haveI := hA.isNoetherianRing
  -- a minimal prime `𝔭` with `|f mod 𝔭|_sup = |f|_sup` (BGR 6.2.1/3), then the domain case on
  -- `A ⧸ 𝔭`
  obtain ⟨𝔭, h𝔭, hsup⟩ := exists_minimalPrimes_supSeminorm_mk_eq (K := K) f
  haveI : 𝔭.IsPrime := IsMinimalPrime.isPrime h𝔭
  obtain ⟨x₀, hx₀⟩ :=
    exists_evalNorm_eq_supSeminorm_of_isDomain (hA.quotient 𝔭) (Ideal.Quotient.mk 𝔭 f)
  exact ⟨comapPoint (Ideal.Quotient.mkₐ K 𝔭) x₀,
    (evalNorm_comapPoint (Ideal.Quotient.mkₐ K 𝔭) x₀ f).symm.trans (hx₀.trans hsup)⟩

/-- The values of `|·|_sup` on an affinoid domain have a power in `‖K‖`, with a uniform exponent:
`|f|_sup ^ n! ∈ ‖K‖` where `n = [Q(A) : Q(T_d)]` bounds the degrees of the minimal polynomials over
`T_d` (BGR 3.8.1/8 with `|T_d|_sup = |K|`). -/
theorem exists_forall_pow_supSeminorm_mem_range_norm_of_isDomain (hA : IsAffinoidAlgebra K A)
    [IsDomain A] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ f : A, supSeminorm K f ^ m ∈ Set.range (fun c : K ↦ ‖c‖) := by
  obtain ⟨d, φ, hφ, hinj⟩ := hA.exists_finite_injective
  letI : Algebra (TateAlgebra K d) A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (TateAlgebra K d) A :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (φ.commutes k).symm
  haveI : Module.Finite (TateAlgebra K d) A := hφ
  haveI : FaithfulSMul (TateAlgebra K d) A := (faithfulSMul_iff_algebraMap_injective _ A).2 hinj
  haveI := hA.hasSupSeminorm
  -- the values `|t|_sup = ‖t‖` on `T_d` lie in `‖K‖` (BGR 5.1.1), and the minimal polynomials over
  -- `T_d` have degree at most the number of generators of `A` (Cayley–Hamilton)
  refine ⟨((⊤ : Submodule (TateAlgebra K d) A).spanFinrank).factorial, Nat.factorial_ne_zero _,
    supSeminorm_pow_factorial_mem_range_norm K (fun t ↦ ?_)
      (minpoly.natDegree_le_spanFinrank (TateAlgebra K d))⟩
  rw [MvPowerSeries.Restricted.supSeminorm_eq_norm]
  exact MvPowerSeries.Restricted.norm_mem_range_norm t

/-- **BGR 6.2.1/4 (ii), uniform form** (roadmap §2.2.2): there is `m ≥ 1` depending only on `A`
such that every `f` with `|f|_sup ≠ 0` has `c ∈ K` with `|c f^m|_sup = 1`. -/
theorem exists_forall_exists_smul_pow_supSeminorm_eq_one (hA : IsAffinoidAlgebra K A) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ f : A, supSeminorm K f ≠ 0 → ∃ c : K, supSeminorm K (c • f ^ m) = 1 := by
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · refine ⟨1, one_ne_zero, fun f hf ↦ absurd ?_ hf⟩
    rw [Subsingleton.elim f 0]
    exact supSeminorm_zero K
  haveI := hA.hasSupSeminorm
  haveI := hA.isNoetherianRing
  haveI : Fintype (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  -- a uniform exponent `m 𝔭` on each affinoid domain `A ⧸ 𝔭` (the special case)
  have h𝔭 : ∀ 𝔭 : minimalPrimes A, ∃ m : ℕ, m ≠ 0 ∧
      ∀ g : A ⧸ (𝔭 : Ideal A), supSeminorm K g ^ m ∈ Set.range (fun c : K ↦ ‖c‖) := fun 𝔭 ↦ by
    haveI : (𝔭 : Ideal A).IsPrime := IsMinimalPrime.isPrime 𝔭.2
    exact (hA.quotient _).exists_forall_pow_supSeminorm_mem_range_norm_of_isDomain
  choose m hm0 hm using h𝔭
  have hM : ∏ 𝔭, m 𝔭 ≠ 0 := Finset.prod_ne_zero_iff.2 fun 𝔭 _ ↦ hm0 𝔭
  refine ⟨∏ 𝔭, m 𝔭, hM, fun f hf ↦ ?_⟩
  -- `|f|_sup = |f mod 𝔭|_sup` for a minimal prime `𝔭` (BGR 6.2.1/3)
  obtain ⟨𝔭, h𝔭, hsup⟩ := exists_minimalPrimes_supSeminorm_mk_eq (K := K) f
  obtain ⟨d, hd⟩ := hm ⟨𝔭, h𝔭⟩ (Ideal.Quotient.mk 𝔭 f)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (⟨𝔭, h𝔭⟩ : minimalPrimes A))
  -- `|f|_sup ^ (∏ m) = ‖d ^ k‖`, nonzero
  have hpow : supSeminorm K f ^ (∏ 𝔭, m 𝔭) = ‖d ^ k‖ := by
    rw [hk, pow_mul, ← hsup, norm_pow]
    exact congrArg (· ^ k) hd.symm
  have hne : ‖d ^ k‖ ≠ 0 := by
    rw [← hpow]
    exact pow_ne_zero _ hf
  refine ⟨(d ^ k)⁻¹, ?_⟩
  rw [supSeminorm_smul, supSeminorm_pow K f hM, hpow, norm_inv, inv_mul_cancel₀ hne]

/-- **BGR 6.2.1/4 (ii)** (Bosch 1.4/15): for `|f|_sup ≠ 0` there are `c ∈ K` and `m ≥ 1` with
`|c f^m|_sup = 1`. -/
theorem exists_smul_pow_supSeminorm_eq_one (hA : IsAffinoidAlgebra K A) {f : A}
    (hf : supSeminorm K f ≠ 0) : ∃ (c : K) (m : ℕ), m ≠ 0 ∧ supSeminorm K (c • f ^ m) = 1 := by
  obtain ⟨m, hm, h⟩ := hA.exists_forall_exists_smul_pow_supSeminorm_eq_one
  obtain ⟨c, hc⟩ := h f hf
  exact ⟨c, m, hm, hc⟩

/-- **BGR 6.2.1/4 (iii)**: `|f|_sup = 0` iff `f` is nilpotent (the Jacobson radical of an affinoid
algebra is its nilradical, Layer 1 `isJacobsonRing`, with BGR 3.8.1/9). -/
theorem supSeminorm_eq_zero_iff_isNilpotent (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = 0 ↔ IsNilpotent f := by
  haveI := hA.hasSupSeminorm
  haveI := hA.isJacobsonRing
  rw [supSeminorm_eq_zero_iff_mem_jacobson_bot K f]
  -- in a Jacobson ring the Jacobson radical of `0` is its radical, the nilradical
  constructor
  · intro hf
    have h := Ideal.jacobson_mono (Ideal.le_radical (I := (⊥ : Ideal A))) hf
    rw [IsJacobsonRing.out ‹_› (Ideal.radical_isRadical _)] at h
    exact mem_nilradical.1 h
  · intro hf
    exact Ideal.radical_le_jacobson (mem_nilradical.2 hf)

/-- **BGR 6.2.1/4 (iii)**, second half: on a reduced affinoid algebra `|·|_sup` is a norm. -/
theorem eq_zero_of_supSeminorm_eq_zero (hA : IsAffinoidAlgebra K A) [IsReduced A] {f : A}
    (hf : supSeminorm K f = 0) : f = 0 :=
  ((hA.supSeminorm_eq_zero_iff_isNilpotent f).1 hf).eq_zero

/-- The converse: if `|·|_sup` is a norm then `A` is reduced (a ring with a power-multiplicative
norm is reduced, BGR 1.3.1). -/
theorem isReduced_of_forall_supSeminorm_eq_zero_imp (hA : IsAffinoidAlgebra K A)
    (h : ∀ f : A, supSeminorm K f = 0 → f = 0) : IsReduced A :=
  ⟨fun f hf ↦ h f ((hA.supSeminorm_eq_zero_iff_isNilpotent f).2 hf)⟩

end MaximumModulus

section Continuity

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]

/-- **BGR 6.2.1/5**: every `K`-algebra homomorphism from a (not necessarily noetherian) Banach
algebra into a reduced affinoid Banach algebra is continuous (BGR 3.8.2/3 + 6.2.1/4 (iii)). -/
theorem _root_.AlgHom.continuous_of_isReduced_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A)
    [IsReduced A] (φ : B →ₐ[K] A) : Continuous φ := by
  haveI := hA.hasSupSeminorm
  exact φ.continuous_of_supSeminorm_eq_zero_imp
    (fun x ↦ haveI := x.isMaximal; hA.finiteDimensional_quotient_of_isMaximal x.asIdeal)
    (fun _ hf ↦ hA.eq_zero_of_supSeminorm_eq_zero hf)

end Continuity

section Integral

/-- **BGR 6.2.2/1**, second half: an integral monomorphism of affinoid algebras is an isometry for
`|·|_sup` (BGR 3.8.1/6 (a)). The first half, "every homomorphism is a contraction", is
`Affinoid.supSeminorm_map_le`. -/
theorem supSeminorm_map_eq_of_isIntegral (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (φ : B →ₐ[K] A) (hint : φ.toRingHom.IsIntegral) (hinj : Function.Injective φ) (b : B) :
    supSeminorm K (φ b) = supSeminorm K b := by
  letI : Algebra B A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun k ↦ (φ.commutes k).symm
  haveI : Algebra.IsIntegral B A := ⟨hint⟩
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).2 hinj
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  exact supSeminorm_algebraMap_eq K b

variable {d : ℕ} [Algebra (TateAlgebra K d) A] [IsScalarTower K (TateAlgebra K d) A]

/-- **BGR 6.2.2/2**, the equation `|f|_sup = max |tᵢ|^{1/i}` for an affinoid domain `A` integral
over `T_d` with injective structure map (BGR 3.8.1/7 (a) with `T_d` integrally closed and
`|·|_sup = ‖·‖` on `T_d`). -/
theorem supSeminorm_eq_supSpectralValue_minpoly_tateAlgebra (hA : IsAffinoidAlgebra K A)
    [IsDomain A] [Algebra.IsIntegral (TateAlgebra K d) A] [FaithfulSMul (TateAlgebra K d) A]
    (f : A) : supSeminorm K f = supSpectralValue K (minpoly (TateAlgebra K d) f) := by
  haveI := hA.hasSupSeminorm
  exact supSeminorm_eq_supSpectralValue_minpoly K f

/-- **BGR 6.2.2/2**, `|·|_sup` is a faithful `T_d`-algebra norm: `|φ(t) f|_sup = |t| |f|_sup`
(BGR 3.8.1/7 (d), the Gauss norm being multiplicative). -/
theorem supSeminorm_algebraMap_tateAlgebra_mul (hA : IsAffinoidAlgebra K A) [IsDomain A]
    [Algebra.IsIntegral (TateAlgebra K d) A] [FaithfulSMul (TateAlgebra K d) A]
    (t : TateAlgebra K d) (f : A) :
    supSeminorm K (algebraMap (TateAlgebra K d) A t * f) = ‖t‖ * supSeminorm K f := by
  haveI := hA.hasSupSeminorm
  have hT : ∀ t : TateAlgebra K d, supSeminorm K t = ‖t‖ := fun t ↦
    MvPowerSeries.Restricted.supSeminorm_eq_norm t
  rw [supSeminorm_algebraMap_mul K (fun t t' ↦ by rw [hT, hT, hT, norm_mul]) t f, hT]

/-- **BGR 6.2.2/4** for an affinoid domain `A`: for `φ : B → A` finite (plan D10) there is a monic
`q ∈ B[X]` with `q(f) = 0` and `|f|_sup = σ(q)` (compose with `ψ : T_d → B` from Theorem
6.1.2/1 so that `φ ∘ ψ` is an integral monomorphism, take the minimal polynomial over `T_d` and
push its coefficients into `B`; `σ(q) ≤ σ(p)` by contraction, `≥` by 6.2.2/3). -/
theorem exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue_of_isDomain
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) [IsDomain A] (φ : B →ₐ[K] A)
    (hfin : φ.toRingHom.Finite) (f : A) :
    ∃ q : B[X], q.Monic ∧ q.eval₂ (φ : B →+* A) f = 0 ∧ supSeminorm K f = supSpectralValue K q := by
  obtain ⟨d, ψ, hψfin, hψinj⟩ := hB.exists_finite_injective_comp φ hfin
  letI : Algebra (TateAlgebra K d) A := (φ.comp ψ).toRingHom.toAlgebra
  haveI : IsScalarTower K (TateAlgebra K d) A :=
    IsScalarTower.of_algebraMap_eq fun k ↦ ((φ.comp ψ).commutes k).symm
  haveI : Module.Finite (TateAlgebra K d) A := hψfin
  haveI : FaithfulSMul (TateAlgebra K d) A := (faithfulSMul_iff_algebraMap_injective _ A).2 hψinj
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  -- `|f|_sup = σ(p)` for the minimal polynomial `p` of `f` over `T_d` (BGR 6.2.2/2)
  have hp : (minpoly (TateAlgebra K d) f).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral f)
  have hpf := hA.supSeminorm_eq_supSpectralValue_minpoly_tateAlgebra (d := d) f
  -- `q := ψ(p)` has `q(f) = p(f) = 0`
  have heval : ((minpoly (TateAlgebra K d) f).map (ψ : TateAlgebra K d →+* B)).eval₂
      (φ : B →+* A) f = 0 := by
    have h := minpoly.aeval (TateAlgebra K d) f
    rw [Polynomial.aeval_def] at h
    rw [Polynomial.eval₂_map]
    exact h
  -- `|f|_sup ≤ σ(q) ≤ σ(p) = |f|_sup`
  refine ⟨_, hp.map _, heval, le_antisymm
    (supSeminorm_le_supSpectralValue_of_eval₂_eq_zero K φ (hp.map _) heval) ?_⟩
  rw [hpf]
  exact supSpectralValue_map_le K ψ hp

/-- **BGR 6.2.2/4** (Bosch 1.4/13): for `φ : B → A` finite (plan D10) between affinoid algebras and
`f ∈ A` there is a monic `q ∈ B[X]` with `q(f) = 0` and `|f|_sup = σ(q)`. From the domain case
through the minimal primes: `q := (∏ qᵢ)^e` with `qᵢ(f) ∈ 𝔭ᵢ` and `e` killing the nilradical, then
BGR 1.5.4/1 and 6.2.1/3. -/
theorem exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (φ : B →ₐ[K] A) (hfin : φ.toRingHom.Finite) (f : A) :
    ∃ q : B[X], q.Monic ∧ q.eval₂ (φ : B →+* A) f = 0 ∧ supSeminorm K f = supSpectralValue K q := by
  classical
  haveI := hA.hasSupSeminorm
  haveI := hB.hasSupSeminorm
  haveI := hA.isNoetherianRing
  have hfinset := minimalPrimes.finite_of_isNoetherianRing A
  -- the domain case on each `A ⧸ 𝔭`: `qᵢ(f) ∈ 𝔭ᵢ` and `σ(qᵢ) = |f mod 𝔭ᵢ|_sup ≤ |f|_sup`
  have h𝔭 : ∀ 𝔭 ∈ minimalPrimes A, ∃ q : B[X], q.Monic ∧ q.eval₂ (φ : B →+* A) f ∈ 𝔭 ∧
      supSpectralValue K q ≤ supSeminorm K f := by
    intro 𝔭 h𝔭
    haveI : 𝔭.IsPrime := IsMinimalPrime.isPrime h𝔭
    have hfin' : ((Ideal.Quotient.mkₐ K 𝔭).comp φ).toRingHom.Finite :=
      (RingHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective K 𝔭)).comp hfin
    obtain ⟨q, hq, hqf, hσ⟩ :=
      exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue_of_isDomain (hA.quotient 𝔭) hB
        ((Ideal.Quotient.mkₐ K 𝔭).comp φ) hfin' (Ideal.Quotient.mk 𝔭 f)
    refine ⟨q, hq, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
      exact hqf
    · rw [← hσ]
      exact supSeminorm_mk_le K 𝔭 f
  choose! q hq hqf hσ using h𝔭
  have hmon : ∀ 𝔭 ∈ hfinset.toFinset, (q 𝔭).Monic := fun 𝔭 h ↦ hq 𝔭 (hfinset.mem_toFinset.1 h)
  have hqs : (∏ 𝔭 ∈ hfinset.toFinset, q 𝔭).Monic := monic_prod_of_monic _ q hmon
  -- `q*(f) ∈ ⋂ 𝔭ᵢ = nilradical A`, so `q*(f)ᵉ = 0` for some `e`
  have hnil : IsNilpotent ((∏ 𝔭 ∈ hfinset.toFinset, q 𝔭).eval₂ (φ : B →+* A) f) := by
    have hmem : (∏ 𝔭 ∈ hfinset.toFinset, q 𝔭).eval₂ (φ : B →+* A) f ∈
        sInf ((⊥ : Ideal A).minimalPrimes) := by
      rw [Ideal.mem_sInf]
      intro 𝔭 h𝔭
      rw [Polynomial.eval₂_finsetProd]
      exact Ideal.prod_mem 𝔭 (hfinset.mem_toFinset.2 h𝔭) (hqf 𝔭 h𝔭)
    rw [Ideal.sInf_minimalPrimes] at hmem
    exact mem_nilradical.1 hmem
  obtain ⟨e, he⟩ := hnil
  have heval : ((∏ 𝔭 ∈ hfinset.toFinset, q 𝔭) ^ e).eval₂ (φ : B →+* A) f = 0 := by
    rw [Polynomial.eval₂_pow, he]
  -- `|f|_sup ≤ σ(q*ᵉ) ≤ σ(q*) ≤ max σ(qᵢ) ≤ |f|_sup` (BGR 1.5.4/1)
  refine ⟨_, hqs.pow e, heval, le_antisymm
    (supSeminorm_le_supSpectralValue_of_eval₂_eq_zero K φ (hqs.pow e) heval) ?_⟩
  exact (supSpectralValue_pow_le K hqs e).trans (supSpectralValue_prod_le_of_forall_le K hmon
    (supSeminorm_nonneg K f) fun 𝔭 h ↦ hσ 𝔭 (hfinset.mem_toFinset.1 h))

end Integral

end IsAffinoidAlgebra
