import Mathlib.RingTheory.MvPowerSeries.Restricted
import Mathlib.RingTheory.MvPowerSeries.GaussNorm
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Rigid analytic geometry: representative interfaces

The README is definitive. All definitions below have bodies; `sorry` occurs only in theorem
targets. No admitted instances, opaque geometric carriers or roadmap imports are used.

At this Mathlib pin the named normed restricted-series carrier is not available. `weightedTate`
is only the native restricted subring viewed as a subalgebra for stating signatures. Production
code imports RestrictedPowerSeries' carrier and its norms, rather than implementing it again.
The point seminorm uses Mathlib's spectral norm on the actual maximal-ideal quotient. Affinoid
hypotheses are explicit propositions; they do not install a norm or assume reducedness.

The geometric constructions, completed tensors, Kiehl operators and numerical slopes have shared
owners and are specified in the README. They are not represented here by axiomatic substitutes.
The filtration helper at the end only states an algebraic implication; it does not pretend to
prove the geometric stability or uniform cokernel assertion of formal functions.
-/

namespace TauCetiRoadmap.RigidAnalyticGeometry

noncomputable section

open scoped Topology

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The native restricted-series carrier, as a subalgebra. -/
def weightedTate (n : ℕ) (ρ : Fin n → ℝ) : Subalgebra K (MvPowerSeries (Fin n) K) where
  __ := MvPowerSeries.IsRestricted.subring ρ
  algebraMap_mem' a := by
    rw [MvPowerSeries.algebraMap_apply]
    exact MvPowerSeries.isRestricted_C ρ (algebraMap K K a)

abbrev TateAlgebra (n : ℕ) := weightedTate K n (fun _ ↦ 1)

def gaussNorm {n : ℕ} (f : TateAlgebra K n) : ℝ :=
  MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ 1) (f : MvPowerSeries (Fin n) K)

/-- This predicate makes no choice of topology (README Convention 3). -/
def IsAffinoidAlgebra (A : Type*) [CommRing A] [Algebra K A] : Prop :=
  ∃ (n : ℕ) (π : TateAlgebra K n →ₐ[K] A), Function.Surjective π

/-- Positive divisible value-group radii. Positivity excludes zero. -/
def IsStrictRadius (r : ℝ) : Prop :=
  0 < r ∧ ∃ (m : ℕ) (c : K), 0 < m ∧ c ≠ 0 ∧ r ^ m = ‖c‖

section Algebra

variable {A : Type*} [CommRing A] [Algebra K A]

theorem isNoetherianRing (hA : IsAffinoidAlgebra K A) : IsNoetherianRing A := by
  sorry

theorem isJacobsonRing (hA : IsAffinoidAlgebra K A) : IsJacobsonRing A := by
  sorry

/-- Nontriviality is necessary for the injective normalisation map. -/
theorem exists_finite_injective [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    ∃ (d : ℕ) (π : TateAlgebra K d →ₐ[K] A), Function.Injective π ∧
      (letI := π.toRingHom.toAlgebra; Module.Finite (TateAlgebra K d) A) := by
  sorry

theorem finite_residue (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) :
    FiniteDimensional K (A ⧸ x.asIdeal) := by
  sorry

/-- The domain hypothesis cannot be weakened to arbitrary reduced affinoids. -/
theorem height_eq_ringKrullDim_of_isDomain [IsDomain A]
    (hA : IsAffinoidAlgebra K A) (x : MaximalSpectrum A) :
    x.asIdeal.height = ringKrullDim A := by
  sorry

theorem weightedTate_isAffinoid_iff (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
    IsAffinoidAlgebra K (weightedTate K n ρ) ↔ ∀ i, IsStrictRadius K (ρ i) := by
  sorry

end Algebra

section Points

variable {A : Type*} [CommRing A] [Algebra K A]

/-- This raw value becomes an evaluation norm after finite-residue-field theorems. -/
def pointNorm (x : MaximalSpectrum A) (f : A) : ℝ :=
  letI := x.isMaximal
  letI := Ideal.Quotient.field x.asIdeal
  spectralNorm K (A ⧸ x.asIdeal) (Ideal.Quotient.mk x.asIdeal f)

/-- The real supremum has empty value zero; its boundedness is a separate target. -/
def supSeminorm (f : A) : ℝ := ⨆ x : MaximalSpectrum A, pointNorm K x f

theorem bddAbove_pointNorm (hA : IsAffinoidAlgebra K A) (f : A) :
    BddAbove (Set.range (fun x : MaximalSpectrum A ↦ pointNorm K x f)) := by
  sorry

theorem exists_pointNorm_eq_supSeminorm [Nontrivial A]
    (hA : IsAffinoidAlgebra K A) (f : A) :
    ∃ x : MaximalSpectrum A, pointNorm K x f = supSeminorm K f := by
  sorry

theorem supSeminorm_pow (hA : IsAffinoidAlgebra K A) (f : A) (n : ℕ) (hn : 0 < n) :
    supSeminorm K (f ^ n) = supSeminorm K f ^ n := by
  sorry

theorem supSeminorm_eq_zero_iff (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = 0 ↔ IsNilpotent f := by
  sorry

/-- One exponent for the whole affinoid, including elements of supremum zero. -/
theorem exists_uniform_valueGroup_exponent (hA : IsAffinoidAlgebra K A) :
    ∃ m : ℕ, 0 < m ∧ ∀ f : A, ∃ c : K, supSeminorm K f ^ m = ‖c‖ := by
  sorry

theorem supSeminorm_eq_zero_of_subsingleton [Subsingleton A] (f : A) :
    supSeminorm K f = 0 := by
  sorry

end Points

section Normed

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
  [IsUltrametricDist A] [CompleteSpace A]

theorem powerBounded_iff (hA : IsAffinoidAlgebra K A) (f : A) :
    Bornology.IsBounded (Set.range (fun n : ℕ ↦ f ^ n)) ↔ supSeminorm K f ≤ 1 := by
  sorry

theorem topologicallyNilpotent_iff (hA : IsAffinoidAlgebra K A) (f : A) :
    Filter.Tendsto (fun n : ℕ ↦ f ^ n) Filter.atTop (nhds 0) ↔ supSeminorm K f < 1 := by
  sorry

theorem banachFunctionAlgebra [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A,
      supSeminorm K f ≤ ‖f‖ ∧ ‖f‖ ≤ C * supSeminorm K f := by
  sorry

/-- The affinoid identification of the supplier's general ring-of-definition criterion.
The unit is an element of the ring of definition, not necessarily a scalar in K. -/
theorem mem_iff_supSeminorm_le_one_of_isReduced (hA : IsAffinoidAlgebra K A)
    (B : Subring A) (hBo : IsOpen (B : Set A)) (hBb : Bornology.IsBounded (B : Set A))
    (ϖ : B) (hϖu : IsUnit (ϖ : A))
    (hϖ : Filter.Tendsto (fun n : ℕ ↦ (ϖ : A) ^ n) Filter.atTop (nhds 0))
    (hred : IsReduced (B ⧸ Ideal.span {ϖ})) (f : A) :
    f ∈ B ↔ supSeminorm K f ≤ 1 := by
  sorry

end Normed

section IntegralModels

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Membership characterisation of the actual presentation ring; no norm instance is invented. -/
def IsPresentationRing {n : ℕ} (π : TateAlgebra K n →ₐ[K] A) (S : Subring A) : Prop :=
  ∀ a : A, a ∈ S ↔ ∃ t, gaussNorm K t ≤ 1 ∧ π t = a

theorem integral_iff_supSeminorm_le_one {n : ℕ} (π : TateAlgebra K n →ₐ[K] A)
    (hπ : Function.Surjective π) (S : Subring A) (hS : IsPresentationRing K π S) (a : A) :
    IsIntegral S a ↔ supSeminorm K a ≤ 1 := by
  sorry

/-- One finite submodule works uniformly for all small scalar elements of S. -/
theorem exists_fg_smul_le_of_presentation {n : ℕ} (π : TateAlgebra K n →ₐ[K] A)
    (hπ : Function.Surjective π) (S : Subring A) (hS : IsPresentationRing K π S)
    {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (N : Submodule S M) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ N' : Submodule S M, N'.FG ∧ N' ≤ N ∧
      ∀ s : S, (∃ c : K, ‖c‖ ≤ ε ∧ (s : A) = algebraMap K A c) →
        ∀ x ∈ N, s • x ∈ N' := by
  sorry

theorem isNoetherian_of_presentation_of_discrete
    (hK : ∃ ρ : ℝ, ρ < 1 ∧ ∀ c : K, ‖c‖ < 1 → ‖c‖ ≤ ρ)
    {n : ℕ} (π : TateAlgebra K n →ₐ[K] A) (hπ : Function.Surjective π)
    (S : Subring A) (hS : IsPresentationRing K π S) : IsNoetherianRing S := by
  sorry

end IntegralModels

section PrincipalFiltration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The actual image aN, not scalar multiplication of a predicate. -/
def scalarImage (a : R) (N : Submodule R M) : Submodule R M :=
  N.map (a • LinearMap.id)

/-- Algebraic cofinality once the geometric stable-filtration theorem is supplied.
The proper-cohomology theorem must separately prove stability and the uniform cokernel shift. -/
theorem stable_filtration_cofinal (a : R) (F : ℕ → Submodule R M)
    (hstable : ∃ d : ℕ, ∀ n, d ≤ n → F (n + 1) = scalarImage a (F n)) :
    ∃ d : ℕ, ∀ n, F (n + d) ≤ LinearMap.range ((a ^ n) • (LinearMap.id : M →ₗ[R] M)) := by
  sorry

end PrincipalFiltration

end

end TauCetiRoadmap.RigidAnalyticGeometry
