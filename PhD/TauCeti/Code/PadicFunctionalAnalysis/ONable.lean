/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.Topology.MetricSpace.Ultra.Pi
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthogonal
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Reindex
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Truncation
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.OpenMapping
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Finite

/-!
# Orthonormalisable modules and the property (Pr)

A normed module `M` over a nonarchimedean normed ring `R` is *orthonormalisable* (`IsONable R M`)
when it is isometrically isomorphic to a model space `C₀(I, R)`, *potentially orthonormalisable*
(`IsPotentiallyONable R M`) when it is continuously linearly isomorphic to one, and has *property
(Pr)* (`HasPr R M`) when it is a retract (equivalently, a closed direct summand) of a model space
— Johansson–Newton's definitions, with the index set in the universe of `M` (roadmap convention 4).
`M` is orthonormalisable exactly when it has an orthonormal basis (§2.2.3), the three notions are
stable under reindexing, finite products and `C₀(J, −)`, a closed direct summand of a potentially
orthonormalisable module has (Pr), (Pr) is the lifting property against continuous surjections of
Banach modules (Bellaïche, Exercise II.1.19), and a finitely generated module with (Pr) is
projective (Bellaïche, Proposition II.1.20). For an orthonormal basis `e` and `S ⊆ I`, the closed
span of `e|_S` is a closed direct summand with a projection of norm at most `1` (§2.2.5).

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, convention 4, §2.2.3–2.2.5.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/ONable.lean`.

## Main declarations

* `Module.IsONable`, `Module.IsPotentiallyONable`, `Module.HasPr`.
* `Module.isONable_zeroAtInfty`, `isOrthonormalBasis_single` — the model space with its canonical
  basis.
* `IsOrthonormalBasis.linearIsometryEquiv`, `Module.isONable_iff_exists_isOrthonormalBasis` — the
  dictionary between isometries and bases.
* `Module.HasPr.exists_lift`, `Module.hasPr_iff_forall_exists_lift`, `Module.HasPr.projective`.
* `IsOrthonormalBasis.closedComplemented_topologicalClosure_span`,
  `IsOrthonormalBasis.exists_projection` — orthogonal complements.
-/

universe u v w

open Filter Topology Function
open scoped ZeroAtInfty ContinuousLinearMap.Ultra
open ZeroAtInftyContinuousMap NormedRing

namespace Module

section Defs

variable (R : Type u) (M : Type v) [NormedRing R] [NormedAddCommGroup M] [Module R M]

/-- **Orthonormalisable**: isometrically isomorphic to a model space `C₀(I, R)`, for an index type
in the universe of `M`. Source: roadmap convention 4 ("`IsONable R M` is the existence of an
`R`-linear isometric isomorphism `M ≃ₗᵢ[R] C₀(I, R)` for some `I`"); Johansson–Newton, Definition
2.1.5 ("`M` is orthonormalisable if there is an isometric isomorphism `M ≅ c(I, A)`"). -/
def IsONable : Prop :=
  ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I), Nonempty (M ≃ₗᵢ[R] C₀(I, R))

/-- **Potentially orthonormalisable**: continuously linearly isomorphic to a model space. Source:
roadmap convention 4; Johansson–Newton, Definition 2.1.5 ("potentially orthonormalisable if there
is a continuous isomorphism `M ≅ c(I, A)`"). -/
def IsPotentiallyONable : Prop :=
  ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I), Nonempty (M ≃L[R] C₀(I, R))

/-- **Property (Pr)**: a retract of a model space, i.e. a direct summand of a potentially
orthonormalisable module (`HasPr.exists_closedComplemented`, `Submodule.ClosedComplemented.hasPr`).
Source: roadmap convention 4 ("`HasPr R M` is 'a direct summand of a potentially orthonormalisable
module'"); Bellaïche, Definition II.1.6 ("`M` satisfies (Pr) if it is a direct summand of a
potentially orthonormalisable module"). -/
def HasPr : Prop :=
  ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I) (ι : M →L[R] C₀(I, R))
    (π : C₀(I, R) →L[R] M), π.comp ι = ContinuousLinearMap.id R M

end Defs

section Basic

variable {R : Type u} {M : Type v} [NormedRing R] [NormedAddCommGroup M] [Module R M]

/-- Source: roadmap §2.2.3 ("the implications `IsONable → IsPotentiallyONable → HasPr`"). -/
theorem IsONable.isPotentiallyONable (h : IsONable R M) : IsPotentiallyONable R M := by
  sorry

/-- Source: roadmap §2.2.3. -/
theorem IsPotentiallyONable.hasPr (h : IsPotentiallyONable R M) : HasPr R M := by
  sorry

theorem IsONable.hasPr (h : IsONable R M) : HasPr R M :=
  h.isPotentiallyONable.hasPr

/-- The model space is orthonormalisable, by reindexing along `ULift`. Source: roadmap §2.2.3
("`C₀(I, R)` is ON-able with the canonical basis"). -/
theorem isONable_zeroAtInfty (R : Type u) [NormedRing R] (I : Type w) [TopologicalSpace I]
    [DiscreteTopology I] : IsONable R C₀(I, R) := by
  sorry

variable {N : Type v} [NormedAddCommGroup N] [Module R N]

/-- Source: roadmap §2.2.3 ("stable under reindexing"). -/
theorem IsONable.of_linearIsometryEquiv (e : M ≃ₗᵢ[R] N) (h : IsONable R M) : IsONable R N := by
  sorry

/-- Source: roadmap §2.2.3 ("stable under … bounded-equivalent norms (potentially ON-able and
(Pr) only)"): an equivalent norm is a continuous linear equivalence with the renormed module. -/
theorem IsPotentiallyONable.of_continuousLinearEquiv (e : M ≃L[R] N)
    (h : IsPotentiallyONable R M) : IsPotentiallyONable R N := by
  sorry

/-- Source: roadmap §2.2.3. -/
theorem HasPr.of_continuousLinearEquiv (e : M ≃L[R] N) (h : HasPr R M) : HasPr R N := by
  sorry

/-- Source: roadmap §2.2.3 ("stable under … finite products"); the model-space identity is
`ZeroAtInftyContinuousMap.sumEquiv`. -/
theorem IsONable.prod (hM : IsONable R M) (hN : IsONable R N) : IsONable R (M × N) := by
  sorry

/-- Source: roadmap §2.2.3. -/
theorem IsPotentiallyONable.prod (hM : IsPotentiallyONable R M) (hN : IsPotentiallyONable R N) :
    IsPotentiallyONable R (M × N) := by
  sorry

/-- Source: roadmap §2.2.3. -/
theorem HasPr.prod (hM : HasPr R M) (hN : HasPr R N) : HasPr R (M × N) := by
  sorry

variable [IsBoundedSMul R M] (J : Type v) [TopologicalSpace J] [DiscreteTopology J]

/-- Source: roadmap §2.2.3 ("stable under … `C₀(J, −)`"); the model-space identity is
`ZeroAtInftyContinuousMap.prodEquiv`. -/
theorem IsONable.zeroAtInfty (h : IsONable R M) : IsONable R C₀(J, M) := by
  sorry

/-- Source: roadmap §2.2.3. -/
theorem IsPotentiallyONable.zeroAtInfty [NormOneClass R] [IsTate R] (h : IsPotentiallyONable R M) :
    IsPotentiallyONable R C₀(J, M) := by
  sorry

/-- Source: roadmap §2.2.3. -/
theorem HasPr.zeroAtInfty [NormOneClass R] [IsTate R] (h : HasPr R M) : HasPr R C₀(J, M) := by
  sorry

end Basic

end Module

/-! ### Isometries to the model space and orthonormal bases -/

section Basis

open Module

variable {R : Type u} {M : Type v} [NormedRing R] [NormedAddCommGroup M] [Module R M]
  {I : Type w} [TopologicalSpace I] [DiscreteTopology I]

/-- The coordinate vectors form an orthonormal basis of the model space. Source: roadmap §2.2.3
("`C₀(I, R)` is ON-able with the canonical basis"), Examples ("`C₀(ℕ, ℚ_p)` with its canonical
basis"). -/
theorem isOrthonormalBasis_single [NormOneClass R] [DecidableEq I] :
    IsOrthonormalBasis R fun i : I ↦ single i (1 : R) := by
  sorry

/-- The image of the canonical basis under an isometry to the model space is an orthonormal basis.
Source: roadmap §2.2.3 ("an isometry `M ≃ₗᵢ C₀(I, R)` corresponds to the basis
`i ↦ e⁻¹ (single i 1)`"). -/
theorem LinearIsometryEquiv.isOrthonormalBasis_symm_single [NormOneClass R] [DecidableEq I]
    (e : M ≃ₗᵢ[R] C₀(I, R)) : IsOrthonormalBasis R fun i ↦ e.symm (single i 1) := by
  sorry

/-- An orthonormal family is injective: `eᵢ = eⱼ` with `i ≠ j` would give the combination
`eᵢ - eⱼ = 0` of sup norm `‖1‖ = 1`. -/
theorem IsOrthonormalFamily.injective [NormOneClass R] {e : I → M} (he : IsOrthonormalFamily R e) :
    Injective e := by
  sorry

variable [CompleteSpace R] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M] {e : I → M}

/-- The isometric embedding given by an orthonormal basis is onto: every vector is the sum of its
expansion, whose coefficients tend to `0`. Source: roadmap §2.2.3; Schneider §10, Prop 10.1 ("For
the surjectivity of `f` it therefore suffices to show that the vector subspace `V₀` is dense"). -/
theorem IsOrthonormalBasis.surjective_linearIsometry (he : IsOrthonormalBasis R e) :
    Surjective he.1.linearIsometry := by
  sorry

/-- The isometric isomorphism `C₀(I, R) ≃ₗᵢ[R] M` given by an orthonormal basis. Source: roadmap
§2.2.3 ("`IsONable R M ↔ ∃ (I : Type) (e : I → M), IsOrthonormalBasis e`"). -/
noncomputable def IsOrthonormalBasis.linearIsometryEquiv (he : IsOrthonormalBasis R e) :
    C₀(I, R) ≃ₗᵢ[R] M :=
  LinearIsometryEquiv.ofSurjective he.1.linearIsometry he.surjective_linearIsometry

@[simp]
theorem IsOrthonormalBasis.linearIsometryEquiv_apply (he : IsOrthonormalBasis R e) (f : C₀(I, R)) :
    he.linearIsometryEquiv f = ∑' i, f i • e i := rfl

theorem IsOrthonormalBasis.linearIsometryEquiv_single [DecidableEq I] (he : IsOrthonormalBasis R e)
    (i : I) : he.linearIsometryEquiv (single i 1) = e i :=
  he.1.linearIsometry_single i

/-- A module with an orthonormal basis, indexed by a type in any universe, is orthonormalisable:
reindex along the range of the basis. Source: roadmap §2.2.3. -/
theorem IsOrthonormalBasis.isONable [NormOneClass R] (he : IsOrthonormalBasis R e) :
    IsONable R M := by
  sorry

/-- **Orthonormalisable means having an orthonormal basis.** Source: roadmap §2.2.3
("`IsONable R M ↔ ∃ (I : Type) (e : I → M), IsOrthonormalBasis e`"). -/
theorem Module.isONable_iff_exists_isOrthonormalBasis [NormOneClass R] :
    IsONable R M ↔ ∃ (I : Type v) (e : I → M), IsOrthonormalBasis R e := by
  sorry

end Basis

/-! ### Closed direct summands -/

section Complemented

open Module

variable {R : Type u} {M : Type v} [NormedRing R] [NormedAddCommGroup M] [Module R M]

/-- A closed direct summand of a potentially orthonormalisable module has (Pr). Source: roadmap
§2.2.3 ("a closed direct summand of a potentially ON-able module has (Pr)"); Bellaïche, Definition
II.1.6. -/
theorem Submodule.ClosedComplemented.hasPr (hM : IsPotentiallyONable R M) {p : Submodule R M}
    (hp : p.ClosedComplemented) : HasPr R p := by
  sorry

/-- A module with (Pr) is a closed direct summand of a model space. Source: Bellaïche, Definition
II.1.6; roadmap convention 4. -/
theorem Module.HasPr.exists_closedComplemented (h : HasPr R M) :
    ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I) (p : Submodule R C₀(I, R)),
      p.ClosedComplemented ∧ Nonempty (M ≃L[R] p) := by
  sorry

variable [CompleteSpace R] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]
  {I : Type w} [TopologicalSpace I] [DiscreteTopology I] {e : I → M}

/-- For an orthonormal basis `e` and `S ⊆ I`, the closed span of `e|_S` is a closed direct summand.
Source: roadmap §2.2.5 ("the closed span of `e|_S` is a closed direct summand"). -/
theorem IsOrthonormalBasis.closedComplemented_topologicalClosure_span (he : IsOrthonormalBasis R e)
    (S : Set I) : (Submodule.span R (e '' S)).topologicalClosure.ClosedComplemented := by
  sorry

/-- The projection onto the closed span of `e|_S` of norm at most `1`: the truncation to `S`
transported along the isometry. Source: roadmap §2.2.5 ("with the projection `π_S` of norm at most
`1`"). -/
theorem IsOrthonormalBasis.exists_projection (he : IsOrthonormalBasis R e) (S : Set I) :
    ∃ π : M →L[R] M, (∀ x, ‖π x‖ ≤ ‖x‖) ∧
      (∀ x, π x ∈ (Submodule.span R (e '' S)).topologicalClosure) ∧
      ∀ x ∈ (Submodule.span R (e '' S)).topologicalClosure, π x = x := by
  sorry

/-- Source: roadmap §2.2.5 ("and `M ≅ C₀(S, R) × C₀(I ∖ S, R)`"). -/
theorem IsOrthonormalBasis.nonempty_linearIsometryEquiv_prod (he : IsOrthonormalBasis R e)
    (S : Set I) [DecidablePred (· ∈ S)] :
    Nonempty (M ≃ₗᵢ[R] C₀(S, R) × C₀((Sᶜ : Set I), R)) := by
  sorry

end Complemented

/-! ### The lifting characterisation of (Pr) -/

section Lifting

open Module

variable {R : Type u} [NormedRing R] [NormOneClass R] [IsTate R] {M : Type v}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {N N' : Type*} [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [IsUltrametricDist N]
  [CompleteSpace N] [NormedAddCommGroup N'] [Module R N'] [IsBoundedSMul R N'] [CompleteSpace N']

/-- The model space has the lifting property: lift the images of the coordinate vectors with the
bounds of the open mapping theorem and assemble by the universal property. Source: Bellaïche,
Exercise II.1.19 (the model-space case); roadmap §2.2.4. -/
theorem ZeroAtInftyContinuousMap.exists_lift {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    (u : N →L[R] N') (hu : Surjective u) (v : C₀(I, R) →L[R] N') :
    ∃ w : C₀(I, R) →L[R] N, u.comp w = v := by
  sorry

/-- A module with (Pr) has the lifting property. Source: roadmap §2.2.4 ("`P` has property (Pr)
if and only if every continuous surjection `M → N` of Banach modules and every continuous map
`P → N` admit a continuous lift `P → M`"), the "only if"; Bellaïche, Exercise II.1.19. -/
theorem Module.HasPr.exists_lift (hM : HasPr R M) (u : N →L[R] N') (hu : Surjective u)
    (v : M →L[R] N') : ∃ w : M →L[R] N, u.comp w = v := by
  sorry

/-- Every Banach module is a quotient of a model space: the universal property applied to the
family of all elements of the unit ball, which generates by the scaling trick. Source: roadmap
§2.2.4 (the "if" direction needs a surjection from a model space); Johansson–Newton §2.1. -/
theorem Module.exists_surjective_zeroAtInfty [IsUltrametricDist M] [CompleteSpace M] :
    ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I) (u : C₀(I, R) →L[R] M),
      Surjective u := by
  sorry

/-- A Banach module with the lifting property has (Pr): lift the identity along a surjection from
a model space. Source: roadmap §2.2.4, the "if"; Bellaïche, Exercise II.1.19. -/
theorem Module.hasPr_of_forall_exists_lift [IsUltrametricDist M] [CompleteSpace M]
    (h : ∀ (N : Type (max u v)) (N' : Type v) [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
      [IsUltrametricDist N] [CompleteSpace N] [NormedAddCommGroup N'] [Module R N']
      [IsBoundedSMul R N'] [CompleteSpace N'] (u : N →L[R] N'), Surjective u →
      ∀ v : M →L[R] N', ∃ w : M →L[R] N, u.comp w = v) : HasPr R M := by
  sorry

/-- **The lifting characterisation of (Pr).** Source: roadmap §2.2.4; Bellaïche, Exercise
II.1.19. -/
theorem Module.hasPr_iff_forall_exists_lift [IsUltrametricDist M] [CompleteSpace M] :
    HasPr R M ↔ ∀ (N : Type (max u v)) (N' : Type v) [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
      [IsUltrametricDist N] [CompleteSpace N] [NormedAddCommGroup N'] [Module R N']
      [IsBoundedSMul R N'] [CompleteSpace N'] (u : N →L[R] N'), Surjective u →
      ∀ v : M →L[R] N', ∃ w : M →L[R] N, u.comp w = v :=
  ⟨fun h _ _ _ _ _ _ _ _ _ _ _ u hu v ↦ h.exists_lift u hu v, hasPr_of_forall_exists_lift⟩

/-- A finitely generated Banach module with (Pr) is projective: the surjection from a finite free
module is continuous, so the identity lifts along it and splits it. Source: roadmap §2.2.4 ("a
finitely generated module with (Pr) is projective"); Bellaïche, Proposition II.1.20. -/
theorem Module.HasPr.projective [CompleteSpace R] [IsUltrametricDist R] [IsUltrametricDist M]
    [CompleteSpace M] [Module.Finite R M] (hM : HasPr R M) : Module.Projective R M := by
  sorry

end Lifting
