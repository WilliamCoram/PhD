/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Universal

/-!
# Orthogonal, `t`-orthogonal and orthonormal families

A family `e : I → M` in a normed module over a nonarchimedean normed ring is *orthogonal* when
`‖∑ aᵢ eᵢ‖ = max ‖aᵢ eᵢ‖` for every finite combination, *`t`-orthogonal* (`0 < t ≤ 1`) when
`‖∑ aᵢ eᵢ‖ ≥ t · max ‖aᵢ eᵢ‖`, and *orthonormal* (`IsOrthonormalFamily`, in `Orthonormal.lean`)
when `‖eᵢ‖ = 1` and `‖∑ aᵢ eᵢ‖ = max ‖aᵢ‖`. Orthonormal implies orthogonal implies `t`-orthogonal;
an orthogonal family with nonzero members is linearly independent when the action is multiplicative;
the scaled family of an orthogonal family is orthogonal; and an orthonormal family in a Banach module
gives an isometric embedding of the model space. For an orthonormal basis the expansion coefficients
are continuous linear functionals, and the basis property is equivalent to Bellaïche's and Colmez's
formulation "every `x` has a unique expansion `∑' aᵢ • eᵢ` and `‖x‖ = sup ‖aᵢ‖`".

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, convention 5 and §2.2.1–2.2.2.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/Orthogonal.lean`.

## Main declarations

* `IsOrthogonalFamily`, `IsTOrthogonalFamily` — the predicates.
* `IsOrthonormalFamily.isOrthogonalFamily`, `IsOrthogonalFamily.isTOrthogonalFamily`,
  `IsOrthogonalFamily.linearIndependent`, `IsOrthogonalFamily.smul`.
* `IsOrthonormalFamily.linearIsometry` — the isometric embedding `C₀(I, R) →ₗᵢ[R] M`.
* `IsOrthonormalBasis.coeff`, `IsOrthonormalBasis.coeffCLM` — the expansion coefficients.
* `isOrthonormalBasis_iff` — the Bellaïche–Colmez formulation.
-/

open Filter Topology
open scoped ZeroAtInfty

section Defs

variable (R : Type*) [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M] {I : Type*}

/-- A family is **orthogonal** when every finite combination has norm the maximum of the norms of
its terms. Source: roadmap convention 5 ("*orthogonal* if `‖∑ aᵢ eᵢ‖ = max ‖aᵢ eᵢ‖` for every
finitely supported `a`"); Schneider §10 (the inequality (c) with `r = 1`). -/
def IsOrthogonalFamily (e : I → M) : Prop :=
  ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i • e i‖₊

/-- A family is **`t`-orthogonal** when every finite combination has norm at least `t` times the
maximum of the norms of its terms, stated termwise. Source: roadmap convention 5 ("for `0 < t ≤ 1`
it is *`t`-orthogonal* if `‖∑ aᵢ eᵢ‖ ≥ t · max ‖aᵢ eᵢ‖`"); Schneider §10, Prop 10.4 (c). -/
def IsTOrthogonalFamily (t : ℝ) (e : I → M) : Prop :=
  ∀ (s : Finset I) (a : I → R), ∀ i ∈ s, t * ‖a i • e i‖ ≤ ‖∑ j ∈ s, a j • e j‖

end Defs

section Basic

variable {R : Type*} [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M] {I : Type*}
  {e : I → M}

theorem IsOrthonormalFamily.exists_bound (he : IsOrthonormalFamily R e) : ∃ C, ∀ i, ‖e i‖ ≤ C :=
  ⟨1, fun i ↦ (he.1 i).le⟩

/-- Source: roadmap §2.2.1 ("orthonormal implies orthogonal"). -/
theorem IsOrthonormalFamily.isOrthogonalFamily (he : IsOrthonormalFamily R e) :
    IsOrthogonalFamily R e := by
  sorry

/-- Source: roadmap §2.2.1 ("orthogonal implies `t`-orthogonal"). -/
theorem IsOrthogonalFamily.isTOrthogonalFamily (he : IsOrthogonalFamily R e) {t : ℝ}
    (ht : t ≤ 1) : IsTOrthogonalFamily R t e := by
  sorry

/-- In an orthogonal family each term of a finite combination is bounded by the combination. -/
theorem IsOrthogonalFamily.norm_smul_le_norm_sum (he : IsOrthogonalFamily R e) (s : Finset I)
    (a : I → R) {i : I} (hi : i ∈ s) : ‖a i • e i‖ ≤ ‖∑ j ∈ s, a j • e j‖ := by
  sorry

/-- An orthogonal family with nonzero members is linearly independent when the action is
multiplicative. Source: roadmap §2.2.1 ("an orthogonal family with nonzero members is linearly
independent") — ⚠ over a ring the multiplicativity `‖a • m‖ = ‖a‖ ‖m‖` is needed, since
`a • eᵢ = 0` with `eᵢ ≠ 0` does not force `a = 0` (plan erratum E21). -/
theorem IsOrthogonalFamily.linearIndependent [NormSMulClass R M] (he : IsOrthogonalFamily R e)
    (h0 : ∀ i, e i ≠ 0) : LinearIndependent R e := by
  sorry

/-- A `t`-orthogonal family (`t > 0`) with nonzero members is linearly independent when the action
is multiplicative. Source: Schneider §10, Prop 10.4 (a)–(c). -/
theorem IsTOrthogonalFamily.linearIndependent [NormSMulClass R M] {t : ℝ} (ht : 0 < t)
    (he : IsTOrthogonalFamily R t e) (h0 : ∀ i, e i ≠ 0) : LinearIndependent R e := by
  sorry

/-- The scaled family of an orthogonal family is orthogonal. Source: roadmap §2.2.1 ("the scaled
family `aᵢ • eᵢ` of an orthogonal family is orthogonal"); Schneider §10 ("We obviously can scale
the vectors `vₙ` without changing the properties"). -/
theorem IsOrthogonalFamily.smul (he : IsOrthogonalFamily R e) (a : I → R) :
    IsOrthogonalFamily R fun i ↦ a i • e i := by
  sorry

/-- The scaled family of a `t`-orthogonal family is `t`-orthogonal. Source: Schneider §10 ("We
obviously can scale the vectors `vₙ` without changing the properties (a) and (b) and hence (c)"). -/
theorem IsTOrthogonalFamily.smul {t : ℝ} (he : IsTOrthogonalFamily R t e) (a : I → R) :
    IsTOrthogonalFamily R t fun i ↦ a i • e i := by
  sorry

/-- An orthonormal family reindexed by a bijection is orthonormal. -/
theorem IsOrthonormalFamily.comp_equiv {J : Type*} (he : IsOrthonormalFamily R e) (σ : J ≃ I) :
    IsOrthonormalFamily R (e ∘ σ) := by
  sorry

/-- An orthonormal basis reindexed by a bijection is an orthonormal basis. Source: roadmap §2.7.2
("after a reindexing by a bijection of `ℕ`"). -/
theorem IsOrthonormalBasis.comp_equiv {J : Type*} (he : IsOrthonormalBasis R e) (σ : J ≃ I) :
    IsOrthonormalBasis R (e ∘ σ) := by
  sorry

end Basic

section Isometry

open ZeroAtInftyContinuousMap

variable {R : Type*} [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M] {I : Type*} [TopologicalSpace I]
  [DiscreteTopology I] {e : I → M}

/-- The map `a ↦ ∑' aᵢ • eᵢ` out of the model space is norm-preserving for an orthonormal family.
Source: roadmap §2.2.1 ("for an orthonormal family the map `C₀(I, R) → M`, `a ↦ ∑' aᵢ • eᵢ` is an
isometric embedding"); Schneider §10, Prop 10.1 ("A continuity argument now shows that we have
`‖f()‖ = ‖‖_∞`"). -/
theorem IsOrthonormalFamily.norm_ofBounded_apply (he : IsOrthonormalFamily R e) (f : C₀(I, R)) :
    ‖ofBounded R e he.exists_bound f‖ = ‖f‖ := by
  sorry

/-- The isometric embedding of the model space given by an orthonormal family. -/
noncomputable def IsOrthonormalFamily.linearIsometry (he : IsOrthonormalFamily R e) :
    C₀(I, R) →ₗᵢ[R] M :=
  ⟨(ofBounded R e he.exists_bound : C₀(I, R) →ₗ[R] M), he.norm_ofBounded_apply⟩

@[simp]
theorem IsOrthonormalFamily.linearIsometry_apply (he : IsOrthonormalFamily R e) (f : C₀(I, R)) :
    he.linearIsometry f = ∑' i, f i • e i := rfl

theorem IsOrthonormalFamily.linearIsometry_single [DecidableEq I] (he : IsOrthonormalFamily R e)
    (i : I) : he.linearIsometry (single i 1) = e i := by
  sorry

end Isometry

section Coeff

variable {R : Type*} [NormedRing R] [CompleteSpace R] {M : Type*} [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M] {I : Type*}
  {e : I → M}

/-- Every vector of a Banach module over a Banach ring has an expansion in an orthonormal basis:
the ring form of `IsOrthonormalBasis.exists_hasSum`. Source: Bosch 1.3/5 (ii); Bellaïche,
Definition II.1.5. -/
theorem IsOrthonormalBasis.exists_hasSum' (he : IsOrthonormalBasis R e) (x : M) :
    ∃ a : I → R, HasSum (fun i ↦ a i • e i) x := by
  sorry

/-- The expansion coefficients of `x` in an orthonormal basis. Source: roadmap §2.2.2 ("every `x`
has a unique expansion `x = ∑' aᵢ • eᵢ`"). -/
noncomputable def IsOrthonormalBasis.coeff (he : IsOrthonormalBasis R e) (x : M) : I → R :=
  Classical.choose (he.exists_hasSum' x)

theorem IsOrthonormalBasis.hasSum_coeff (he : IsOrthonormalBasis R e) (x : M) :
    HasSum (fun i ↦ he.coeff x i • e i) x :=
  Classical.choose_spec (he.exists_hasSum' x)

/-- Uniqueness of the expansion. Source: roadmap §2.2.2 ("a unique expansion"). -/
theorem IsOrthonormalBasis.coeff_eq_of_hasSum (he : IsOrthonormalBasis R e) {a : I → R} {x : M}
    (ha : HasSum (fun i ↦ a i • e i) x) : he.coeff x = a := by
  sorry

theorem IsOrthonormalBasis.tendsto_coeff (he : IsOrthonormalBasis R e) (x : M) :
    Tendsto (he.coeff x) cofinite (𝓝 0) := by
  sorry

theorem IsOrthonormalBasis.norm_coeff_le (he : IsOrthonormalBasis R e) (x : M) (i : I) :
    ‖he.coeff x i‖ ≤ ‖x‖ := by
  sorry

/-- The norm of a convergent expansion is the supremum of the norms of its coefficients. Source:
roadmap §2.2.2 ("and then `‖x‖ = sup ‖aᵢ‖`"); Bellaïche, Definition II.1.5 (ii). -/
theorem IsOrthonormalBasis.norm_eq_iSup_of_hasSum (he : IsOrthonormalBasis R e) {a : I → R} {x : M}
    (ha : HasSum (fun i ↦ a i • e i) x) : ‖x‖ = ⨆ i, ‖a i‖ := by
  sorry

theorem IsOrthonormalBasis.norm_eq_iSup_coeff (he : IsOrthonormalBasis R e) (x : M) :
    ‖x‖ = ⨆ i, ‖he.coeff x i‖ :=
  he.norm_eq_iSup_of_hasSum (he.hasSum_coeff x)

/-- The `i`-th expansion coefficient, as a continuous linear functional of norm at most `1`.
Source: roadmap §2.2.2 ("the expansion coefficients are continuous linear functionals"). -/
noncomputable def IsOrthonormalBasis.coeffCLM (he : IsOrthonormalBasis R e) (i : I) : M →L[R] R :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ he.coeff x i
      map_add' := by sorry
      map_smul' := by sorry }
    1 (fun x ↦ by rw [one_mul]; exact he.norm_coeff_le x i)

@[simp]
theorem IsOrthonormalBasis.coeffCLM_apply (he : IsOrthonormalBasis R e) (i : I) (x : M) :
    he.coeffCLM i x = he.coeff x i := rfl

/-- The converse: a family such that every vector has an expansion whose norm is the supremum of
the coefficients is an orthonormal basis. Source: roadmap §2.2.2 ("Prove the equivalent
formulations"); Bellaïche, Definition II.1.5. -/
theorem isOrthonormalBasis_of_forall_hasSum [NormOneClass R]
    (h₁ : ∀ x : M, ∃ a : I → R, HasSum (fun i ↦ a i • e i) x)
    (h₂ : ∀ (a : I → R) (x : M), HasSum (fun i ↦ a i • e i) x → ‖x‖ = ⨆ i, ‖a i‖) :
    IsOrthonormalBasis R e := by
  sorry

/-- **Bellaïche's and Colmez's formulation of an orthonormal basis.** Source: roadmap §2.2.2;
Bellaïche, Definition II.1.5; Colmez, Définition 1.1.3. -/
theorem isOrthonormalBasis_iff [NormOneClass R] :
    IsOrthonormalBasis R e ↔ (∀ x : M, ∃ a : I → R, HasSum (fun i ↦ a i • e i) x) ∧
      ∀ (a : I → R) (x : M), HasSum (fun i ↦ a i • e i) x → ‖x‖ = ⨆ i, ‖a i‖ :=
  ⟨fun he ↦ ⟨he.exists_hasSum', fun _ _ ha ↦ he.norm_eq_iSup_of_hasSum ha⟩,
    fun h ↦ isOrthonormalBasis_of_forall_hasSum h.1 h.2⟩

end Coeff

theorem IsOrthonormalFamily.norm_le_one {R : Type*} [NormedRing R] {M : Type*}
    [NormedAddCommGroup M] [Module R M] {I : Type*} {e : I → M} (he : IsOrthonormalFamily R e)
    (i : I) : ‖e i‖ ≤ 1 :=
  (he.1 i).le
