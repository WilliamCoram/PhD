import PhD.TateFredholm.Compact

/-!
# The model space, ON-able modules, property (Pr)
([Bel] Definitions II.1.5–II.1.6, Example II.1.7; [JN] Definition 2.1.5; blueprint
6.3–6.7.  See `Tate.lean` for the development's overview and dictionary.)

Definitional choice: as in [JN], (potentially) ON-able is *defined* by (isometric)
isomorphism to the model space; the `ONBasis`-structure formulation and the equivalence
between the two live in the Bellaïche blueprint file. -/

open Filter Topology
open scoped ZeroAtInfty

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

/-- The model Banach `R`-module `c_R(I)` of families tending to `0` cofinitely, with the
sup norm — realised as `C₀(Ix I, R)`. -/
def cSpace (I : Type*) : Type _ := C₀(Ix I, R)

@[inherit_doc] scoped notation "c(" I ", " R ")" => cSpace R I

namespace cSpace

variable {R}
variable {I J : Type*}

instance : NormedAddCommGroup c(I, R) :=
  inferInstanceAs (NormedAddCommGroup C₀(Ix I, R))

instance : Module R c(I, R) :=
  inferInstanceAs (Module R C₀(Ix I, R))

instance : CompleteSpace c(I, R) :=
  inferInstanceAs (CompleteSpace C₀(Ix I, R))

instance : FunLike c(I, R) I R :=
  inferInstanceAs (FunLike C₀(Ix I, R) (Ix I) R)

/-- The `R`-action is bounded (pointwise `norm_mul_le` + `norm_eq_iSup`). -/
instance : IsBoundedSMul R c(I, R) :=
  .of_norm_smul_le fun _ _ => by sorry

/-- Membership: the family tends to `0` along the cofinite filter. -/
theorem tendsto_cofinite (f : c(I, R)) : Tendsto (f : I → R) cofinite (𝓝 0) := by
  have h := (f : C₀(Ix I, R)).zero_at_infty'
  rwa [Filter.cocompact_eq_cofinite] at h

/-- The sup-norm formula `‖f‖ = ⨆ i, ‖f i‖`. -/
theorem norm_eq_iSup (f : c(I, R)) : ‖f‖ = ⨆ i : I, ‖f i‖ := by
  sorry

/-- The ultrametric inequality for the sup norm. -/
instance : IsUltrametricDist c(I, R) := by
  sorry

section single

variable [DecidableEq I]

/-- The canonical basis vector `eᵢ` scaled by `r`. -/
def single (i : I) (r : R) : c(I, R) :=
  ⟨⟨Pi.single (i : Ix I) r, continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_cofinite_ne (i : Ix I)] with j hj
    exact (Pi.single_eq_of_ne (M := fun _ : Ix I => R) hj r).symm⟩

@[simp] theorem single_apply_self (i : I) (r : R) : single i r i = r :=
  show Pi.single (M := fun _ : Ix I => R) i r i = r from Pi.single_eq_same _ _

theorem single_apply_of_ne {i j : I} (h : j ≠ i) (r : R) : single i r j = 0 :=
  show Pi.single (M := fun _ : Ix I => R) i r j = 0 from Pi.single_eq_of_ne h _

/-- `‖eᵢ‖ = 1` (uses `‖1‖ = 1`). -/
@[simp] theorem norm_single_one (i : I) : ‖single i (1 : R)‖ = 1 := by
  sorry

end single

end cSpace

section ONable

variable (M : Type*) [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- *ON-able*: `R`-linearly isometric to a model space ([JN] Definition 2.1.5; equivalent
to the `ONBasis` formulation of [Bel] Definition II.1.5 / blueprint 6.6 — see the
Bellaïche file's `isONable_iff`). -/
def IsONable : Prop :=
  ∃ s : Set M, Nonempty (M ≃ₗᵢ[R] c(s, R))

/-- *Potentially ON-able*: `R`-linearly homeomorphic to a model space (equivalently,
ON-able for an equivalent norm). -/
def IsPotentiallyONable : Prop :=
  ∃ s : Set M, Nonempty (M ≃L[R] c(s, R))

/-- *Property (Pr)*: a continuous direct summand of a model space (equivalently, of a
potentially ON-able module — [Bel] §II.1.6, [JN] Definition 2.1.5). -/
def HasPr : Prop :=
  ∃ (s : Set M) (ι : M →L[R] c(s, R)) (π : c(s, R) →L[R] M),
    π.comp ι = ContinuousLinearMap.id R M

variable {R M}

/-- ON-able ⟹ potentially ON-able. -/
theorem IsONable.isPotentiallyONable (h : IsONable R M) : IsPotentiallyONable R M := by
  obtain ⟨s, ⟨e⟩⟩ := h
  exact ⟨s, ⟨e.toContinuousLinearEquiv⟩⟩

/-- Potentially ON-able ⟹ (Pr). -/
theorem IsPotentiallyONable.hasPr (h : IsPotentiallyONable R M) : HasPr R M := by
  obtain ⟨s, ⟨e⟩⟩ := h
  refine ⟨s, (e : M →L[R] c(s, R)), (e.symm : c(s, R) →L[R] M), ?_⟩
  ext x
  simp

/-- Model spaces are ON-able (re-index along `i ↦ eᵢ`, injective since `1 ≠ 0`). -/
theorem isONable_cSpace {I : Type*} [DecidableEq I] : IsONable R c(I, R) := by
  sorry

end ONable

end TateFredholm

end
