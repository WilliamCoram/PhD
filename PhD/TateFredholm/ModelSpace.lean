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

/-- Membership: the family tends to `0` along the cofinite filter. -/
theorem tendsto_cofinite (f : c(I, R)) : Tendsto (f : I → R) cofinite (𝓝 0) := by
  have h := (f : C₀(Ix I, R)).zero_at_infty'
  rwa [Filter.cocompact_eq_cofinite] at h

/-- The sup-norm formula `‖f‖ = ⨆ i, ‖f i‖`. -/
theorem norm_eq_iSup (f : c(I, R)) : ‖f‖ = ⨆ i : I, ‖f i‖ :=
  BoundedContinuousFunction.norm_eq_iSup_norm ((f : C₀(Ix I, R)).toBCF)

/-- Coordinate evaluation is norm-nonincreasing. -/
theorem norm_apply_le (f : c(I, R)) (i : I) : ‖f i‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_coe_le_norm ((f : C₀(Ix I, R)).toBCF) i

/-- Coordinate evaluation `f ↦ f j` as a continuous `R`-linear map `c(I, R) →L[R] R`.
(Addition and scalar multiplication are pointwise on `C₀`, hence definitional; continuity
is the `1`-Lipschitz estimate `norm_apply_le`.) -/
def evalCLM (j : I) : c(I, R) →L[R] R where
  toFun f := f j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
    calc dist (f j) (g j) = ‖f j - g j‖ := dist_eq_norm _ _
    _ = ‖(f - g) j‖ := rfl
    _ ≤ ‖f - g‖ := norm_apply_le (f - g) j
    _ = 1 * dist f g := by rw [one_mul, dist_eq_norm]

@[simp] theorem evalCLM_apply (j : I) (f : c(I, R)) : evalCLM j f = f j := rfl

/-- The `R`-action is bounded (pointwise `norm_mul_le` + `norm_eq_iSup`). -/
instance : IsBoundedSMul R c(I, R) :=
  .of_norm_smul_le fun r f => by
    rcases isEmpty_or_nonempty I with hI | hI
    · rw [norm_eq_iSup, Real.iSup_of_isEmpty]
      positivity
    · rw [norm_eq_iSup]
      refine ciSup_le fun i => ?_
      calc ‖(r • f) i‖ = ‖r * f i‖ := rfl
      _ ≤ ‖r‖ * ‖f i‖ := norm_mul_le _ _
      _ ≤ ‖r‖ * ‖f‖ := mul_le_mul_of_nonneg_left (norm_apply_le f i) (norm_nonneg r)

/-- The ultrametric inequality for the sup norm. -/
instance : IsUltrametricDist c(I, R) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g => ?_
  rcases isEmpty_or_nonempty I with hI | hI
  · rw [norm_eq_iSup, Real.iSup_of_isEmpty]
    exact le_max_of_le_left (norm_nonneg f)
  · rw [norm_eq_iSup]
    refine ciSup_le fun i => ?_
    calc ‖(f + g) i‖ = ‖f i + g i‖ := rfl
    _ ≤ max ‖f i‖ ‖g i‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max ‖f‖ ‖g‖ := max_le_max (norm_apply_le f i) (norm_apply_le g i)

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
  have : Nonempty I := ⟨i⟩
  rw [norm_eq_iSup]
  refine le_antisymm (ciSup_le fun j => ?_) ?_
  · rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [single_apply_of_ne hj, zero_le_one]
  · have hb : BddAbove (Set.range fun j => ‖single i (1 : R) j‖) := by
      refine ⟨1, ?_⟩
      rintro y ⟨j, rfl⟩
      rcases eq_or_ne j i with rfl | hj
      · simp
      · simp [single_apply_of_ne hj, zero_le_one]
    simpa using le_ciSup hb i

/-- Every element of the model space is the (unconditional) sum of the coordinate multiples
of the canonical basis vectors: `f = ∑' i, f i • eᵢ`. -/
theorem hasSum_single (f : c(I, R)) : HasSum (fun i => f i • single i (1 : R)) f := by
  have hsummable : Summable fun i => f i • single i (1 : R) := by
    refine summable_of_tendsto_cofinite
      (squeeze_zero_norm (a := fun i => ‖f i‖) (fun i => ?_) ?_)
    · calc ‖f i • single i (1 : R)‖ ≤ ‖f i‖ * ‖single i (1 : R)‖ := norm_smul_le _ _
      _ = ‖f i‖ := by rw [norm_single_one, mul_one]
    · simpa using (tendsto_cofinite f).norm
  have key : ∑' i, f i • single i (1 : R) = f := by
    refine DFunLike.ext _ _ fun j => ?_
    have hlhs : (∑' i, f i • single i (1 : R)) j = ∑' i, f i • single i (1 : R) j := by
      simpa only [evalCLM_apply, map_smul] using
        ContinuousLinearMap.map_tsum (evalCLM j) hsummable
    rw [hlhs, tsum_eq_single j (fun i hij => by
      simp [single_apply_of_ne (Ne.symm hij)]), single_apply_self, smul_eq_mul, mul_one]
  have hHS := hsummable.hasSum
  rwa [key] at hHS

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
  have : Nontrivial R := NormOneClass.nontrivial
  set e : I → c(I, R) := fun i => cSpace.single i 1 with he
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    have h1 : e i i = 1 := cSpace.single_apply_self i 1
    have h0 : e j i = 0 := cSpace.single_apply_of_ne hne 1
    rw [hij, h0] at h1
    exact zero_ne_one h1
  set σ : I ≃ Set.range e := Equiv.ofInjective e hinj with hσ
  have hσc : Tendsto (σ.symm : Set.range e → I) cofinite cofinite :=
    σ.symm.injective.tendsto_cofinite
  have hσc' : Tendsto (σ : I → Set.range e) cofinite cofinite :=
    σ.injective.tendsto_cofinite
  -- the two reindexing maps, as `C₀` functions on the discrete index types
  set F : c(I, R) → c((Set.range e : Set (c(I, R))), R) := fun g =>
    ⟨⟨fun x => g (σ.symm x), continuous_of_discreteTopology⟩, by
      rw [Filter.cocompact_eq_cofinite]
      exact (cSpace.tendsto_cofinite g).comp hσc⟩ with hF
  set G : c((Set.range e : Set (c(I, R))), R) → c(I, R) := fun h =>
    ⟨⟨fun i => h (σ i), continuous_of_discreteTopology⟩, by
      rw [Filter.cocompact_eq_cofinite]
      exact (cSpace.tendsto_cofinite h).comp hσc'⟩ with hG
  have iso : c(I, R) ≃ₗᵢ[R] c((Set.range e : Set (c(I, R))), R) :=
    { toFun := F
      invFun := G
      map_add' := fun g h => DFunLike.ext _ _ fun x => rfl
      map_smul' := fun r g => DFunLike.ext _ _ fun x => rfl
      left_inv := fun g => DFunLike.ext _ _ fun i => congrArg g (Equiv.symm_apply_apply σ i)
      right_inv := fun h => DFunLike.ext _ _ fun x => congrArg h (Equiv.apply_symm_apply σ x)
      norm_map' := fun g => by
        rw [cSpace.norm_eq_iSup, cSpace.norm_eq_iSup, iSup, iSup]
        congr 1
        exact σ.symm.surjective.range_comp fun i => ‖g i‖ }
  exact ⟨Set.range e, ⟨iso⟩⟩

end ONable

end TateFredholm

end
