import PhD.Main.TateFredholm.«05_Fredholm»
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-!
# Property (Pr) as a lifting property; the one Noetherian statement
([Bel] Exercise II.1.19, Propositions II.1.20–II.1.21.  See `00_Tate.lean` for the
development's overview and dictionary.) -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Pr

variable {R}
variable {P : Type*} [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- The lifting property for the model space itself: lift each basis vector with norm
control (`exists_preimage_norm_le`), then assemble the bounded family into an operator. -/
theorem exists_lift_cSpace [IsTate R] {I : Type*} [DecidableEq I]
    {M N : Type*}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]
    [CompleteSpace M]
    [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [CompleteSpace N]
    (f : M →L[R] N) (hf : Function.Surjective f) (γ : c(I, R) →L[R] N) :
    ∃ β₀ : c(I, R) →L[R] M, f.comp β₀ = γ := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le f hf
  choose m hm hmle using fun i : I => hC (γ (cSpace.single i 1))
  have hmbound : ∀ i, ‖m i‖ ≤ C * ‖γ‖ := fun i =>
    (hmle i).trans <| by
      have h1 : ‖γ (cSpace.single i 1)‖ ≤ ‖γ‖ :=
        (le_opNorm γ _).trans_eq (by rw [cSpace.norm_single_one, mul_one])
      exact mul_le_mul_of_nonneg_left h1 hC0.le
  have htend : ∀ h : c(I, R), Tendsto (fun i => h i • m i) cofinite (𝓝 0) := fun h => by
    refine squeeze_zero_norm (a := fun i => ‖h i‖ * (C * ‖γ‖)) (fun i => ?_) ?_
    · exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hmbound i) (norm_nonneg _))
    · have h0 : Tendsto (fun i => ‖h i‖) cofinite (𝓝 0) := by
        simpa using (cSpace.tendsto_cofinite h).norm
      simpa using h0.mul_const (C * ‖γ‖)
  have hsummable : ∀ h : c(I, R), Summable fun i => h i • m i := fun h =>
    summable_of_tendsto_cofinite (htend h)
  have hβnorm : ∀ h : c(I, R), ‖∑' i, h i • m i‖ ≤ C * ‖γ‖ * ‖h‖ := fun h => by
    refine (norm_tsum_le_iSup (htend h)).trans
      (Real.iSup_le (fun i => ?_)
        (mul_nonneg (mul_nonneg hC0.le (opNorm_nonneg γ)) (norm_nonneg _)))
    calc ‖h i • m i‖ ≤ ‖h i‖ * (C * ‖γ‖) :=
          (norm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_left (hmbound i) (norm_nonneg _))
    _ ≤ ‖h‖ * (C * ‖γ‖) :=
          mul_le_mul_of_nonneg_right (cSpace.norm_apply_le h i)
            (mul_nonneg hC0.le (opNorm_nonneg γ))
    _ = C * ‖γ‖ * ‖h‖ := mul_comm _ _
  let β₀ : c(I, R) →L[R] M :=
    LinearMap.mkContinuous
      { toFun := fun h => ∑' i, h i • m i
        map_add' := fun h₁ h₂ => by
          rw [← ((hsummable h₁).hasSum.add (hsummable h₂).hasSum).tsum_eq]
          exact tsum_congr fun i => add_smul (h₁ i) (h₂ i) (m i)
        map_smul' := fun r h => by
          simp only [RingHom.id_apply]
          rw [← (hsummable h).tsum_const_smul r]
          refine tsum_congr fun i => ?_
          show (r • h i) • m i = r • h i • m i
          rw [smul_eq_mul, mul_smul] } (C * ‖γ‖) hβnorm
  refine ⟨β₀, ?_⟩
  ext h
  show f (∑' i, h i • m i) = γ h
  calc f (∑' i, h i • m i) = ∑' i, h i • f (m i) := by
        simpa only [map_smul] using (((hsummable h).hasSum.mapL f).tsum_eq).symm
  _ = ∑' i, h i • γ (cSpace.single i 1) :=
        tsum_congr fun i => by rw [hm i]
  _ = γ h := by
        simpa only [map_smul] using ((cSpace.hasSum_single h).mapL γ).tsum_eq

omit [IsBoundedSMul R P] in
/-- (Pr) as a lifting property, forward direction ([Bel] Exercise II.1.19): a (Pr)
module lifts continuous maps through continuous surjections of Banach `R`-modules.

*Proof sketch.*  Reduce to `P = c_R(I)` (`exists_lift_cSpace`): a direct summand inherits
the lifting property along its inclusion/projection pair. -/
theorem HasPr.exists_lift [IsTate R] (hP : HasPr R P)
    {M N : Type*}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]
    [CompleteSpace M]
    [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [CompleteSpace N]
    (f : M →L[R] N) (hf : Function.Surjective f) (α : P →L[R] N) :
    ∃ β : P →L[R] M, f.comp β = α := by
  obtain ⟨s, ι, pr, hpri⟩ := hP
  classical
  obtain ⟨β₀, hβ₀⟩ := exists_lift_cSpace f hf (α.comp pr)
  refine ⟨β₀.comp ι, ?_⟩
  calc f.comp (β₀.comp ι) = (f.comp β₀).comp ι := by
        ext x
        simp [ContinuousLinearMap.comp_apply]
  _ = (α.comp pr).comp ι := by rw [hβ₀]
  _ = α.comp (pr.comp ι) := by
        ext x
        simp [ContinuousLinearMap.comp_apply]
  _ = α := by rw [hpri, ContinuousLinearMap.comp_id]

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] in
/-- Any linear map out of a finite free module over a normed ring is continuous:
expand along the standard basis and use continuity of coordinates and of `smul`. -/
theorem continuous_linearMap_pi {n : ℕ} {M : Type*}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    (g : (Fin n → R) →ₗ[R] M) : Continuous g := by
  have hrepr : ∀ x : Fin n → R, g x = ∑ i, x i • g fun j => if i = j then 1 else 0 := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  have : Continuous fun x : Fin n → R => ∑ i, x i • g fun j => if i = j then 1 else 0 :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  exact this.congr fun x => (hrepr x).symm

/-- Finitely generated (Pr) modules are projective ([Bel] Proposition II.1.20). -/
theorem HasPr.projective [IsTate R] [CompleteSpace P] (hP : HasPr R P) [Module.Finite R P] :
    Module.Projective R P := by
  obtain ⟨n, gsurj, hgsurj⟩ := Module.Finite.exists_fin' R P
  let F : (Fin n → R) →L[R] P := ⟨gsurj, continuous_linearMap_pi gsurj⟩
  obtain ⟨β, hβ⟩ := hP.exists_lift F hgsurj (ContinuousLinearMap.id R P)
  refine Module.Projective.of_split (β.toLinearMap) gsurj ?_
  ext p
  exact DFunLike.congr_fun hβ p

omit [IsUltrametricDist R] in
/-- **[Bel] Proposition II.1.21, finiteness part, Noetherian-free**: a Banach module carrying
a compact `u` with `1 − u` nilpotent is finitely generated (the identity is a polynomial in
`u`, hence compact; a finite-rank approximant within Neumann distance `1` is invertible). -/
theorem finite_of_one_sub_compact_nilpotent [IsTate R] [CompleteSpace P] (u : P →L[R] P)
    (hu : IsCompletelyContinuous u) (hnil : ∃ n : ℕ, (ContinuousLinearMap.id R P - u) ^ n = 0) :
    Module.Finite R P := by
  obtain ⟨n, hn⟩ := hnil
  set t : P →L[R] P := ContinuousLinearMap.id R P - u with ht_def
  have hut : u = 1 - t := by rw [ht_def, ContinuousLinearMap.one_def]; abel
  set S : P →L[R] P := ∑ k ∈ Finset.range n, t ^ k with hS_def
  -- geometric factorisation: `u · Sₙ = 1 − tⁿ = 1` since `tⁿ = 0`
  have huS' : u * S = 1 := by
    have hgeo : u * S = 1 - t ^ n := by
      simp only [hS_def]
      rw [hut, ← neg_sub t 1, neg_mul, mul_geom_sum]; abel
    rw [hgeo, hn, sub_zero]
  -- hence `id = u ∘ Sₙ` is completely continuous
  have huScomp : u.comp S = ContinuousLinearMap.id R P := by
    rw [← ContinuousLinearMap.mul_def, huS', ContinuousLinearMap.one_def]
  have hid : IsCompletelyContinuous (ContinuousLinearMap.id R P) := by
    rw [← huScomp]; exact hu.comp_right S
  -- approximate `id` by a finite-rank `w` within operator distance `1`
  obtain ⟨w, hw_fr, hw_lt⟩ := hid 1 one_pos
  -- invert `w` by the Neumann series (`exists_inverse_of_norm_id_sub_lt_one`)
  obtain ⟨v, hwv, hvw⟩ := exists_inverse_of_norm_id_sub_lt_one w hw_lt
  -- `w` has a right inverse, hence is surjective, hence `range w = ⊤`
  have hrange : LinearMap.range (w : P →ₗ[R] P) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨v y, ?_⟩
    have h := DFunLike.congr_fun hwv y
    simpa using h
  -- finite rank of `w` then forces `⊤` to be finitely generated
  obtain ⟨Q, hQ_fg, hQle⟩ := hw_fr
  rw [hrange] at hQle
  have hQtop : Q = ⊤ := le_antisymm le_top hQle
  rw [Module.finite_def, ← hQtop]
  exact hQ_fg

/-- **[Bel] Proposition II.1.21** (no Noetherian hypothesis is needed): if `P` has (Pr) and
carries a compact `u` with `1 − u` nilpotent, then `P` is finitely generated and projective —
the germ of Riesz theory. -/
theorem finite_projective_of_one_sub_compact_nilpotent [IsTate R] [CompleteSpace P]
    (hP : HasPr R P) (u : P →L[R] P) (hu : IsCompletelyContinuous u)
    (hnil : ∃ n : ℕ, (ContinuousLinearMap.id R P - u) ^ n = 0) :
    Module.Finite R P ∧ Module.Projective R P :=
  have := finite_of_one_sub_compact_nilpotent u hu hnil
  ⟨this, hP.projective⟩

end Pr

end TateFredholm

end
