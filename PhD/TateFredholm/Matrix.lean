import PhD.TateFredholm.ModelSpace

/-!
# Matrices, truncations, and the compactness criterion
([Bel] §II.1.3: Lemma II.1.8, Proposition II.1.9, Scholium II.1.10; blueprint 6.11,
6.14.  See `Tate.lean` for the development's overview and dictionary.)

The organising notion is `IsCompactoid` (cofinite row decay): the determinant theory
consumes it Noetherian-free, `IsCompactoid.isCompletelyContinuous` holds unconditionally,
and `isCompletelyContinuous_iff_rowNorm` recovers [JN]'s criterion under
`[IsNoetherianRing R]`.  The equivalence of compactoid with completely continuous is *not*
Noetherian-free: it rests on the closedness of finitely generated submodules ([Bel]
Hypothesis 3.1.8), so the converse direction lives in `Noetherian.lean`.  See
`exists_truncation_near`'s docstring for why closedness cannot be dropped. -/

open Filter Topology
open scoped BoundedContinuousFunction

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Matrix

variable {R}
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- Matrix coefficients in the canonical bases: `matrixCoeff u j i = (u eᵢ)_j`. -/
def matrixCoeff (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) : R :=
  u (cSpace.single i 1) j

/-- Columns decay cofinitely. -/
theorem tendsto_matrixCoeff_column (u : c(I, R) →L[R] c(J, R)) (i : I) :
    Tendsto (fun j => matrixCoeff u j i) cofinite (𝓝 0) :=
  cSpace.tendsto_cofinite (u (cSpace.single i 1))

/-- Matrix coefficients are additive in the operator. -/
@[simp] theorem matrixCoeff_sub (u v : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    matrixCoeff (u - v) j i = matrixCoeff u j i - matrixCoeff v j i := rfl

/-- Matrix coefficients are homogeneous in the operator (definitional). -/
@[simp] theorem matrixCoeff_smul (a : R) (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    matrixCoeff (a • u) j i = a * matrixCoeff u j i := rfl

/-- Matrix coefficients are additive in the operator (definitional). -/
@[simp] theorem matrixCoeff_add (u v : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    matrixCoeff (u + v) j i = matrixCoeff u j i + matrixCoeff v j i := rfl

/-- The zero operator has zero matrix (definitional). -/
@[simp] theorem matrixCoeff_zero (j : J) (i : I) :
    matrixCoeff (0 : c(I, R) →L[R] c(J, R)) j i = 0 := rfl

/-- **Matrix extensionality**: operators out of a model space are determined by their
matrices, because every `f` is the unconditional sum `∑' i, f i • eᵢ`
(`cSpace.hasSum_single`), which a continuous linear map transports term by term.

Stated here — the common ancestor of the two consuming branches — rather than in either
of them; `Jacobs.ext_matrixCoeff` (`PhD.Jacobs.GenFun`) is the norm-theoretic proof of
the same fact over a nontrivially normed field, kept because it is the form the Tate
algebra's `IsTate` API consumes. -/
theorem ext_matrixCoeff {u v : c(I, R) →L[R] c(J, R)}
    (h : ∀ j i, matrixCoeff u j i = matrixCoeff v j i) : u = v := by
  have hsingle : ∀ i : I, u (cSpace.single i (1 : R)) = v (cSpace.single i (1 : R)) :=
    fun i => DFunLike.ext _ _ fun j => h j i
  refine ContinuousLinearMap.ext fun f => ?_
  have hu : HasSum (fun i => f i • u (cSpace.single i (1 : R))) (u f) := by
    simpa only [map_smul] using (cSpace.hasSum_single f).mapL u
  have hv : HasSum (fun i => f i • v (cSpace.single i (1 : R))) (v f) := by
    simpa only [map_smul] using (cSpace.hasSum_single f).mapL v
  exact hu.unique (by simpa only [hsingle] using hv)

/-- Evaluating an operator coordinatewise is the convergent matrix-times-vector sum. -/
theorem hasSum_matrixCoeff (u : c(I, R) →L[R] c(J, R)) (f : c(I, R)) (j : J) :
    HasSum (fun i => f i * matrixCoeff u j i) ((u f) j) := by
  simpa only [ContinuousLinearMap.comp_apply, cSpace.evalCLM_apply, map_smul, smul_eq_mul,
    matrixCoeff] using (cSpace.hasSum_single f).mapL ((cSpace.evalCLM j).comp u)

/-- **The matrix of a composition is the (convergent) matrix product.** -/
theorem matrixCoeff_comp {L : Type*} [DecidableEq L] (u : c(J, R) →L[R] c(L, R))
    (v : c(I, R) →L[R] c(J, R)) (l : L) (i : I) :
    matrixCoeff (u.comp v) l i = ∑' j : J, matrixCoeff v j i * matrixCoeff u l j :=
  (hasSum_matrixCoeff u (v (cSpace.single i 1)) l).tsum_eq.symm

/-- `‖u‖ = sup_{i,j} ‖a_{ij}‖` ([Buz07, p. 65]; [Bel] §II.1.3). -/
theorem norm_eq_iSup_matrixCoeff [IsTate R] (u : c(I, R) →L[R] c(J, R)) :
    ‖u‖ = ⨆ j : J, ⨆ i : I, ‖matrixCoeff u j i‖ := by
  set D := ⨆ j : J, ⨆ i : I, ‖matrixCoeff u j i‖ with hD
  -- Each coefficient is bounded by the operator norm.
  have hbound_term : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖u‖ := fun j i => by
    calc ‖matrixCoeff u j i‖ = ‖u (cSpace.single i 1) j‖ := rfl
    _ ≤ ‖u (cSpace.single i 1)‖ := cSpace.norm_apply_le _ _
    _ ≤ ‖u‖ * ‖cSpace.single i (1 : R)‖ := le_opNorm _ _
    _ = ‖u‖ := by rw [cSpace.norm_single_one, mul_one]
  have hbdd_inner : ∀ j, BddAbove (Set.range fun i => ‖matrixCoeff u j i‖) := fun j =>
    ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact hbound_term j i⟩
  have hinner_le : ∀ j, (⨆ i, ‖matrixCoeff u j i‖) ≤ ‖u‖ := fun j =>
    Real.iSup_le (hbound_term j) (opNorm_nonneg u)
  have hbdd_outer : BddAbove (Set.range fun j => ⨆ i, ‖matrixCoeff u j i‖) :=
    ⟨‖u‖, by rintro _ ⟨j, rfl⟩; exact hinner_le j⟩
  have hmc_le : ∀ j i, ‖matrixCoeff u j i‖ ≤ D := fun j i =>
    (le_ciSup (hbdd_inner j) i).trans (le_ciSup hbdd_outer j)
  have hD_nonneg : (0 : ℝ) ≤ D :=
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun i => norm_nonneg _
  refine le_antisymm ?_ (Real.iSup_le hinner_le (opNorm_nonneg u))
  -- The reverse bound: `‖u f‖ ≤ D ‖f‖` for every `f`, coordinatewise.
  refine opNorm_le_of_forall u hD_nonneg fun f => ?_
  have hcoord : ∀ j, HasSum (fun i => f i * matrixCoeff u j i) ((u f) j) := fun j => by
    simpa only [ContinuousLinearMap.comp_apply, cSpace.evalCLM_apply, map_smul, smul_eq_mul,
      matrixCoeff]
      using (cSpace.hasSum_single f).mapL ((cSpace.evalCLM j).comp u)
  have htend : ∀ j, Tendsto (fun i => f i * matrixCoeff u j i) cofinite (𝓝 0) := fun j => by
    refine squeeze_zero_norm (a := fun i => ‖f i‖ * D) (fun i => ?_) ?_
    · calc ‖f i * matrixCoeff u j i‖ ≤ ‖f i‖ * ‖matrixCoeff u j i‖ := norm_mul_le _ _
      _ ≤ ‖f i‖ * D := mul_le_mul_of_nonneg_left (hmc_le j i) (norm_nonneg _)
    · have h0 : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0) := by
        simpa using (cSpace.tendsto_cofinite f).norm
      simpa using h0.mul_const D
  rw [cSpace.norm_eq_iSup (u f)]
  refine Real.iSup_le (fun j => ?_) (mul_nonneg hD_nonneg (norm_nonneg f))
  rw [← (hcoord j).tsum_eq]
  refine (norm_tsum_le_iSup (htend j)).trans ?_
  refine Real.iSup_le (fun i => ?_) (mul_nonneg hD_nonneg (norm_nonneg f))
  calc ‖f i * matrixCoeff u j i‖ ≤ ‖f i‖ * ‖matrixCoeff u j i‖ := norm_mul_le _ _
  _ ≤ ‖f‖ * D := mul_le_mul (cSpace.norm_apply_le f i) (hmc_le j i) (norm_nonneg _) (norm_nonneg _)
  _ = D * ‖f‖ := mul_comm _ _

/-- Bounded families = operators out of the model space, norm-preservingly
([Bel] §II.1.3; blueprint Proposition 6.11). -/
theorem exists_coeffEquiv [IsTate R] (N : Type*) [NormedAddCommGroup N] [Module R N]
    [IsBoundedSMul R N] [IsUltrametricDist N] [CompleteSpace N] :
    ∃ φ : (c(I, R) →L[R] N) ≃ₗ[R] (Ix I →ᵇ N), ∀ u, ‖φ u‖ = ‖u‖ := by
  -- Termwise `‖f i • g i‖ ≤ ‖f i‖ ‖g‖`, whence the columns decay and are summable.
  have hsmul_le : ∀ (g : Ix I →ᵇ N) (f : c(I, R)) (i : I), ‖f i • g i‖ ≤ ‖f i‖ * ‖g‖ :=
    fun g f i => (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm i) (norm_nonneg _))
  have htend : ∀ (g : Ix I →ᵇ N) (f : c(I, R)),
      Tendsto (fun i => f i • g i) cofinite (𝓝 0) := fun g f => by
    refine squeeze_zero_norm (a := fun i => ‖f i‖ * ‖g‖) (fun i => hsmul_le g f i) ?_
    have h0 : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0) := by
      simpa using (cSpace.tendsto_cofinite f).norm
    simpa using h0.mul_const ‖g‖
  have hsummable : ∀ (g : Ix I →ᵇ N) (f : c(I, R)), Summable fun i => f i • g i :=
    fun g f => summable_of_tendsto_cofinite (htend g f)
  have hinv_norm_le : ∀ (g : Ix I →ᵇ N) (f : c(I, R)), ‖∑' i, f i • g i‖ ≤ ‖g‖ * ‖f‖ :=
    fun g f => by
      refine (norm_tsum_le_iSup (htend g f)).trans (Real.iSup_le (fun i => ?_) (by positivity))
      calc ‖f i • g i‖ ≤ ‖f i‖ * ‖g‖ := hsmul_le g f i
      _ ≤ ‖f‖ * ‖g‖ := mul_le_mul_of_nonneg_right (cSpace.norm_apply_le f i) (norm_nonneg _)
      _ = ‖g‖ * ‖f‖ := mul_comm _ _
  have hfwd_bound : ∀ (u : c(I, R) →L[R] N) (i : I), ‖u (cSpace.single i 1)‖ ≤ ‖u‖ :=
    fun u i => (le_opNorm u _).trans_eq (by rw [cSpace.norm_single_one, mul_one])
  -- The forward map: an operator to its column function `i ↦ u eᵢ`.
  let fwd : (c(I, R) →L[R] N) → (Ix I →ᵇ N) := fun u =>
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun i => u (cSpace.single i 1)) ‖u‖ (hfwd_bound u)
  -- The inverse map: a bounded family to the operator `f ↦ ∑' i, f i • g i`.
  let inv : (Ix I →ᵇ N) → (c(I, R) →L[R] N) := fun g =>
    LinearMap.mkContinuous
      { toFun := fun f => ∑' i, f i • g i
        map_add' := fun f₁ f₂ => by
          rw [← ((hsummable g f₁).hasSum.add (hsummable g f₂).hasSum).tsum_eq]
          exact tsum_congr fun i => add_smul (f₁ i) (f₂ i) (g i)
        map_smul' := fun r f => by
          simp only [RingHom.id_apply]
          rw [← (hsummable g f).tsum_const_smul r]
          refine tsum_congr fun i => ?_
          show (r • f i) • g i = r • f i • g i
          rw [smul_eq_mul, mul_smul] } ‖g‖ (hinv_norm_le g)
  have hinv_op : ∀ g : Ix I →ᵇ N, ‖inv g‖ ≤ ‖g‖ :=
    fun g => opNorm_le_of_forall (inv g) (norm_nonneg g) (fun f => hinv_norm_le g f)
  have hleft_inv : Function.LeftInverse inv fwd := fun u => by
    ext f
    show (∑' i, f i • u (cSpace.single i 1)) = u f
    simpa only [map_smul] using ((cSpace.hasSum_single f).mapL u).tsum_eq
  have hright_inv : Function.RightInverse inv fwd := fun g => by
    ext i
    show (∑' k, cSpace.single i (1 : R) k • g k) = g i
    rw [tsum_eq_single i fun k hk => by rw [cSpace.single_apply_of_ne hk, zero_smul],
      cSpace.single_apply_self, one_smul]
  refine ⟨{ toFun := fwd
            map_add' := fun u v => by
              ext i
              show (u + v) (cSpace.single i 1)
                  = u (cSpace.single i 1) + v (cSpace.single i 1)
              rw [add_apply]
            map_smul' := fun r u => by
              ext i
              show (r • u) (cSpace.single i 1)
                  = (RingHom.id R) r • u (cSpace.single i 1)
              rw [RingHom.id_apply, smul_apply]
            invFun := inv
            left_inv := hleft_inv
            right_inv := hright_inv }, fun u => ?_⟩
  show ‖fwd u‖ = ‖u‖
  refine le_antisymm ((BoundedContinuousFunction.norm_le (opNorm_nonneg u)).2 fun i => ?_) ?_
  · show ‖u (cSpace.single i 1)‖ ≤ ‖u‖
    exact hfwd_bound u i
  · calc ‖u‖ = ‖inv (fwd u)‖ := by rw [hleft_inv u]
    _ ≤ ‖fwd u‖ := hinv_op (fwd u)

/-- The underlying `c(I, R)`-element of the coordinate truncation. -/
private def truncationFun (S : Finset I) (f : c(I, R)) : c(I, R) :=
  ⟨⟨fun i : I => if i ∈ S then f i else 0, continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [S.eventually_cofinite_notMem] with j hj
    exact (if_neg hj).symm⟩

private theorem truncationFun_apply (S : Finset I) (f : c(I, R)) (i : I) :
    truncationFun S f i = if i ∈ S then f i else 0 := rfl

private theorem truncationFun_sub (S : Finset I) (f g : c(I, R)) :
    truncationFun S f - truncationFun S g = truncationFun S (f - g) :=
  DFunLike.ext _ _ fun i => by
    show (if i ∈ S then f i else 0) - (if i ∈ S then g i else 0)
        = if i ∈ S then (f - g) i else 0
    by_cases h : i ∈ S
    · simp only [if_pos h]; rfl
    · simp only [if_neg h, sub_zero]

private theorem norm_truncationFun_le (S : Finset I) (f : c(I, R)) :
    ‖truncationFun S f‖ ≤ ‖f‖ := by
  rcases isEmpty_or_nonempty I with hI | hI
  · rw [cSpace.norm_eq_iSup, Real.iSup_of_isEmpty]
    exact norm_nonneg f
  · rw [cSpace.norm_eq_iSup]
    refine ciSup_le fun i => ?_
    rw [truncationFun_apply]
    by_cases h : i ∈ S
    · rw [if_pos h]; exact cSpace.norm_apply_le f i
    · rw [if_neg h, norm_zero]; exact norm_nonneg f

/-- The coordinate truncation `π_S` — Bellaïche's workhorse, now over a Tate ring. -/
def truncation (S : Finset I) : c(I, R) →L[R] c(I, R) where
  toFun := truncationFun S
  map_add' f g := DFunLike.ext _ _ fun i => by
    show (if i ∈ S then (f + g) i else 0)
        = (if i ∈ S then f i else 0) + (if i ∈ S then g i else 0)
    by_cases h : i ∈ S
    · simp only [if_pos h]; rfl
    · simp only [if_neg h, add_zero]
  map_smul' r f := DFunLike.ext _ _ fun i => by
    show (if i ∈ S then (r • f) i else 0) = r • (if i ∈ S then f i else 0)
    by_cases h : i ∈ S
    · simp only [if_pos h]; rfl
    · simp only [if_neg h, smul_zero]
  cont := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
    calc dist (truncationFun S f) (truncationFun S g)
        = ‖truncationFun S f - truncationFun S g‖ := dist_eq_norm _ _
    _ = ‖truncationFun S (f - g)‖ := by rw [truncationFun_sub]
    _ ≤ ‖f - g‖ := norm_truncationFun_le S (f - g)
    _ = 1 * dist f g := by rw [one_mul, dist_eq_norm]

@[simp] theorem truncation_apply (S : Finset I) (f : c(I, R)) (i : I) :
    truncation S f i = if i ∈ S then f i else 0 := rfl

/-- Truncations are contractions. -/
theorem norm_truncation_apply_le (S : Finset I) (f : c(I, R)) :
    ‖truncation S f‖ ≤ ‖f‖ :=
  norm_truncationFun_le S f

/-- The truncation of `f` lies in the span of the touched basis vectors. -/
theorem truncation_mem_span (S : Finset I) (f : c(I, R)) :
    truncation (R := R) S f ∈
      Submodule.span R ((fun i => cSpace.single i (1 : R)) '' (S : Set I)) := by
  induction S using Finset.induction_on with
  | empty =>
      have h0 : truncation (R := R) (∅ : Finset I) f = 0 := by
        refine DFunLike.ext _ _ fun j => ?_
        rw [truncation_apply, if_neg (Finset.notMem_empty j)]
        rfl
      rw [h0]
      exact Submodule.zero_mem _
  | @insert i S' hi ih =>
      have hins : truncation (R := R) (insert i S') f
          = f i • cSpace.single i (1 : R) + truncation (R := R) S' f := by
        refine DFunLike.ext _ _ fun j => ?_
        rw [truncation_apply]
        show (if j ∈ insert i S' then f j else 0)
            = f i • (cSpace.single i (1 : R)) j + truncation (R := R) S' f j
        rw [truncation_apply]
        by_cases hj : j = i
        · subst hj
          simp [hi, smul_eq_mul]
        · simp [Finset.mem_insert, hj, cSpace.single_apply_of_ne hj, smul_eq_mul]
      rw [hins]
      refine Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
        (Submodule.span_mono
          (Set.image_mono (Finset.coe_subset.2 (Finset.subset_insert i S'))) ih)
      exact Set.mem_image_of_mem _ (Finset.mem_coe.2 (Finset.mem_insert_self i S'))

/-- Truncations have finite rank. -/
theorem isFiniteRank_truncation (S : Finset I) :
    IsFiniteRank (truncation (R := R) S) := by
  refine ⟨Submodule.span R ((fun i => cSpace.single i (1 : R)) '' (S : Set I)),
    Submodule.fg_span (S.finite_toSet.image _), ?_⟩
  rintro x ⟨f, rfl⟩
  exact truncation_mem_span S f

/-- Coordinatewise evaluation of a difference in `c(I, R)` (via linearity of `evalCLM`). -/
private theorem cSpace_sub_apply (f g : c(I, R)) (i : I) : (f - g) i = f i - g i := by
  rw [← cSpace.evalCLM_apply i (f - g), map_sub, cSpace.evalCLM_apply, cSpace.evalCLM_apply]

/-- If `f` is uniformly small off `S`, then `π_S f` approximates `f` within that bound: off `S`
the difference is `-f j`, on `S` it vanishes.  Bellaïche's per-generator truncation estimate. -/
private theorem norm_truncation_sub_le_of_forall {S : Finset I} {f : c(I, R)} {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ j ∉ S, ‖f j‖ ≤ δ) : ‖truncation S f - f‖ ≤ δ := by
  rw [cSpace.norm_eq_iSup]
  refine Real.iSup_le (fun j => ?_) hδ
  rw [cSpace_sub_apply, truncation_apply]
  by_cases hj : j ∈ S
  · rw [if_pos hj, sub_self, norm_zero]; exact hδ
  · rw [if_neg hj, zero_sub, norm_neg]; exact h j hj

/-- **[Bel] Lemma 3.1.12 (draft Lemma II.1.8) over a Tate ring**: finitely generated
**closed** submodules of `c_R(I)` are uniformly approximated by coordinate truncations.

The closedness hypothesis is exactly the published [Bel] Hypothesis 3.1.8 ("every finitely
generated submodule of an ON-able Banach `A`-module is closed"), which the draft §II.1
predates; Bellaïche notes there that it can fail and restricts to the case where it holds.
It cannot be dropped: over the non-Noetherian Banach–Tate ring `R = ℚₚ ⊕ c(ℕ, ℚₚ)`
(pointwise multiplication) the principal submodule generated by `g = (pʲeⱼ)ⱼ` contains the
unit vectors `p⁻ⁿeₙ • g` concentrated at coordinate `n`, so no single truncation
approximates it uniformly.  The proof applies the open mapping theorem to `Rʳ → P`, which
requires `P` Banach; per [JN, p. 7] completeness of finitely generated submodules is
precisely the Noetherian input, and over a field it is automatic — so this statement still
subsumes [Buz]/[Ser].

*Proof sketch.*  Exactly Bellaïche's: a continuous surjection `Rʳ → P`, norm-controlled
preimages from the quantitative OMT (`exists_preimage_norm_le` — the only input needing
`[IsTate R]`), truncate the `r` generators, estimate ultrametrically. -/
theorem exists_truncation_near [IsTate R] (P : Submodule R c(I, R)) (hP : P.FG)
    (hPc : IsClosed (P : Set c(I, R))) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset I, ∀ p ∈ P, ‖truncation S p - p‖ ≤ ε * ‖p‖ := by
  -- `↥P` is a Banach `R`-module: complete by closedness, bounded-`smul` by restriction.
  haveI : CompleteSpace ↥P := hPc.isComplete.completeSpace_coe
  haveI : IsBoundedSMul R ↥P := .of_norm_smul_le fun r x => by
    simp only [Submodule.coe_norm, SetLike.val_smul]
    exact norm_smul_le r (x : c(I, R))
  -- A finite generating family `s : Fin n → c(I, R)` for `P`.
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hP
  have hmem : ∀ a : Fin n → R, Fintype.linearCombination R s a ∈ P := fun a => by
    rw [Fintype.linearCombination_apply, ← hs]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  -- The (ordinary-triangle) norm bound making `a ↦ ∑ k, a k • s k` continuous into `↥P`.
  have hbound : ∀ a : Fin n → R,
      ‖((Fintype.linearCombination R s).codRestrict P hmem) a‖ ≤ (∑ k, ‖s k‖) * ‖a‖ := fun a => by
    rw [Submodule.coe_norm, LinearMap.codRestrict_apply, Fintype.linearCombination_apply]
    calc ‖∑ k, a k • s k‖ ≤ ∑ k, ‖a k • s k‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖s k‖ * ‖a‖ := Finset.sum_le_sum fun k _ => by
          calc ‖a k • s k‖ ≤ ‖a k‖ * ‖s k‖ := norm_smul_le _ _
          _ ≤ ‖a‖ * ‖s k‖ := mul_le_mul_of_nonneg_right (norm_le_pi_norm a k) (norm_nonneg _)
          _ = ‖s k‖ * ‖a‖ := mul_comm _ _
    _ = (∑ k, ‖s k‖) * ‖a‖ := by rw [Finset.sum_mul]
  -- The continuous surjection `π : Rⁿ → ↥P`, `π a = ∑ k, a k • s k`.
  let π : (Fin n → R) →L[R] ↥P :=
    ((Fintype.linearCombination R s).codRestrict P hmem).mkContinuous (∑ k, ‖s k‖) hbound
  have hπ_coe : ∀ a : (Fin n → R), (π a : c(I, R)) = ∑ k, a k • s k := fun _ => rfl
  have hsurj : Function.Surjective π := fun q => by
    have hq : (q : c(I, R)) ∈ Submodule.span R (Set.range s) := hs ▸ q.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hq
    obtain ⟨a, ha⟩ := hq
    exact ⟨a, Subtype.ext (by rw [hπ_coe]; exact ha)⟩
  -- Quantitative OMT: norm-controlled preimages (`[IsTate R]` used here).
  obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le π hsurj
  -- Each generator decays cofinitely, so `{j | ε/C ≤ ‖(s k) j‖}` is finite.
  have hfin : ∀ k : Fin n, {j : I | ε / C ≤ ‖(s k) j‖}.Finite := fun k => by
    have h0 : Tendsto (fun j => ‖(s k) j‖) cofinite (𝓝 0) := by
      simpa using (cSpace.tendsto_cofinite (s k)).norm
    have hev : ∀ᶠ j in cofinite, ‖(s k) j‖ < ε / C := by
      have := Metric.tendsto_nhds.1 h0 (ε / C) (div_pos hε hC0)
      filter_upwards [this] with j hj
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hj
    simpa only [not_lt] using Filter.eventually_cofinite.1 hev
  -- The truncation set: all coordinates where some generator is large.
  let S : Finset I := Finset.univ.biUnion fun k => (hfin k).toFinset
  have hgen : ∀ k : Fin n, ‖truncation S (s k) - s k‖ ≤ ε / C := fun k => by
    refine norm_truncation_sub_le_of_forall (div_nonneg hε.le hC0.le) fun j hj => ?_
    have hjk : j ∉ (hfin k).toFinset :=
      fun h => hj (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, h⟩)
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hjk
    exact le_of_lt (not_le.1 hjk)
  refine ⟨S, fun p hp => ?_⟩
  -- Pull `p` back through `π` and expand ultrametrically.
  obtain ⟨a, ha, hnorm⟩ := hC ⟨p, hp⟩
  have hLp : (∑ k, a k • s k) = p := by rw [← hπ_coe a, ha]
  have hnorm' : ‖a‖ ≤ C * ‖p‖ := by simpa using hnorm
  have hexpand : truncation S p - p = ∑ k, a k • (truncation S (s k) - s k) := by
    rw [← hLp, map_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_sub]
  rw [hexpand]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg hε.le (norm_nonneg p)) fun k _ => ?_
  calc ‖a k • (truncation S (s k) - s k)‖
      ≤ ‖a k‖ * ‖truncation S (s k) - s k‖ := norm_smul_le _ _
    _ ≤ ‖a‖ * (ε / C) :=
        mul_le_mul (norm_le_pi_norm a k) (hgen k) (norm_nonneg _) (norm_nonneg _)
    _ ≤ (C * ‖p‖) * (ε / C) :=
        mul_le_mul_of_nonneg_right hnorm' (div_nonneg hε.le hC0.le)
    _ = ε * ‖p‖ := by
        rw [mul_comm (C * ‖p‖) (ε / C), ← mul_assoc, div_mul_cancel₀ ε hC0.ne']

/-- The row sup `r_j(u) = sup_i ‖a_{ij}‖`. -/
def rowNorm (u : c(I, R) →L[R] c(J, R)) (j : J) : ℝ :=
  ⨆ i : I, ‖matrixCoeff u j i‖

theorem rowNorm_nonneg (u : c(I, R) →L[R] c(J, R)) (j : J) : 0 ≤ rowNorm u j :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- *Compactoid*: the row sups decay cofinitely — the notion the Fredholm-determinant
theory actually consumes, and the reason that theory needs no Noetherian hypothesis.
`IsCompactoid.isCompletelyContinuous` holds unconditionally; the converse needs the
closedness of finitely generated submodules ([Bel] Hypothesis 3.1.8), supplied over
Noetherian bases in `Noetherian.lean`. -/
def IsCompactoid (u : c(I, R) →L[R] c(J, R)) : Prop :=
  Tendsto (rowNorm u) cofinite (𝓝 0)

/-- The zero operator is compactoid (its rows are zero). -/
theorem isCompactoid_zero : IsCompactoid (0 : c(I, R) →L[R] c(J, R)) := by
  have h : ∀ j, rowNorm (0 : c(I, R) →L[R] c(J, R)) j = 0 := fun j =>
    le_antisymm (Real.iSup_le (fun i => by
      show ‖(0 : c(J, R)) j‖ ≤ 0
      rw [show ((0 : c(J, R)) j) = 0 from rfl, norm_zero]) le_rfl) (rowNorm_nonneg _ j)
  have : rowNorm (0 : c(I, R) →L[R] c(J, R)) = fun _ => 0 := funext h
  unfold IsCompactoid
  rw [this]
  exact tendsto_const_nhds

private theorem matrixCoeff_truncation_comp_sub (u : c(I, R) →L[R] c(J, R))
    (S : Finset J) (j : J) (i : I) :
    matrixCoeff ((truncation S).comp u - u) j i
      = if j ∈ S then 0 else -(matrixCoeff u j i) := by
  show ((truncation S).comp u - u) (cSpace.single i 1) j = _
  rw [sub_apply, ContinuousLinearMap.comp_apply]
  show truncation S (u (cSpace.single i 1)) j - u (cSpace.single i 1) j = _
  rw [truncation_apply]
  by_cases h : j ∈ S
  · rw [if_pos h, if_pos h, sub_self]
  · rw [if_neg h, if_neg h, zero_sub]
    rfl

private theorem norm_matrixCoeff_le (u : c(I, R) →L[R] c(J, R)) [IsTate R] (j : J)
    (i : I) : ‖matrixCoeff u j i‖ ≤ ‖u‖ :=
  calc ‖matrixCoeff u j i‖ ≤ ‖u (cSpace.single i 1)‖ := cSpace.norm_apply_le _ _
  _ ≤ ‖u‖ * ‖cSpace.single i (1 : R)‖ := le_opNorm _ _
  _ = ‖u‖ := by rw [cSpace.norm_single_one, mul_one]

private theorem norm_matrixCoeff_le_rowNorm (u : c(I, R) →L[R] c(J, R)) [IsTate R]
    (j : J) (i : I) : ‖matrixCoeff u j i‖ ≤ rowNorm u j :=
  le_ciSup ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact norm_matrixCoeff_le u j i⟩ i

/-- The tail bound behind the compactoid theory: if the rows off `S` are `≤ ε`, then
`‖π_S∘u − u‖ ≤ ε`. -/
private theorem norm_truncation_comp_sub_le [IsTate R] (u : c(I, R) →L[R] c(J, R))
    (S : Finset J) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ j ∉ S, rowNorm u j ≤ ε) :
    ‖(truncation S).comp u - u‖ ≤ ε := by
  rw [norm_eq_iSup_matrixCoeff]
  refine Real.iSup_le (fun j => Real.iSup_le (fun i => ?_) hε) hε
  rw [matrixCoeff_truncation_comp_sub]
  by_cases hj : j ∈ S
  · rw [if_pos hj, norm_zero]; exact hε
  · rw [if_neg hj, norm_neg]
    exact (norm_matrixCoeff_le_rowNorm u j i).trans (h j hj)

/-- Compactoid operators are completely continuous, Noetherian-free
([Bel] Prop II.1.9, ⇐ direction): the truncations `π_S ∘ u` are finite rank and
converge to `u` since `‖π_S∘u − u‖ = sup_{j∉S} r_j(u)`. -/
theorem IsCompactoid.isCompletelyContinuous [IsTate R] {u : c(I, R) →L[R] c(J, R)}
    (hu : IsCompactoid u) : IsCompletelyContinuous u := by
  intro ε hε
  have hev := Metric.tendsto_nhds.mp hu (ε / 2) (half_pos hε)
  have hfin : {j : J | ¬ rowNorm u j < ε / 2}.Finite := by
    refine (Filter.eventually_cofinite.mp hev).subset fun j hj => ?_
    intro habs
    exact hj (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at habs)
  refine ⟨(truncation hfin.toFinset).comp u, isFiniteRank_truncation _ |>.comp_right u, ?_⟩
  have hle : ‖(truncation hfin.toFinset).comp u - u‖ ≤ ε / 2 := by
    refine norm_truncation_comp_sub_le u _ (half_pos hε).le fun j hj => ?_
    have : rowNorm u j < ε / 2 := by
      by_contra habs
      exact hj (hfin.mem_toFinset.2 habs)
    exact this.le
  calc ‖u - (truncation hfin.toFinset).comp u‖
      = ‖(truncation hfin.toFinset).comp u - u‖ := opNorm_sub_comm _ _
  _ ≤ ε / 2 := hle
  _ < ε := half_lt_self hε

-- The bridge `IsCompletelyContinuous.isCompactoid` and the recovered criterion
-- `isCompletelyContinuous_iff_rowNorm` live in `Noetherian.lean`: they consume the
-- closedness of finitely generated submodules ([Bel] Hypothesis 3.1.8).

/-- **[Bel] Scholium II.1.10 over a Tate ring**, compactoid form: truncations of a
compactoid operator converge to it in operator norm along the directed family of finite
sets. -/
theorem tendsto_truncation_comp [IsTate R] (u : c(I, R) →L[R] c(J, R))
    (hu : IsCompactoid u) :
    Tendsto (fun S : Finset J => ‖(truncation S).comp u - u‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := Metric.tendsto_nhds.mp hu (ε / 2) (half_pos hε)
  have hfin : {j : J | ¬ rowNorm u j < ε / 2}.Finite := by
    refine (Filter.eventually_cofinite.mp hev).subset fun j hj => ?_
    intro habs
    exact hj (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at habs)
  rw [Filter.eventually_atTop]
  refine ⟨hfin.toFinset, fun S hS => ?_⟩
  have hle : ‖(truncation S).comp u - u‖ ≤ ε / 2 := by
    refine norm_truncation_comp_sub_le u S (half_pos hε).le fun j hj => ?_
    have hjB : j ∉ hfin.toFinset := fun hmem => hj (hS hmem)
    have : rowNorm u j < ε / 2 := by
      by_contra habs
      exact hjB (hfin.mem_toFinset.2 habs)
    exact this.le
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (opNorm_nonneg _)]
  exact lt_of_le_of_lt hle (half_lt_self hε)

/-- Coordinatewise bound through the row sup: `‖(u f)(j)‖ ≤ r_j(u) ‖f‖`. -/
private theorem norm_apply_coord_le [IsTate R] (u : c(I, R) →L[R] c(J, R))
    (f : c(I, R)) (j : J) : ‖(u f) j‖ ≤ rowNorm u j * ‖f‖ := by
  have hcoord : HasSum (fun i => f i * matrixCoeff u j i) ((u f) j) := by
    simpa only [ContinuousLinearMap.comp_apply, cSpace.evalCLM_apply, map_smul,
      smul_eq_mul, matrixCoeff] using (cSpace.hasSum_single f).mapL ((cSpace.evalCLM j).comp u)
  have htend : Tendsto (fun i => f i * matrixCoeff u j i) cofinite (𝓝 0) := by
    refine squeeze_zero_norm (a := fun i => ‖f i‖ * rowNorm u j) (fun i => ?_) ?_
    · calc ‖f i * matrixCoeff u j i‖ ≤ ‖f i‖ * ‖matrixCoeff u j i‖ := norm_mul_le _ _
      _ ≤ ‖f i‖ * rowNorm u j :=
          mul_le_mul_of_nonneg_left (norm_matrixCoeff_le_rowNorm u j i) (norm_nonneg _)
    · have h0 : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0) := by
        simpa using (cSpace.tendsto_cofinite f).norm
      simpa using h0.mul_const (rowNorm u j)
  rw [← hcoord.tsum_eq]
  refine (norm_tsum_le_iSup htend).trans
    (Real.iSup_le (fun i => ?_) (mul_nonneg (rowNorm_nonneg u j) (norm_nonneg f)))
  calc ‖f i * matrixCoeff u j i‖ ≤ ‖f i‖ * ‖matrixCoeff u j i‖ := norm_mul_le _ _
  _ ≤ ‖f‖ * rowNorm u j :=
      mul_le_mul (cSpace.norm_apply_le f i) (norm_matrixCoeff_le_rowNorm u j i)
        (norm_nonneg _) (norm_nonneg f)
  _ = rowNorm u j * ‖f‖ := mul_comm _ _

/-- Compactoids absorb continuous maps on the right ([Bel] Lemma II.1.4 analogue). -/
theorem IsCompactoid.comp_right [IsTate R] {K : Type*} [DecidableEq K]
    {u : c(I, R) →L[R] c(J, R)} (hu : IsCompactoid u) (w : c(K, R) →L[R] c(I, R)) :
    IsCompactoid (u.comp w) := by
  have hbound : ∀ j, rowNorm (u.comp w) j ≤ rowNorm u j * ‖w‖ := fun j => by
    refine Real.iSup_le (fun k => ?_) (mul_nonneg (rowNorm_nonneg u j) (opNorm_nonneg w))
    show ‖(u.comp w) (cSpace.single k 1) j‖ ≤ _
    rw [ContinuousLinearMap.comp_apply]
    refine (norm_apply_coord_le u _ j).trans
      (mul_le_mul_of_nonneg_left ?_ (rowNorm_nonneg u j))
    exact (le_opNorm w _).trans_eq (by rw [cSpace.norm_single_one, mul_one])
  refine squeeze_zero (fun j => rowNorm_nonneg _ j) hbound ?_
  simpa using hu.mul_const ‖w‖

private theorem cSpace_finset_sum_apply {α : Type*} (T : Finset α) (g : α → c(J, R))
    (k : J) : (∑ a ∈ T, g a) k = ∑ a ∈ T, g a k := by
  induction T using Finset.cons_induction_on with
  | empty => rfl
  | cons a T ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, ← ih]
      rfl

private theorem truncation_eq_sum_single (S : Finset J) (f : c(J, R)) :
    truncation (R := R) S f = ∑ j ∈ S, f j • cSpace.single j (1 : R) := by
  refine DFunLike.ext _ _ fun k => ?_
  rw [truncation_apply, cSpace_finset_sum_apply]
  by_cases hk : k ∈ S
  · rw [if_pos hk, Finset.sum_eq_single k
      (fun j _ hjk => by
        show f j • (cSpace.single j (1 : R)) k = 0
        rw [cSpace.single_apply_of_ne (Ne.symm hjk), smul_zero])
      (fun habs => absurd hk habs)]
    show f k = f k • (cSpace.single k (1 : R)) k
    rw [cSpace.single_apply_self, smul_eq_mul, mul_one]
  · rw [if_neg hk]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    show f j • (cSpace.single j (1 : R)) k = 0
    rw [cSpace.single_apply_of_ne fun h => hk (by rw [h]; exact hj), smul_zero]

/-- Compactoids absorb continuous maps on the left: split off a truncation, use the
column decay of `w` on the finitely many surviving rows, and bound the tail by the
operator norm. -/
theorem IsCompactoid.comp_left [IsTate R] {K : Type*} [DecidableEq K]
    {u : c(I, R) →L[R] c(J, R)} (hu : IsCompactoid u) (w : c(J, R) →L[R] c(K, R)) :
    IsCompactoid (w.comp u) := by
  rw [IsCompactoid, Metric.tendsto_nhds]
  intro ε hε
  have hw1 : (0 : ℝ) < ‖w‖ + 1 := lt_of_lt_of_le one_pos (by simpa using opNorm_nonneg w)
  have hu1 : (0 : ℝ) < ‖u‖ + 1 := lt_of_lt_of_le one_pos (by simpa using opNorm_nonneg u)
  set ε' : ℝ := ε / (2 * (‖w‖ + 1)) with hε'def
  have hε' : 0 < ε' := div_pos hε (mul_pos two_pos hw1)
  -- the truncation set from the compactoid decay of `u`
  have hev := Metric.tendsto_nhds.mp hu ε' hε'
  have hfin : {j : J | ¬ rowNorm u j < ε'}.Finite := by
    refine (Filter.eventually_cofinite.mp hev).subset fun j hj => ?_
    intro habs
    exact hj (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at habs)
  set S : Finset J := hfin.toFinset with hSdef
  have htail : ‖(truncation S).comp u - u‖ ≤ ε' := by
    refine norm_truncation_comp_sub_le u S hε'.le fun j hj => ?_
    have : rowNorm u j < ε' := by
      by_contra habs
      exact hj (hfin.mem_toFinset.2 habs)
    exact this.le
  -- head: finitely many columns of `w`, each decaying in `k`
  set δ : ℝ := ε / (2 * (‖u‖ + 1)) with hδdef
  have hδ : 0 < δ := div_pos hε (mul_pos two_pos hu1)
  have hcols : Tendsto (fun k => ∑ j ∈ S, ‖matrixCoeff w k j‖) cofinite (𝓝 0) := by
    have h0 : Tendsto (fun k => ∑ j ∈ S, ‖matrixCoeff w k j‖) cofinite
        (𝓝 (∑ j ∈ S, 0)) :=
      tendsto_finsetSum _ fun j _ => by
        simpa using (tendsto_matrixCoeff_column w j).norm
    simpa using h0
  have hevk : ∀ᶠ k in cofinite, ∑ j ∈ S, ‖matrixCoeff w k j‖ < δ := by
    have := Metric.tendsto_nhds.mp hcols δ hδ
    refine this.mono fun k hk => ?_
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at hk
  refine hevk.mono fun k hk => ?_
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg _ k)]
  have hhalf : (0 : ℝ) < ε / 2 := half_pos hε
  -- per-coefficient decomposition
  have hbound : rowNorm (w.comp u) k ≤ ε / 2 := by
    refine Real.iSup_le (fun i => ?_) hhalf.le
    -- split `u eᵢ` into its truncation and the tail
    have hdecomp : u (cSpace.single i 1)
        = truncation S (u (cSpace.single i 1))
          + (u (cSpace.single i 1) - truncation S (u (cSpace.single i 1))) :=
      (add_sub_cancel _ _).symm
    have hval : matrixCoeff (w.comp u) k i
        = (w (truncation S (u (cSpace.single i 1)))) k
          + (w (u (cSpace.single i 1) - truncation S (u (cSpace.single i 1)))) k := by
      show (w (u (cSpace.single i 1))) k = _
      conv_lhs => rw [hdecomp, map_add w]
      rfl
    -- head bound
    have hhead : ‖(w (truncation S (u (cSpace.single i 1)))) k‖
        ≤ ‖u‖ * ∑ j ∈ S, ‖matrixCoeff w k j‖ := by
      rw [truncation_eq_sum_single, map_sum, cSpace_finset_sum_apply]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      show ‖(w ((u (cSpace.single i 1)) j • cSpace.single j (1 : R))) k‖
        ≤ ‖u‖ * ‖matrixCoeff w k j‖
      rw [map_smul]
      show ‖(u (cSpace.single i 1)) j * (w (cSpace.single j (1 : R))) k‖ ≤ _
      calc ‖(u (cSpace.single i 1)) j * (w (cSpace.single j (1 : R))) k‖
          ≤ ‖(u (cSpace.single i 1)) j‖ * ‖matrixCoeff w k j‖ := norm_mul_le _ _
      _ ≤ ‖u‖ * ‖matrixCoeff w k j‖ :=
          mul_le_mul_of_nonneg_right (norm_matrixCoeff_le u j i) (norm_nonneg _)
    -- tail bound
    have htail' : ‖(w (u (cSpace.single i 1) - truncation S (u (cSpace.single i 1)))) k‖
        ≤ ‖w‖ * ε' := by
      refine (cSpace.norm_apply_le _ _).trans ((le_opNorm w _).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ (opNorm_nonneg w)
      have : u (cSpace.single i 1) - truncation S (u (cSpace.single i 1))
          = -(((truncation S).comp u - u) (cSpace.single i 1)) := by
        rw [sub_apply, ContinuousLinearMap.comp_apply, neg_sub]
      rw [this, norm_neg]
      exact ((le_opNorm _ _).trans_eq
        (by rw [cSpace.norm_single_one, mul_one])).trans htail
    -- combine ultrametrically
    have hcomb := IsUltrametricDist.norm_add_le_max
      ((w (truncation S (u (cSpace.single i 1)))) k)
      ((w (u (cSpace.single i 1) - truncation S (u (cSpace.single i 1)))) k)
    rw [← hval] at hcomb
    refine hcomb.trans (max_le ?_ ?_)
    · refine (hhead.trans (mul_le_mul_of_nonneg_left hk.le (opNorm_nonneg u))).trans ?_
      have hid : (‖u‖ + 1) * δ = ε / 2 := by
        rw [hδdef]
        field_simp
      calc ‖u‖ * δ ≤ (‖u‖ + 1) * δ :=
            mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 2 := hid
    · refine htail'.trans ?_
      have hid : (‖w‖ + 1) * ε' = ε / 2 := by
        rw [hε'def]
        field_simp
      calc ‖w‖ * ε' ≤ (‖w‖ + 1) * ε' :=
            mul_le_mul_of_nonneg_right (by linarith) hε'.le
      _ = ε / 2 := hid
  exact lt_of_le_of_lt hbound (half_lt_self hε)

end Matrix

end TateFredholm

end
