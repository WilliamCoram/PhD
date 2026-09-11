import PhD.TateFredholm.OperatorNorm

/-!
# Finite-rank and completely continuous operators
([Bel] Definition II.1.3, Lemma II.1.4; [JN] Definition 2.1.5; blueprint 6.13.  See
`Tate.lean` for the development's overview and dictionary.)

The two definitions and everything provable about them by pure algebra live in the
`Definitions` section, under the weakest hypotheses that make them typecheck: a semiring
of scalars and seminormed modules (a ring of scalars once subtraction is involved).  No
`IsTate`, no completeness, no `IsBoundedSMul` — those enter only in `Compact` below,
where the operator norm has to be compared with the norms of `M` and `N` through
`le_opNorm`. -/

open Filter Topology

noncomputable section

namespace TateFredholm

section Definitions

section SemiringScalars

variable {R : Type*} [Semiring R] {M N P : Type*}
  [SeminormedAddCommGroup M] [Module R M] [SeminormedAddCommGroup N] [Module R N]
  [SeminormedAddCommGroup P] [Module R P]

/-- *Finite rank*: the image is contained in a finitely generated submodule. -/
def IsFiniteRank (u : M →L[R] N) : Prop :=
  ∃ Q : Submodule R N, Q.FG ∧ LinearMap.range (u : M →ₗ[R] N) ≤ Q

/-- Finite-rank operators are stable under sums (`range (u+v) ≤ range u ⊔ range v`). -/
theorem IsFiniteRank.add {u v : M →L[R] N} (hu : IsFiniteRank u) (hv : IsFiniteRank v) :
    IsFiniteRank (u + v) := by
  obtain ⟨Qu, hQu, hleu⟩ := hu
  obtain ⟨Qv, hQv, hlev⟩ := hv
  refine ⟨Qu ⊔ Qv, hQu.sup hQv, ?_⟩
  rintro x ⟨m, rfl⟩
  exact Submodule.add_mem_sup (hleu ⟨m, rfl⟩) (hlev ⟨m, rfl⟩)

/-- Two-sided-ideal property, finite-rank half, post-composition ([Bel] Lemma II.1.4). -/
theorem IsFiniteRank.comp_left {u : M →L[R] N} (hu : IsFiniteRank u) (f : N →L[R] P) :
    IsFiniteRank (f.comp u) := by
  obtain ⟨Q, hQ, hle⟩ := hu
  refine ⟨Q.map (f : N →ₗ[R] P), hQ.map _, ?_⟩
  rintro x ⟨m, rfl⟩
  exact Submodule.mem_map_of_mem (hle ⟨m, rfl⟩)

/-- Two-sided-ideal property, finite-rank half, pre-composition ([Bel] Lemma II.1.4). -/
theorem IsFiniteRank.comp_right {u : M →L[R] N} (hu : IsFiniteRank u) (f : P →L[R] M) :
    IsFiniteRank (u.comp f) := by
  obtain ⟨Q, hQ, hle⟩ := hu
  refine ⟨Q, hQ, ?_⟩
  rintro x ⟨m, rfl⟩
  exact hle ⟨f m, rfl⟩

end SemiringScalars

section RingScalars

variable {R : Type*} [Ring R] {M N : Type*}
  [SeminormedAddCommGroup M] [Module R M] [SeminormedAddCommGroup N] [Module R N]

/-- *Completely continuous* (= compact): an operator-norm limit of finite-rank operators,
phrased metrically.  (Not Mathlib's `IsCompactOperator`, which asks instead that some
neighbourhood of `0` have relatively compact image; the two agree only in the presence of
the approximation property.) -/
def IsCompletelyContinuous (u : M →L[R] N) : Prop :=
  ∀ ε > 0, ∃ v : M →L[R] N, IsFiniteRank v ∧ ‖u - v‖ < ε

theorem IsFiniteRank.isCompletelyContinuous {u : M →L[R] N} (hu : IsFiniteRank u) :
    IsCompletelyContinuous u := by
  intro ε hε
  refine ⟨u, hu, ?_⟩
  rw [sub_self, opNorm_zero]
  exact hε

end RingScalars

end Definitions

variable (R : Type*) [NormedCommRing R] [CompleteSpace R] [NormOneClass R]

section Compact

variable {R}
variable {M N P : Type*}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- The operator norm is submultiplicative under composition.  (Homed here rather than in
`OperatorNorm.lean` for organisational reasons; consumed by the ideal lemmas below.) -/
theorem opNorm_comp_le [IsTate R] (f : N →L[R] P) (u : M →L[R] N) :
    ‖f.comp u‖ ≤ ‖f‖ * ‖u‖ :=
  opNorm_le_of_forall _ (mul_nonneg (opNorm_nonneg f) (opNorm_nonneg u)) fun x => by
    calc ‖(f.comp u) x‖ = ‖f (u x)‖ := by rw [ContinuousLinearMap.comp_apply]
    _ ≤ ‖f‖ * ‖u x‖ := le_opNorm f (u x)
    _ ≤ ‖f‖ * (‖u‖ * ‖x‖) := mul_le_mul_of_nonneg_left (le_opNorm u x) (opNorm_nonneg f)
    _ = ‖f‖ * ‖u‖ * ‖x‖ := (mul_assoc _ _ _).symm

/-- Compacts are stable under operator-norm limits (`ε/2` + `norm_add_le`).
(`[IsTate R]` is needed: subadditivity of the operator norm runs through `le_opNorm`.) -/
theorem isCompletelyContinuous_of_tendsto [IsTate R] (u : ℕ → M →L[R] N) (v : M →L[R] N)
    (hu : ∀ n, IsCompletelyContinuous (u n))
    (huv : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)) :
    IsCompletelyContinuous v := by
  intro ε hε
  rw [Metric.tendsto_atTop] at huv
  obtain ⟨n₀, hn₀⟩ := huv (ε / 2) (half_pos hε)
  obtain ⟨w, hw, hww⟩ := hu n₀ (ε / 2) (half_pos hε)
  refine ⟨w, hw, ?_⟩
  have h1 : ‖u n₀ - v‖ < ε / 2 := by
    have := hn₀ n₀ le_rfl
    rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (opNorm_nonneg _)] at this
  calc ‖v - w‖ = ‖(v - u n₀) + (u n₀ - w)‖ := by rw [sub_add_sub_cancel]
  _ ≤ ‖v - u n₀‖ + ‖u n₀ - w‖ := norm_add_le _ _
  _ = ‖u n₀ - v‖ + ‖u n₀ - w‖ := by rw [opNorm_sub_comm]
  _ < ε / 2 + ε / 2 := add_lt_add h1 hww
  _ = ε := add_halves ε

/-- Two-sided-ideal property, compact half, post-composition ([Bel] Lemma II.1.4;
`‖f∘u − f∘v‖ ≤ ‖f‖‖u − v‖` via `le_opNorm`, whence `[IsTate R]`). -/
theorem IsCompletelyContinuous.comp_left [IsTate R] {u : M →L[R] N}
    (hu : IsCompletelyContinuous u) (f : N →L[R] P) :
    IsCompletelyContinuous (f.comp u) := by
  intro ε hε
  have hf1 : (0 : ℝ) < ‖f‖ + 1 := add_pos_of_nonneg_of_pos (opNorm_nonneg f) zero_lt_one
  obtain ⟨v, hv, hvv⟩ := hu (ε / (‖f‖ + 1)) (div_pos hε hf1)
  refine ⟨f.comp v, hv.comp_left f, ?_⟩
  have hdiff : f.comp u - f.comp v = f.comp (u - v) := by
    ext x
    simp [ContinuousLinearMap.comp_apply]
  rw [hdiff]
  calc ‖f.comp (u - v)‖ ≤ ‖f‖ * ‖u - v‖ := opNorm_comp_le f (u - v)
  _ ≤ ‖f‖ * (ε / (‖f‖ + 1)) := mul_le_mul_of_nonneg_left hvv.le (opNorm_nonneg f)
  _ = ε * (‖f‖ / (‖f‖ + 1)) := by ring
  _ < ε * 1 :=
        mul_lt_mul_of_pos_left ((div_lt_one hf1).2 (by linarith [opNorm_nonneg f])) hε
  _ = ε := mul_one ε

/-- Two-sided-ideal property, compact half, pre-composition ([Bel] Lemma II.1.4). -/
theorem IsCompletelyContinuous.comp_right [IsTate R] {u : M →L[R] N}
    (hu : IsCompletelyContinuous u) (f : P →L[R] M) :
    IsCompletelyContinuous (u.comp f) := by
  intro ε hε
  have hf1 : (0 : ℝ) < ‖f‖ + 1 := add_pos_of_nonneg_of_pos (opNorm_nonneg f) zero_lt_one
  obtain ⟨v, hv, hvv⟩ := hu (ε / (‖f‖ + 1)) (div_pos hε hf1)
  refine ⟨v.comp f, hv.comp_right f, ?_⟩
  have hdiff : u.comp f - v.comp f = (u - v).comp f := by
    ext x
    simp [ContinuousLinearMap.comp_apply]
  rw [hdiff]
  calc ‖(u - v).comp f‖ ≤ ‖u - v‖ * ‖f‖ := opNorm_comp_le (u - v) f
  _ ≤ ε / (‖f‖ + 1) * ‖f‖ := mul_le_mul_of_nonneg_right hvv.le (opNorm_nonneg f)
  _ = ε * (‖f‖ / (‖f‖ + 1)) := by ring
  _ < ε * 1 :=
        mul_lt_mul_of_pos_left ((div_lt_one hf1).2 (by linarith [opNorm_nonneg f])) hε
  _ = ε := mul_one ε

end Compact

end TateFredholm

end
