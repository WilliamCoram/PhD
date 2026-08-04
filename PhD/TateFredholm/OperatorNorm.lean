import PhD.TateFredholm.Tate
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The operator norm on `Hom_R(M, N)` over a Banach–Tate ring
([Bel] II.1.1 under [JN]'s hypotheses; blueprint 6.8–6.10.  See `Tate.lean` for the
development's overview and dictionary.)

Banach `R`-modules are the usual package.  The operator norm is the `sInf` formula (no
Mathlib instance exists over a normed ring); it is `scoped`, as in the parent files.
Boundedness of continuous maps and the Open Mapping Theorem are powered by `ϖ`-scaling —
`[IsTate R]` appears exactly where the parent field-based files needed
`[NormedSpace K M]`. -/

open Filter Topology

noncomputable section

namespace TateFredholm

/-! ### The operator norm, in minimal generality

The `sInf` formula and the facts that follow from it by pure order theory need no
scalar norm, no boundedness of `•`, and no completeness: a semiring of scalars and
seminorms on the modules suffice.  Everything from `le_opNorm` onwards genuinely needs
the Banach–Tate hypotheses, and is stated in the `Modules` section below. -/

section OperatorNorm

section SemiringScalars

variable {R : Type*} [Semiring R] {M N : Type*}
  [SeminormedAddCommGroup M] [Module R M] [SeminormedAddCommGroup N] [Module R N]

/-- The operator norm on `Hom_R(M, N)` — scoped instance, `K`- and `ϖ`-free as a
definition ([Bel] II.1.1, [JN] Definition 2.1.4, blueprint 6.8/6.10). -/
scoped instance instNorm : Norm (M →L[R] N) :=
  ⟨fun u => sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}⟩

theorem norm_def (u : M →L[R] N) :
    ‖u‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖} := rfl

/-- The operator norm is nonnegative (with the convention `sInf ∅ = 0` this needs no
boundedness). -/
theorem opNorm_nonneg (u : M →L[R] N) : 0 ≤ ‖u‖ :=
  Real.sInf_nonneg fun _ hc => hc.1

/-- Any uniform bound witnesses an upper bound for the operator norm. -/
theorem opNorm_le_of_forall (u : M →L[R] N) {C : ℝ} (h0 : 0 ≤ C)
    (h : ∀ x, ‖u x‖ ≤ C * ‖x‖) : ‖u‖ ≤ C :=
  csInf_le ⟨0, fun _ hc => hc.1⟩ ⟨h0, h⟩

@[simp] theorem opNorm_zero : ‖(0 : M →L[R] N)‖ = 0 :=
  le_antisymm (opNorm_le_of_forall _ le_rfl fun x => by simp) (opNorm_nonneg _)

end SemiringScalars

section RingScalars

/-! Negation and subtraction of continuous linear maps are `Ring`-scalar notions in
Mathlib, so the two lemmas that mention them ask for that much and no more. -/

variable {R : Type*} [Ring R] {M N : Type*}
  [SeminormedAddCommGroup M] [Module R M] [SeminormedAddCommGroup N] [Module R N]

@[simp] theorem opNorm_neg (u : M →L[R] N) : ‖-u‖ = ‖u‖ := by
  simp only [norm_def, neg_apply, norm_neg]

theorem opNorm_sub_comm (u v : M →L[R] N) : ‖u - v‖ = ‖v - u‖ := by
  rw [← opNorm_neg, neg_sub]

end RingScalars

end OperatorNorm

variable (R : Type*) [NormedCommRing R] [NormOneClass R]

section Modules

variable {R}
variable {M N : Type*}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Multiplicative units scale module norms exactly: `‖ϖ • m‖ = ‖ϖ‖‖m‖`
([JN] Definition 2.1.4, remark).

*Proof sketch.*  Sandwich `‖m‖ = ‖ϖ⁻¹ • ϖ • m‖ ≤ ‖ϖ⁻¹‖‖ϖ • m‖` with `‖ϖ⁻¹‖ = ‖ϖ‖⁻¹`. -/
theorem norm_pseudoUniformizer_smul (ϖ : PseudoUniformizer R) (m : M) :
    ‖(ϖ : R) • m‖ = ‖(ϖ : R)‖ * ‖m‖ := by
  have : Nontrivial R := NormOneClass.nontrivial
  refine le_antisymm (norm_smul_le _ _) ?_
  have key : ‖m‖ ≤ ‖(ϖ : R)‖⁻¹ * ‖(ϖ : R) • m‖ := by
    calc ‖m‖ = ‖((ϖ.unit⁻¹ : Rˣ) : R) • (ϖ : R) • m‖ := by
          rw [smul_smul, PseudoUniformizer.coe_eq, Units.inv_mul, one_smul]
    _ ≤ ‖((ϖ.unit⁻¹ : Rˣ) : R)‖ * ‖(ϖ : R) • m‖ := norm_smul_le _ _
    _ = ‖(ϖ : R)‖⁻¹ * ‖(ϖ : R) • m‖ := by rw [ϖ.norm_inv]
  calc ‖(ϖ : R)‖ * ‖m‖ ≤ ‖(ϖ : R)‖ * (‖(ϖ : R)‖⁻¹ * ‖(ϖ : R) • m‖) :=
        mul_le_mul_of_nonneg_left key ϖ.norm_pos.le
  _ = ‖(ϖ : R) • m‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ ϖ.norm_pos.ne', one_mul]

/-- Inverse scaling: `‖ϖ⁻¹ • m‖ = ‖ϖ‖⁻¹ ‖m‖`. -/
theorem norm_pseudoUniformizer_inv_smul (ϖ : PseudoUniformizer R) (m : M) :
    ‖((ϖ.unit⁻¹ : Rˣ) : R) • m‖ = ‖(ϖ : R)‖⁻¹ * ‖m‖ := by
  have : Nontrivial R := NormOneClass.nontrivial
  have h := norm_pseudoUniformizer_smul ϖ (((ϖ.unit⁻¹ : Rˣ) : R) • m)
  rw [smul_smul, PseudoUniformizer.coe_eq, Units.mul_inv, one_smul] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ ϖ.norm_pos.ne', one_mul]

/-- Integer-power scaling: `‖ϖⁿ • m‖ = ‖ϖ‖ⁿ ‖m‖` for `n : ℤ` — the exact scaling that
powers Buzzard's `ρ`-trick. -/
theorem norm_pseudoUniformizer_zpow_smul (ϖ : PseudoUniformizer R) (n : ℤ) (m : M) :
    ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ = ‖(ϖ : R)‖ ^ n * ‖m‖ := by
  have : Nontrivial R := NormOneClass.nontrivial
  induction n using Int.induction_on generalizing m with
  | zero => simp
  | succ k ih =>
      rw [zpow_add_one, Units.val_mul, mul_smul, ih, ← PseudoUniformizer.coe_eq,
        norm_pseudoUniformizer_smul, zpow_add_one₀ ϖ.norm_pos.ne']
      ring
  | pred k ih =>
      rw [zpow_sub_one, Units.val_mul, mul_smul, ih, norm_pseudoUniformizer_inv_smul,
        zpow_sub_one₀ ϖ.norm_pos.ne']
      ring

variable [IsTate R]

/-- Continuous ⟹ bounded over a Tate ring, with the fundamental estimate
`‖u x‖ ≤ ‖u‖‖x‖`.

*Proof sketch* (Buzzard's `ρ`-trick, `ϖ` for `ρ`).  Continuity at `0` gives `δ` with
`‖y‖ ≤ δ → ‖u y‖ ≤ 1`; scale `x` by an integer power of `ϖ` into the annulus
`(δ‖ϖ‖, δ]` — exact scaling by `norm_pseudoUniformizer_smul` — and unscale. -/
theorem le_opNorm (u : M →L[R] N) (x : M) : ‖u x‖ ≤ ‖u‖ * ‖x‖ := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨ϖ⟩ := IsTate.nonempty_pseudoUniformizer (A := R)
  have hπpos : 0 < ‖(ϖ : R)‖ := ϖ.norm_pos
  have hπlt : ‖(ϖ : R)‖ < 1 := by rw [PseudoUniformizer.coe_eq]; exact ϖ.norm_lt_one
  -- continuity at `0` gives a δ-ball bound
  obtain ⟨δ, hδpos, hδ'⟩ : ∃ δ > 0, ∀ y : M, ‖y‖ < δ → ‖u y‖ < 1 := by
    have hc : ContinuousAt u 0 := u.continuous.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδpos, h⟩ := hc 1 zero_lt_one
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    have := h (show dist y 0 < δ by rwa [dist_zero_right])
    rwa [map_zero, dist_zero_right] at this
  -- the bound set is nonempty, witnessed by `(δ‖ϖ‖)⁻¹` via ϖ-scaling
  have hmem : (δ * ‖(ϖ : R)‖)⁻¹ ∈ {c : ℝ | 0 ≤ c ∧ ∀ y, ‖u y‖ ≤ c * ‖y‖} := by
    refine ⟨by positivity, fun y => ?_⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
      have hb : 1 < ‖(ϖ : R)‖⁻¹ := (one_lt_inv₀ hπpos).2 hπlt
      obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (div_pos hypos hδpos) hb
      have hnpos : (0 : ℝ) < ‖(ϖ : R)‖ ^ (k + 1) := zpow_pos hπpos _
      -- upper: `‖ϖ‖^(k+1) ‖y‖ < δ`
      have hupper : ‖(ϖ : R)‖ ^ (k + 1) * ‖y‖ < δ := by
        rw [inv_zpow] at hk2
        have h2 := mul_lt_mul_of_pos_left hk2 hnpos
        rw [mul_inv_cancel₀ hnpos.ne'] at h2
        calc ‖(ϖ : R)‖ ^ (k + 1) * ‖y‖
            = ‖(ϖ : R)‖ ^ (k + 1) * (‖y‖ / δ) * δ := by
              rw [mul_assoc, div_mul_cancel₀ _ hδpos.ne']
        _ < 1 * δ := mul_lt_mul_of_pos_right h2 hδpos
        _ = δ := one_mul δ
      -- lower: `δ‖ϖ‖ ≤ ‖ϖ‖^(k+1) ‖y‖`
      have hlower : δ * ‖(ϖ : R)‖ ≤ ‖(ϖ : R)‖ ^ (k + 1) * ‖y‖ := by
        rw [inv_zpow] at hk1
        have hkpos : (0 : ℝ) < ‖(ϖ : R)‖ ^ k := zpow_pos hπpos _
        have h1' : δ ≤ ‖(ϖ : R)‖ ^ k * ‖y‖ := by
          calc δ = ‖(ϖ : R)‖ ^ k * (‖(ϖ : R)‖ ^ k)⁻¹ * δ := by
                rw [mul_inv_cancel₀ hkpos.ne', one_mul]
          _ ≤ ‖(ϖ : R)‖ ^ k * (‖y‖ / δ) * δ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hk1 hkpos.le) hδpos.le
          _ = ‖(ϖ : R)‖ ^ k * ‖y‖ := by
                rw [mul_assoc, div_mul_cancel₀ _ hδpos.ne']
        calc δ * ‖(ϖ : R)‖ ≤ ‖(ϖ : R)‖ ^ k * ‖y‖ * ‖(ϖ : R)‖ :=
              mul_le_mul_of_nonneg_right h1' hπpos.le
        _ = ‖(ϖ : R)‖ ^ (k + 1) * ‖y‖ := by
              rw [zpow_add_one₀ hπpos.ne']; ring
      -- scale into the ball, apply the δ-bound, unscale
      have h1 : ‖u (((ϖ.unit ^ (k + 1) : Rˣ) : R) • y)‖ < 1 := by
        apply hδ'
        rw [norm_pseudoUniformizer_zpow_smul]
        exact hupper
      rw [map_smul, norm_pseudoUniformizer_zpow_smul] at h1
      -- multiply the chain through: `(δ‖ϖ‖) ‖u y‖ ≤ ‖y‖`
      have hchain : δ * ‖(ϖ : R)‖ * ‖u y‖ ≤ ‖y‖ := by
        calc δ * ‖(ϖ : R)‖ * ‖u y‖
            ≤ ‖(ϖ : R)‖ ^ (k + 1) * ‖y‖ * ‖u y‖ :=
              mul_le_mul_of_nonneg_right hlower (norm_nonneg _)
        _ = ‖y‖ * (‖(ϖ : R)‖ ^ (k + 1) * ‖u y‖) := by ring
        _ ≤ ‖y‖ * 1 := mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
        _ = ‖y‖ := mul_one _
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]
      exact hchain
  -- conclude via the greatest-lower-bound property of `sInf`
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hlb : ‖u x‖ / ‖x‖ ∈ lowerBounds {c : ℝ | 0 ≤ c ∧ ∀ y, ‖u y‖ ≤ c * ‖y‖} :=
      fun c hc => (div_le_iff₀ hxpos).2 (hc.2 x)
    have hle : ‖u x‖ / ‖x‖ ≤ ‖u‖ := le_csInf ⟨_, hmem⟩ hlb
    calc ‖u x‖ = ‖u x‖ / ‖x‖ * ‖x‖ := (div_mul_cancel₀ _ hxpos.ne').symm
    _ ≤ ‖u‖ * ‖x‖ := mul_le_mul_of_nonneg_right hle hxpos.le

/-- Subadditivity of the operator norm (stated as a lemma: no `SeminormedAddCommGroup`
instance on `M →L[R] N`, deliberately — see the parent files). -/
theorem norm_add_le (u v : M →L[R] N) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ :=
  opNorm_le_of_forall _ (add_nonneg (opNorm_nonneg u) (opNorm_nonneg v)) fun x => by
    calc ‖(u + v) x‖ = ‖u x + v x‖ := by rw [ContinuousLinearMap.add_apply]
    _ ≤ ‖u x‖ + ‖v x‖ := _root_.norm_add_le _ _
    _ ≤ ‖u‖ * ‖x‖ + ‖v‖ * ‖x‖ := add_le_add (le_opNorm u x) (le_opNorm v x)
    _ = (‖u‖ + ‖v‖) * ‖x‖ := (add_mul _ _ _).symm

/-- `Hom_R(M, N)` is Banach: operator-norm Cauchy sequences converge (metric phrasing). -/
theorem exists_lim_of_cauchySeq [CompleteSpace N] (u : ℕ → M →L[R] N)
    (hu : ∀ ε > 0, ∃ M₀, ∀ m n, M₀ ≤ m → M₀ ≤ n → ‖u m - u n‖ < ε) :
    ∃ v : M →L[R] N, Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
  -- pointwise Cauchy, hence pointwise limits
  have hptwise : ∀ x : M, CauchySeq fun n => u n x := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := hu (ε / (‖x‖ + 1)) (div_pos hε (by positivity))
    refine ⟨M₀, fun m hm n hn => ?_⟩
    have hb := le_opNorm (u m - u n) x
    rw [ContinuousLinearMap.sub_apply] at hb
    calc dist (u m x) (u n x) = ‖u m x - u n x‖ := dist_eq_norm _ _
    _ ≤ ‖u m - u n‖ * ‖x‖ := hb
    _ ≤ ‖u m - u n‖ * (‖x‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) (opNorm_nonneg _)
    _ < ε / (‖x‖ + 1) * (‖x‖ + 1) :=
          mul_lt_mul_of_pos_right (hM₀ m n hm hn) (by positivity)
    _ = ε := div_mul_cancel₀ ε (by positivity)
  choose v₀ hv₀ using fun x => cauchySeq_tendsto_of_complete (hptwise x)
  -- the pointwise limit is linear
  have hadd : ∀ x y, v₀ (x + y) = v₀ x + v₀ y := fun x y =>
    tendsto_nhds_unique (hv₀ (x + y)) (by simpa [map_add] using (hv₀ x).add (hv₀ y))
  have hsmul : ∀ (c : R) (x), v₀ (c • x) = c • v₀ x := fun c x =>
    tendsto_nhds_unique (hv₀ (c • x)) (by simpa [map_smul] using (hv₀ x).const_smul c)
  -- and bounded, hence Lipschitz, hence continuous
  obtain ⟨M₀, hM₀⟩ := hu 1 zero_lt_one
  have hC0 : (0 : ℝ) ≤ ‖u M₀‖ + 1 := add_nonneg (opNorm_nonneg _) zero_le_one
  have hbound : ∀ x, ‖v₀ x‖ ≤ (‖u M₀‖ + 1) * ‖x‖ := by
    intro x
    refine le_of_tendsto (hv₀ x).norm (Filter.eventually_atTop.2 ⟨M₀, fun n hn => ?_⟩)
    calc ‖u n x‖ = ‖((u n - u M₀) + u M₀) x‖ := by rw [sub_add_cancel]
    _ = ‖(u n - u M₀) x + u M₀ x‖ := by rw [ContinuousLinearMap.add_apply]
    _ ≤ ‖(u n - u M₀) x‖ + ‖u M₀ x‖ := _root_.norm_add_le _ _
    _ ≤ ‖u n - u M₀‖ * ‖x‖ + ‖u M₀‖ * ‖x‖ := add_le_add (le_opNorm _ _) (le_opNorm _ _)
    _ ≤ 1 * ‖x‖ + ‖u M₀‖ * ‖x‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right (hM₀ n M₀ hn le_rfl).le (norm_nonneg x)) le_rfl
    _ = (‖u M₀‖ + 1) * ‖x‖ := by ring
  let vlin : M →ₗ[R] N := { toFun := v₀, map_add' := hadd, map_smul' := hsmul }
  have hcont : Continuous vlin :=
    (LipschitzWith.of_dist_le_mul (K := ⟨‖u M₀‖ + 1, hC0⟩) fun x y => by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub vlin]
      exact hbound (x - y)).continuous
  refine ⟨⟨vlin, hcont⟩, ?_⟩
  -- convergence in the operator norm
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₁, hM₁⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨M₁, fun n hn => ?_⟩
  have hle : ‖u n - (⟨vlin, hcont⟩ : M →L[R] N)‖ ≤ ε / 2 := by
    refine opNorm_le_of_forall _ (half_pos hε).le fun x => ?_
    have htend : Tendsto (fun m => ‖u n x - u m x‖) atTop
        (𝓝 ‖(u n - (⟨vlin, hcont⟩ : M →L[R] N)) x‖) := by
      rw [ContinuousLinearMap.sub_apply]
      exact (tendsto_const_nhds.sub (hv₀ x)).norm
    refine le_of_tendsto htend (Filter.eventually_atTop.2 ⟨M₁, fun m hm => ?_⟩)
    calc ‖u n x - u m x‖ = ‖(u n - u m) x‖ := by rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖u n - u m‖ * ‖x‖ := le_opNorm _ _
    _ ≤ ε / 2 * ‖x‖ := mul_le_mul_of_nonneg_right (hM₁ n m hn hm).le (norm_nonneg x)
  calc dist ‖u n - (⟨vlin, hcont⟩ : M →L[R] N)‖ 0
      = ‖u n - (⟨vlin, hcont⟩ : M →L[R] N)‖ := by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (opNorm_nonneg _)]
  _ ≤ ε / 2 := hle
  _ < ε := by linarith

omit [IsTate R] in
/-- Rescaling to a shell by an integer power of `ϖ` — the pseudo-uniformizer analogue of
Mathlib's `rescale_to_shell` (which rescales by a field scalar `c` with `1 < ‖c‖`).  Given
`ε > 0` and `y ≠ 0`, some power `ϖ ^ j` scales `y` into the annulus `(ε‖ϖ‖, ε]`.  The
computation mirrors `le_opNorm` above, with `δ` replaced by `ε`. -/
private theorem exists_zpow_smul_mem_shell (ϖ : PseudoUniformizer R) {ε : ℝ} (εpos : 0 < ε)
    {y : M} (hy : y ≠ 0) :
    ∃ j : ℤ, ‖((ϖ.unit ^ j : Rˣ) : R) • y‖ < ε ∧
      ε * ‖(ϖ : R)‖ ≤ ‖((ϖ.unit ^ j : Rˣ) : R) • y‖ := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hπpos : 0 < ‖(ϖ : R)‖ := ϖ.norm_pos
  have hπlt : ‖(ϖ : R)‖ < 1 := by rw [PseudoUniformizer.coe_eq]; exact ϖ.norm_lt_one
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hb : 1 < ‖(ϖ : R)‖⁻¹ := (one_lt_inv₀ hπpos).2 hπlt
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (div_pos hypos εpos) hb
  have hnpos : (0 : ℝ) < ‖(ϖ : R)‖ ^ (k + 1) := zpow_pos hπpos _
  refine ⟨k + 1, ?_, ?_⟩
  · rw [norm_pseudoUniformizer_zpow_smul]
    rw [inv_zpow] at hk2
    have h2 := mul_lt_mul_of_pos_left hk2 hnpos
    rw [mul_inv_cancel₀ hnpos.ne'] at h2
    calc ‖(ϖ : R)‖ ^ (k + 1) * ‖y‖
        = ‖(ϖ : R)‖ ^ (k + 1) * (‖y‖ / ε) * ε := by
          rw [mul_assoc, div_mul_cancel₀ _ εpos.ne']
    _ < 1 * ε := mul_lt_mul_of_pos_right h2 εpos
    _ = ε := one_mul ε
  · rw [norm_pseudoUniformizer_zpow_smul]
    rw [inv_zpow] at hk1
    have hkpos : (0 : ℝ) < ‖(ϖ : R)‖ ^ k := zpow_pos hπpos _
    have h1' : ε ≤ ‖(ϖ : R)‖ ^ k * ‖y‖ := by
      calc ε = ‖(ϖ : R)‖ ^ k * (‖(ϖ : R)‖ ^ k)⁻¹ * ε := by
            rw [mul_inv_cancel₀ hkpos.ne', one_mul]
      _ ≤ ‖(ϖ : R)‖ ^ k * (‖y‖ / ε) * ε :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hk1 hkpos.le) εpos.le
      _ = ‖(ϖ : R)‖ ^ k * ‖y‖ := by
            rw [mul_assoc, div_mul_cancel₀ _ εpos.ne']
    calc ε * ‖(ϖ : R)‖ ≤ ‖(ϖ : R)‖ ^ k * ‖y‖ * ‖(ϖ : R)‖ :=
          mul_le_mul_of_nonneg_right h1' hπpos.le
    _ = ‖(ϖ : R)‖ ^ (k + 1) * ‖y‖ := by
          rw [zpow_add_one₀ hπpos.ne']; ring

/-- **First step of the Open Mapping Theorem** (Baire + `ϖ`-rescaling): every `y : N` is
approximated within `‖y‖ / 2` by the image of some `x : M` with `‖x‖ ≤ C‖y‖`.  The
pseudo-uniformizer analogue of Mathlib's `exists_approx_preimage_norm_le`: where Mathlib
rescales an arbitrary `y` into the Baire ball by a field scalar, we use an integer power of
`ϖ` (via `exists_zpow_smul_mem_shell`). -/
private theorem exists_approx_preimage_norm_le [CompleteSpace N]
    (f : M →L[R] N) (hf : Function.Surjective f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : N, ∃ x : M,
      dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨ϖ⟩ := IsTate.nonempty_pseudoUniformizer (A := R)
  have hπpos : 0 < ‖(ϖ : R)‖ := ϖ.norm_pos
  -- Baire: the closures of images of balls cover `N`
  have hcover : ⋃ nn : ℕ, closure (f '' Metric.ball 0 nn) = Set.univ := by
    refine Set.Subset.antisymm (Set.subset_univ _) fun y _ => ?_
    obtain ⟨x, hx⟩ := hf y
    obtain ⟨nn, hn⟩ := exists_nat_gt ‖x‖
    refine Set.mem_iUnion.2 ⟨nn, subset_closure ?_⟩
    refine ⟨x, ?_, hx⟩
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  obtain ⟨nn, a, ha⟩ :=
    nonempty_interior_of_iUnion_of_closed (fun nn => isClosed_closure) hcover
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at ha
  obtain ⟨ε, εpos, H⟩ := ha
  refine ⟨4 * (nn : ℝ) / (ε * ‖(ϖ : R)‖),
    div_nonneg (by positivity) (mul_pos εpos hπpos).le, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  · -- scale `y` into the shell around `a`, so `a + dy ∈ ball a ε`
    obtain ⟨j, hjlt, hjle⟩ := exists_zpow_smul_mem_shell ϖ (half_pos εpos) hy
    set dy : N := ((ϖ.unit ^ j : Rˣ) : R) • y with hdy_def
    have hdynorm : ‖dy‖ = ‖(ϖ : R)‖ ^ j * ‖y‖ := by
      rw [hdy_def, norm_pseudoUniformizer_zpow_smul]
    have hdypos : 0 < ‖dy‖ := by
      rw [hdynorm]; exact mul_pos (zpow_pos hπpos j) (norm_pos_iff.2 hy)
    set δ : ℝ := ‖dy‖ / 4 with hδdef
    have δpos : 0 < δ := by rw [hδdef]; exact div_pos hdypos (by norm_num)
    -- approximate `a + dy` and `a` by images of small-norm elements
    have hmem1 : a + dy ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact lt_trans hjlt (half_lt_self εpos)
    obtain ⟨z₁, hz₁im, hz₁⟩ := Metric.mem_closure_iff.1 (H hmem1) δ δpos
    obtain ⟨x₁, hx₁ball, hx₁eq⟩ := hz₁im
    rw [← hx₁eq] at hz₁
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx₁ball
    have hmem2 : a ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, dist_self]; exact εpos
    obtain ⟨z₂, hz₂im, hz₂⟩ := Metric.mem_closure_iff.1 (H hmem2) δ δpos
    obtain ⟨x₂, hx₂ball, hx₂eq⟩ := hz₂im
    rw [← hx₂eq] at hz₂
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx₂ball
    -- the difference `x₁ - x₂` maps close to `dy`
    have hI : ‖f (x₁ - x₂) - dy‖ ≤ 2 * δ := by
      have hb1 : ‖f x₁ - (a + dy)‖ ≤ δ := by
        rw [← dist_eq_norm, dist_comm]; exact hz₁.le
      have hb2 : ‖f x₂ - a‖ ≤ δ := by
        rw [← dist_eq_norm, dist_comm]; exact hz₂.le
      have e1 : f (x₁ - x₂) - dy = (f x₁ - (a + dy)) - (f x₂ - a) := by
        rw [map_sub]; abel
      rw [e1]
      calc ‖(f x₁ - (a + dy)) - (f x₂ - a)‖
          ≤ ‖f x₁ - (a + dy)‖ + ‖f x₂ - a‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add hb1 hb2
      _ = 2 * δ := by ring
    -- unscale: `x' = ϖ^(-j) • (x₁ - x₂)` is the approximate preimage of `y`
    set x' : M := ((ϖ.unit ^ (-j) : Rˣ) : R) • (x₁ - x₂) with hx'_def
    have hcancel : ((ϖ.unit ^ (-j) : Rˣ) : R) • dy = y := by
      rw [hdy_def, smul_smul, ← Units.val_mul, zpow_neg, inv_mul_cancel,
        Units.val_one, one_smul]
    have hfx' : f x' = ((ϖ.unit ^ (-j) : Rˣ) : R) • f (x₁ - x₂) := by
      rw [hx'_def, map_smul]
    have e2 : f x' - y = ((ϖ.unit ^ (-j) : Rˣ) : R) • (f (x₁ - x₂) - dy) := by
      rw [smul_sub, hcancel, hfx']
    have hJnorm : ‖f x' - y‖ = ‖(ϖ : R)‖ ^ (-j) * ‖f (x₁ - x₂) - dy‖ := by
      rw [e2, norm_pseudoUniformizer_zpow_smul]
    have hkey : ‖(ϖ : R)‖ ^ (-j) * ‖dy‖ = ‖y‖ := by
      rw [hdynorm, ← mul_assoc, ← zpow_add₀ hπpos.ne', neg_add_cancel, zpow_zero, one_mul]
    -- the approximation bound `J`
    have hJ : ‖f x' - y‖ ≤ 1 / 2 * ‖y‖ := by
      rw [hJnorm]
      have h2δ : ‖f (x₁ - x₂) - dy‖ ≤ ‖dy‖ / 2 := by
        have e : (2 : ℝ) * δ = ‖dy‖ / 2 := by rw [hδdef]; ring
        rw [← e]; exact hI
      calc ‖(ϖ : R)‖ ^ (-j) * ‖f (x₁ - x₂) - dy‖
          ≤ ‖(ϖ : R)‖ ^ (-j) * (‖dy‖ / 2) :=
            mul_le_mul_of_nonneg_left h2δ (zpow_nonneg hπpos.le _)
      _ = ‖(ϖ : R)‖ ^ (-j) * ‖dy‖ / 2 := by ring
      _ = ‖y‖ / 2 := by rw [hkey]
      _ = 1 / 2 * ‖y‖ := by ring
    -- the norm bound `K`
    have hzpnn : (0 : ℝ) ≤ ‖(ϖ : R)‖ ^ (-j) := zpow_nonneg hπpos.le _
    have hx12 : ‖x₁ - x₂‖ ≤ 2 * (nn : ℝ) := by
      calc ‖x₁ - x₂‖ ≤ ‖x₁‖ + ‖x₂‖ := norm_sub_le _ _
      _ ≤ (nn : ℝ) + (nn : ℝ) := add_le_add hx₁ball.le hx₂ball.le
      _ = 2 * (nn : ℝ) := by ring
    have hbnd : ‖(ϖ : R)‖ ^ (-j) * (ε * ‖(ϖ : R)‖) ≤ 2 * ‖y‖ := by
      have hmul := mul_le_mul_of_nonneg_left hjle hzpnn
      rw [hkey] at hmul
      have e : ‖(ϖ : R)‖ ^ (-j) * (ε * ‖(ϖ : R)‖)
          = 2 * (‖(ϖ : R)‖ ^ (-j) * (ε / 2 * ‖(ϖ : R)‖)) := by ring
      rw [e]; linarith
    have hxnorm : ‖x'‖ = ‖(ϖ : R)‖ ^ (-j) * ‖x₁ - x₂‖ := by
      rw [hx'_def, norm_pseudoUniformizer_zpow_smul]
    have hK : ‖x'‖ ≤ 4 * (nn : ℝ) / (ε * ‖(ϖ : R)‖) * ‖y‖ := by
      rw [hxnorm, div_mul_eq_mul_div, le_div_iff₀ (mul_pos εpos hπpos)]
      calc ‖(ϖ : R)‖ ^ (-j) * ‖x₁ - x₂‖ * (ε * ‖(ϖ : R)‖)
          = ‖x₁ - x₂‖ * (‖(ϖ : R)‖ ^ (-j) * (ε * ‖(ϖ : R)‖)) := by ring
      _ ≤ 2 * (nn : ℝ) * (2 * ‖y‖) :=
            mul_le_mul hx12 hbnd (mul_nonneg hzpnn (mul_pos εpos hπpos).le) (by positivity)
      _ = 4 * (nn : ℝ) * ‖y‖ := by ring
    exact ⟨x', by rw [dist_eq_norm]; exact hJ, hK⟩

/-- **Quantitative Open Mapping Theorem over a Banach–Tate ring** ([Bel] II.1.1 over a
field; [JN] Definition 2.1.4 citing [Hub94, Lemma 2.4(i)] in this generality).

This generalises Mathlib's `ContinuousLinearMap.exists_preimage_norm_le` in the scalar
direction: Mathlib's version needs `NontriviallyNormedField` scalars, whereas Baire plus
`ϖ`-scaling only needs a pseudo-uniformizer.  Every nontrivially normed field is `IsTate`,
so specialising `R` to one recovers Mathlib's statement for `σ = RingHom.id`; the
`σ`-semilinear case is the part Mathlib covers and this does not. -/
theorem exists_preimage_norm_le [CompleteSpace M] [CompleteSpace N]
    (f : M →L[R] N) (hf : Function.Surjective f) :
    ∃ C > 0, ∀ n : N, ∃ m : M, f m = n ∧ ‖m‖ ≤ C * ‖n‖ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f hf
  choose g hg using hC
  -- iterate the approximation, leaving a residual `h^[n] y → 0`
  let h := fun y : N => y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    show ‖y - f (g y)‖ ≤ 1 / 2 * ‖y‖
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, Function.iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [Function.iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  -- the series `∑ u n` of approximate preimages converges in the complete space `M`
  let u := fun n : ℕ => g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := ∑' n, u n
  have x_ineq : ‖x‖ ≤ (2 * C + 1) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  -- `f` sends the partial sums to `y - h^[n] y`, hence the total sum to `y`
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [Finset.sum_range_succ, map_add, IH, Function.iterate_succ_apply', sub_add]
  have hxt : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) :=
    su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp hxt
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

/-- The operator norm detects the zero operator: `‖u‖ = 0 ↔ u = 0` (forward via the
fundamental estimate `le_opNorm`, backward via `opNorm_zero`). -/
theorem opNorm_eq_zero_iff (u : M →L[R] N) : ‖u‖ = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext x
    have hx : ‖u x‖ ≤ 0 := by have := le_opNorm u x; rwa [h, zero_mul] at this
    rw [ContinuousLinearMap.zero_apply]
    exact norm_le_zero_iff.mp hx
  · intro h; rw [h]; exact opNorm_zero

/-- Submultiplicativity of the operator norm on endomorphisms, for the ring product
(`*` is composition, `ContinuousLinearMap.mul_def`).  Proved inline here — the general
`opNorm_comp_le` lives downstream in `Compact.lean` — to power the Neumann series below. -/
theorem opNorm_mul_le (f g : M →L[R] M) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [ContinuousLinearMap.mul_def]
  refine opNorm_le_of_forall _ (mul_nonneg (opNorm_nonneg f) (opNorm_nonneg g)) fun x => ?_
  calc ‖(f.comp g) x‖ = ‖f (g x)‖ := by rw [ContinuousLinearMap.comp_apply]
  _ ≤ ‖f‖ * ‖g x‖ := le_opNorm f (g x)
  _ ≤ ‖f‖ * (‖g‖ * ‖x‖) := mul_le_mul_of_nonneg_left (le_opNorm g x) (opNorm_nonneg f)
  _ = ‖f‖ * ‖g‖ * ‖x‖ := (mul_assoc _ _ _).symm

omit [NormOneClass R] [IsBoundedSMul R M] [IsTate R] in
/-- The identity operator has operator norm at most `1` (`‖id x‖ = ‖x‖ = 1·‖x‖`). -/
theorem opNorm_one_le : ‖(1 : M →L[R] M)‖ ≤ 1 :=
  opNorm_le_of_forall _ zero_le_one fun x =>
    le_of_eq (by rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, one_mul])

/-- Triangle inequality for finite sums of operators (`norm_sum_le` does not apply: there is
no `SeminormedAddCommGroup` on `M →L[R] N`).  Proved by `Finset.induction` from
`norm_add_le` and `opNorm_zero`. -/
theorem opNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → M →L[R] N) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (norm_add_le _ _) (add_le_add le_rfl ih)

/-- Powers of an endomorphism obey `‖tᵏ‖ ≤ ‖t‖ᵏ` (submultiplicativity + induction;
`k = 0` uses `opNorm_one_le`). -/
theorem opNorm_pow_le (t : M →L[R] M) : ∀ k : ℕ, ‖t ^ k‖ ≤ ‖t‖ ^ k := by
  intro k
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact opNorm_one_le
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact le_trans (opNorm_mul_le (t ^ k) t) (mul_le_mul_of_nonneg_right ih (opNorm_nonneg t))

/-- **Neumann series** ([Bel] II.1, Riesz theory input): if `‖1 − w‖ < 1` then `w` is a
two-sided unit in the endomorphism ring.  The inverse is the operator-norm limit of the
partial sums `Sₙ = ∑_{k<n} (1 − w)ᵏ`, which is Cauchy because `‖Sₚ − S_q‖ ≤ ‖t‖^q/(1−‖t‖)`
(with `t = 1 − w`); telescoping `w·Sₙ = Sₙ·w = 1 − tⁿ` gives `w·v = v·w = 1` in the limit. -/
theorem exists_inverse_of_norm_id_sub_lt_one [CompleteSpace M]
    (w : M →L[R] M) (hw : ‖ContinuousLinearMap.id R M - w‖ < 1) :
    ∃ v : M →L[R] M, w.comp v = ContinuousLinearMap.id R M ∧
      v.comp w = ContinuousLinearMap.id R M := by
  rw [← ContinuousLinearMap.one_def] at hw
  set t : M →L[R] M := 1 - w with ht_def
  have hr0 : 0 ≤ ‖t‖ := opNorm_nonneg t
  have hr1 : ‖t‖ < 1 := hw
  have hwt : w = 1 - t := by rw [ht_def]; abel
  set S : ℕ → (M →L[R] M) := fun n => ∑ k ∈ Finset.range n, t ^ k with hS_def
  -- telescoping identities `w · Sₙ = Sₙ · w = 1 − tⁿ`
  have hgeomR : ∀ n : ℕ, w * S n = 1 - t ^ n := by
    intro n; simp only [hS_def]
    rw [hwt, ← neg_sub t 1, neg_mul, mul_geom_sum]; abel
  have hgeomL : ∀ n : ℕ, S n * w = 1 - t ^ n := by
    intro n; simp only [hS_def]
    rw [hwt, ← neg_sub t 1, mul_neg, geom_sum_mul]; abel
  -- the partial sums are Cauchy: an `Ico`-block bound plus the geometric tail
  have hbound : ∀ p q : ℕ, q ≤ p → ‖S p - S q‖ ≤ ‖t‖ ^ q / (1 - ‖t‖) := by
    intro p q hqp
    have hsplit : S p - S q = ∑ k ∈ Finset.Ico q p, t ^ k := by
      simp only [hS_def]; exact (Finset.sum_Ico_eq_sub (fun k => t ^ k) hqp).symm
    rw [hsplit]
    calc ‖∑ k ∈ Finset.Ico q p, t ^ k‖
        ≤ ∑ k ∈ Finset.Ico q p, ‖t ^ k‖ := opNorm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico q p, ‖t‖ ^ k := Finset.sum_le_sum fun k _ => opNorm_pow_le t k
      _ ≤ ‖t‖ ^ q / (1 - ‖t‖) := geom_sum_Ico_le_of_lt_one hr0 hr1
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ‖S m - S n‖ < ε := by
    intro ε hε
    have htendDiv : Tendsto (fun n => ‖t‖ ^ n / (1 - ‖t‖)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).div_const (1 - ‖t‖)
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htendDiv) ε hε
    have hval : ∀ n, N ≤ n → ‖t‖ ^ n / (1 - ‖t‖) < ε := by
      intro n hn
      have := hN n hn
      rwa [Real.dist_eq, sub_zero,
        abs_of_nonneg (div_nonneg (pow_nonneg hr0 n) (by linarith))] at this
    refine ⟨N, fun m n hm hn => ?_⟩
    rcases le_total n m with h | h
    · exact lt_of_le_of_lt (hbound m n h) (hval n hn)
    · rw [opNorm_sub_comm]; exact lt_of_le_of_lt (hbound n m h) (hval m hm)
  obtain ⟨v, hv⟩ := exists_lim_of_cauchySeq S hcauchy
  -- limit passage on the right: `w · v = 1`
  have key : ∀ n : ℕ, ‖w * v - 1‖ ≤ ‖w‖ * ‖S n - v‖ + ‖t‖ ^ n := by
    intro n
    have hg := hgeomR n
    have e : w * v - 1 = w * (v - S n) - t ^ n := by rw [mul_sub, hg]; abel
    calc ‖w * v - 1‖ = ‖w * (v - S n) - t ^ n‖ := by rw [e]
      _ ≤ ‖w * (v - S n)‖ + ‖t ^ n‖ := by
          rw [sub_eq_add_neg, ← opNorm_neg (t ^ n)]; exact norm_add_le _ _
      _ ≤ ‖w‖ * ‖v - S n‖ + ‖t‖ ^ n :=
          add_le_add (opNorm_mul_le w (v - S n)) (opNorm_pow_le t n)
      _ = ‖w‖ * ‖S n - v‖ + ‖t‖ ^ n := by rw [opNorm_sub_comm v (S n)]
  have htend0 : Tendsto (fun n => ‖w‖ * ‖S n - v‖ + ‖t‖ ^ n) atTop (𝓝 0) := by
    have h1 := hv.const_mul ‖w‖
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using h1.add h2
  have hwv : w * v = 1 := by
    have hz : ‖w * v - 1‖ = 0 := le_antisymm (ge_of_tendsto' htend0 key) (opNorm_nonneg _)
    exact sub_eq_zero.mp ((opNorm_eq_zero_iff _).mp hz)
  -- limit passage on the left: `v · w = 1`
  have keyL : ∀ n : ℕ, ‖v * w - 1‖ ≤ ‖S n - v‖ * ‖w‖ + ‖t‖ ^ n := by
    intro n
    have hg := hgeomL n
    have e : v * w - 1 = (v - S n) * w - t ^ n := by rw [sub_mul, hg]; abel
    calc ‖v * w - 1‖ = ‖(v - S n) * w - t ^ n‖ := by rw [e]
      _ ≤ ‖(v - S n) * w‖ + ‖t ^ n‖ := by
          rw [sub_eq_add_neg, ← opNorm_neg (t ^ n)]; exact norm_add_le _ _
      _ ≤ ‖S n - v‖ * ‖w‖ + ‖t‖ ^ n := by
          refine add_le_add ?_ (opNorm_pow_le t n)
          calc ‖(v - S n) * w‖ ≤ ‖v - S n‖ * ‖w‖ := opNorm_mul_le (v - S n) w
            _ = ‖S n - v‖ * ‖w‖ := by rw [opNorm_sub_comm v (S n)]
  have htend0L : Tendsto (fun n => ‖S n - v‖ * ‖w‖ + ‖t‖ ^ n) atTop (𝓝 0) := by
    have h1 := hv.mul_const ‖w‖
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using h1.add h2
  have hvw : v * w = 1 := by
    have hz : ‖v * w - 1‖ = 0 := le_antisymm (ge_of_tendsto' htend0L keyL) (opNorm_nonneg _)
    exact sub_eq_zero.mp ((opNorm_eq_zero_iff _).mp hz)
  refine ⟨v, ?_, ?_⟩
  · rw [← ContinuousLinearMap.mul_def, hwv]; exact ContinuousLinearMap.one_def
  · rw [← ContinuousLinearMap.mul_def, hvw]; exact ContinuousLinearMap.one_def

end Modules

end TateFredholm

end
