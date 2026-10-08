/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Continuity
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.SupSeminorm

/-!
# Power-bounded and topologically nilpotent elements of an affinoid algebra

Layer 2, §2.3.1–§2.3.3 and the first half of §2.3.5 (BGR 6.2.3/1–3). For an affinoid algebra
`A` with any complete `K`-algebra norm, `f` is power-bounded iff `|f|_sup ≤ 1` (6.2.3/1),
topologically nilpotent iff `|f|_sup < 1` iff `|f(x)| < 1` at every point (6.2.3/2), and
`|f|_sup = inf_i ‖fⁱ‖^{1/i}` (6.2.3/3, Mathlib's `smoothingFun`). Hence the power-bounded elements
`Å = {|f|_sup ≤ 1}` form a subring independent of the norm with the ideal `Ǎ = {|f|_sup < 1}` of
topologically nilpotent elements; `Å` is open and closed and `Ǎ` is open; and `Å` is bounded iff
`|·|_sup` is equivalent to the norm.

## Main declarations

* `Affinoid.powerBounded K A`, `Affinoid.topologicallyNilpotent K A`: `Å` and `Ǎ` (for
  `[HasSupSeminorm K A]`), with `Affinoid.topologicallyNilpotent_isRadical` and
  `Affinoid.algebraMap_mem_powerBounded`.
* `IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`,
  `IsAffinoidAlgebra.isPowerBounded_iff_mem_powerBounded`: BGR 6.2.3/1 (M3).
* `IsAffinoidAlgebra.isTopologicallyNilpotent_iff_supSeminorm_lt_one`,
  `IsAffinoidAlgebra.isTopologicallyNilpotent_iff_forall_evalNorm_lt_one`,
  `IsAffinoidAlgebra.isTopologicallyNilpotent_iff_mem_topologicallyNilpotent`: BGR 6.2.3/2.
* `IsAffinoidAlgebra.supSeminorm_eq_smoothingFun`: BGR 6.2.3/3 (M3).
* `IsAffinoidAlgebra.lipschitzWith_supSeminorm`, `IsAffinoidAlgebra.isClosed_powerBounded`,
  `IsAffinoidAlgebra.isOpen_powerBounded`, `IsAffinoidAlgebra.isOpen_setOf_supSeminorm_lt_one`:
  §2.4.3.
* `IsAffinoidAlgebra.exists_norm_le_mul_supSeminorm_iff_isBounded_powerBounded`,
  `IsAffinoidAlgebra.isReduced_of_isBounded_powerBounded`: §2.3.5.
-/

open Affinoid PowerBounded

namespace Affinoid

section Subring

variable (K : Type*) [NormedField K] [IsUltrametricDist K] (A : Type*) [CommRing A] [Algebra K A]
  [HasSupSeminorm K A]

/-- `Å = {f | |f|_sup ≤ 1}`, the power-bounded elements of an affinoid algebra (BGR 6.2.3/1,
1.2.5/2): a subring by BGR 3.8.1/3. -/
noncomputable def powerBounded : Subring A where
  carrier := {f | supSeminorm K f ≤ 1}
  mul_mem' := fun {a b} ha hb ↦
    (supSeminorm_mul_le K a b).trans (mul_le_one₀ ha (supSeminorm_nonneg K b) hb)
  one_mem' := supSeminorm_one_le K
  add_mem' := fun {a b} ha hb ↦ (supSeminorm_add_le_max K a b).trans (max_le ha hb)
  zero_mem' := (supSeminorm_zero K).trans_le zero_le_one
  neg_mem' := fun {a} ha ↦ (supSeminorm_neg K a).trans_le ha

/-- `Ǎ = {f | |f|_sup < 1}`, the topologically nilpotent elements, an ideal of `Å`
(BGR 6.2.3/2, 1.2.5/2). -/
noncomputable def topologicallyNilpotent : Ideal (powerBounded K A) where
  carrier := {f | supSeminorm K (f : A) < 1}
  add_mem' := fun {a b} ha hb ↦ (supSeminorm_add_le_max K (a : A) b).trans_lt (max_lt ha hb)
  zero_mem' := (supSeminorm_zero K).trans_lt zero_lt_one
  smul_mem' := fun c {f} hf ↦ (supSeminorm_mul_le K (c : A) f).trans_lt
    (mul_lt_one_of_nonneg_of_lt_one_right c.2 (supSeminorm_nonneg K _) hf)

variable {K A}

@[simp]
theorem mem_powerBounded {f : A} : f ∈ powerBounded K A ↔ supSeminorm K f ≤ 1 := Iff.rfl

@[simp]
theorem mem_topologicallyNilpotent {f : powerBounded K A} :
    f ∈ topologicallyNilpotent K A ↔ supSeminorm K (f : A) < 1 := Iff.rfl

/-- `Ǎ` is a radical ideal of `Å` (BGR 1.2.5/7: `Ã = Å/Ǎ` is reduced), by power-multiplicativity. -/
theorem topologicallyNilpotent_isRadical : (topologicallyNilpotent K A).IsRadical := by
  rintro f ⟨n, hn⟩
  rw [mem_topologicallyNilpotent, SubmonoidClass.coe_pow] at hn
  rw [mem_topologicallyNilpotent]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- `|1|_sup < 1` forces `|f|_sup ≤ |1|_sup |f|_sup < 1`
    rw [pow_zero] at hn
    calc supSeminorm K (f : A) = supSeminorm K (1 * (f : A)) := by rw [one_mul]
      _ ≤ supSeminorm K (1 : A) * supSeminorm K (f : A) := supSeminorm_mul_le K _ _
      _ ≤ supSeminorm K (1 : A) * 1 := mul_le_mul_of_nonneg_left f.2 (supSeminorm_nonneg K _)
      _ < 1 := by rwa [mul_one]
  · rw [supSeminorm_pow K _ hn0.ne'] at hn
    exact (pow_lt_one_iff_of_nonneg (supSeminorm_nonneg K _) hn0.ne').1 hn

/-- The scalars of absolute value `≤ 1` are power-bounded. -/
theorem algebraMap_mem_powerBounded {c : K} (hc : ‖c‖ ≤ 1) :
    algebraMap K A c ∈ powerBounded K A := by
  rw [mem_powerBounded, Algebra.algebraMap_eq_smul_one, supSeminorm_smul]
  exact mul_le_one₀ hc (supSeminorm_nonneg K _) (supSeminorm_one_le K)

end Subring

end Affinoid

namespace IsAffinoidAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A]

/-- **BGR 6.2.3/1** (Bosch 1.4/16): `f` is power-bounded iff `|f|_sup ≤ 1`. "⇒" is 3.8.2/2 with
power-multiplicativity; "⇐": choose a finite `φ : T_d → A`, an integral equation with
`|f|_sup = max |tᵢ|^{1/i}` (6.2.2/4), so `tᵢ ∈ T̊_d`, and `f^{n+ν} ∈ Σ_{i<n} φ(T̊_d) fⁱ` by
induction, a bounded set since `φ(T̊_d)` is bounded (`φ` continuous, Layer 1). -/
theorem isPowerBounded_iff_supSeminorm_le_one (hA : IsAffinoidAlgebra K A) (f : A) :
    IsPowerBounded f ↔ supSeminorm K f ≤ 1 := by
  haveI := hA.hasSupSeminorm
  refine ⟨fun hf ↦ IsPowerBounded.supSeminorm_le_one K hf, fun hf ↦ ?_⟩
  -- a presentation `α : Tₙ ↠ A`, continuous (Layer 1), hence bounded
  obtain ⟨n, α, hα⟩ := id hA
  obtain ⟨C, hC0, hC⟩ :=
    SemilinearMapClass.bound_of_continuous α.toLinearMap (hA.continuous_presentation α)
  -- an integral equation `q(f) = 0` over `Tₙ` with `σ(q) = |f|_sup ≤ 1` (BGR 6.2.2/4)
  obtain ⟨q, hq, hqf, hσ⟩ := hA.exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue
    (tateAlgebra n) α (RingHom.Finite.of_surjective _ hα) f
  have hσ1 : supSpectralValue K q ≤ 1 := hσ ▸ hf
  -- the coefficients of `q` lie in `T̊ₙ`, which `α` maps into the ball of radius `C`
  refine isPowerBounded_of_eval₂_eq_zero (α : TateAlgebra K n →+* A)
    (powerBounded K (TateAlgebra K n)) hq (fun i ↦ ?_) (M := C) (fun c hc ↦ ?_) hqf
  · exact mem_powerBounded.2 ((supSeminorm_coeff_le_supSpectralValue_pow_of_monic K hq i).trans
      (pow_le_one₀ (supSpectralValue_nonneg K _) hσ1))
  · have hc' : ‖c‖ ≤ 1 :=
      (MvPowerSeries.Restricted.supSeminorm_eq_norm c).symm.trans_le (mem_powerBounded.1 hc)
    exact (hC c).trans (mul_le_of_le_one_right hC0.le hc')

/-- The subring `Å` is the set of power-bounded elements for every complete algebra norm. -/
theorem isPowerBounded_iff_mem_powerBounded (hA : IsAffinoidAlgebra K A) (f : A) :
    haveI := hA.hasSupSeminorm
    IsPowerBounded f ↔ f ∈ powerBounded K A :=
  hA.isPowerBounded_iff_supSeminorm_le_one f

/-- **BGR 6.2.3/2 (i) ⇔ (iii)** (Bosch 1.4/17): `f` is topologically nilpotent iff `|f|_sup < 1`.
"⇒" by 3.8.2/2 and power-multiplicativity; "⇐" by 6.2.1/4 (ii): `|c f^m|_sup ≤ 1` for some
`|c| > 1`, so `c f^m` is power-bounded and `f^m ∈ c⁻¹ Å ⊆ Ǎ`. -/
theorem isTopologicallyNilpotent_iff_supSeminorm_lt_one (hA : IsAffinoidAlgebra K A) (f : A) :
    IsTopologicallyNilpotent f ↔ supSeminorm K f < 1 := by
  haveI := hA.hasSupSeminorm
  refine ⟨fun hf ↦ IsTopologicallyNilpotent.supSeminorm_lt_one K hf, fun hf ↦ ?_⟩
  rcases eq_or_ne (supSeminorm K f) 0 with h0 | h0
  · -- `f` is nilpotent (BGR 6.2.1/4 (iii))
    obtain ⟨n, hn⟩ := (hA.supSeminorm_eq_zero_iff_isNilpotent f).1 h0
    refine isTopologicallyNilpotent_of_norm_pow_lt_one (Nat.succ_ne_zero n) ?_
    rw [pow_succ, hn, zero_mul, norm_zero]
    exact zero_lt_one
  -- `|c fᵐ|_sup = 1` (BGR 6.2.1/4 (ii)): `c fᵐ` is power-bounded and `‖c‖ > 1`
  obtain ⟨c, m, hm, hc⟩ := hA.exists_smul_pow_supSeminorm_eq_one h0
  obtain ⟨M, hM⟩ := PowerBounded.IsPowerBounded.exists_norm_pow_le K
    ((hA.isPowerBounded_iff_supSeminorm_le_one _).2 hc.le)
  have hfm : supSeminorm K f ^ m < 1 := pow_lt_one₀ (supSeminorm_nonneg K f) hf hm
  have hc1 : 1 < ‖c‖ := by
    rw [supSeminorm_smul, supSeminorm_pow K f hm] at hc
    refine lt_of_not_ge fun h ↦ ?_
    exact ((mul_le_of_le_one_left (pow_nonneg (supSeminorm_nonneg K f) m) h).trans_lt hfm).ne hc
  -- `‖c‖ᵏ ‖f^{mk}‖ = ‖(c fᵐ)ᵏ‖ ≤ M < ‖c‖ᵏ` for large `k`, so `‖f^{mk}‖ < 1`
  obtain ⟨k, hk, hk1⟩ := (((tendsto_pow_atTop_atTop_of_one_lt hc1).eventually_gt_atTop M).and
    (Filter.eventually_ge_atTop 1)).exists
  refine isTopologicallyNilpotent_of_norm_pow_lt_one (m := m * k) (Nat.mul_ne_zero hm (by omega)) ?_
  have hck : 0 < ‖c‖ ^ k := pow_pos (zero_lt_one.trans hc1) k
  have h := hM k
  rw [smul_pow, norm_smul, norm_pow c k, ← pow_mul] at h
  refine lt_of_mul_lt_mul_left (a := ‖c‖ ^ k) ?_ hck.le
  rw [mul_one]
  exact h.trans_lt hk

/-- **BGR 6.2.3/2 (i) ⇔ (ii)**: `f` is topologically nilpotent iff `|f(x)| < 1` at every point
(the maximum modulus principle). -/
theorem isTopologicallyNilpotent_iff_forall_evalNorm_lt_one (hA : IsAffinoidAlgebra K A)
    [Nontrivial A] (f : A) :
    IsTopologicallyNilpotent f ↔ ∀ x : MaximalSpectrum A, evalNorm K x f < 1 := by
  haveI := hA.hasSupSeminorm
  rw [hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one]
  refine ⟨fun hf x ↦ (evalNorm_le_supSeminorm K x f).trans_lt hf, fun hf ↦ ?_⟩
  -- the supremum is attained (the maximum modulus principle, M2)
  obtain ⟨x, hx⟩ := hA.exists_evalNorm_eq_supSeminorm f
  exact hx.symm.trans_lt (hf x)

theorem isTopologicallyNilpotent_iff_mem_topologicallyNilpotent (hA : IsAffinoidAlgebra K A)
    (f : A) (hf : supSeminorm K f ≤ 1) :
    haveI := hA.hasSupSeminorm
    IsTopologicallyNilpotent f ↔ (⟨f, hf⟩ : powerBounded K A) ∈ topologicallyNilpotent K A :=
  hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one f

/-- **BGR 6.2.3/3** (the spectral radius formula): `|f|_sup = inf_i ‖fⁱ‖^{1/i}` for every complete
`K`-algebra norm on `A`. "≤" is 3.8.2/2; "≥": if `|f|_sup < |f|'` then by 6.2.1/4 (ii) one may
assume `|f|_sup = 1 < |f|'`, so `‖fⁱ‖ ≥ |f|'^i → ∞` and `f` is not power-bounded, contradicting
6.2.3/1. -/
theorem supSeminorm_eq_smoothingFun (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = smoothingFun (SeminormedRing.toRingSeminorm A) f := by
  haveI := hA.hasSupSeminorm
  -- a presentation `α : Tₙ ↠ A`, bounded: `‖α t‖ ≤ C ‖t‖ = C |t|_sup`
  obtain ⟨n, α, hα⟩ := id hA
  obtain ⟨C, -, hC⟩ :=
    SemilinearMapClass.bound_of_continuous α.toLinearMap (hA.continuous_presentation α)
  have hC' : ∀ t : TateAlgebra K n, ‖(α : TateAlgebra K n →+* A) t‖ ≤ C * supSeminorm K t :=
    fun t ↦ (hC t).trans_eq (by rw [MvPowerSeries.Restricted.supSeminorm_eq_norm])
  -- `μ'(g) ≤ max 1 C · σ(q) = max 1 C · |g|_sup` for an integral equation `q` of `g` over `Tₙ`
  -- with `σ(q) = |g|_sup` (BGR 6.2.2/4), and the constant disappears (BGR 3.8.2/5)
  refine supSeminorm_eq_smoothingFun_of_forall_le K (C := max 1 C) (fun g ↦ ?_) f
  obtain ⟨q, hq, hqg, hσ⟩ := hA.exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue
    (tateAlgebra n) α (RingHom.Finite.of_surjective _ hα) g
  rw [hσ]
  exact smoothingFun_le_mul_supSpectralValue_of_eval₂_eq_zero K _ hC' hq hqg

omit [NormOneClass A] in
/-- `|·|_sup` is `1`-Lipschitz for any complete algebra norm: `|f|_sup ≤ ‖f‖` and the
ultrametric inequality, so `|f|_sup - |g|_sup ≤ ‖f - g‖`. -/
theorem lipschitzWith_supSeminorm (hA : IsAffinoidAlgebra K A) :
    LipschitzWith 1 (supSeminorm K : A → ℝ) := by
  haveI := hA.hasSupSeminorm
  refine LipschitzWith.of_le_add fun f g ↦ ?_
  have h1 : supSeminorm K (f - g) ≤ dist f g :=
    (supSeminorm_le_norm (K := K) (f - g)).trans_eq (dist_eq_norm f g).symm
  calc supSeminorm K f = supSeminorm K ((f - g) + g) := by rw [sub_add_cancel]
    _ ≤ max (supSeminorm K (f - g)) (supSeminorm K g) := supSeminorm_add_le_max K _ _
    _ ≤ supSeminorm K g + dist f g := max_le (h1.trans (le_add_of_nonneg_left
          (supSeminorm_nonneg K g))) (le_add_of_nonneg_right dist_nonneg)

omit [NormOneClass A] in
/-- `Å` is closed (§2.4.3). -/
theorem isClosed_powerBounded (hA : IsAffinoidAlgebra K A) :
    haveI := hA.hasSupSeminorm
    IsClosed (powerBounded K A : Set A) :=
  isClosed_le hA.lipschitzWith_supSeminorm.continuous continuous_const

omit [NormOneClass A] in
/-- `Å` is open: it contains the open unit ball of the norm and is an additive subgroup (§2.4.3). -/
theorem isOpen_powerBounded (hA : IsAffinoidAlgebra K A) :
    haveI := hA.hasSupSeminorm
    IsOpen (powerBounded K A : Set A) := by
  haveI := hA.hasSupSeminorm
  have hball : Metric.ball (0 : A) 1 ⊆ (powerBounded K A : Set A) := fun f hf ↦ by
    rw [Metric.mem_ball, dist_zero_right] at hf
    exact mem_powerBounded.2 ((supSeminorm_le_norm (K := K) f).trans hf.le)
  exact (powerBounded K A).toAddSubgroup.isOpen_of_mem_nhds
    (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) hball)

omit [NormOneClass A] in
/-- `Ǎ` is open in `A` (§2.4.3). -/
theorem isOpen_setOf_supSeminorm_lt_one (hA : IsAffinoidAlgebra K A) :
    IsOpen {f : A | supSeminorm K f < 1} :=
  isOpen_lt hA.lipschitzWith_supSeminorm.continuous continuous_const

omit [CompleteSpace A] [IsUltrametricDist A] [NormOneClass A] in
/-- **Uniformity, norm form** (§2.3.5): `Å` is bounded in `A` iff `|·|_sup` is equivalent to the
norm of `A`. "⇐" is clear; "⇒" (BGR p. 181, end of the proof of 3.8.3/6): for `|f|_sup ≠ 0` pick
`c ∈ K`, `|c| > 1`, and `m` with `|c|^{m−1} < |f|_sup ≤ |c|^m`; then `c^{−m} f ∈ Å` is bounded by
`M`, so `‖f‖ ≤ M |c|^m ≤ M |c| |f|_sup`; for `|f|_sup = 0`, `c^{-m} f ∈ Å` for all `m` forces
`f = 0`. -/
theorem exists_norm_le_mul_supSeminorm_iff_isBounded_powerBounded (hA : IsAffinoidAlgebra K A) :
    haveI := hA.hasSupSeminorm
    (∃ C : ℝ, ∀ f : A, ‖f‖ ≤ C * supSeminorm K f) ↔
      TopologicalRing.IsBounded (powerBounded K A : Set A) := by
  haveI := hA.hasSupSeminorm
  constructor
  · -- `‖f‖ ≤ C |f|_sup ≤ max C 0` on `Å`
    rintro ⟨C, hC⟩
    refine TopologicalRing.isBounded_of_forall_norm_le (C := max C 0) fun f hf ↦ (hC f).trans ?_
    have hs := supSeminorm_nonneg K f
    exact (mul_le_mul_of_nonneg_right (le_max_left C 0) hs).trans
      (mul_le_of_le_one_right (le_max_right C 0) (mem_powerBounded.1 hf))
  -- BGR p. 181: rescale `f` into `Å` by a power of `c`, `1 < ‖c‖`
  intro hb
  obtain ⟨M, hM⟩ := TopologicalRing.IsBounded.exists_norm_le_of_normedAlgebra K hb
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have hc0 : c ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans hc)
  refine ⟨max M 0 * ‖c‖, fun f ↦ ?_⟩
  rcases (supSeminorm_nonneg K f).eq_or_lt with h0 | hpos
  · -- `|f|_sup = 0`: `‖cᵐ • f‖ ≤ M` for every `m`, so `f = 0`
    have hfm : ∀ m : ℕ, ‖c‖ ^ m * ‖f‖ ≤ M := fun m ↦ by
      have hg : c ^ m • f ∈ powerBounded K A := by
        rw [mem_powerBounded, supSeminorm_smul, ← h0, mul_zero]
        exact zero_le_one
      have h := hM _ hg
      rwa [norm_smul, norm_pow] at h
    have hf0 : ‖f‖ = 0 := by
      refine le_antisymm (le_of_not_gt fun hpos' ↦ ?_) (norm_nonneg f)
      obtain ⟨m, hm⟩ :=
        ((tendsto_pow_atTop_atTop_of_one_lt hc).eventually_gt_atTop (M / ‖f‖)).exists
      rw [div_lt_iff₀ hpos'] at hm
      exact absurd (hfm m) (not_le.2 hm)
    exact hf0.trans_le (le_of_eq (by rw [← h0, mul_zero]))
  -- `‖c‖ⁿ < |f|_sup ≤ ‖c‖ⁿ⁺¹`, so `c⁻⁽ⁿ⁺¹⁾ • f ∈ Å` and `‖f‖ ≤ ‖c‖ⁿ⁺¹ M < M ‖c‖ |f|_sup`
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hpos hc
  have hcn : (0 : ℝ) < ‖c‖ ^ (n + 1) := zpow_pos (zero_lt_one.trans hc) _
  have hg : (c ^ (n + 1))⁻¹ • f ∈ powerBounded K A := by
    rw [mem_powerBounded, supSeminorm_smul, norm_inv, norm_zpow, inv_mul_le_iff₀ hcn, mul_one]
    exact hn2
  have hf : f = c ^ (n + 1) • ((c ^ (n + 1))⁻¹ • f) := by
    rw [smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ hc0), one_smul]
  have hpow : ‖c‖ ^ (n + 1) = ‖c‖ ^ n * ‖c‖ := zpow_add_one₀ (norm_ne_zero_iff.2 hc0) n
  calc ‖f‖ = ‖c‖ ^ (n + 1) * ‖(c ^ (n + 1))⁻¹ • f‖ := by
        conv_lhs => rw [hf]
        rw [norm_smul, norm_zpow]
    _ ≤ ‖c‖ ^ (n + 1) * max M 0 := mul_le_mul_of_nonneg_left ((hM _ hg).trans (le_max_left _ _))
        hcn.le
    _ = max M 0 * ‖c‖ * ‖c‖ ^ n := by rw [hpow]; ring
    _ ≤ max M 0 * ‖c‖ * supSeminorm K f := mul_le_mul_of_nonneg_left hn1.le
        (mul_nonneg (le_max_right _ _) (norm_nonneg _))

omit [CompleteSpace A] [IsUltrametricDist A] [NormOneClass A] in
/-- If `Å` is bounded then `A` is reduced (a nonzero nilpotent `f` has `c^{-m} f ∈ Å` for every
`m`). -/
theorem isReduced_of_isBounded_powerBounded (hA : IsAffinoidAlgebra K A)
    (h : haveI := hA.hasSupSeminorm; TopologicalRing.IsBounded (powerBounded K A : Set A)) :
    IsReduced A := by
  haveI := hA.hasSupSeminorm
  obtain ⟨C, hC⟩ := hA.exists_norm_le_mul_supSeminorm_iff_isBounded_powerBounded.2 h
  -- a nilpotent `f` has `|f|_sup = 0` (BGR 6.2.1/4 (iii)), so `‖f‖ ≤ C · 0`
  refine ⟨fun f hf ↦ ?_⟩
  have hle := hC f
  rw [(hA.supSeminorm_eq_zero_iff_isNilpotent f).2 hf, mul_zero] at hle
  exact norm_le_zero_iff.1 hle

end IsAffinoidAlgebra
