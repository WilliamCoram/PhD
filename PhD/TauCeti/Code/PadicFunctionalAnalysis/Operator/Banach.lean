/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import PhD.TauCeti.Code.PadicFunctionalAnalysis.UnitBall
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Norm

/-!
# Bounded operators over a Tate normed ring form a Banach module

Over a Tate normed ring `R` the operator norm makes `M →L[R] N` a normed group, ultrametric when
`N` is, complete when `N` is, a normed `R`-module when `R` is commutative, and `M →L[R] M` a
normed ring with `‖1‖ = 1` when `M ≠ 0`. All of these are *scoped* instances in
`ContinuousLinearMap.Ultra` (roadmap convention 6). With them, a family of operators tending to `0`
cofinitely is summable in operator norm and its sum is computed pointwise, and the Neumann series
`Units.oneSub` inverts every operator `u` with `‖1 − u‖ < 1`, with `‖u⁻¹‖ = 1`.

For a nontrivially normed field of scalars the scoped normed-group instance coincides with
Mathlib's `ContinuousLinearMap.toNormedAddCommGroup` (`instNormedAddCommGroup_eq`), which is the
remaining half of roadmap §1.1.6.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §1.1.3–§1.1.6. Tau Ceti home:
`TauCeti/Analysis/Normed/Operator/Ultra/Banach.lean`.

## Main results

* `ContinuousLinearMap.Ultra.instNormedAddCommGroup`, `instIsUltrametricDist`, `instCompleteSpace`,
  `instNormedRing`, `instNormOneClass`, `instIsBoundedSMul` — the scoped instances.
* `ContinuousLinearMap.Ultra.opNorm_comp_le` — submultiplicativity.
* `ContinuousLinearMap.Ultra.tsum_apply` — sums of operators are pointwise sums.
* `ContinuousLinearMap.Ultra.norm_inv_eq_one_of_norm_one_sub_lt_one` — the Neumann series.
* `ContinuousLinearMap.Ultra.instNormedAddCommGroup_eq` — agreement with Mathlib.
-/

open Filter Topology

namespace ContinuousLinearMap.Ultra

open NormedRing

/-! ### The normed group of bounded operators -/

section NormedAddCommGroup

variable {R M N : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Source: Bellaïche, §II.1.1 (`Hom_R(M, N)` "is a Banach `R`-module for the norm we just
defined"); Mathlib, `ContinuousLinearMap.opNorm_add_le`. -/
theorem opNorm_add_le (u v : M →L[R] N) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ :=
  opNorm_le_bound _ (add_nonneg (opNorm_nonneg u) (opNorm_nonneg v)) fun x ↦ by
    rw [add_apply, add_mul]
    exact norm_add_le_of_le (le_opNorm u x) (le_opNorm v x)

/-- Source: Mathlib, `ContinuousLinearMap.opNorm_zero_iff`. -/
theorem opNorm_eq_zero_iff (u : M →L[R] N) : ‖u‖ = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun x ↦ ?_, fun h ↦ h ▸ opNorm_zero⟩
  have hux := le_opNorm u x
  rw [h, zero_mul] at hux
  exact norm_le_zero_iff.1 hux

/-- The operator norm is a norm. Source: roadmap §1.1.3; Johansson–Newton, Definition 2.1.4
(`Hom_{R,cts}(M, N)` "becomes a normed `R`-module with respect to this norm"). -/
noncomputable scoped instance instNormedAddCommGroup : NormedAddCommGroup (M →L[R] N) where
  toMetricSpace :=
    (AddGroupNorm.toNormedAddCommGroup
      { toFun := fun u : M →L[R] N ↦ ‖u‖
        map_zero' := opNorm_zero
        add_le' := opNorm_add_le
        neg' := opNorm_neg
        eq_zero_of_map_eq_zero' := fun u hu ↦ (opNorm_eq_zero_iff u).1 hu }).toMetricSpace
  dist_eq _ _ := rfl

/-- Source: roadmap §1.1.3 ("a complete ultrametric norm"). -/
theorem opNorm_add_le_max [IsUltrametricDist N] (u v : M →L[R] N) :
    ‖u + v‖ ≤ max ‖u‖ ‖v‖ :=
  opNorm_le_bound _ (le_max_of_le_left (opNorm_nonneg u)) fun x ↦ by
    rw [add_apply, max_mul_of_nonneg _ _ (norm_nonneg x)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (le_opNorm u x) (le_opNorm v x))

/-- Source: roadmap §1.1.3. -/
scoped instance instIsUltrametricDist [IsUltrametricDist N] : IsUltrametricDist (M →L[R] N) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm opNorm_add_le_max

/-- Source: roadmap §1.1.3; Schneider, Proposition 3.3; Bellaïche, §II.1.1; Ludwig, §2.1
("Completeness follows for if `φₙ` is a Cauchy sequence ... `φₙ(m)` is a Cauchy sequence
in `N`"). -/
scoped instance instCompleteSpace [CompleteSpace N] : CompleteSpace (M →L[R] N) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  rw [Metric.cauchySeq_iff] at hu
  have hcau (x : M) : CauchySeq fun n ↦ u n x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hu (ε / (‖x‖ + 1)) (div_pos hε (by positivity))
    refine ⟨N₀, fun m hm n hn ↦ ?_⟩
    have h := hN₀ m hm n hn
    rw [dist_eq_norm] at h ⊢
    calc ‖u m x - u n x‖ = ‖(u m - u n) x‖ := rfl
      _ ≤ ‖u m - u n‖ * ‖x‖ := le_opNorm _ x
      _ ≤ ‖u m - u n‖ * (‖x‖ + 1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (opNorm_nonneg _)
      _ < ε / (‖x‖ + 1) * (‖x‖ + 1) := mul_lt_mul_of_pos_right h (by positivity)
      _ = ε := div_mul_cancel₀ ε (by positivity)
  choose v₀ hv₀ using fun x ↦ cauchySeq_tendsto_of_complete (hcau x)
  have hadd (x y : M) : v₀ (x + y) = v₀ x + v₀ y :=
    tendsto_nhds_unique (hv₀ (x + y)) (by simpa only [map_add] using (hv₀ x).add (hv₀ y))
  have hsmul (c : R) (x : M) : v₀ (c • x) = c • v₀ x :=
    tendsto_nhds_unique (hv₀ (c • x)) (by simpa only [map_smul] using (hv₀ x).const_smul c)
  obtain ⟨N₀, hN₀⟩ := hu 1 one_pos
  have hbound (x : M) : ‖v₀ x‖ ≤ (‖u N₀‖ + 1) * ‖x‖ := by
    refine le_of_tendsto (hv₀ x).norm (eventually_atTop.2 ⟨N₀, fun n hn ↦ ?_⟩)
    have h := hN₀ n hn N₀ le_rfl
    rw [dist_eq_norm] at h
    calc ‖u n x‖ = ‖(u n - u N₀) x + u N₀ x‖ := by rw [sub_apply, sub_add_cancel]
      _ ≤ ‖(u n - u N₀) x‖ + ‖u N₀ x‖ := norm_add_le _ _
      _ ≤ ‖u n - u N₀‖ * ‖x‖ + ‖u N₀‖ * ‖x‖ := add_le_add (le_opNorm _ x) (le_opNorm _ x)
      _ ≤ 1 * ‖x‖ + ‖u N₀‖ * ‖x‖ := by gcongr
      _ = (‖u N₀‖ + 1) * ‖x‖ := by ring
  let v : M →L[R] N := LinearMap.mkContinuous ⟨⟨v₀, hadd⟩, hsmul⟩ (‖u N₀‖ + 1) hbound
  refine ⟨v, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  obtain ⟨N₁, hN₁⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨N₁, fun n hn ↦ ?_⟩
  have hle : ‖u n - v‖ ≤ ε / 2 := by
    refine opNorm_le_bound _ (half_pos hε).le fun x ↦ ?_
    have htend : Tendsto (fun m ↦ ‖u n x - u m x‖) atTop (𝓝 ‖(u n - v) x‖) :=
      (tendsto_const_nhds.sub (hv₀ x)).norm
    refine le_of_tendsto htend (eventually_atTop.2 ⟨N₁, fun m hm ↦ ?_⟩)
    have h := hN₁ n hn m hm
    rw [dist_eq_norm] at h
    calc ‖u n x - u m x‖ = ‖(u n - u m) x‖ := rfl
      _ ≤ ‖u n - u m‖ * ‖x‖ := le_opNorm _ x
      _ ≤ ε / 2 * ‖x‖ := mul_le_mul_of_nonneg_right h.le (norm_nonneg x)
  rw [dist_eq_norm]
  linarith

/-- Source: Bellaïche, §II.1.1 ("One evidently has `|φ'φ| ≤ |φ'||φ|`"); roadmap §1.1.3. -/
theorem opNorm_comp_le {P : Type*} [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]
    (v : N →L[R] P) (u : M →L[R] N) : ‖v.comp u‖ ≤ ‖v‖ * ‖u‖ :=
  opNorm_le_bound _ (mul_nonneg (opNorm_nonneg v) (opNorm_nonneg u)) fun x ↦ by
    rw [comp_apply, mul_assoc]
    exact (le_opNorm v _).trans (mul_le_mul_of_nonneg_left (le_opNorm u x) (opNorm_nonneg v))

/-- Source: roadmap §1.1.3 (`‖1‖ ≤ 1` "with equality when `M ≠ 0`"). -/
theorem norm_id [Nontrivial M] : ‖ContinuousLinearMap.id R M‖ = 1 := by
  refine le_antisymm norm_id_le ?_
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have h := le_opNorm (ContinuousLinearMap.id R M) x
  rw [id_apply] at h
  exact le_of_mul_le_mul_right (by rwa [one_mul]) (norm_pos_iff.2 hx)

/-- Source: roadmap §1.1.3 ("it makes `M →L[R] M` a nonarchimedean Banach ring"). -/
noncomputable scoped instance instNormedRing : NormedRing (M →L[R] M) :=
  { instNormedAddCommGroup, ContinuousLinearMap.ring with
    norm_mul_le := fun u v ↦ opNorm_comp_le u v }

/-- Source: roadmap §1.1.3. -/
scoped instance instNormOneClass [Nontrivial M] : NormOneClass (M →L[R] M) := ⟨norm_id⟩

end NormedAddCommGroup

/-! ### Scalars -/

section Comm

variable {R M N : Type*} [NormedCommRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Source: roadmap §1.1.3 (`‖a • u‖ ≤ ‖a‖ ‖u‖`); Mathlib, `ContinuousLinearMap.opNorm_smul_le`. -/
theorem opNorm_smul_le (a : R) (u : M →L[R] N) : ‖a • u‖ ≤ ‖a‖ * ‖u‖ :=
  opNorm_le_bound _ (mul_nonneg (norm_nonneg a) (opNorm_nonneg u)) fun x ↦ by
    rw [smul_apply, mul_assoc]
    exact (norm_smul_le a _).trans (mul_le_mul_of_nonneg_left (le_opNorm u x) (norm_nonneg a))

/-- Source: Johansson–Newton, Definition 2.1.4 ("a normed `R`-module with respect to this norm"). -/
scoped instance instIsBoundedSMul : IsBoundedSMul R (M →L[R] N) :=
  IsBoundedSMul.of_norm_smul_le opNorm_smul_le

/-- Source: roadmap §1.1.3 ("with equality for multiplicative `a`" — a multiplicative *unit*). -/
theorem opNorm_smul_of_isMultiplicative {a : Rˣ} (ha : IsMultiplicative (a : R))
    (u : M →L[R] N) : ‖(a : R) • u‖ = ‖(a : R)‖ * ‖u‖ := by
  refine le_antisymm (opNorm_smul_le _ _) ?_
  have h := opNorm_smul_le ((a⁻¹ : Rˣ) : R) ((a : R) • u)
  rw [smul_smul, Units.inv_mul, one_smul, ha.norm_inv] at h
  exact (le_inv_mul_iff₀ ha.norm_pos).1 h

end Comm

/-! ### Sums of operators -/

section Sums

variable {R M N : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  [CompleteSpace N] {ι : Type*}

/-- Source: roadmap §1.1.4 ("`∑' uᵢ` converges in operator norm"); Mathlib,
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`. -/
theorem summable_of_tendsto_cofinite_zero [IsUltrametricDist N] {u : ι → M →L[R] N}
    (hu : Tendsto u cofinite (𝓝 0)) : Summable u :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hu

omit [CompleteSpace N] in
/-- Source: roadmap §1.1.4 ("and pointwise"). -/
theorem hasSum_apply {u : ι → M →L[R] N} {v : M →L[R] N} (hu : HasSum u v) (x : M) :
    HasSum (fun i ↦ u i x) (v x) := by
  let e : (M →L[R] N) →+ N := AddMonoidHom.mk' (fun w ↦ w x) fun _ _ ↦ rfl
  have he : Continuous e := AddMonoidHomClass.continuous_of_bound e ‖x‖ fun w ↦ by
    rw [mul_comm]
    exact le_opNorm w x
  exact hu.map e he

omit [CompleteSpace N] in
/-- Source: roadmap §1.1.4. -/
theorem tsum_apply {u : ι → M →L[R] N} (hu : Summable u) (x : M) :
    (∑' i, u i) x = ∑' i, u i x :=
  (hasSum_apply hu.hasSum x).tsum_eq.symm

end Sums

/-! ### The Neumann series -/

section Neumann

variable {R M : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]

/-- Source: roadmap §1.1.5 ("`u` is invertible in `M →L[R] M`"); BGR 1.2.4/4; Mathlib,
`Units.oneSub`. -/
theorem isUnit_of_norm_one_sub_lt_one (u : M →L[R] M) (hu : ‖1 - u‖ < 1) : IsUnit u :=
  ⟨Units.oneSub (1 - u) hu, by rw [Units.val_oneSub, sub_sub_cancel]⟩

omit [CompleteSpace M] in
/-- Source: roadmap §0.2.3 applied to the Banach ring `M →L[R] M` (`‖1 − x‖ = 1`). -/
theorem norm_eq_one_of_norm_one_sub_lt_one [Nontrivial M] (u : M →L[R] M) (hu : ‖1 - u‖ < 1) :
    ‖u‖ = 1 := by
  have h := NormedRing.norm_one_sub_of_norm_lt_one hu
  rwa [sub_sub_cancel] at h

/-- Source: roadmap §1.1.5 (`‖u⁻¹‖ = 1`). -/
theorem norm_inv_eq_one_of_norm_one_sub_lt_one [Nontrivial M] (u : (M →L[R] M)ˣ)
    (hu : ‖1 - (u : M →L[R] M)‖ < 1) : ‖((u⁻¹ : (M →L[R] M)ˣ) : M →L[R] M)‖ = 1 := by
  have hval : ((u⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) =
      ((Units.oneSub (1 - (u : M →L[R] M)) hu)⁻¹ : (M →L[R] M)ˣ) :=
    Units.inv_unique (by rw [Units.val_oneSub, sub_sub_cancel])
  rw [hval]
  exact NormedRing.norm_tsum_geometric hu

/-- Source: roadmap §1.1.5 ("the units of `M →L[R] M` are open"); BGR 1.2.4/5; Mathlib,
`Units.isOpen`. -/
theorem isOpen_setOf_isUnit : IsOpen {u : M →L[R] M | IsUnit u} :=
  Units.isOpen

end Neumann

/-! ### Agreement with Mathlib -/

section Field

variable {K M N : Type*} [NontriviallyNormedField K] [NormedAddCommGroup M] [NormedSpace K M]
  [NormedAddCommGroup N] [NormedSpace K N]

/-- Two normed group structures with the same norm, group and metric are equal. -/
private theorem normedAddCommGroup_ext {E : Type*} {i j : NormedAddCommGroup E}
    (h₁ : i.toNorm = j.toNorm) (h₂ : i.toAddCommGroup = j.toAddCommGroup)
    (h₃ : i.toMetricSpace = j.toMetricSpace) : i = j := by
  cases i
  cases j
  cases h₁
  cases h₂
  cases h₃
  rfl

/-- **Agreement with Mathlib** (roadmap §1.1.6): for field scalars the scoped normed-group
structure is Mathlib's. -/
theorem instNormedAddCommGroup_eq :
    (instNormedAddCommGroup : NormedAddCommGroup (M →L[K] N)) =
      ContinuousLinearMap.toNormedAddCommGroup :=
  normedAddCommGroup_ext rfl rfl (MetricSpace.ext rfl)

end Field

end ContinuousLinearMap.Ultra
