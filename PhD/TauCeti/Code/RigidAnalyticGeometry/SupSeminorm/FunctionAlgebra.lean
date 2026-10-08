/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.BanachAlgebra.Module
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm.Integral
import PhD.TauCeti.Code.RigidAnalyticGeometry.WeaklyStable

/-!
# Banach function algebras

Layer 2, §2.4.2 (BGR 3.8.3/1–3.8.3/5 and 3.8.3/7). A `K`-Banach algebra `A` is a *Banach
function algebra* when its norm is equivalent to `|·|_sup` (BGR 3.8.3/1–2; the inequality
`|·|_sup ≤ ‖·‖` always holds, so this is one constant `C` with `‖f‖ ≤ C * |f|_sup`). Then
`|·|_sup` is the only power-multiplicative complete algebra norm (3.8.3/3), closed subalgebras and
finite subalgebras inherit the property (3.8.3/4–5), and — the theorem used for 6.2.4/1 — a domain
finite over a valued integrally closed noetherian Banach function algebra `B` with weakly stable
fraction field is a Banach function algebra (3.8.3/7, for `A` a domain: plan D1).

## Main declarations

* `Affinoid.IsBanachFunctionAlgebra K A`: `∃ C, ∀ f, ‖f‖ ≤ C * supSeminorm K f`.
* `Affinoid.IsBanachFunctionAlgebra.norm_eq_supSeminorm_of_isPowMul`: BGR 3.8.3/3.
* `Affinoid.IsBanachFunctionAlgebra.of_isClosed_range`: BGR 3.8.3/4.
* `Affinoid.IsBanachFunctionAlgebra.of_finite_injective`: BGR 3.8.3/5.
* `Affinoid.IsBanachFunctionAlgebra.of_finite_domain`: BGR 3.8.3/7 for `A` a domain, assembled
  from `Affinoid.exists_basis_universalDenominator` (a `Q(B)`-basis of `Q(A)` inside `A` with a
  universal denominator), `Affinoid.exists_coordinateMap` and
  `Affinoid.exists_norm_le_mul_norm_coordinateMap` (the coordinate map `A → Bⁿ`, closed graph and
  open mapping), `Affinoid.spectralNorm_fractionRing_eq_supSeminorm` (`|f|_sup = |f|_sp`) and
  `Affinoid.exists_norm_coordinateMap_le_mul_supSeminorm` (weak stability).
-/

open Filter Polynomial Topology

namespace Affinoid

section Def

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : Type*) [NormedCommRing A] [NormedAlgebra K A]

/-- **BGR 3.8.3/1–2**: a `K`-Banach algebra is a *Banach function algebra* if its norm is
equivalent to the supremum seminorm, i.e. `‖f‖ ≤ C * |f|_sup` for some `C` (the other inequality
`|f|_sup ≤ ‖f‖` is BGR 3.8.2/2, Layer 0 `supSeminorm_le_norm`). -/
def IsBanachFunctionAlgebra : Prop :=
  ∃ C : ℝ, ∀ f : A, ‖f‖ ≤ C * supSeminorm K f

end Def

/-- If `aⁿ ≤ C bⁿ` for every `n ≥ 1` with `a, b ≥ 0`, then `a ≤ b`: the constant disappears in
the `n`-th root (BGR 1.3.1/2). -/
private theorem le_of_forall_pow_le_mul_pow {a b C : ℝ} (hb : 0 ≤ b)
    (h : ∀ n : ℕ, 1 ≤ n → a ^ n ≤ C * b ^ n) : a ≤ b := by
  refine le_of_not_gt fun hlt ↦ ?_
  rcases hb.eq_or_lt with rfl | hpos
  · exact absurd hlt (not_lt.2 (by simpa using h 1 le_rfl))
  have hr : 1 < a / b := (one_lt_div hpos).2 hlt
  obtain ⟨n, hn, hn1⟩ := (((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop C).and
    (Filter.eventually_ge_atTop 1)).exists
  rw [div_pow, lt_div_iff₀ (pow_pos hpos n)] at hn
  exact absurd (h n hn1) (not_le.2 hn)

section Basic

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A]

omit [IsUltrametricDist K] [CompleteSpace K] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A] in
/-- In a Banach function algebra `|·|_sup` is a norm: `|f|_sup = 0 → f = 0`. -/
theorem IsBanachFunctionAlgebra.eq_zero_of_supSeminorm_eq_zero
    (hA : IsBanachFunctionAlgebra K A) {f : A} (hf : supSeminorm K f = 0) : f = 0 := by
  obtain ⟨C, hC⟩ := hA
  have h := hC f
  rw [hf, mul_zero] at h
  exact norm_le_zero_iff.1 h

omit [NormOneClass A] in
/-- **BGR 3.8.3/3** (with 1.3.1/3): a power-multiplicative complete algebra norm on a Banach
function algebra is the supremum seminorm. -/
theorem IsBanachFunctionAlgebra.norm_eq_supSeminorm_of_isPowMul [HasSupSeminorm K A]
    (hA : IsBanachFunctionAlgebra K A) (hpm : IsPowMul (fun f : A ↦ ‖f‖)) (f : A) :
    ‖f‖ = supSeminorm K f := by
  obtain ⟨C, hC⟩ := hA
  refine le_antisymm (le_of_forall_pow_le_mul_pow (C := C) (supSeminorm_nonneg K f)
    fun n hn ↦ ?_) (supSeminorm_le_norm (K := K) f)
  calc ‖f‖ ^ n = ‖f ^ n‖ := (hpm f hn).symm
    _ ≤ C * supSeminorm K (f ^ n) := hC _
    _ = C * supSeminorm K f ^ n := by rw [supSeminorm_pow K f (by omega)]

variable {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B] [IsUltrametricDist B]
  [NormOneClass B]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist A] [NormOneClass A]
  [IsUltrametricDist B] [NormOneClass B] in
/-- **BGR 3.8.3/4**: a Banach algebra `B` mapping continuously and injectively with closed range
into a Banach function algebra `A` is a Banach function algebra (open mapping onto the closed range,
then the contraction `|φ b|_sup ≤ |b|_sup`). -/
theorem IsBanachFunctionAlgebra.of_isClosed_range [HasSupSeminorm K A] [HasSupSeminorm K B]
    (hA : IsBanachFunctionAlgebra K A) (φ : B →ₐ[K] A) (hφ : Continuous φ)
    (hinj : Function.Injective φ) (hcl : IsClosed (Set.range φ)) : IsBanachFunctionAlgebra K B := by
  obtain ⟨C₂, hC₂⟩ := hA
  -- the open mapping theorem onto the closed range
  let R : Submodule K A := LinearMap.range φ.toLinearMap
  haveI : CompleteSpace R := (show IsClosed (R : Set A) by
    rw [LinearMap.coe_range]
    exact hcl).completeSpace_coe
  let φ' : B →L[K] R := ⟨φ.toLinearMap.rangeRestrict, hφ.subtype_mk _⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    ContinuousLinearMap.exists_preimage_norm_le φ' (LinearMap.surjective_rangeRestrict _)
  refine ⟨C₁ * max C₂ 0, fun b ↦ ?_⟩
  obtain ⟨b', hb', hnb'⟩ := hC₁ (φ' b)
  have hbb : b' = b := hinj (congrArg Subtype.val hb')
  rw [hbb] at hnb'
  calc ‖b‖ ≤ C₁ * ‖φ' b‖ := hnb'
    _ = C₁ * ‖φ b‖ := rfl
    _ ≤ C₁ * (max C₂ 0 * supSeminorm K (φ b)) :=
        mul_le_mul_of_nonneg_left ((hC₂ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (supSeminorm_nonneg K _))) hC₁0.le
    _ ≤ C₁ * (max C₂ 0 * supSeminorm K b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (supSeminorm_map_le φ b)
          (le_max_right _ _)) hC₁0.le
    _ = C₁ * max C₂ 0 * supSeminorm K b := (mul_assoc _ _ _).symm

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist A] [NormOneClass A] in
/-- **BGR 3.8.3/5**: for `φ : B → A` finite, injective and continuous with `B` noetherian and `A` a
Banach function algebra, `B` is a Banach function algebra (`φ(B)` is closed in the finite normed
`B`-module `A` by 3.7.3/1). -/
theorem IsBanachFunctionAlgebra.of_finite_injective [HasSupSeminorm K A] [HasSupSeminorm K B]
    [IsNoetherianRing B] (hA : IsBanachFunctionAlgebra K A) (φ : B →ₐ[K] A) (hφ : Continuous φ)
    (hinj : Function.Injective φ) (hfin : φ.toRingHom.Finite) : IsBanachFunctionAlgebra K B := by
  letI : Algebra B A := φ.toRingHom.toAlgebra
  haveI : Module.Finite B A := hfin
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun k ↦ (φ.commutes k).symm
  haveI : ContinuousSMul B A := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  refine hA.of_isClosed_range φ hφ hinj ?_
  -- `φ(B)` is a submodule of the finite `B`-module `A`, hence closed (BGR 3.7.3/1)
  have h := Submodule.isClosed_of_isNoetherianRing_of_finite K (A := B) (M := A)
    (LinearMap.range (Algebra.linearMap B A))
  rw [LinearMap.coe_range] at h
  exact h

end Basic

section Algebraic

variable {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]

/-- The coordinates of `A` inside `Q(A) = Q(B)ⁿ`: `Q(A)` is finite-dimensional over `Q(B)` (Layer 1
`FractionRing.finiteDimensional_of_finite`) with a basis `a₁, …, aₙ` of elements of `A`, and there
is a universal denominator `b ≠ 0` in `B` with `b • A ⊆ Σ B aᵢ` (BGR p. 181, "there is a universal
denominator `b ∈ B − {0}` such that `A ⊂ A' := Σ B aᵢ/b`"). -/
theorem exists_basis_universalDenominator [Module.Finite B A] :
    ∃ (n : ℕ) (a : Fin n → A) (b : B), b ≠ 0 ∧
      LinearIndependent B a ∧ ∀ f : A, ∃ β : Fin n → B, b • f = ∑ i, β i • a i := by
  classical
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := B) (M := A)
  -- a maximal independent subfamily of the generators (BGR: "a `Q(B)`-basis of `Q(A)`")
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn B g
  have hmul : ∀ i, ∃ c : B, c ≠ 0 ∧ c • g i ∈ Submodule.span B (g '' s) := by
    intro i
    by_cases hi : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩
    · exact hmax i hi
  choose c hc0 hc using hmul
  -- the universal denominator `b = ∏ cᵢ`
  have hb0 : ∏ i, c i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hc0 i
  have hbg : ∀ i, (∏ j, c j) • g i ∈ Submodule.span B (g '' s) := by
    intro i
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
    exact Submodule.smul_mem _ _ (hc i)
  have hbA : ∀ f : A, (∏ j, c j) • f ∈ Submodule.span B (g '' s) := by
    intro f
    have hf : f ∈ Submodule.span B (Set.range g) := hg ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hbg i
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  -- index the independent generators by `Fin n`
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  have hrange : g '' s = Set.range fun j : Fin (Fintype.card s) ↦ g (e.symm j) := by
    rw [Set.image_eq_range, ← e.symm.surjective.range_comp]
    rfl
  refine ⟨Fintype.card s, fun j ↦ g (e.symm j), ∏ j, c j, hb0, hs.comp e.symm e.symm.injective,
    fun f ↦ ?_⟩
  have hf := hbA f
  rw [hrange] at hf
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hf
  exact ⟨β, hβ.symm⟩

end Algebraic

section Theorem7

universe u

-- `B` and `A` share a universe: `IsWeaklyStable (FractionRing B)` quantifies over the finite
-- extensions of `FractionRing B` in its own universe, and `FractionRing A` must be one of them.
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type u} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B] [IsUltrametricDist B]
  [NormOneClass B] [NormMulClass B] [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]
  [HasSupSeminorm K B]
  {A : Type u} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsDomain A] [Algebra B A]
  [IsScalarTower K B A] [Module.Finite B A] [FaithfulSMul B A]

omit [IsUltrametricDist K] [CompleteSpace K] [NormMulClass B] [IsDomain B] [IsIntegrallyClosed B]
  [HasSupSeminorm K B] [NormedAlgebra K A] [CompleteSpace A] [IsScalarTower K B A]
  [Module.Finite B A] in
variable (K) in
include K in
/-- The coordinate map `θ : A → Bⁿ`, `f ↦ β` with `b • f = Σ βᵢ • aᵢ`, is `B`-linear, injective,
and has closed range in `Bⁿ` (BGR 3.7.2/2, `Submodule.isClosed_of_isNoetherianRing_pi`). -/
theorem exists_coordinateMap {n : ℕ} {a : Fin n → A} {b : B} (hb : b ≠ 0)
    (ha : LinearIndependent B a) (hA : ∀ f : A, ∃ β : Fin n → B, b • f = ∑ i, β i • a i) :
    ∃ θ : A →ₗ[B] (Fin n → B), Function.Injective θ ∧
      (∀ f, b • f = ∑ i, θ f i • a i) ∧ IsClosed (Set.range θ) := by
  -- `f ↦ b • f` lands in the span of the `aᵢ`; read off coordinates there
  have hmem : ∀ f : A, (b • LinearMap.id : A →ₗ[B] A) f ∈ Submodule.span B (Set.range a) := by
    intro f
    obtain ⟨β, hβ⟩ := hA f
    rw [LinearMap.smul_apply, LinearMap.id_apply, hβ]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let θ : A →ₗ[B] (Fin n → B) := (Finsupp.linearEquivFunOnFinite B B (Fin n)).toLinearMap ∘ₗ
    ha.repr ∘ₗ (b • LinearMap.id).codRestrict _ hmem
  have hθa : ∀ f, b • f = ∑ i, θ f i • a i := by
    intro f
    have h := ha.linearCombination_repr ((b • LinearMap.id).codRestrict _ hmem f)
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ fun i ↦ zero_smul B (a i)] at h
    exact h.symm
  refine ⟨θ, ?_, hθa, ?_⟩
  · -- `θ f = 0` forces `b • f = 0`, hence `f = 0`
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h := hθa f
    rw [hf] at h
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h
    rw [Algebra.smul_def] at h
    have hb' : algebraMap B A b ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap B A)]
      exact (FaithfulSMul.algebraMap_injective B A).ne hb
    exact (mul_eq_zero.1 h).resolve_left hb'
  · have h := Submodule.isClosed_of_isNoetherianRing_pi K (LinearMap.range θ)
    rwa [LinearMap.coe_range] at h

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist B] [NormOneClass B] [NormMulClass B]
  [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B] [HasSupSeminorm K B]
  [Module.Finite B A] in
variable (K) in
include K in
/-- The coordinate map is continuous (closed graph theorem, BGR 3.8.2/3-style: if `fₖ → f` and
`θ fₖ → v` then `b • f = Σ vᵢ • aᵢ` by continuity of `algebraMap B A`, so `θ f = v`), hence by the
open mapping theorem onto its closed range `‖f‖ ≤ C * max ‖θ f i‖`. -/
theorem exists_norm_le_mul_norm_coordinateMap (hcont : Continuous (algebraMap B A)) {n : ℕ}
    {a : Fin n → A} {b : B} (hb : b ≠ 0) (θ : A →ₗ[B] (Fin n → B)) (hθ : Function.Injective θ)
    (hθa : ∀ f, b • f = ∑ i, θ f i • a i) (hcl : IsClosed (Set.range θ)) :
    ∃ C : ℝ, ∀ f : A, ‖f‖ ≤ C * ‖θ f‖ := by
  have hb' : algebraMap B A b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B A)]
    exact (FaithfulSMul.algebraMap_injective B A).ne hb
  have hθa' : ∀ f, algebraMap B A b * f = ∑ i, algebraMap B A (θ f i) * a i := fun f ↦ by
    simpa only [Algebra.smul_def] using hθa f
  let θk : A →ₗ[K] (Fin n → B) := θ.restrictScalars K
  -- the graph of `θ` is closed: limits of `b fₖ = Σ θ(fₖ)ᵢ aᵢ` stay in the closed range
  have hgraph : IsClosed (θk.graph : Set (A × (Fin n → B))) := by
    refine IsSeqClosed.isClosed fun u p hu hlim ↦ ?_
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff] at hu ⊢
    have hfst : Tendsto (fun k ↦ (u k).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hlim
    have hsnd : Tendsto (fun k ↦ (u k).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hlim
    obtain ⟨g, hg⟩ : p.2 ∈ Set.range θ :=
      hcl.mem_of_tendsto hsnd (Eventually.of_forall fun k ↦ ⟨(u k).1, (hu k).symm⟩)
    have h1 : Tendsto (fun k ↦ algebraMap B A b * (u k).1) atTop (𝓝 (algebraMap B A b * p.1)) :=
      hfst.const_mul _
    have h2 : Tendsto (fun k ↦ ∑ i, algebraMap B A ((u k).2 i) * a i) atTop
        (𝓝 (∑ i, algebraMap B A (p.2 i) * a i)) :=
      tendsto_finsetSum _ fun i _ ↦ by
        have hi : Tendsto (fun k ↦ (u k).2 i) atTop (𝓝 (p.2 i)) :=
          ((continuous_apply i).tendsto p.2).comp hsnd
        exact ((hcont.tendsto _).comp hi).mul_const (a i)
    have heq : (fun k ↦ algebraMap B A b * (u k).1) =
        fun k ↦ ∑ i, algebraMap B A ((u k).2 i) * a i := funext fun k ↦ by
      rw [hu k]
      exact hθa' (u k).1
    rw [← heq] at h2
    have hlimeq := tendsto_nhds_unique h1 h2
    have hp1 : p.1 = g := mul_left_cancel₀ hb' (hlimeq.trans (by rw [← hg]; exact (hθa' g).symm))
    rw [hp1]
    exact hg.symm
  have hθk : Continuous θk := LinearMap.continuous_of_isClosed_graph θk hgraph
  -- the open mapping theorem onto the closed range
  let R : Submodule K (Fin n → B) := LinearMap.range θk
  haveI : CompleteSpace R := (show IsClosed (R : Set (Fin n → B)) by
    rw [LinearMap.coe_range]
    exact hcl).completeSpace_coe
  let θ' : A →L[K] R := ⟨θk.rangeRestrict, hθk.subtype_mk _⟩
  obtain ⟨C, -, hC⟩ :=
    ContinuousLinearMap.exists_preimage_norm_le θ' (LinearMap.surjective_rangeRestrict _)
  refine ⟨C, fun f ↦ ?_⟩
  obtain ⟨f', hf', hnf'⟩ := hC (θ' f)
  have hff : f' = f := hθ (congrArg Subtype.val hf')
  rw [hff] at hnf'
  exact hnf'

omit [CompleteSpace B] [IsUltrametricDist B] [NormOneClass B] [IsNoetherianRing B]
  [CompleteSpace A] in
/-- **The spectral norm of `Q(A)` over `Q(B)` restricts to `|·|_sup` on `A`** (BGR 3.8.3/7, "From
Proposition 3.8.1/7 (a), we derive `|f|_sup = |f|_sp`"; the Remark after 3.8.1/9): when
`|·|_sup = ‖·‖` on `B`, the spectral norm of `f ∈ A ⊆ Q(A)` for the absolute value of `Q(B)`
extending `‖·‖` equals `supSeminorm K f`. -/
theorem spectralNorm_fractionRing_eq_supSeminorm (hBsup : ∀ b : B, supSeminorm K b = ‖b‖)
    [HasSupSeminorm K A] [Algebra (FractionRing B) (FractionRing A)]
    [IsScalarTower B (FractionRing B) (FractionRing A)] (f : A) :
    letI := IsFractionRing.normedField B (FractionRing B)
    spectralNorm (FractionRing B) (FractionRing A) (algebraMap A (FractionRing A) f) =
      supSeminorm K f := by
  letI := IsFractionRing.normedField B (FractionRing B)
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hfi : IsIntegral B f := Algebra.IsIntegral.isIntegral f
  have hfiL : IsIntegral B (algebraMap A (FractionRing A) f) :=
    hfi.map (IsScalarTower.toAlgHom B A (FractionRing A))
  -- the minimal polynomial over `Q(B)` is the image of the one over `B` (`B` integrally closed)
  have hmin : minpoly (FractionRing B) (algebraMap A (FractionRing A) f) =
      (minpoly B f).map (algebraMap B (FractionRing B)) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing B) hfiL]
    congr 1
    exact minpoly.algHom_eq (IsScalarTower.toAlgHom B A (FractionRing A))
      (IsFractionRing.injective A (FractionRing A)) f
  have hnorm : ∀ c : B, ‖algebraMap B (FractionRing B) c‖ = supSeminorm K c := fun c ↦
    (IsFractionRing.normAbsoluteValue_algebraMap B (FractionRing B) c).trans (hBsup c).symm
  show spectralValue (minpoly (FractionRing B) (algebraMap A (FractionRing A) f)) = _
  rw [hmin, supSeminorm_eq_supSpectralValue_minpoly K (B := B) f]
  unfold spectralValue supSpectralValue
  congr 1
  funext m
  simp only [spectralValueTerms, supSpectralValueTerms,
    natDegree_map_eq_of_injective (IsFractionRing.injective B (FractionRing B)), coeff_map, hnorm]

omit [CompleteSpace B] [IsUltrametricDist B] [NormOneClass B] [IsNoetherianRing B]
  [CompleteSpace A] in
/-- Weak stability bounds the coordinates by the spectral norm: `‖θ f i‖ ≤ C * |f|_sup`
(BGR 3.8.3/7, "Since `Q(B)` is weakly stable, all these extensions are weakly `Q(B)`-cartesian
under their spectral norm"). -/
theorem exists_norm_coordinateMap_le_mul_supSeminorm (hBsup : ∀ b : B, supSeminorm K b = ‖b‖)
    (hws : letI := IsFractionRing.normedField B (FractionRing B); IsWeaklyStable (FractionRing B))
    [HasSupSeminorm K A] {n : ℕ} {a : Fin n → A} {b : B} (hb : b ≠ 0) (ha : LinearIndependent B a)
    (θ : A →ₗ[B] (Fin n → B)) (hθa : ∀ f, b • f = ∑ i, θ f i • a i) :
    ∃ C : ℝ, ∀ f : A, ‖θ f‖ ≤ C * supSeminorm K f := by
  classical
  letI := IsFractionRing.normedField B (FractionRing B)
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hAL : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A _
  have hBL : Function.Injective (algebraMap B (FractionRing A)) := by
    rw [IsScalarTower.algebraMap_eq B A (FractionRing A)]
    exact hAL.comp (FaithfulSMul.algebraMap_injective B A)
  haveI : FaithfulSMul B (FractionRing A) := (faithfulSMul_iff_algebraMap_injective B _).2 hBL
  letI : Algebra (FractionRing B) (FractionRing A) := FractionRing.liftAlgebra B (FractionRing A)
  haveI : IsScalarTower B (FractionRing B) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra B (FractionRing A)
  have hBF : ∀ c : B, algebraMap (FractionRing B) (FractionRing A)
      (algebraMap B (FractionRing B) c) = algebraMap B (FractionRing A) c := fun c ↦
    (IsScalarTower.algebraMap_apply B (FractionRing B) (FractionRing A) c).symm
  have hBAL : ∀ c : B, algebraMap A (FractionRing A) (algebraMap B A c) =
      algebraMap B (FractionRing A) c := fun c ↦
    (IsScalarTower.algebraMap_apply B A (FractionRing A) c).symm
  have hbL : algebraMap B (FractionRing A) b ≠ 0 := (map_ne_zero_iff _ hBL).2 hb
  -- `f = Σ (θ(f)ᵢ / b) aᵢ` in `Q(A)`
  have hexp : ∀ f : A, algebraMap A (FractionRing A) f =
      ∑ i, (algebraMap B (FractionRing B) (θ f i) / algebraMap B (FractionRing B) b) •
        algebraMap A (FractionRing A) (a i) := by
    intro f
    have h := congrArg (algebraMap A (FractionRing A)) (hθa f)
    simp only [Algebra.smul_def, map_mul, map_sum, hBAL] at h
    simp only [Algebra.smul_def, map_div₀, hBF]
    calc algebraMap A (FractionRing A) f = (algebraMap B (FractionRing A) b)⁻¹ *
          (algebraMap B (FractionRing A) b * algebraMap A (FractionRing A) f) := by
          rw [inv_mul_cancel_left₀ hbL]
      _ = (algebraMap B (FractionRing A) b)⁻¹ * ∑ i, algebraMap B (FractionRing A) (θ f i) *
          algebraMap A (FractionRing A) (a i) := by rw [h]
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [div_eq_mul_inv]
          ring
  -- the `aᵢ` form a basis of `Q(A)` over `Q(B)` (BGR: "a `Q(B)`-basis of `Q(A)`")
  have hli : LinearIndependent (FractionRing B) fun i ↦ algebraMap A (FractionRing A) (a i) :=
    (LinearIndependent.iff_fractionRing B (FractionRing B)).1
      (ha.map' (IsScalarTower.toAlgHom B A (FractionRing A)).toLinearMap
        (LinearMap.ker_eq_bot.2 hAL))
  have hsp : ⊤ ≤ Submodule.span (FractionRing B)
      (Set.range fun i ↦ algebraMap A (FractionRing A) (a i)) := by
    intro x _
    obtain ⟨f, s, hx⟩ :=
      IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) x
    obtain ⟨c, hc, hcs⟩ := Submonoid.mem_map.1 s.2
    have hc0 : algebraMap B (FractionRing A) c ≠ 0 :=
      (map_ne_zero_iff _ hBL).2 (nonZeroDivisors.ne_zero hc)
    have hspec := IsLocalization.mk'_spec (FractionRing A) f s
    rw [hx, ← hcs, hBAL] at hspec
    have hxe : x = (algebraMap B (FractionRing B) c)⁻¹ • algebraMap A (FractionRing A) f := by
      rw [Algebra.smul_def, map_inv₀, hBF, ← hspec, mul_comm, mul_inv_cancel_right₀ hc0]
    rw [hxe, hexp f]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let β := Module.Basis.mk hli hsp
  haveI : FiniteDimensional (FractionRing B) (FractionRing A) := Module.Finite.of_basis β
  have hcoord : ∀ f i, β.equivFun (algebraMap A (FractionRing A) f) i =
      algebraMap B (FractionRing B) (θ f i) / algebraMap B (FractionRing B) b := by
    intro f i
    have h : algebraMap A (FractionRing A) f = β.equivFun.symm fun j ↦
        algebraMap B (FractionRing B) (θ f j) / algebraMap B (FractionRing B) b := by
      rw [Module.Basis.equivFun_symm_apply, hexp f]
      simp only [β, Module.Basis.mk_apply]
    rw [h, LinearEquiv.apply_symm_apply]
  -- weak stability bounds each coordinate functional by the spectral norm
  choose C hC using fun i : Fin n ↦
    hws (FractionRing A) ((LinearMap.proj i).comp β.equivFun.toLinearMap)
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hi : ∀ f i, ‖θ f i‖ ≤ ‖b‖ * C i * supSeminorm K f := by
    intro f i
    have h := hC i (algebraMap A (FractionRing A) f)
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply, hcoord f i, norm_div,
      spectralNorm_fractionRing_eq_supSeminorm hBsup f] at h
    have hθ : ‖algebraMap B (FractionRing B) (θ f i)‖ = ‖θ f i‖ :=
      IsFractionRing.normAbsoluteValue_algebraMap B (FractionRing B) (θ f i)
    have hbb : ‖algebraMap B (FractionRing B) b‖ = ‖b‖ :=
      IsFractionRing.normAbsoluteValue_algebraMap B (FractionRing B) b
    rw [hθ, hbb, div_le_iff₀ hnb] at h
    calc ‖θ f i‖ ≤ C i * supSeminorm K f * ‖b‖ := h
      _ = ‖b‖ * C i * supSeminorm K f := by ring
  refine ⟨‖b‖ * ∑ i, max (C i) 0, fun f ↦ ?_⟩
  have hs := supSeminorm_nonneg K f
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hnb.le
    (Finset.sum_nonneg fun i _ ↦ le_max_right _ _)) hs)).2 fun i ↦ (hi f i).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hnb.le) hs
  exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun j ↦ max (C j) 0)
    (fun j _ ↦ le_max_right _ _) (Finset.mem_univ i))

/-- **BGR 3.8.3/7** (for `A` a domain, plan D1): `A` finite over `B` with injective continuous
structure map, `B` a valued (`NormMulClass`) integrally closed noetherian Banach function algebra
(`|·|_sup = ‖·‖`) with weakly stable fraction field, then `A` is a Banach function algebra:
`‖f‖ ≤ C * |f|_sup`. -/
theorem IsBanachFunctionAlgebra.of_finite_domain (hBsup : ∀ b : B, supSeminorm K b = ‖b‖)
    (hws : letI := IsFractionRing.normedField B (FractionRing B); IsWeaklyStable (FractionRing B))
    (hcont : Continuous (algebraMap B A)) : IsBanachFunctionAlgebra K A := by
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  haveI : HasSupSeminorm K A := HasSupSeminorm.of_isIntegral K (B := B)
  obtain ⟨n, a, b, hb, ha, hA⟩ := exists_basis_universalDenominator (B := B) (A := A)
  obtain ⟨θ, hθ, hθa, hcl⟩ := exists_coordinateMap K hb ha hA
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_mul_norm_coordinateMap K hcont hb θ hθ hθa hcl
  obtain ⟨C₂, hC₂⟩ := exists_norm_coordinateMap_le_mul_supSeminorm hBsup hws hb ha θ hθa
  refine ⟨max C₁ 0 * C₂, fun f ↦ ?_⟩
  calc ‖f‖ ≤ C₁ * ‖θ f‖ := hC₁ f
    _ ≤ max C₁ 0 * ‖θ f‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max C₁ 0 * (C₂ * supSeminorm K f) :=
        mul_le_mul_of_nonneg_left (hC₂ f) (le_max_right _ _)
    _ = max C₁ 0 * C₂ * supSeminorm K f := (mul_assoc _ _ _).symm

end Theorem7

end Affinoid
