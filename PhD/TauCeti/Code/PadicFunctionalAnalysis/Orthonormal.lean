/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Sequences

/-!
# Orthonormal families and orthonormal bases

A family `e : I → M` in a normed module over a normed ring `R` is *orthonormal* when its members have
norm one and every finite combination `∑ aᵢ eᵢ` has norm `max ‖aᵢ‖`; it is an *orthonormal basis* when
moreover its span is dense. In a complete nonarchimedean normed module over a complete normed ring, an
orthonormal basis gives every vector a unique expansion `x = ∑' aᵢ • eᵢ` with `a → 0` along the cofinite
filter, and then every `‖aᵢ‖ ≤ ‖x‖`; the existence of the expansion uses that the ring is complete.

The sup-norm identity is stated with `‖aᵢ‖`, not with `‖aᵢ • eᵢ‖` (Bellaïche, Definition II.1.5;
Buzzard §2; Colmez, Définition 1.1.3). Over a normed field with a normed space the two forms agree,
since `‖aᵢ • eᵢ‖ = ‖aᵢ‖ ‖eᵢ‖ = ‖aᵢ‖`; over a ring only this form makes "orthonormalisable ⟺ has an
orthonormal basis" true (`p`-adic functional analysis roadmap, Layer 2 plan, erratum E19: with the
other form `{1}` would be an orthonormal basis of the torsion `ℚ_p⟨X⟩`-module `ℚ_p`).

This file is the slice of the `p`-adic functional analysis roadmap's §2.2 that the rigid analytic
geometry roadmap's Layer 0 consumes (the strict closedness of ideals of the Tate algebra): the two
predicates and the expansion lemmas. The rest of §2.2 (orthogonal and `t`-orthogonal families, the
model space, bases over Banach–Tate rings) is in `Orthogonal.lean` and `ONable.lean`.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, convention 5 and §2.2.1–2.2.2
(Bosch, *Lectures*, 1.3/5; Bellaïche, Definition II.1.5). Tau Ceti home:
`TauCeti/Analysis/Normed/Module/Ultra/Orthonormal.lean`.

## Main definitions

* `IsOrthonormalFamily R e` — members of norm one, finite combinations have the sup norm of their
  coefficients.
* `IsOrthonormalBasis R e` — an orthonormal family with dense span.

## Main results

* `IsOrthonormalFamily.linearIndependent`.
* `IsOrthonormalFamily.norm_coeff_le_of_hasSum`, `IsOrthonormalFamily.norm_le_of_hasSum` — the
  coefficients of a convergent expansion are bounded by its norm, and bound it.
* `IsOrthonormalBasis.exists_hasSum` — every vector has an expansion (Bosch 1.3/5 (ii)).
-/

open Filter Topology

/-- A family is **orthonormal** when its members have norm one and finite combinations have the sup
norm of their coefficients. Source: `p`-adic functional analysis roadmap, convention 5; Bellaïche,
Definition II.1.5 ("`|m| = sup_i |a_i|`"); Bosch 1.3/5 (i), (iii). -/
def IsOrthonormalFamily (R : Type*) [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M]
    {I : Type*} (e : I → M) : Prop :=
  (∀ i, ‖e i‖ = 1) ∧ ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊

/-- An orthonormal family whose span is dense is an **orthonormal basis**. Source: `p`-adic
functional analysis roadmap, §2.2.2; Bosch 1.3/5. -/
def IsOrthonormalBasis (R : Type*) [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M]
    {I : Type*} (e : I → M) : Prop :=
  IsOrthonormalFamily R e ∧ Dense (Submodule.span R (Set.range e) : Set M)

namespace IsOrthonormalFamily

variable {R : Type*} [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M] {I : Type*}
  {e : I → M}

theorem norm_eq_one (he : IsOrthonormalFamily R e) (i : I) : ‖e i‖ = 1 := he.1 i

/-- The sup-norm identity at a singleton: `‖c • eᵢ‖₊ = ‖c‖₊`. -/
theorem nnnorm_smul_eq (he : IsOrthonormalFamily R e) (c : R) (i : I) : ‖c • e i‖₊ = ‖c‖₊ := by
  have h := he.2 {i} fun _ ↦ c
  rwa [Finset.sum_singleton, Finset.sup_singleton] at h

/-- The sup-norm identity at a singleton: `‖c • eᵢ‖ = ‖c‖`. -/
theorem norm_smul_eq (he : IsOrthonormalFamily R e) (c : R) (i : I) : ‖c • e i‖ = ‖c‖ := by
  rw [← coe_nnnorm, he.nnnorm_smul_eq, coe_nnnorm]

/-- In a finite combination of an orthonormal family every coefficient is bounded by the norm of
the combination. -/
theorem norm_coeff_le_norm_sum (he : IsOrthonormalFamily R e) (s : Finset I) (a : I → R) {i : I}
    (hi : i ∈ s) : ‖a i‖ ≤ ‖∑ j ∈ s, a j • e j‖ := by
  have h : ‖a i‖₊ ≤ ‖∑ j ∈ s, a j • e j‖₊ := by
    rw [he.2 s a]
    exact Finset.le_sup (f := fun j ↦ ‖a j‖₊) hi
  exact_mod_cast h

/-- A finite combination of an orthonormal family is bounded by any bound on its coefficients. -/
theorem norm_sum_le (he : IsOrthonormalFamily R e) (s : Finset I) (a : I → R) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i ∈ s, ‖a i‖ ≤ C) : ‖∑ i ∈ s, a i • e i‖ ≤ C := by
  lift C to NNReal using hC
  have h' : ‖∑ i ∈ s, a i • e i‖₊ ≤ C := by
    rw [he.2 s a]
    exact Finset.sup_le fun i hi ↦ by exact_mod_cast h i hi
  exact_mod_cast h'

/-- An orthonormal family is linearly independent. -/
theorem linearIndependent (he : IsOrthonormalFamily R e) : LinearIndependent R e :=
  linearIndependent_iff'.2 fun s g hg _ hi ↦ norm_le_zero_iff.1
    ((he.norm_coeff_le_norm_sum s g hi).trans_eq (by rw [hg, norm_zero]))

/-- The coefficients of a convergent expansion in an orthonormal family tend to zero. -/
theorem tendsto_cofinite_of_hasSum (he : IsOrthonormalFamily R e) {a : I → R} {x : M}
    (hx : HasSum (fun i ↦ a i • e i) x) : Tendsto a cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := hx.summable.tendsto_cofinite_zero.norm
  simp only [he.norm_smul_eq, norm_zero] at h
  exact h

/-- In a convergent expansion in an orthonormal family every coefficient is bounded by the norm of
the sum. Source: Bosch 1.3/5 (iii). -/
theorem norm_coeff_le_of_hasSum (he : IsOrthonormalFamily R e) {a : I → R} {x : M}
    (hx : HasSum (fun i ↦ a i • e i) x) (i : I) : ‖a i‖ ≤ ‖x‖ := by
  have hx' : Tendsto (fun s : Finset I ↦ ∑ j ∈ s, a j • e j) atTop (𝓝 x) := hx
  exact ge_of_tendsto hx'.norm ((eventually_ge_atTop {i}).mono fun s hs ↦
    he.norm_coeff_le_norm_sum s a (hs (Finset.mem_singleton_self i)))

/-- A convergent expansion in an orthonormal family is bounded by any bound on its coefficients.
Source: Bosch 1.3/5 (iii). -/
theorem norm_le_of_hasSum (he : IsOrthonormalFamily R e) {a : I → R} {x : M}
    (hx : HasSum (fun i ↦ a i • e i) x) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖a i‖ ≤ C) : ‖x‖ ≤ C := by
  have hx' : Tendsto (fun s : Finset I ↦ ∑ j ∈ s, a j • e j) atTop (𝓝 x) := hx
  exact le_of_tendsto' hx'.norm fun s ↦ he.norm_sum_le s a hC fun i _ ↦ h i

/-- The coefficients of an expansion in an orthonormal family are unique.
Source: Bosch 1.3/5 ("In particular, the coefficients `c_ν` in (ii) are unique"). -/
theorem eq_of_hasSum (he : IsOrthonormalFamily R e) {a b : I → R} {x : M}
    (ha : HasSum (fun i ↦ a i • e i) x) (hb : HasSum (fun i ↦ b i • e i) x) : a = b := by
  funext i
  have hab : HasSum (fun j ↦ (a - b) j • e j) 0 := by
    simpa only [Pi.sub_apply, sub_smul, sub_self] using ha.sub hb
  have h := he.norm_coeff_le_of_hasSum hab i
  rw [norm_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- In a complete nonarchimedean module a family of coefficients tending to zero is summable against
an orthonormal family. -/
theorem summable_smul [IsUltrametricDist M] [CompleteSpace M] (he : IsOrthonormalFamily R e)
    {a : I → R} (ha : Tendsto a cofinite (𝓝 0)) : Summable fun i ↦ a i • e i := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero] at ha ⊢
  simpa only [he.norm_smul_eq] using ha

end IsOrthonormalFamily

namespace IsOrthonormalBasis

variable {R : Type*} [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M]
  [IsUltrametricDist M] [CompleteSpace M] {I : Type*} {e : I → M}

/-- Every vector of a complete nonarchimedean module over a complete normed ring has an expansion in
an orthonormal basis. Source: Bosch 1.3/5 (ii); Bellaïche, Lemma II.1.12.

Completeness of the ring is necessary: `ℚ_[p]` is a complete normed space over `ℚ` with its
`p`-adic norm, the family `{1}` is orthonormal with dense span, and an element of `ℚ_[p]` outside
`ℚ` has no expansion. -/
theorem exists_hasSum [CompleteSpace R] (he : IsOrthonormalBasis R e) (x : M) :
    ∃ a : I → R, HasSum (fun i ↦ a i • e i) x := by
  classical
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.1 (he.2 x)
  choose l hl using fun k ↦ Finsupp.mem_span_range_iff_exists_finsupp.1 (hu_mem k)
  have hu_cauchy := hu_lim.cauchySeq
  have hcoef (k m : ℕ) (i : I) : ‖l k i - l m i‖ ≤ ‖u k - u m‖ := by
    have hk : u k = ∑ j ∈ insert i ((l k).support ∪ (l m).support), l k j • e j := by
      rw [← hl k, Finsupp.sum_of_support_subset _
        (fun j hj ↦ Finset.mem_insert_of_mem (Finset.mem_union_left _ hj))
        (fun j c ↦ c • e j) (fun _ _ ↦ zero_smul R _)]
    have hm : u m = ∑ j ∈ insert i ((l k).support ∪ (l m).support), l m j • e j := by
      rw [← hl m, Finsupp.sum_of_support_subset _
        (fun j hj ↦ Finset.mem_insert_of_mem (Finset.mem_union_right _ hj))
        (fun j c ↦ c • e j) (fun _ _ ↦ zero_smul R _)]
    rw [hk, hm, ← Finset.sum_sub_distrib]
    simp_rw [← sub_smul]
    exact he.1.norm_coeff_le_norm_sum _ (fun j ↦ l k j - l m j) (Finset.mem_insert_self i _)
  have hcauchy (i : I) : CauchySeq fun k ↦ l k i := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu_cauchy ε hε
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [dist_eq_norm]
    exact (hcoef m n i).trans_lt (by rw [← dist_eq_norm]; exact hN m hm n hn)
  choose a ha using fun i ↦ cauchySeq_tendsto_of_complete (hcauchy i)
  have hunif (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k ≥ N, ∀ i, ‖l k i - a i‖ ≤ ε := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu_cauchy ε hε
    refine ⟨N, fun k hk i ↦ ?_⟩
    have hlim : Tendsto (fun m ↦ ‖l k i - l m i‖) atTop (𝓝 ‖l k i - a i‖) :=
      (tendsto_const_nhds.sub (ha i)).norm
    refine le_of_tendsto hlim ((eventually_ge_atTop N).mono fun m hm ↦ ?_)
    exact (hcoef k m i).trans (by rw [← dist_eq_norm]; exact (hN k hk m hm).le)
  have hnull : Tendsto a cofinite (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    refine eventually_cofinite.2 ((l N).support.finite_toSet.subset fun i hi ↦ ?_)
    by_contra hni
    rw [Finset.mem_coe, Finsupp.notMem_support_iff] at hni
    have h := hN N le_rfl i
    rw [hni, zero_sub, norm_neg] at h
    exact hi (by rw [dist_zero_right]; linarith)
  have hy := (he.1.summable_smul hnull).hasSum
  have hlk (k : ℕ) : HasSum (fun i ↦ l k i • e i) (u k) := by
    rw [← hl k]
    exact hasSum_sum_of_ne_finset_zero fun i hi ↦ by rw [Finsupp.notMem_support_iff.1 hi, zero_smul]
  have hconv : Tendsto u atTop (𝓝 (∑' i, a i • e i)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    refine ⟨N, fun k hk ↦ ?_⟩
    have hdiff : HasSum (fun i ↦ (a - ⇑(l k)) i • e i) (∑' i, a i • e i - u k) := by
      simpa only [Pi.sub_apply, sub_smul] using hy.sub (hlk k)
    have hle := he.1.norm_le_of_hasSum hdiff (half_pos hε).le fun i ↦ by
      rw [Pi.sub_apply, norm_sub_rev]
      exact hN k hk i
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  rw [tendsto_nhds_unique hu_lim hconv]
  exact ⟨a, hy⟩

end IsOrthonormalBasis
