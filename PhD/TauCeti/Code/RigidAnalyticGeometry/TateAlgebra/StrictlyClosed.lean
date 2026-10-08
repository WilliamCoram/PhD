/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.MetricSpace.Ultra.Pi
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Sums
import PhD.TauCeti.Code.RigidAnalyticGeometry.OrthonormalLift
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Reduction

/-!
# Ideals of the Tate algebra are strictly closed

Let `T` be the Tate algebra over a complete nonarchimedean field `K` in finitely many variables and
`N` a submodule of a finite free module `Tˢ` with the maximum norm. Then `N` has generators
`g₁, …, g_r` of norm one such that every `x ∈ N` is `Σ qⱼ gⱼ` with `‖qⱼ‖ ≤ ‖x‖`; `N` is closed; and
`N` is *strictly closed*: every `f ∈ Tˢ` has a nearest point in `N`, so that the residue norm on
`Tˢ ⧸ N` takes its values in `‖K‖`. For `s = 1` these are the statements about ideals.

The proof is Bosch's: the reduction `Ñ` of `N` is a finitely generated module over the polynomial
ring `k[X]`; multiples `X^ν gⱼ` of lifts of generators are chosen whose reductions are a `k`-basis
of `Ñ`, and completed by monomials `X^ν eᵢ` to a family whose reductions are a `k`-basis of
`k[X]ˢ`; the coordinates of this family lie in a bald subring, so by the lifting theorem it is an
orthonormal basis of `Tˢ`, and the part of it in `N` is an orthonormal basis of `N`.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.3.1 and §0.3.5 (Bosch 1.3/7–10;
BGR 5.2.7/1, 5.2.7/2, 5.2.7/7, 5.2.7/8). Tau Ceti home:
`TauCeti/RingTheory/TateAlgebra/StrictlyClosed.lean`.

## Main definitions

* `MvPowerSeries.Restricted.reductionSubmodule N` — the reduction `Ñ` of a submodule of `Tˢ`.
* `MvPowerSeries.Restricted.adaptedFamily g A B` — the family `X^ν gⱼ`, `X^ν eᵢ`.

## Main results

* `MvPowerSeries.Restricted.exists_generators_norm_le` — Bosch 1.3/10; BGR 5.2.7/1 with `ρ = 1`.
* `MvPowerSeries.Restricted.exists_forall_norm_sub_le` — submodules are strictly closed
  (BGR 5.2.7/7).
* `MvPowerSeries.Restricted.isClosed_ideal` — ideals are closed (Bosch 1.3/8; BGR 5.2.7/2).
* `MvPowerSeries.Restricted.exists_forall_norm_sub_le_ideal` — ideals are strictly closed
  (Bosch 1.3/9; BGR 5.2.7/8).
* `MvPowerSeries.Restricted.norm_quotient_mk_mem_range_norm` — `|T ⧸ 𝔞| = |K|` (BGR 5.2.7/8).
-/

open Filter Topology Subring NormedRing IsLocalRing

/-! ### Selection of a basis in a free module over a polynomial ring -/

namespace MvPolynomial

variable {k : Type*} [Field k] {σ ι : Type*} [DecidableEq ι]

/-- The family of the multiples `X^ν • h j`, for `(ν, j)` in `A`, and of the monomial vectors
`X^ν eᵢ`, for `(i, ν)` in `B`. -/
noncomputable def adaptedFamily {r : ℕ} (h : Fin r → ι → MvPolynomial σ k)
    (A : Set ((σ →₀ ℕ) × Fin r)) (B : Set (Σ _ : ι, σ →₀ ℕ)) : A ⊕ B → ι → MvPolynomial σ k :=
  Sum.elim (fun a ↦ monomial a.1.1 (1 : k) • h a.1.2)
    (fun b ↦ Pi.single b.1.1 (monomial b.1.2 (1 : k)))

/-- For finitely many vectors `h j` of a free module `k[X]^ι` there are monomial multiples
`X^ν • h j` forming a `k`-basis of the submodule they generate, and monomial vectors completing
them to a `k`-basis of `k[X]^ι`. Source: Bosch 1.3/7 and 1.3/10 ("we can find a system `(y_μ)` of
elements of type `ζ^ν aᵢ` such that its residue classes form a `k`-basis of `ã`. Adding monomials
of type `ζ^ν` …"). -/
theorem exists_basis_adaptedFamily [Fintype ι] {r : ℕ} (h : Fin r → ι → MvPolynomial σ k) :
    ∃ (A : Set ((σ →₀ ℕ) × Fin r)) (B : Set (Σ _ : ι, σ →₀ ℕ)),
      LinearIndependent k (adaptedFamily h A B) ∧
        Submodule.span k (Set.range (adaptedFamily h A B)) = ⊤ ∧
          Submodule.span k (Set.range fun a : A ↦ monomial a.1.1 (1 : k) • h a.1.2) =
            (Submodule.span (MvPolynomial σ k) (Set.range h)).restrictScalars k := by
  classical
  let G : (σ →₀ ℕ) × Fin r → ι → MvPolynomial σ k := fun a ↦ monomial a.1 (1 : k) • h a.2
  let E : (Σ _ : ι, σ →₀ ℕ) → ι → MvPolynomial σ k := fun b ↦ Pi.single b.1 (monomial b.2 (1 : k))
  let v : ((σ →₀ ℕ) × Fin r) ⊕ (Σ _ : ι, σ →₀ ℕ) → ι → MvPolynomial σ k := Sum.elim G E
  have h0 : LinearIndepOn k v ∅ := linearIndepOn_empty k v
  have hA₀sub := h0.extend_subset (Set.empty_subset (Set.range Sum.inl))
  have hA₀li := h0.linearIndepOn_extend (Set.empty_subset (Set.range Sum.inl))
  have hA₀span := h0.image_subset_span_image_extend (Set.empty_subset (Set.range Sum.inl))
  set A₀ := h0.extend (Set.empty_subset (Set.range Sum.inl))
  have hCli := hA₀li.linearIndepOn_extend (Set.subset_univ A₀)
  have hA₀C := hA₀li.subset_extend (Set.subset_univ A₀)
  have hCspan := hA₀li.image_subset_span_image_extend (Set.subset_univ A₀)
  set C := hA₀li.extend (Set.subset_univ A₀)
  have hCinl (a : (σ →₀ ℕ) × Fin r) (ha : Sum.inl a ∈ C) : Sum.inl a ∈ A₀ := by
    by_contra hna
    exact (hCli.mono (Set.insert_subset ha hA₀C)).notMem_span_of_insert hna
      (hA₀span ⟨Sum.inl a, ⟨a, rfl⟩, rfl⟩)
  refine ⟨Sum.inl ⁻¹' C, Sum.inr ⁻¹' C, ?_, ?_, ?_⟩
  · let g : (Sum.inl ⁻¹' C : Set ((σ →₀ ℕ) × Fin r)) ⊕ (Sum.inr ⁻¹' C : Set (Σ _ : ι, σ →₀ ℕ)) →
        C := Sum.elim (fun a ↦ ⟨Sum.inl a.1, a.2⟩) (fun b ↦ ⟨Sum.inr b.1, b.2⟩)
    have hg : Function.Injective g := by
      rintro (⟨a, ha⟩ | ⟨b, hb⟩) (⟨a', ha'⟩ | ⟨b', hb'⟩) hab <;>
        simp only [g, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Sum.inl.injEq,
          Sum.inr.injEq, reduceCtorEq] at hab
      · subst hab
        rfl
      · subst hab
        rfl
    have hli : LinearIndependent k ((fun x : C ↦ v x) ∘ g) := LinearIndependent.comp hCli g hg
    convert hli using 1
    funext x
    rcases x with a | b <;> rfl
  · have hE : Submodule.span k (Set.range E) = ⊤ := by
      have hb := (Pi.basis fun _ : ι ↦ MvPolynomial.basisMonomials σ k).span_eq
      have hfun : ⇑(Pi.basis fun _ : ι ↦ MvPolynomial.basisMonomials σ k) = E := by
        funext b
        rw [Pi.basis_apply, MvPolynomial.coe_basisMonomials]
      rwa [hfun] at hb
    have hrange : v '' C ⊆ Set.range (adaptedFamily h (Sum.inl ⁻¹' C) (Sum.inr ⁻¹' C)) := by
      rintro _ ⟨(a | b), hx, rfl⟩
      · exact ⟨Sum.inl ⟨a, hx⟩, rfl⟩
      · exact ⟨Sum.inr ⟨b, hx⟩, rfl⟩
    refine eq_top_iff.2 (hE.symm.le.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨b, rfl⟩
    exact Submodule.span_mono hrange (hCspan ⟨Sum.inr b, Set.mem_univ _, rfl⟩)
  · have hGA : Set.range (fun a : (Sum.inl ⁻¹' C : Set ((σ →₀ ℕ) × Fin r)) ↦
        monomial a.1.1 (1 : k) • h a.1.2) = v '' A₀ := by
      ext w
      constructor
      · rintro ⟨⟨a, ha⟩, rfl⟩
        exact ⟨Sum.inl a, hCinl a ha, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨a, rfl⟩ := hA₀sub hx
        exact ⟨⟨a, hA₀C hx⟩, rfl⟩
    have hspanG : Submodule.span k (v '' A₀) = Submodule.span k (Set.range G) := by
      refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨a, rfl⟩ := hA₀sub hx
        exact ⟨a, rfl⟩
      · rintro _ ⟨a, rfl⟩
        exact hA₀span ⟨Sum.inl a, ⟨a, rfl⟩, rfl⟩
    rw [hGA, hspanG]
    have hmon (μ : σ →₀ ℕ) (c : k) (w : ι → MvPolynomial σ k)
        (hw : w ∈ Submodule.span k (Set.range G)) :
        monomial μ c • w ∈ Submodule.span k (Set.range G) := by
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨ν, j⟩, rfl⟩ := hw
        have hcalc : monomial μ c • (monomial ν (1 : k) • h j) =
            c • (monomial (μ + ν) (1 : k) • h j) := by
          rw [smul_smul, monomial_mul, mul_one, ← smul_assoc, smul_monomial, smul_eq_mul, mul_one]
        change monomial μ c • (monomial ν (1 : k) • h j) ∈ _
        rw [hcalc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(μ + ν, j), rfl⟩)
      | zero =>
        rw [smul_zero]
        exact zero_mem _
      | add w₁ w₂ _ _ h₁ h₂ =>
        rw [smul_add]
        exact add_mem h₁ h₂
      | smul a w _ hw =>
        rw [smul_comm]
        exact Submodule.smul_mem _ _ hw
    refine le_antisymm (Submodule.span_le.2 ?_) fun w hw ↦ ?_
    · rintro _ ⟨a, rfl⟩
      change G a ∈ Submodule.span (MvPolynomial σ k) (Set.range h)
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a.2, rfl⟩)
    · rw [Submodule.restrictScalars_mem] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨j, rfl⟩ := hw
        have h1 : h j = monomial (0 : σ →₀ ℕ) (1 : k) • h j := by
          rw [show (monomial (0 : σ →₀ ℕ) (1 : k) : MvPolynomial σ k) = 1 from rfl, one_smul]
        rw [h1]
        exact Submodule.subset_span ⟨(0, j), rfl⟩
      | zero => exact zero_mem _
      | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
      | smul p w _ hw =>
        rw [p.as_sum, Finset.sum_smul]
        exact Submodule.sum_mem _ fun μ _ ↦ hmon μ _ w hw

end MvPolynomial

namespace MvPowerSeries.Restricted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ ι : Type*}

local notation "𝕋" => Restricted K (1 : σ → ℝ)

local notation "𝕜" => ResidueField (unitClosedBall K)

/-! ### The monomials are an orthonormal basis -/

/-- The monomials are an orthonormal basis of the Tate algebra as a normed `K`-vector space.
Source: Bosch 1.3/5 ("the monomials `ζ^ν ∈ Tₙ` form an orthonormal basis"); BGR 5.1.1/4. -/
theorem isOrthonormalBasis_monomial :
    IsOrthonormalBasis K fun t : σ →₀ ℕ ↦ (monomial (1 : σ → ℝ) t (1 : K) : 𝕋) := by
  classical
  have hnorm (t : σ →₀ ℕ) : ‖(monomial (1 : σ → ℝ) t (1 : K) : 𝕋)‖ = 1 := by
    rw [norm_monomial, norm_one, one_mul]
    simp [Finsupp.prod]
  have hcoeff (s : Finset (σ →₀ ℕ)) (a : (σ →₀ ℕ) → K) (u : σ →₀ ℕ) :
      MvPowerSeries.coeff u (∑ t ∈ s, a t • (monomial (1 : σ → ℝ) t (1 : K) : 𝕋)).1 =
        if u ∈ s then a u else 0 := by
    simp only [val_sum, val_smul, val_monomial, map_sum, MvPowerSeries.coeff_smul,
      MvPowerSeries.coeff_monomial, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  refine ⟨⟨hnorm, fun s a ↦ le_antisymm ?_ (Finset.sup_le fun t ht ↦ ?_)⟩, ?_⟩
  · rw [← NNReal.coe_le_coe, coe_nnnorm]
    refine (norm_le_iff_forall_norm_coeff_le _).2 fun u ↦ ?_
    refine (congrArg norm (hcoeff s a u)).trans_le ?_
    split_ifs with hu
    · rw [← coe_nnnorm, NNReal.coe_le_coe]
      exact Finset.le_sup (f := fun t ↦ ‖a t‖₊) hu
    · rw [norm_zero]
      exact NNReal.coe_nonneg _
  · rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    have h := norm_coeff_le (∑ t ∈ s, a t • (monomial (1 : σ → ℝ) t (1 : K) : 𝕋)) t
    rwa [hcoeff, if_pos ht] at h
  · have hsub : Set.range (MvPolynomial.toRestricted (R := K) (1 : σ → ℝ)) ⊆
        (Submodule.span K (Set.range fun t ↦ (monomial (1 : σ → ℝ) t (1 : K) : 𝕋)) : Set 𝕋) := by
      rintro _ ⟨p, rfl⟩
      rw [p.as_sum, map_sum]
      refine Submodule.sum_mem _ fun t _ ↦ ?_
      rw [MvPolynomial.toRestricted_monomial]
      have hm : (monomial (1 : σ → ℝ) t (MvPolynomial.coeff t p) : 𝕋) =
          MvPolynomial.coeff t p • (monomial (1 : σ → ℝ) t (1 : K) : 𝕋) :=
        Restricted.ext (MvPowerSeries.ext fun u ↦ by
          simp [MvPowerSeries.coeff_monomial])
      rw [hm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
    exact (denseRange_toRestricted (1 : σ → ℝ)).mono hsub

section Pi

variable [Fintype ι] [DecidableEq ι]

/-- The monomial vectors `X^ν eᵢ` are an orthonormal basis of the free module `Tˢ` with the
maximum norm. Source: Bosch 1.3/10 ("the canonical system `Z = (ζ^ν eⱼ)`, which is an orthonormal
basis of `Tₙˢ`"). -/
theorem isOrthonormalBasis_single_monomial :
    IsOrthonormalBasis K fun p : (Σ _ : ι, σ →₀ ℕ) ↦
      (Pi.single p.1 (monomial (1 : σ → ℝ) p.2 (1 : K)) : ι → 𝕋) := by
  classical
  have hmon := isOrthonormalBasis_monomial (K := K) (σ := σ)
  have hterm (q : Σ _ : ι, σ →₀ ℕ) (c : K) (i : ι) (u : σ →₀ ℕ) :
      MvPowerSeries.coeff u ((c • (Pi.single q.1 (monomial (1 : σ → ℝ) q.2 (1 : K)) :
        ι → 𝕋)) i).1 = if q = ⟨i, u⟩ then c else 0 := by
    obtain ⟨j, t⟩ := q
    by_cases hj : j = i
    · subst hj
      by_cases ht : t = u
      · subst ht
        simp
      · simp [MvPowerSeries.coeff_monomial, Ne.symm ht, ht]
    · simp [hj]
  have hcoeff (s : Finset (Σ _ : ι, σ →₀ ℕ)) (a : (Σ _ : ι, σ →₀ ℕ) → K) (i : ι)
      (u : σ →₀ ℕ) :
      MvPowerSeries.coeff u ((∑ q ∈ s, a q • (Pi.single q.1 (monomial (1 : σ → ℝ) q.2 (1 : K)) :
        ι → 𝕋)) i).1 = if (⟨i, u⟩ : Σ _ : ι, σ →₀ ℕ) ∈ s then a ⟨i, u⟩ else 0 := by
    rw [Finset.sum_apply, val_sum, map_sum]
    simp only [hterm, Finset.sum_ite_eq']
  refine ⟨⟨fun q ↦ by rw [Pi.norm_single, hmon.1.1], fun s a ↦ le_antisymm ?_
    (Finset.sup_le fun q hq ↦ ?_)⟩, ?_⟩
  · rw [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonneg (NNReal.coe_nonneg _)]
    intro i
    refine (norm_le_iff_forall_norm_coeff_le _).2 fun u ↦ ?_
    refine (congrArg norm (hcoeff s a i u)).trans_le ?_
    split_ifs with hu
    · rw [← coe_nnnorm, NNReal.coe_le_coe]
      exact Finset.le_sup (f := fun q ↦ ‖a q‖₊) hu
    · rw [norm_zero]
      exact NNReal.coe_nonneg _
  · rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    have h := (norm_coeff_le ((∑ q ∈ s, a q • (Pi.single q.1 (monomial (1 : σ → ℝ) q.2 (1 : K)) :
      ι → 𝕋)) q.1) q.2).trans (norm_le_pi_norm _ q.1)
    rwa [hcoeff, if_pos hq] at h
  · intro x
    rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe, ← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    have hcont : Continuous fun y : 𝕋 ↦ (Pi.single i y : ι → 𝕋) :=
      continuous_single (A := fun _ : ι ↦ 𝕋) i
    refine map_mem_closure hcont (hmon.2 (x i)) fun f hf ↦ ?_
    have hle : Submodule.span K (Set.range fun t ↦ (monomial (1 : σ → ℝ) t (1 : K) : 𝕋)) ≤
        (Submodule.span K (Set.range fun p : (Σ _ : ι, σ →₀ ℕ) ↦
          (Pi.single p.1 (monomial (1 : σ → ℝ) p.2 (1 : K)) : ι → 𝕋))).comap
            (LinearMap.single K (fun _ : ι ↦ 𝕋) i) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact Submodule.subset_span ⟨⟨i, t⟩, rfl⟩
    exact hle hf

omit [Fintype ι] in
/-- The expansion of a tuple of series in the monomial vectors. -/
theorem hasSum_coeff_smul_single_monomial (f : ι → 𝕋) :
    HasSum (fun p : (Σ _ : ι, σ →₀ ℕ) ↦
      coeff p.2 (f p.1).1 • (Pi.single p.1 (monomial (1 : σ → ℝ) p.2 (1 : K)) : ι → 𝕋)) f := by
  refine Pi.hasSum.2 fun i ↦ ?_
  have hg : Function.Injective (Sigma.mk (β := fun _ : ι ↦ σ →₀ ℕ) i) := sigma_mk_injective
  refine (hg.hasSum_iff ?_).1 ?_
  · rintro ⟨j, t⟩ hp
    have hji : j ≠ i := by
      rintro rfl
      exact hp ⟨t, rfl⟩
    simp [Pi.single_eq_of_ne (Ne.symm hji)]
  · convert hasSum_monomial (1 : σ → ℝ) (f i) using 1
    funext t
    simp only [Function.comp_apply, Pi.smul_apply, Pi.single_eq_same]
    exact Restricted.ext (MvPowerSeries.ext fun u ↦ by
      by_cases h : u = t
      · subst h
        simp [MvPowerSeries.coeff_monomial_same]
      · simp [MvPowerSeries.coeff_monomial_ne h])

end Pi

/-! ### The reduction of a submodule -/

section Reduction

variable [Fintype ι]

/-- The componentwise reduction of a tuple of the unit ball of `Tˢ`. -/
noncomputable def reductionPi (x : ι → 𝕋) (hx : ‖x‖ ≤ 1) : ι → MvPolynomial σ 𝕜 :=
  fun i ↦ reduction ⟨x i, mem_unitClosedBall.2 ((norm_le_pi_norm x i).trans hx)⟩

/-- The reduction vanishes exactly on the tuples of norm less than one. -/
theorem reductionPi_eq_zero_iff {x : ι → 𝕋} (hx : ‖x‖ ≤ 1) : reductionPi x hx = 0 ↔ ‖x‖ < 1 := by
  rw [funext_iff, pi_norm_lt_iff zero_lt_one]
  simp only [Pi.zero_apply, reductionPi, reduction_eq_zero_iff]

/-- The reduction `Ñ` of a submodule `N` of `Tˢ`: the reductions of the elements of `N` in the
unit ball, a submodule of `k[X]ˢ`. Source: Bosch 1.3/10 ("Writing `Ñ` for the image of
`N ∩ (R⟨ζ⟩)ˢ`, we see that `Ñ` is a `k[ζ]`-submodule of `(k[ζ])ˢ`"). -/
def reductionSubmodule (N : Submodule 𝕋 (ι → 𝕋)) :
    Submodule (MvPolynomial σ 𝕜) (ι → MvPolynomial σ 𝕜) where
  carrier := {u | ∃ (x : ι → 𝕋) (hx : ‖x‖ ≤ 1), x ∈ N ∧ reductionPi x hx = u}
  add_mem' := by
    rintro _ _ ⟨x, hx, hxN, rfl⟩ ⟨y, hy, hyN, rfl⟩
    refine ⟨x + y, (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy),
      N.add_mem hxN hyN, ?_⟩
    funext i
    simp only [reductionPi, Pi.add_apply]
    rw [← map_add]
    rfl
  zero_mem' := by
    refine ⟨0, by rw [norm_zero]; exact zero_le_one, N.zero_mem, ?_⟩
    funext i
    simp only [reductionPi, Pi.zero_apply]
    rw [← map_zero reduction]
    rfl
  smul_mem' := by
    rintro p _ ⟨x, hx, hxN, rfl⟩
    obtain ⟨P, rfl⟩ := reduction_surjective p
    have hPx : ‖(P : 𝕋) • x‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_
      rw [Pi.smul_apply, smul_eq_mul]
      exact (_root_.norm_mul_le _ _).trans (mul_le_one₀ (Subring.norm_le_one P) (norm_nonneg _)
        ((norm_le_pi_norm x i).trans hx))
    refine ⟨(P : 𝕋) • x, hPx, N.smul_mem _ hxN, ?_⟩
    funext i
    simp only [reductionPi, Pi.smul_apply, smul_eq_mul]
    rw [← map_mul]
    rfl

theorem mem_reductionSubmodule {N : Submodule 𝕋 (ι → 𝕋)} {u : ι → MvPolynomial σ 𝕜} :
    u ∈ reductionSubmodule N ↔ ∃ (x : ι → 𝕋) (hx : ‖x‖ ≤ 1), x ∈ N ∧ reductionPi x hx = u :=
  Iff.rfl

/-- The reduction of a submodule is generated by the reductions of finitely many of its elements
of norm one. Source: Bosch 1.3/10 ("we can choose elements `x₁, …, x_r ∈ N` of norm `1` such that
their residue classes generate `Ñ` as `k[ζ]`-module"). -/
theorem exists_generators_reductionSubmodule [Finite σ] (N : Submodule 𝕋 (ι → 𝕋)) :
    ∃ (r : ℕ) (g : Fin r → ι → 𝕋) (hg : ∀ j, ‖g j‖ = 1), (∀ j, g j ∈ N) ∧
      Submodule.span (MvPolynomial σ 𝕜) (Set.range fun j ↦ reductionPi (g j) (hg j).le) =
        reductionSubmodule N := by
  classical
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (reductionSubmodule N)
  have hS' : Submodule.span (MvPolynomial σ 𝕜) ((S.erase 0 : Finset _) : Set _) =
      reductionSubmodule N := by
    rw [Finset.coe_erase, Submodule.span_sdiff_singleton_zero, hS]
  have hlift (u : ι → MvPolynomial σ 𝕜) (hu : u ∈ S.erase 0) :
      ∃ (x : ι → 𝕋) (hx : ‖x‖ = 1), x ∈ N ∧ reductionPi x hx.le = u := by
    have hmem : u ∈ reductionSubmodule N := by
      rw [← hS]
      exact Submodule.subset_span (Finset.mem_of_mem_erase hu)
    obtain ⟨x, hx, hxN, rfl⟩ := hmem
    have hx1 : ‖x‖ = 1 := le_antisymm hx (not_lt.1 fun hlt ↦
      Finset.ne_of_mem_erase hu ((reductionPi_eq_zero_iff hx).2 hlt))
    exact ⟨x, hx1, hxN, rfl⟩
  choose! X hX1 hXN hXred using hlift
  refine ⟨(S.erase 0).card, fun j ↦ X ((S.erase 0).equivFin.symm j),
    fun j ↦ hX1 _ ((S.erase 0).equivFin.symm j).2,
    fun j ↦ hXN _ ((S.erase 0).equivFin.symm j).2, ?_⟩
  have hrange : Set.range (fun j ↦ reductionPi (X ((S.erase 0).equivFin.symm j))
      (hX1 _ ((S.erase 0).equivFin.symm j).2).le) =
        ((S.erase 0 : Finset _) : Set (ι → MvPolynomial σ 𝕜)) := by
    ext u
    constructor
    · rintro ⟨j, rfl⟩
      beta_reduce
      rw [hXred _ ((S.erase 0).equivFin.symm j).2]
      exact ((S.erase 0).equivFin.symm j).2
    · intro hu
      refine ⟨(S.erase 0).equivFin ⟨u, hu⟩, ?_⟩
      beta_reduce
      rw [Equiv.symm_apply_apply]
      exact hXred u hu
  exact (congrArg (Submodule.span (MvPolynomial σ 𝕜)) hrange).trans hS'

end Reduction

/-! ### The adapted orthonormal basis -/

section Adapted

variable [Fintype ι] [DecidableEq ι]

/-- The family of the multiples `X^ν • g j`, for `(ν, j)` in `A`, and of the monomial vectors
`X^ν eᵢ`, for `(i, ν)` in `B`. Source: Bosch 1.3/10 (the system `(y_μ)`). -/
noncomputable def adaptedFamily {r : ℕ} (g : Fin r → ι → 𝕋) (A : Set ((σ →₀ ℕ) × Fin r))
    (B : Set (Σ _ : ι, σ →₀ ℕ)) : A ⊕ B → ι → 𝕋 :=
  Sum.elim (fun a ↦ monomial (1 : σ → ℝ) a.1.1 (1 : K) • g a.1.2)
    (fun b ↦ Pi.single b.1.1 (monomial (1 : σ → ℝ) b.1.2 (1 : K)))

omit [DecidableEq ι] in
/-- The coefficients of finitely many tuples of the unit ball lie in a bald subring.
Source: Bosch 1.3/10 ("we need finitely many zero sequences in `R`, and the smallest subring
`R' ⊂ R` containing all these coefficients is bald by Proposition 3"). -/
theorem exists_isBald_forall_coeff_mem {r : ℕ} (g : Fin r → ι → 𝕋) (hg : ∀ j, ‖g j‖ ≤ 1) :
    ∃ S : Subring K, S.IsBald ∧ ∀ j i t, coeff t (g j i).1 ∈ S := by
  let a : Fin r × ι × (σ →₀ ℕ) → K := fun q ↦ coeff q.2.2 (g q.1 q.2.1).1
  have ha1 (q : Fin r × ι × (σ →₀ ℕ)) : ‖a q‖ ≤ 1 :=
    (norm_coeff_le _ _).trans ((norm_le_pi_norm (g q.1) q.2.1).trans (hg q.1))
  have ha0 : Tendsto a cofinite (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    refine eventually_cofinite.2 ((Set.finite_univ.biUnion fun (p : Fin r × ι) _ ↦
      (finite_setOf_le_norm_coeff (g p.1 p.2) hε).image fun t ↦ (p.1, p.2, t)).subset ?_)
    intro q hq
    simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hq
    exact Set.mem_biUnion (Set.mem_univ (q.1, q.2.1)) ⟨q.2.2, hq, rfl⟩
  exact ⟨closure (Set.range a), isBald_closure_range ha1 ha0,
    fun j i t ↦ subset_closure ⟨(j, i, t), rfl⟩⟩

/-- The monomials have norm one. -/
private lemma norm_monomial_one (ν : σ →₀ ℕ) : ‖(monomial (1 : σ → ℝ) ν (1 : K) : 𝕋)‖ = 1 := by
  rw [norm_monomial, norm_one, one_mul]
  simp [Finsupp.prod]

/-- The reduction of a monomial. -/
private lemma reduction_monomial_one (ν : σ →₀ ℕ)
    (h : (monomial (1 : σ → ℝ) ν (1 : K) : 𝕋) ∈ unitClosedBall 𝕋) :
    reduction ⟨monomial (1 : σ → ℝ) ν (1 : K), h⟩ = MvPolynomial.monomial ν (1 : 𝕜) := by
  classical
  ext t
  rw [coeff_reduction, MvPolynomial.coeff_monomial]
  by_cases hνt : ν = t
  · subst hνt
    rw [if_pos rfl]
    have h1 : unitBallCoeff ⟨monomial (1 : σ → ℝ) ν (1 : K), h⟩ ν = 1 :=
      Subtype.ext (by simp [MvPowerSeries.coeff_monomial_same])
    rw [h1, map_one]
  · rw [if_neg hνt]
    have h0 : unitBallCoeff ⟨monomial (1 : σ → ℝ) ν (1 : K), h⟩ t = 0 :=
      Subtype.ext (by simp [MvPowerSeries.coeff_monomial_ne (Ne.symm hνt)])
    rw [h0, map_zero]

/-- The members of the adapted family lie in the unit ball componentwise. -/
private lemma norm_adaptedFamily_apply_le {r : ℕ} {g : Fin r → ι → 𝕋} (hg : ∀ j, ‖g j‖ ≤ 1)
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)} (μ : A ⊕ B) (i : ι) :
    ‖adaptedFamily g A B μ i‖ ≤ 1 := by
  rcases μ with ⟨⟨ν, j⟩, _⟩ | ⟨⟨i', ν⟩, _⟩
  · change ‖(monomial (1 : σ → ℝ) ν (1 : K) : 𝕋) * g j i‖ ≤ 1
    refine (_root_.norm_mul_le _ _).trans ?_
    rw [norm_monomial_one, one_mul]
    exact (norm_le_pi_norm (g j) i).trans (hg j)
  · change ‖(Pi.single i' (monomial (1 : σ → ℝ) ν (1 : K)) : ι → 𝕋) i‖ ≤ 1
    by_cases hi : i = i'
    · subst hi
      rw [Pi.single_eq_same, norm_monomial_one]
    · rw [Pi.single_eq_of_ne hi, norm_zero]
      exact zero_le_one

/-- The reduced adapted family is the componentwise reduction of the adapted family. -/
private lemma adaptedFamily_reduction {r : ℕ} {g : Fin r → ι → 𝕋} (hg : ∀ j, ‖g j‖ = 1)
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)} (μ : A ⊕ B) (i : ι) :
    MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B μ i =
      reduction ⟨adaptedFamily g A B μ i, mem_unitClosedBall.2
        (norm_adaptedFamily_apply_le (fun j ↦ (hg j).le) μ i)⟩ := by
  have hm (ν : σ →₀ ℕ) : (monomial (1 : σ → ℝ) ν (1 : K) : 𝕋) ∈ unitClosedBall 𝕋 :=
    mem_unitClosedBall.2 (norm_monomial_one ν).le
  rcases μ with ⟨⟨ν, j⟩, hνj⟩ | ⟨⟨i', ν⟩, hiν⟩
  · have hgji : g j i ∈ unitClosedBall 𝕋 :=
      mem_unitClosedBall.2 ((norm_le_pi_norm (g j) i).trans (hg j).le)
    have hsplit : (⟨adaptedFamily g A B (Sum.inl ⟨(ν, j), hνj⟩) i, mem_unitClosedBall.2
        (norm_adaptedFamily_apply_le (fun j ↦ (hg j).le) (Sum.inl ⟨(ν, j), hνj⟩) i)⟩ :
          unitClosedBall 𝕋) = ⟨_, hm ν⟩ * ⟨g j i, hgji⟩ := Subtype.ext rfl
    rw [hsplit, map_mul, reduction_monomial_one]
    rfl
  · by_cases hi : i = i'
    · subst hi
      have hval : (⟨adaptedFamily g A B (Sum.inr ⟨⟨i, ν⟩, hiν⟩) i, mem_unitClosedBall.2
          (norm_adaptedFamily_apply_le (fun j ↦ (hg j).le) (Sum.inr ⟨⟨i, ν⟩, hiν⟩) i)⟩ :
            unitClosedBall 𝕋) = ⟨_, hm ν⟩ :=
        Subtype.ext (by simp [adaptedFamily])
      rw [hval, reduction_monomial_one]
      simp [MvPolynomial.adaptedFamily]
    · have hval : (⟨adaptedFamily g A B (Sum.inr ⟨⟨i', ν⟩, hiν⟩) i, mem_unitClosedBall.2
          (norm_adaptedFamily_apply_le (fun j ↦ (hg j).le) (Sum.inr ⟨⟨i', ν⟩, hiν⟩) i)⟩ :
            unitClosedBall 𝕋) = 0 :=
        Subtype.ext (by simp [adaptedFamily, Pi.single_eq_of_ne hi])
      rw [hval, map_zero]
      simp [MvPolynomial.adaptedFamily, Pi.single_eq_of_ne hi]

/-- If the reductions of an adapted family are a basis of `k[X]ˢ` over the residue field, the
adapted family is an orthonormal basis of `Tˢ`. Source: Bosch 1.3/10 ("Thus, by Theorem 6,
`(y_μ)` is an orthonormal basis of `Tₙˢ`"). -/
theorem isOrthonormalBasis_adaptedFamily {r : ℕ} {g : Fin r → ι → 𝕋} (hg : ∀ j, ‖g j‖ = 1)
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)}
    (hli : LinearIndependent 𝕜
      (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B))
    (hspan : Submodule.span 𝕜
      (Set.range (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B)) = ⊤) :
    IsOrthonormalBasis K (adaptedFamily g A B) := by
  classical
  obtain ⟨S, hS, hgS⟩ := exists_isBald_forall_coeff_mem g fun j ↦ (hg j).le
  have hcS : ∀ (μ : A ⊕ B) (p : Σ _ : ι, σ →₀ ℕ), coeff p.2 (adaptedFamily g A B μ p.1).1 ∈ S := by
    rintro (⟨⟨ν, j⟩, _⟩ | ⟨⟨i', ν⟩, _⟩) ⟨i, t⟩
    · change coeff t (MvPowerSeries.monomial ν 1 * (g j i).1) ∈ S
      rw [MvPowerSeries.coeff_monomial_mul]
      split_ifs
      · rw [one_mul]
        exact hgS j i _
      · exact S.zero_mem
    · change coeff t ((Pi.single i' (monomial (1 : σ → ℝ) ν (1 : K)) : ι → 𝕋) i).1 ∈ S
      by_cases hi : i = i'
      · subst hi
        rw [Pi.single_eq_same, val_monomial, MvPowerSeries.coeff_monomial]
        split_ifs
        exacts [S.one_mem, S.zero_mem]
      · rw [Pi.single_eq_of_ne hi]
        simp [S.zero_mem]
  have hr : ∀ (μ : A ⊕ B) (p : Σ _ : ι, σ →₀ ℕ),
      (Pi.basis fun _ : ι ↦ MvPolynomial.basisMonomials σ 𝕜).repr
        (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B μ) p =
          residue (unitClosedBall K) ⟨coeff p.2 (adaptedFamily g A B μ p.1).1,
            mem_unitClosedBall.2 (hS.norm_le_one _ (hcS μ p))⟩ := by
    rintro μ ⟨i, t⟩
    rw [Pi.basis_repr]
    change MvPolynomial.coeff t
      (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B μ i) = _
    rw [adaptedFamily_reduction hg μ i, coeff_reduction]
    rfl
  have hli' : LinearIndependent 𝕜 fun μ ↦ (Pi.basis fun _ : ι ↦
      MvPolynomial.basisMonomials σ 𝕜).repr
        (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B μ) :=
    hli.map' _ (Pi.basis fun _ : ι ↦ MvPolynomial.basisMonomials σ 𝕜).repr.ker
  have hspan' : Submodule.span 𝕜 (Set.range fun μ ↦ (Pi.basis fun _ : ι ↦
      MvPolynomial.basisMonomials σ 𝕜).repr
        (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B μ)) = ⊤ := by
    change Submodule.span 𝕜 (Set.range
      (⇑(Pi.basis fun _ : ι ↦ MvPolynomial.basisMonomials σ 𝕜).repr ∘
        MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B)) = ⊤
    rw [Set.range_comp, ← LinearEquiv.coe_coe, Submodule.span_image, hspan, Submodule.map_top,
      LinearEquiv.range]
  exact IsOrthonormalBasis.of_residue_basis isOrthonormalBasis_single_monomial
    (fun μ ↦ hasSum_coeff_smul_single_monomial _) hS hcS _ hr hli' hspan'

omit [Fintype ι] [DecidableEq ι] in
/-- A convergent combination of multiples `X^ν • g j` with coefficients bounded by `C` is a
combination `Σ qⱼ • gⱼ` with `‖qⱼ‖ ≤ C`. Source: Bosch 1.3/7 ("we can write `f' = Σ fᵢaᵢ` with
certain elements `fᵢ ∈ Tₙ` satisfying `|fᵢ| ≤ |f|`"). -/
theorem exists_eq_sum_smul_of_hasSum [CompleteSpace K] {r : ℕ} (g : Fin r → ι → 𝕋)
    {A : Set ((σ →₀ ℕ) × Fin r)} {c : A → K} {a : ι → 𝕋}
    (ha : HasSum (fun μ : A ↦ c μ • (monomial (1 : σ → ℝ) μ.1.1 (1 : K) • g μ.1.2)) a)
    (hc0 : Tendsto c cofinite (𝓝 0)) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ μ, ‖c μ‖ ≤ C) :
    ∃ q : Fin r → 𝕋, (∀ j, ‖q j‖ ≤ C) ∧ a = ∑ j, q j • g j := by
  classical
  let u : Fin r → A → 𝕋 := fun j μ ↦
    if μ.1.2 = j then c μ • (monomial (1 : σ → ℝ) μ.1.1 (1 : K) : 𝕋) else 0
  have hu_le (j : Fin r) (μ : A) : ‖u j μ‖ ≤ ‖c μ‖ := by
    simp only [u]
    split_ifs
    · rw [norm_smul, norm_monomial_one, mul_one]
    · rw [norm_zero]
      exact norm_nonneg _
  have hu0 (j : Fin r) : Tendsto (u j) cofinite (𝓝 0) :=
    squeeze_zero_norm (hu_le j) (tendsto_zero_iff_norm_tendsto_zero.1 hc0)
  have hus (j : Fin r) : HasSum (u j) (∑' μ, u j μ) :=
    (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (hu0 j)).hasSum
  refine ⟨fun j ↦ ∑' μ, u j μ, fun j ↦
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 fun μ ↦ (hu_le j μ).trans (hC μ),
    ha.unique ?_⟩
  have h2 := hasSum_sum fun j (_ : j ∈ Finset.univ) ↦ (hus j).smul_const (g j)
  convert h2 using 1
  funext μ
  rw [Finset.sum_eq_single μ.1.2 (fun j _ hj ↦ by simp [u, Ne.symm hj])
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp [u, smul_assoc]

/-- Splitting an expansion in the adapted family: the part in the multiples `X^ν • g j` is a
combination `Σ qⱼ • gⱼ` with `‖qⱼ‖ ≤ ‖f‖`, and the remainder is the expansion with only the
monomial-vector part. Source: Bosch 1.3/7 ("we may replace `f` by `f − f'`"). -/
private lemma exists_sum_smul_hasSum_inr [CompleteSpace K] {r : ℕ} {g : Fin r → ι → 𝕋}
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)}
    (hON : IsOrthonormalBasis K (adaptedFamily g A B)) {c : A ⊕ B → K} {f : ι → 𝕋}
    (hc : HasSum (fun μ ↦ c μ • adaptedFamily g A B μ) f) :
    ∃ q : Fin r → 𝕋, (∀ j, ‖q j‖ ≤ ‖f‖) ∧
      HasSum (fun μ ↦ Sum.elim (0 : A → K) (fun b ↦ c (Sum.inr b)) μ • adaptedFamily g A B μ)
        (f - ∑ j, q j • g j) := by
  classical
  let cA : A ⊕ B → K := Sum.elim (fun a ↦ c (Sum.inl a)) 0
  have hc0 := hON.1.tendsto_cofinite_of_hasSum hc
  have hcA0 : Tendsto cA cofinite (𝓝 0) := squeeze_zero_norm
    (fun μ ↦ by rcases μ with a | b <;> simp [cA]) (tendsto_zero_iff_norm_tendsto_zero.1 hc0)
  have hxA := (hON.1.summable_smul hcA0).hasSum
  have hxA' : HasSum (fun a : A ↦ c (Sum.inl a) • (monomial (1 : σ → ℝ) a.1.1 (1 : K) •
      g a.1.2)) (∑' μ, cA μ • adaptedFamily g A B μ) := by
    refine (Sum.inl_injective.hasSum_iff (f := fun μ ↦ cA μ • adaptedFamily g A B μ) ?_).2 hxA
    rintro (a | b) hμ
    · exact absurd ⟨a, rfl⟩ hμ
    · simp [cA]
  obtain ⟨q, hqle, hq⟩ := exists_eq_sum_smul_of_hasSum g hxA'
    (hc0.comp Sum.inl_injective.tendsto_cofinite) (norm_nonneg f)
    fun a ↦ hON.1.norm_coeff_le_of_hasSum hc (Sum.inl a)
  refine ⟨q, hqle, ?_⟩
  rw [← hq]
  have hfun : (fun μ ↦ Sum.elim (0 : A → K) (fun b ↦ c (Sum.inr b)) μ • adaptedFamily g A B μ) =
      fun μ ↦ c μ • adaptedFamily g A B μ - cA μ • adaptedFamily g A B μ := by
    funext μ
    rcases μ with a | b <;> simp [cA]
  rw [hfun]
  exact hc.sub hxA

/-- The reduction of a finite combination of the adapted family with coefficients in the unit
ball. -/
private lemma reductionPi_sum {r : ℕ} {g : Fin r → ι → 𝕋} (hg : ∀ j, ‖g j‖ = 1)
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)} (F : Finset (A ⊕ B))
    (d : A ⊕ B → K) (hd : ∀ μ, ‖d μ‖ ≤ 1)
    (hw : ‖∑ μ ∈ F, d μ • adaptedFamily g A B μ‖ ≤ 1) :
    reductionPi (∑ μ ∈ F, d μ • adaptedFamily g A B μ) hw =
      ∑ μ ∈ F, residue (unitClosedBall K) ⟨d μ, mem_unitClosedBall.2 (hd μ)⟩ •
        MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B μ := by
  have hC (μ : A ⊕ B) : Restricted.C (1 : σ → ℝ)
      ((⟨d μ, mem_unitClosedBall.2 (hd μ)⟩ : unitClosedBall K) : K) ∈ unitClosedBall 𝕋 :=
    mem_unitClosedBall.2 (by rw [Restricted.norm_C]; exact hd μ)
  have he (μ : A ⊕ B) (i : ι) : adaptedFamily g A B μ i ∈ unitClosedBall 𝕋 :=
    mem_unitClosedBall.2 (norm_adaptedFamily_apply_le (fun j ↦ (hg j).le) μ i)
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  have heq : (⟨(∑ μ ∈ F, d μ • adaptedFamily g A B μ) i,
      mem_unitClosedBall.2 ((norm_le_pi_norm _ i).trans hw)⟩ : unitClosedBall 𝕋) =
        ∑ μ ∈ F, ⟨_, hC μ⟩ * ⟨_, he μ i⟩ := by
    refine Subtype.ext ?_
    change (∑ μ ∈ F, d μ • adaptedFamily g A B μ) i = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [Subring.coe_mul, Pi.smul_apply, Algebra.smul_def, algebraMap_apply]
  change reduction _ = _
  rw [heq, map_sum]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [map_mul, reduction_C, ← adaptedFamily_reduction hg μ i, MvPolynomial.C_mul']

/-- The reduction of a convergent expansion in the adapted family with coefficients in the unit
ball only sees the coefficients of norm one. -/
private lemma reductionPi_eq_of_hasSum {r : ℕ} {g : Fin r → ι → 𝕋} (hg : ∀ j, ‖g j‖ = 1)
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)}
    (hON : IsOrthonormalBasis K (adaptedFamily g A B)) {d : A ⊕ B → K} {z : ι → 𝕋}
    (hz : HasSum (fun μ ↦ d μ • adaptedFamily g A B μ) z) (hd : ∀ μ, ‖d μ‖ ≤ 1)
    (F : Finset (A ⊕ B)) (hF : ∀ μ ∉ F, ‖d μ‖ < 1) (hzle : ‖z‖ ≤ 1) :
    reductionPi z hzle =
      ∑ μ ∈ F, residue (unitClosedBall K) ⟨d μ, mem_unitClosedBall.2 (hd μ)⟩ •
        MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B μ := by
  classical
  have hw : HasSum (fun μ ↦ (if μ ∈ F then d μ else 0) • adaptedFamily g A B μ)
      (∑ μ ∈ F, d μ • adaptedFamily g A B μ) := by
    have hsum : ∑ μ ∈ F, d μ • adaptedFamily g A B μ =
        ∑ μ ∈ F, (if μ ∈ F then d μ else 0) • adaptedFamily g A B μ :=
      Finset.sum_congr rfl fun μ hμ ↦ by simp [hμ]
    rw [hsum]
    exact hasSum_sum_of_ne_finset_zero fun μ hμ ↦ by simp [hμ]
  have hfun : (fun μ ↦ (if μ ∈ F then 0 else d μ) • adaptedFamily g A B μ) =
      fun μ ↦ d μ • adaptedFamily g A B μ -
        (if μ ∈ F then d μ else 0) • adaptedFamily g A B μ := by
    funext μ
    split_ifs <;> simp
  have hdiff : HasSum (fun μ ↦ (if μ ∈ F then 0 else d μ) • adaptedFamily g A B μ)
      (z - ∑ μ ∈ F, d μ • adaptedFamily g A B μ) := by
    rw [hfun]
    exact hz.sub hw
  have hlt : ‖z - ∑ μ ∈ F, d μ • adaptedFamily g A B μ‖ < 1 := by
    rcases isEmpty_or_nonempty (A ⊕ B) with hE | hE
    · rw [hdiff.unique hasSum_empty, norm_zero]
      exact one_pos
    · obtain ⟨μ₀, hμ₀⟩ := (hON.1.tendsto_cofinite_of_hasSum hdiff).exists_forall_norm_le
      have hμ₀lt : ‖(if μ₀ ∈ F then 0 else d μ₀)‖ < 1 := by
        split_ifs with h
        · rw [norm_zero]
          exact one_pos
        · exact hF μ₀ h
      exact (hON.1.norm_le_of_hasSum hdiff (norm_nonneg _) hμ₀).trans_lt hμ₀lt
  have hwle : ‖∑ μ ∈ F, d μ • adaptedFamily g A B μ‖ ≤ 1 :=
    hON.1.norm_le_of_hasSum hw zero_le_one fun μ ↦ by
      split_ifs
      · exact hd μ
      · rw [norm_zero]
        exact zero_le_one
  have hadd : reductionPi z hzle = reductionPi (∑ μ ∈ F, d μ • adaptedFamily g A B μ) hwle +
      reductionPi (z - ∑ μ ∈ F, d μ • adaptedFamily g A B μ) hlt.le := by
    funext i
    simp only [reductionPi, Pi.add_apply]
    rw [← map_add]
    congr 1
    exact Subtype.ext (by simp)
  rw [hadd, (reductionPi_eq_zero_iff _).2 hlt, add_zero, reductionPi_sum hg F d hd hwle]

/-- For an adapted orthonormal basis whose part in `N` reduces to a basis of the reduction of `N`,
the expansion of an element of `N` involves only the part in `N`. Source: Bosch 1.3/7 ("we may
replace `f` by `f − f'` … and thereby assume `c_μ = 0` for `μ ∈ M'`. Then, if `f ≠ 0` … we would
get a non-trivial equation … which, however, contradicts the construction"). -/
theorem coeff_inr_eq_zero_of_mem [CompleteSpace K] {N : Submodule 𝕋 (ι → 𝕋)} {r : ℕ}
    {g : Fin r → ι → 𝕋} (hg : ∀ j, ‖g j‖ = 1) (hgN : ∀ j, g j ∈ N)
    {A : Set ((σ →₀ ℕ) × Fin r)} {B : Set (Σ _ : ι, σ →₀ ℕ)}
    (hON : IsOrthonormalBasis K (adaptedFamily g A B))
    (hli : LinearIndependent 𝕜
      (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B))
    (hA : Submodule.span 𝕜 (Set.range fun a : A ↦
        MvPolynomial.monomial a.1.1 (1 : 𝕜) • reductionPi (g a.1.2) (hg a.1.2).le) =
      (reductionSubmodule N).restrictScalars 𝕜)
    {x : ι → 𝕋} (hx : x ∈ N) {c : A ⊕ B → K}
    (hc : HasSum (fun μ ↦ c μ • adaptedFamily g A B μ) x) (b : B) : c (Sum.inr b) = 0 := by
  classical
  by_contra hb
  obtain ⟨q, -, hxB⟩ := exists_sum_smul_hasSum_inr hON hc
  have hx'N : ∑ j, q j • g j ∈ N := Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hgN j)
  set cB : A ⊕ B → K := Sum.elim (0 : A → K) (fun b ↦ c (Sum.inr b)) with hcB
  haveI : Nonempty (A ⊕ B) := ⟨Sum.inr b⟩
  obtain ⟨μ₀, hμ₀⟩ := (hON.1.tendsto_cofinite_of_hasSum hxB).exists_forall_norm_le
  have hD : cB μ₀ ≠ 0 := by
    intro h0
    have h := hμ₀ (Sum.inr b)
    rw [h0, norm_zero] at h
    exact hb (norm_le_zero_iff.1 h)
  let d : A ⊕ B → K := fun μ ↦ (cB μ₀)⁻¹ * cB μ
  have hd (μ : A ⊕ B) : ‖d μ‖ ≤ 1 := by
    simp only [d, norm_mul, norm_inv]
    rw [inv_mul_le_iff₀ (norm_pos_iff.2 hD), mul_one]
    exact hμ₀ μ
  have hd₀ : d μ₀ = 1 := inv_mul_cancel₀ hD
  have hz : HasSum (fun μ ↦ d μ • adaptedFamily g A B μ)
      ((cB μ₀)⁻¹ • (x - ∑ j, q j • g j)) := by
    simpa only [d, smul_smul] using hxB.const_smul (cB μ₀)⁻¹
  have hzN : (cB μ₀)⁻¹ • (x - ∑ j, q j • g j) ∈ N :=
    N.smul_of_tower_mem _ (N.sub_mem hx hx'N)
  have hzle := hON.1.norm_le_of_hasSum hz zero_le_one hd
  have hfin : {μ | ¬ dist (d μ) 0 < 1}.Finite :=
    eventually_cofinite.1 (Metric.tendsto_nhds.1 (hON.1.tendsto_cofinite_of_hasSum hz) 1 one_pos)
  have hF (μ : A ⊕ B) (hμ : μ ∉ hfin.toFinset) : ‖d μ‖ < 1 := by
    rw [Set.Finite.mem_toFinset] at hμ
    simpa using hμ
  have hμ₀F : μ₀ ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    simp [hd₀]
  have hred := reductionPi_eq_of_hasSum hg hON hz hd hfin.toFinset hF hzle
  have hwN : reductionPi _ hzle ∈ reductionSubmodule N := ⟨_, hzle, hzN, rfl⟩
  have hwA : reductionPi _ hzle ∈ Submodule.span 𝕜
      (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B ''
        Set.range Sum.inl) := by
    rw [← Set.range_comp]
    have h1 : reductionPi _ hzle ∈ (reductionSubmodule N).restrictScalars 𝕜 := hwN
    rw [← hA] at h1
    exact h1
  have hwB : reductionPi _ hzle ∈ Submodule.span 𝕜
      (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le) A B ''
        Set.range Sum.inr) := by
    rw [hred]
    refine Submodule.sum_mem _ fun μ hμ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨μ, ?_, rfl⟩)
    rcases μ with a | b'
    · exfalso
      have h := (Set.Finite.mem_toFinset hfin).1 hμ
      simp [d, cB] at h
      linarith
    · exact ⟨b', rfl⟩
  have hw0 := Submodule.disjoint_def.1
    (hli.disjoint_span_image Set.isCompl_range_inl_range_inr.disjoint) _ hwA hwB
  rw [hred] at hw0
  have h0 := linearIndependent_iff'.1 hli _ _ hw0 μ₀ hμ₀F
  have h1 : (⟨d μ₀, mem_unitClosedBall.2 (hd μ₀)⟩ : unitClosedBall K) = 1 := Subtype.ext hd₀
  rw [h1, map_one] at h0
  exact one_ne_zero h0

/-- **An orthonormal basis adapted to a submodule**: for every submodule `N` of `Tˢ` there are
generators `g j ∈ N` of norm one and an orthonormal basis of `Tˢ` consisting of multiples
`X^ν • g j` and monomial vectors, in which the elements of `N` are the series in the multiples
`X^ν • g j`. Source: Bosch 1.3/10 and the remark after 1.3/7 ("the system `(y_μ)_{μ ∈ M'}` is seen
to be an orthonormal basis of `𝔞`"). -/
theorem exists_isOrthonormalBasis_adaptedFamily [Finite σ] [CompleteSpace K]
    (N : Submodule 𝕋 (ι → 𝕋)) :
    ∃ (r : ℕ) (g : Fin r → ι → 𝕋) (A : Set ((σ →₀ ℕ) × Fin r)) (B : Set (Σ _ : ι, σ →₀ ℕ)),
      (∀ j, g j ∈ N) ∧ (∀ j, ‖g j‖ = 1) ∧ IsOrthonormalBasis K (adaptedFamily g A B) ∧
        ∀ x ∈ N, ∀ c : A ⊕ B → K, HasSum (fun μ ↦ c μ • adaptedFamily g A B μ) x →
          ∀ b : B, c (Sum.inr b) = 0 := by
  obtain ⟨r, g, hg, hgN, hspan⟩ := exists_generators_reductionSubmodule N
  obtain ⟨A, B, hli, hsp, hA⟩ :=
    MvPolynomial.exists_basis_adaptedFamily (fun j ↦ reductionPi (g j) (hg j).le)
  have hON := isOrthonormalBasis_adaptedFamily hg hli hsp
  refine ⟨r, g, A, B, hgN, hg, hON, fun x hx c hc b ↦ ?_⟩
  exact coeff_inr_eq_zero_of_mem hg hgN hON hli (hA.trans (by rw [hspan])) hx hc b

end Adapted

/-! ### Submodules of free modules -/

section Submodule

variable [Fintype ι] [Finite σ] [CompleteSpace K]

/-- **Generators with a best approximation**: every submodule `N` of `Tˢ` has generators
`g₁, …, g_r` of norm one such that every `f ∈ Tˢ` has a combination `Σ qⱼ gⱼ` with `‖qⱼ‖ ≤ ‖f‖`
which is a nearest point of `N` to `f`. Source: Bosch 1.3/7, 1.3/9, 1.3/10. -/
theorem exists_generators_forall_exists_isNearest (N : Submodule 𝕋 (ι → 𝕋)) :
    ∃ (r : ℕ) (g : Fin r → ι → 𝕋), (∀ j, g j ∈ N) ∧ (∀ j, ‖g j‖ = 1) ∧
      ∀ f : ι → 𝕋, ∃ q : Fin r → 𝕋, (∀ j, ‖q j‖ ≤ ‖f‖) ∧
        ∀ a ∈ N, ‖f - ∑ j, q j • g j‖ ≤ ‖f - ∑ j, q j • g j - a‖ := by
  classical
  obtain ⟨r, g, A, B, hgN, hg, hON, hN⟩ := exists_isOrthonormalBasis_adaptedFamily N
  refine ⟨r, g, hgN, hg, fun f ↦ ?_⟩
  obtain ⟨c, hc⟩ := hON.exists_hasSum f
  obtain ⟨q, hqle, hxB⟩ := exists_sum_smul_hasSum_inr hON hc
  refine ⟨q, hqle, fun a ha ↦ ?_⟩
  obtain ⟨d, hd⟩ := hON.exists_hasSum a
  have hdB := hN a ha d hd
  have hdiff : HasSum (fun μ ↦ (Sum.elim (0 : A → K) (fun b ↦ c (Sum.inr b)) μ - d μ) •
      adaptedFamily g A B μ) (f - ∑ j, q j • g j - a) := by
    simpa only [sub_smul] using hxB.sub hd
  refine hON.1.norm_le_of_hasSum hxB (norm_nonneg _) fun μ ↦ ?_
  rcases μ with a' | b
  · simp
  · have h := hON.1.norm_coeff_le_of_hasSum hdiff (Sum.inr b)
    simpa [hdB b] using h

/-- Every submodule of `Tˢ` has generators `g₁, …, g_r` of norm one such that every element `x` of
it is `Σ qⱼ gⱼ` with `‖qⱼ‖ ≤ ‖x‖`. Source: Bosch 1.3/10; BGR 5.2.7/1 with the bound `ρ = 1`. -/
theorem exists_generators_norm_le (N : Submodule 𝕋 (ι → 𝕋)) :
    ∃ (r : ℕ) (g : Fin r → ι → 𝕋), (∀ j, g j ∈ N) ∧ (∀ j, ‖g j‖ = 1) ∧
      ∀ x ∈ N, ∃ q : Fin r → 𝕋, x = ∑ j, q j • g j ∧ ∀ j, ‖q j‖ ≤ ‖x‖ := by
  obtain ⟨r, g, hgN, hg, h⟩ := exists_generators_forall_exists_isNearest N
  refine ⟨r, g, hgN, hg, fun x hx ↦ ?_⟩
  obtain ⟨q, hq, hmin⟩ := h x
  refine ⟨q, ?_, hq⟩
  have hmem : x - ∑ j, q j • g j ∈ N :=
    N.sub_mem hx (N.sum_mem fun j _ ↦ N.smul_mem _ (hgN j))
  have h0 := hmin _ hmem
  rw [sub_self, norm_zero] at h0
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- **Submodules of `Tˢ` are strictly closed**: every `f` has a nearest point in the submodule.
Source: BGR 5.2.7/7; Bosch 1.3/9. -/
theorem exists_forall_norm_sub_le (N : Submodule 𝕋 (ι → 𝕋)) (f : ι → 𝕋) :
    ∃ a₀ ∈ N, ∀ a ∈ N, ‖f - a₀‖ ≤ ‖f - a‖ := by
  obtain ⟨r, g, hgN, -, h⟩ := exists_generators_forall_exists_isNearest N
  obtain ⟨q, -, hmin⟩ := h f
  have hS : ∑ j, q j • g j ∈ N := N.sum_mem fun j _ ↦ N.smul_mem _ (hgN j)
  refine ⟨_, hS, fun a ha ↦ ?_⟩
  have h1 := hmin (a - ∑ j, q j • g j) (N.sub_mem ha hS)
  rwa [sub_sub_sub_cancel_right] at h1

/-- Submodules of `Tˢ` are closed. Source: BGR 5.2.7/1; Bosch 1.3/8. -/
theorem isClosed_submodule (N : Submodule 𝕋 (ι → 𝕋)) : IsClosed (N : Set (ι → 𝕋)) := by
  refine isClosed_of_closure_subset fun f hf ↦ ?_
  obtain ⟨a₀, ha₀, hmin⟩ := exists_forall_norm_sub_le N f
  have h0 : ‖f - a₀‖ = 0 := by
    by_contra hne
    obtain ⟨b, hb, hfb⟩ := Metric.mem_closure_iff.1 hf _
      (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne))
    rw [dist_eq_norm] at hfb
    exact lt_irrefl _ ((hmin b hb).trans_lt hfb)
  rw [norm_eq_zero, sub_eq_zero] at h0
  rw [h0]
  exact ha₀

/-- The distance of a point of `Tˢ` to a submodule is the norm of an element of `K`: the residue
norm on a finite `T`-module presented as `Tˢ ⧸ N` takes its values in `‖K‖`.
Source: BGR 5.2.7/8. -/
theorem infDist_mem_range_norm (N : Submodule 𝕋 (ι → 𝕋)) (f : ι → 𝕋) :
    Metric.infDist f (N : Set (ι → 𝕋)) ∈ Set.range (norm : K → ℝ) := by
  obtain ⟨a₀, ha₀, hmin⟩ := exists_forall_norm_sub_le N f
  have hinf : Metric.infDist f (N : Set (ι → 𝕋)) = ‖f - a₀‖ := by
    refine le_antisymm ?_ ((Metric.le_infDist ⟨0, N.zero_mem⟩).2 fun a ha ↦ ?_)
    · rw [← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem ha₀
    · rw [dist_eq_norm]
      exact hmin a ha
  rw [hinf]
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, by rw [norm_zero, Subsingleton.elim (f - a₀) 0, norm_zero]⟩
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      fun i ↦ ‖(f - a₀) i‖₊
    rw [Pi.norm_def, hi, coe_nnnorm]
    exact norm_mem_range_norm _

end Submodule

/-! ### Ideals -/

section Ideal

variable [Finite σ] [CompleteSpace K]

omit [Finite σ] [CompleteSpace K] in
/-- The sup norm on `Unit → T` is the norm of the single component. -/
private lemma norm_unit_pi (x : Unit → 𝕋) : ‖x‖ = ‖x ()‖ := by
  rw [Pi.norm_def, Finset.univ_unique, Finset.sup_singleton, coe_nnnorm]

/-- Every ideal of the Tate algebra has generators `a₁, …, a_r` of norm one such that every element
`f` of it is `Σ fᵢ aᵢ` with `‖fᵢ‖ ≤ ‖f‖`. Source: Bosch 1.3/7. -/
theorem exists_generators_norm_le_ideal (I : Ideal 𝕋) :
    ∃ (r : ℕ) (g : Fin r → 𝕋), (∀ j, g j ∈ I) ∧ (∀ j, ‖g j‖ = 1) ∧
      ∀ x ∈ I, ∃ q : Fin r → 𝕋, x = ∑ j, q j * g j ∧ ∀ j, ‖q j‖ ≤ ‖x‖ := by
  obtain ⟨r, g, hgN, hg, h⟩ :=
    exists_generators_norm_le (Submodule.comap (LinearMap.proj () : (Unit → 𝕋) →ₗ[𝕋] 𝕋) I)
  refine ⟨r, fun j ↦ g j (), hgN, fun j ↦ (norm_unit_pi (g j)).symm.trans (hg j),
    fun x hx ↦ ?_⟩
  obtain ⟨q, hq, hqle⟩ := h (fun _ ↦ x) hx
  refine ⟨q, ?_, fun j ↦ (hqle j).trans_eq (norm_unit_pi _)⟩
  have h1 := congrFun hq ()
  rw [Finset.sum_apply] at h1
  exact h1

/-- **Ideals of the Tate algebra are strictly closed**: every series has a nearest point in the
ideal. Source: BGR 5.2.7/8; Bosch 1.3/9. -/
theorem exists_forall_norm_sub_le_ideal (I : Ideal 𝕋) (f : 𝕋) :
    ∃ a₀ ∈ I, ∀ a ∈ I, ‖f - a₀‖ ≤ ‖f - a‖ := by
  obtain ⟨a₀, ha₀, hmin⟩ := exists_forall_norm_sub_le
    (Submodule.comap (LinearMap.proj () : (Unit → 𝕋) →ₗ[𝕋] 𝕋) I) (fun _ ↦ f)
  refine ⟨a₀ (), ha₀, fun a ha ↦ ?_⟩
  calc ‖f - a₀ ()‖ = ‖(fun _ ↦ f) - a₀‖ := (norm_unit_pi ((fun _ ↦ f) - a₀)).symm
    _ ≤ ‖(fun _ ↦ f) - fun _ ↦ a‖ := hmin (fun _ ↦ a) ha
    _ = ‖f - a‖ := norm_unit_pi ((fun _ ↦ f) - fun _ ↦ a)

/-- **Ideals of the Tate algebra are closed.** Source: BGR 5.2.7/2; Bosch 1.3/8. -/
theorem isClosed_ideal (I : Ideal 𝕋) : IsClosed (I : Set 𝕋) := by
  refine isClosed_of_closure_subset fun f hf ↦ ?_
  obtain ⟨a₀, ha₀, hmin⟩ := exists_forall_norm_sub_le_ideal I f
  have h0 : ‖f - a₀‖ = 0 := by
    by_contra hne
    obtain ⟨b, hb, hfb⟩ := Metric.mem_closure_iff.1 hf _
      (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne))
    rw [dist_eq_norm] at hfb
    exact lt_irrefl _ ((hmin b hb).trans_lt hfb)
  rw [norm_eq_zero, sub_eq_zero] at h0
  rw [h0]
  exact ha₀

/-- The residue norm on a quotient of the Tate algebra takes its values in `‖K‖`:
`|Tₙ ⧸ 𝔞| = |K|`. Source: BGR 5.2.7/8. -/
theorem norm_quotient_mk_mem_range_norm (I : Ideal 𝕋) (f : 𝕋) :
    ‖Ideal.Quotient.mk I f‖ ∈ Set.range (norm : K → ℝ) := by
  obtain ⟨a₀, ha₀, hmin⟩ := exists_forall_norm_sub_le_ideal I f
  have hq : ‖Ideal.Quotient.mk I f‖ = Metric.infDist f (I : Set 𝕋) :=
    QuotientAddGroup.norm_mk (S := I.toAddSubgroup) f
  have hinf : Metric.infDist f (I : Set 𝕋) = ‖f - a₀‖ := by
    refine le_antisymm ?_ ((Metric.le_infDist ⟨0, I.zero_mem⟩).2 fun a ha ↦ ?_)
    · rw [← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem ha₀
    · rw [dist_eq_norm]
      exact hmin a ha
  rw [hq, hinf]
  exact norm_mem_range_norm _

end Ideal

end MvPowerSeries.Restricted
