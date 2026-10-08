/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal
import PhD.TauCeti.Code.PadicFunctionalAnalysis.UnitBall
import PhD.TauCeti.Code.RigidAnalyticGeometry.Bald
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.HausdorffDistance

/-!
# Lifting orthonormal bases from the reduction

Let `V` be a nonarchimedean normed space over a nonarchimedean field `K` with an orthonormal
basis `x`, and let `y` be a family of the unit ball of `V` whose coordinates with
respect to `x` lie in a bald subring of `K`. If the reductions of the `y μ` form a basis of the
reduction of `V` over the residue field, then `y` is an orthonormal basis of `V`.

Without the baldness hypothesis the statement is false over a densely valued field: in `c₀(ℕ, ℂ_p)`
the family `y n = x n - π n • x (n + 1)` with `|π n| < 1` and `∏ |π n| > 0` reduces to the standard
basis, but its closed span does not contain `x 0`.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.3.1 (Bosch 1.3/6). Tau Ceti
home: `TauCeti/Analysis/Normed/Module/Ultra/OrthonormalLift.lean`.

## Main definitions

* `Subring.IsBRing.residueSubfield` — the image of a B-ring in the residue field, a subfield.

## Main results

* `Finsupp.mem_span_range_of_mapRange_mem_span` — a linear system with coefficients in a subfield
  that is solvable over the field is solvable over the subfield.
* `IsOrthonormalFamily.of_linearIndependent_residue` — independent reductions are orthonormal.
* `IsOrthonormalBasis.of_residue_basis` — Bosch 1.3/6.
-/

open Filter Topology Subring NormedRing IsLocalRing

/-- A vector with coefficients in a subfield `F` that lies in the span over the field `E` of a
family of vectors with coefficients in `F` lies in its span over `F`. -/
theorem Finsupp.mem_span_range_of_mapRange_mem_span {F E : Type*} [Field F] [Field E]
    [Algebra F E] {N M : Type*} (v : M → N →₀ F) (w : N →₀ F)
    (h : Finsupp.mapRange (algebraMap F E) (map_zero _) w ∈
      Submodule.span E (Set.range fun μ ↦ Finsupp.mapRange (algebraMap F E) (map_zero _) (v μ))) :
    w ∈ Submodule.span F (Set.range v) := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have hπa (a : F) : π (algebraMap F E a) = a := LinearMap.congr_fun hπ a
  have hterm (b : E) (a : F) : π (b * algebraMap F E a) = π b * a := by
    rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h
  refine Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨l.mapRange π (map_zero π), ?_⟩
  ext n
  have hn := congrArg (fun f : N →₀ E ↦ f n) hl
  simp only [Finsupp.sum_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul] at hn
  rw [Finsupp.sum_mapRange_index (fun μ ↦ zero_smul F (v μ)), Finsupp.sum_apply, ← hπa (w n), ← hn]
  simp only [Finsupp.sum, map_sum, Finsupp.smul_apply, smul_eq_mul, hterm]

section Residue

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The image of a B-ring in the residue field of `K` is a subfield. Source: Bosch 1.3/3 ("Then
`S` contains a unique maximal ideal `𝔪`, and `S̃ = S/𝔪` is a field"). -/
def Subring.IsBRing.residueSubfield {S : Subring K} (hS : S.IsBRing) :
    Subfield (ResidueField (unitClosedBall K)) where
  carrier := {z | ∃ (s : K) (hs : s ∈ S),
    z = residue (unitClosedBall K) ⟨s, mem_unitClosedBall.2 (hS.norm_le_one s hs)⟩}
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s * t, S.mul_mem hs ht, by rw [← map_mul]; rfl⟩
  one_mem' := ⟨1, S.one_mem, (map_one (residue (unitClosedBall K))).symm⟩
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s + t, S.add_mem hs ht, by rw [← map_add]; rfl⟩
  zero_mem' := ⟨0, S.zero_mem, (map_zero (residue (unitClosedBall K))).symm⟩
  neg_mem' := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨-s, S.neg_mem hs, by rw [← map_neg]; rfl⟩
  inv_mem' := by
    rintro _ ⟨s, hs, rfl⟩
    rcases (hS.norm_le_one s hs).lt_or_eq with h | h
    · refine ⟨0, S.zero_mem, ?_⟩
      have hmem : (⟨s, mem_unitClosedBall.2 (hS.norm_le_one s hs)⟩ : unitClosedBall K) ∈
          maximalIdeal (unitClosedBall K) := by
        rw [maximalIdeal_unitClosedBall, mem_openUnitBallIdeal]
        exact h
      rw [(residue_eq_zero_iff _).2 hmem, inv_zero]
      exact (map_zero (residue (unitClosedBall K))).symm
    · have hs0 : s ≠ 0 := norm_ne_zero_iff.1 (by rw [h]; exact one_ne_zero)
      have hprod : (⟨s⁻¹, mem_unitClosedBall.2 (hS.norm_le_one _ (hS.inv_mem s hs h))⟩ :
          unitClosedBall K) * ⟨s, mem_unitClosedBall.2 (hS.norm_le_one s hs)⟩ = 1 :=
        Subtype.ext (inv_mul_cancel₀ hs0)
      refine ⟨s⁻¹, hS.inv_mem s hs h, (eq_inv_of_mul_eq_one_left ?_).symm⟩
      rw [← map_mul, hprod, map_one]

theorem Subring.IsBRing.mem_residueSubfield {S : Subring K} (hS : S.IsBRing)
    {z : ResidueField (unitClosedBall K)} :
    z ∈ hS.residueSubfield ↔ ∃ (s : K) (hs : s ∈ S),
      z = residue (unitClosedBall K) ⟨s, mem_unitClosedBall.2 (hS.norm_le_one s hs)⟩ :=
  Iff.rfl

/-- An element of norm at most one as an element of the unit ball, and `0` otherwise. -/
private noncomputable def toUnitBall (t : K) : unitClosedBall K :=
  if h : ‖t‖ ≤ 1 then ⟨t, mem_unitClosedBall.2 h⟩ else 0

private lemma toUnitBall_of_le {t : K} (h : ‖t‖ ≤ 1) :
    toUnitBall t = ⟨t, mem_unitClosedBall.2 h⟩ :=
  dif_pos h

/-- An element of the unit ball with nonzero residue has norm one. -/
private lemma one_le_norm_of_residue_ne_zero {t : K} (ht : ‖t‖ ≤ 1)
    (h : residue (unitClosedBall K) ⟨t, mem_unitClosedBall.2 ht⟩ ≠ 0) : 1 ≤ ‖t‖ := by
  refine not_lt.1 fun hlt ↦ h ((residue_eq_zero_iff _).2 ?_)
  rw [maximalIdeal_unitClosedBall, mem_openUnitBallIdeal]
  exact hlt

end Residue

section Lift

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]
  {N M : Type*} {x : N → V} {y : M → V} {c : M → N → K}

/-- A family of the unit ball whose reductions are linearly independent over the residue field is
orthonormal. Source: Bosch 1.3/6 ("In particular, `(y_μ)` is an orthonormal basis of a subspace
`V' ⊂ V`"). -/
theorem IsOrthonormalFamily.of_linearIndependent_residue (hx : IsOrthonormalFamily K x)
    (hy : ∀ μ, HasSum (fun ν ↦ c μ ν • x ν) (y μ)) (hc : ∀ μ ν, ‖c μ ν‖ ≤ 1)
    (r : M → N →₀ ResidueField (unitClosedBall K))
    (hr : ∀ μ ν, r μ ν = residue (unitClosedBall K) ⟨c μ ν, mem_unitClosedBall.2 (hc μ ν)⟩)
    (hli : LinearIndependent (ResidueField (unitClosedBall K)) r) : IsOrthonormalFamily K y := by
  classical
  have hy1 (μ : M) : ‖y μ‖ = 1 := by
    refine le_antisymm (hx.norm_le_of_hasSum (hy μ) zero_le_one (hc μ)) ?_
    obtain ⟨ν, hν⟩ := DFunLike.ne_iff.1 (hli.ne_zero μ)
    rw [Finsupp.coe_zero, Pi.zero_apply, hr] at hν
    exact (one_le_norm_of_residue_ne_zero (hc μ ν) hν).trans (hx.norm_coeff_le_of_hasSum (hy μ) ν)
  have hkey (s : Finset M) (a : M → K) (μ : M) (hμ : μ ∈ s) :
      ‖a μ‖ ≤ ‖∑ μ ∈ s, a μ • y μ‖ := by
    obtain ⟨μ₀, hμ₀, hmax⟩ := Finset.exists_max_image s (fun μ ↦ ‖a μ‖) ⟨μ, hμ⟩
    refine (hmax μ hμ).trans ?_
    by_cases ha0 : a μ₀ = 0
    · rw [ha0, norm_zero]
      exact norm_nonneg _
    let b : M → K := fun μ ↦ (a μ₀)⁻¹ * a μ
    have hb (μ : M) (hμ : μ ∈ s) : ‖b μ‖ ≤ 1 := by
      simp only [b, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.2 ha0), mul_one]
      exact hmax μ hμ
    have hsum : ∑ μ ∈ s, a μ • y μ = a μ₀ • ∑ μ ∈ s, b μ • y μ := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [smul_smul, mul_inv_cancel_left₀ ha0]
    rw [hsum, norm_smul]
    refine le_mul_of_one_le_right (norm_nonneg _) ?_
    have hz : HasSum (fun ν ↦ (∑ μ ∈ s, b μ * c μ ν) • x ν) (∑ μ ∈ s, b μ • y μ) := by
      have h := hasSum_sum fun μ (_ : μ ∈ s) ↦ (hy μ).const_smul (b μ)
      simpa only [Finset.sum_smul, smul_smul] using h
    have hd1 (ν : N) : ‖∑ μ ∈ s, b μ * c μ ν‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ hμ ↦ by
        rw [norm_mul]
        exact mul_le_one₀ (hb μ hμ) (norm_nonneg _) (hc μ ν)
    let g : M → ResidueField (unitClosedBall K) := fun μ ↦
      residue (unitClosedBall K) (toUnitBall (b μ))
    have hres (ν : N) : residue (unitClosedBall K) ⟨_, mem_unitClosedBall.2 (hd1 ν)⟩ =
        (∑ μ ∈ s, g μ • r μ) ν := by
      have heq : (⟨_, mem_unitClosedBall.2 (hd1 ν)⟩ : unitClosedBall K) =
          ∑ μ ∈ s, toUnitBall (b μ) * ⟨c μ ν, mem_unitClosedBall.2 (hc μ ν)⟩ := by
        refine Subtype.ext ?_
        change ∑ μ ∈ s, b μ * c μ ν = _
        rw [AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun μ hμ ↦ ?_
        rw [Subring.coe_mul, toUnitBall_of_le (hb μ hμ)]
      rw [heq, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [map_mul, Finsupp.smul_apply, smul_eq_mul, hr]
    have hg0 : g μ₀ ≠ 0 := by
      have hb0 : b μ₀ = 1 := inv_mul_cancel₀ ha0
      have h1 : toUnitBall (b μ₀) = 1 := by
        rw [hb0, toUnitBall_of_le (by rw [norm_one])]
        rfl
      simp only [g, h1, map_one]
      exact one_ne_zero
    have hne : ∑ μ ∈ s, g μ • r μ ≠ 0 := fun h0 ↦
      hg0 (linearIndependent_iff'.1 hli s g h0 μ₀ hμ₀)
    obtain ⟨ν, hν⟩ := DFunLike.ne_iff.1 hne
    rw [Finsupp.coe_zero, Pi.zero_apply, ← hres ν] at hν
    exact (one_le_norm_of_residue_ne_zero (hd1 ν) hν).trans (hx.norm_coeff_le_of_hasSum hz ν)
  refine ⟨hy1, fun s a ↦ le_antisymm ((Finset.nnnorm_sum_le_sup_nnnorm s _).trans
    (Finset.sup_mono_fun fun μ _ ↦ ?_)) (Finset.sup_le fun μ hμ ↦ ?_)⟩
  · have h1 : ‖y μ‖₊ = 1 := by rw [← NNReal.coe_inj, coe_nnnorm, hy1, NNReal.coe_one]
    rw [nnnorm_smul, h1, mul_one]
  · rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    exact hkey s a μ hμ

/-- If the reductions of the `y μ` span the reduction of `V` and the coordinates of the `y μ` lie
in a bald subring, then every basis vector `x ν` is approximated by the span of `y` up to a uniform
`ε < 1`. Source: Bosch 1.3/6 ("for any `x_ν`, there is an element `z_ν ∈ V'_S` satisfying
`|x_ν − z_ν| ≤ ε`"). -/
theorem exists_norm_sub_le_of_span_residue (hx : IsOrthonormalFamily K x)
    (hy : ∀ μ, HasSum (fun ν ↦ c μ ν • x ν) (y μ)) {S : Subring K} (hS : S.IsBald)
    (hcS : ∀ μ ν, c μ ν ∈ S) (r : M → N →₀ ResidueField (unitClosedBall K))
    (hr : ∀ μ ν, r μ ν = residue (unitClosedBall K)
      ⟨c μ ν, mem_unitClosedBall.2 (hS.norm_le_one _ (hcS μ ν))⟩)
    (hspan : Submodule.span (ResidueField (unitClosedBall K)) (Set.range r) = ⊤) :
    ∃ ε : ℝ, ε < 1 ∧ ∀ ν, ∃ z ∈ Submodule.span K (Set.range y), ‖x ν - z‖ ≤ ε := by
  classical
  have hB := isBRing_unitLocalization hS.norm_le_one
  obtain ⟨ε, hε, hbald⟩ := hS.unitLocalization.exists_norm_le
  have hcS' (μ : M) (ν : N) : c μ ν ∈ S.unitLocalization := le_unitLocalization S (hcS μ ν)
  have hrF (μ : M) (ν : N) : r μ ν ∈ hB.residueSubfield := ⟨c μ ν, hcS' μ ν, hr μ ν⟩
  let rF : M → N →₀ hB.residueSubfield := fun μ ↦ Finsupp.onFinset (r μ).support
    (fun ν ↦ ⟨r μ ν, hrF μ ν⟩) fun ν hν ↦ Finsupp.mem_support_iff.2 fun h0 ↦ hν (Subtype.ext h0)
  have hfun : (fun μ ↦ Finsupp.mapRange (algebraMap hB.residueSubfield
      (ResidueField (unitClosedBall K))) (map_zero _) (rF μ)) = r := by
    funext μ
    ext ν
    rfl
  refine ⟨max ε 0, max_lt hε zero_lt_one, fun ν ↦ ?_⟩
  have hsingle : Finsupp.mapRange (algebraMap hB.residueSubfield
      (ResidueField (unitClosedBall K))) (map_zero _) (Finsupp.single ν 1) ∈
        Submodule.span (ResidueField (unitClosedBall K)) (Set.range fun μ ↦
          Finsupp.mapRange (algebraMap hB.residueSubfield (ResidueField (unitClosedBall K)))
            (map_zero _) (rF μ)) := by
    rw [hfun, hspan]
    exact Submodule.mem_top
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (Finsupp.mem_span_range_of_mapRange_mem_span rF _ hsingle)
  choose b hbS hbl using fun μ ↦ hB.mem_residueSubfield.1 (l μ).2
  refine ⟨∑ μ ∈ l.support, b μ • y μ, Submodule.sum_mem _ fun μ _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩), ?_⟩
  have hδ : HasSum (fun ν' ↦ (Pi.single ν (1 : K) : N → K) ν' • x ν') (x ν) := by
    have h := hasSum_single (f := fun ν' ↦ (Pi.single ν (1 : K) : N → K) ν' • x ν') ν
      fun ν' hν' ↦ by rw [Pi.single_eq_of_ne hν', zero_smul]
    simpa only [Pi.single_eq_same, one_smul] using h
  have hz : HasSum (fun ν' ↦ (∑ μ ∈ l.support, b μ * c μ ν') • x ν')
      (∑ μ ∈ l.support, b μ • y μ) := by
    have h := hasSum_sum fun μ (_ : μ ∈ l.support) ↦ (hy μ).const_smul (b μ)
    simpa only [Finset.sum_smul, smul_smul] using h
  have hdiff := hδ.sub hz
  simp only [← sub_smul] at hdiff
  refine hx.norm_le_of_hasSum hdiff (le_max_right _ _) fun ν' ↦ ?_
  have hδS : (Pi.single ν (1 : K) : N → K) ν' ∈ S.unitLocalization := by
    by_cases h : ν' = ν
    · rw [h, Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  have hdS : (Pi.single ν (1 : K) : N → K) ν' - ∑ μ ∈ l.support, b μ * c μ ν' ∈
      S.unitLocalization :=
    sub_mem hδS (sum_mem fun μ _ ↦ mul_mem (hbS μ) (hcS' μ ν'))
  have hd1 := hB.norm_le_one _ hdS
  have hlν : ∑ μ ∈ l.support, ((l μ : hB.residueSubfield) : ResidueField (unitClosedBall K)) *
      r μ ν' = ((Finsupp.single ν (1 : hB.residueSubfield) ν' : hB.residueSubfield) :
        ResidueField (unitClosedBall K)) := by
    have h := congrArg (fun f : N →₀ hB.residueSubfield ↦
      ((f ν' : hB.residueSubfield) : ResidueField (unitClosedBall K))) hl
    simp only [Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at h
    rw [← h, AddSubmonoidClass.coe_finsetSum]
    rfl
  have hres : residue (unitClosedBall K) ⟨_, mem_unitClosedBall.2 hd1⟩ = 0 := by
    have heq : (⟨_, mem_unitClosedBall.2 hd1⟩ : unitClosedBall K) =
        ⟨_, mem_unitClosedBall.2 (hB.norm_le_one _ hδS)⟩ - ∑ μ ∈ l.support,
          ⟨b μ, mem_unitClosedBall.2 (hB.norm_le_one _ (hbS μ))⟩ *
            ⟨c μ ν', mem_unitClosedBall.2 (hS.norm_le_one _ (hcS μ ν'))⟩ := by
      refine Subtype.ext ?_
      rw [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [heq, map_sub, map_sum]
    simp only [map_mul, ← hbl, ← hr]
    rw [hlν, sub_eq_zero]
    by_cases h : ν' = ν
    · subst h
      simp only [Pi.single_eq_same, Finsupp.single_eq_same]
      exact (map_one _).trans rfl
    · simp only [Pi.single_eq_of_ne h]
      rw [Finsupp.single_apply, if_neg (Ne.symm h)]
      exact (map_zero _).trans rfl
  have hlt : ‖(Pi.single ν (1 : K) : N → K) ν' - ∑ μ ∈ l.support, b μ * c μ ν'‖ < 1 := by
    have hmem := (residue_eq_zero_iff _).1 hres
    rw [maximalIdeal_unitClosedBall, mem_openUnitBallIdeal] at hmem
    exact hmem
  exact (hbald _ hdS hlt).trans (le_max_left _ _)

omit [IsUltrametricDist K] in
/-- If every vector of an orthonormal basis is approximated by a subspace up to a uniform `ε < 1`,
the subspace is dense. Source: Bosch 1.3/6 ("for any `x ∈ V_S`, there is an element `z ∈ V'_S`
with `|x − z| ≤ ε|x|`. But then … we get `V'_S = V_S` by iteration"); BGR 1.1.4/2. -/
theorem dense_span_of_forall_exists_norm_sub_le (hx : IsOrthonormalBasis K x) {ε : ℝ}
    (hε : ε < 1) (h : ∀ ν, ∃ z ∈ Submodule.span K (Set.range y), ‖x ν - z‖ ≤ ε) :
    Dense (Submodule.span K (Set.range y) : Set V) := by
  classical
  have hε'1 : max ε (1 / 2) < 1 := max_lt hε (by norm_num)
  have hε'0 : 0 < max ε (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  choose z hzU hz using h
  have hz' (ν : N) : ‖x ν - z ν‖ ≤ max ε (1 / 2) := (hz ν).trans (le_max_left _ _)
  show Dense ((Submodule.span K (Set.range y)).toAddSubgroup : Set V)
  refine AddSubgroup.dense_of_infDist_le _ _ hε'0 hε'1 fun v ↦ ?_
  rw [dist_zero_right]
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [norm_zero, mul_zero]
    exact (Metric.infDist_zero_of_mem (zero_mem _)).le
  obtain ⟨v', hv'mem, hvv'⟩ := Metric.mem_closure_iff.1 (hx.2 v) (max ε (1 / 2) * ‖v‖)
    (mul_pos hε'0 (norm_pos_iff.2 hv0))
  rw [dist_eq_norm] at hvv'
  have hv'le : ‖v'‖ ≤ ‖v‖ := by
    have h1 : v' = v + -(v - v') := by abel
    rw [h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_neg]
    exact hvv'.le.trans (mul_le_of_le_one_left (norm_nonneg _) hε'1.le)
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv'mem
  have hv'z' : ‖v' - l.sum (fun ν a ↦ a • z ν)‖ ≤ max ε (1 / 2) * ‖v'‖ := by
    rw [← hl]
    simp only [Finsupp.sum]
    rw [← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg hε'0.le (norm_nonneg _)) fun ν hν ↦ ?_
    rw [← smul_sub, norm_smul, mul_comm]
    exact mul_le_mul (hz' ν) (hx.1.norm_coeff_le_norm_sum l.support l hν) (norm_nonneg _)
      hε'0.le
  have hz'U : l.sum (fun ν a ↦ a • z ν) ∈ Submodule.span K (Set.range y) :=
    Submodule.sum_mem _ fun ν _ ↦ Submodule.smul_mem _ _ (hzU ν)
  refine (Metric.infDist_le_dist_of_mem hz'U).trans ?_
  rw [dist_eq_norm]
  have h2 : v - l.sum (fun ν a ↦ a • z ν) = (v - v') + (v' - l.sum (fun ν a ↦ a • z ν)) := by
    abel
  rw [h2]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le hvv'.le (hv'z'.trans (mul_le_mul_of_nonneg_left hv'le hε'0.le)))

/-- **Lifting of orthonormal bases.** Let `x` be an orthonormal basis of a nonarchimedean space
`V` and `y` a family whose coordinates `c μ ν` with respect to `x` lie in a bald subring. If
the reductions of the `y μ` form a basis of the reduction of `V` over the residue field, then `y`
is an orthonormal basis of `V`. Source: Bosch 1.3/6. -/
theorem IsOrthonormalBasis.of_residue_basis (hx : IsOrthonormalBasis K x)
    (hy : ∀ μ, HasSum (fun ν ↦ c μ ν • x ν) (y μ)) {S : Subring K} (hS : S.IsBald)
    (hcS : ∀ μ ν, c μ ν ∈ S) (r : M → N →₀ ResidueField (unitClosedBall K))
    (hr : ∀ μ ν, r μ ν = residue (unitClosedBall K)
      ⟨c μ ν, mem_unitClosedBall.2 (hS.norm_le_one _ (hcS μ ν))⟩)
    (hli : LinearIndependent (ResidueField (unitClosedBall K)) r)
    (hspan : Submodule.span (ResidueField (unitClosedBall K)) (Set.range r) = ⊤) :
    IsOrthonormalBasis K y := by
  refine ⟨hx.1.of_linearIndependent_residue hy (fun μ ν ↦ hS.norm_le_one _ (hcS μ ν)) r hr hli, ?_⟩
  obtain ⟨ε, hε, h⟩ := exists_norm_sub_le_of_span_residue hx.1 hy hS hcS r hr hspan
  exact dense_span_of_forall_exists_norm_sub_le hx hε h

end Lift
