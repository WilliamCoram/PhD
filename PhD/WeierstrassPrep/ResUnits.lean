import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted

import PhD.WeierstrassPrep.Restricted_powerbounded_topnil
import PhD.WeierstrassPrep.EpsilonDense
import PhD.WeierstrassPrep.ResPoly
import PhD.WeierstrassPrep.ResC
import PhD.WeierstrassPrep.idealBalls
import PhD.WeierstrassPrep.Polylift

import Mathlib.RingTheory.Polynomial.Nilpotent

open Topology

-- I should probably add my local notation for PowerBounded subring of res power series
-- I also need to sort out my variable line and get it working correctly

-- The following are repeats from numerous files, need to work out a global place to put them

-- still need to get around this
local instance : StrongPos (fun _ : Unit ↦ (1 : ℝ)) where
  pos := by simp

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R]
  [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R]

local instance : NormMulClass (PowerSeries.Restricted R 1) :=
  MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ 1)

-- note this should not be proven like this
-- instead it should be a general statement for MvPowerSeries and this as a corollary
-- do when I clean up Restricted and MvRestricted
local instance : NormOneClass (PowerSeries.Restricted R 1) where
  norm_one := by
    rw [← PowerSeries.Restricted.C_one (S := R) 1, PowerSeries.Restricted.norm_C, norm_one]

-- this can be tidied later when I decide where the global place to put it is
-- perhaps a TateAlgebra.instances file?
local instance : Filter.NeBot (𝓝[≠] (0 : (PowerSeries.Restricted R 1))) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr_ne, hr⟩ : ∃ r : R, r ≠ 0 ∧ ‖r‖ < ε := by
    have hR : (0 : R) ∈ closure ({0}ᶜ : Set R) :=
      mem_closure_iff_nhdsWithin_neBot.mpr inferInstance
    obtain ⟨r, hr_mem, hr_dist⟩ := Metric.mem_closure_iff.mp hR ε hε
    rw [dist_comm, dist_zero_right] at hr_dist
    exact ⟨r, hr_mem, hr_dist⟩
  have hcoe : (Restricted.monomial 1 0 r).1 = PowerSeries.monomial 0 r := rfl
  have hub : ‖Restricted.monomial 1 0 r‖ ≤ ‖r‖ := by
    rw [Restricted.norm_eq, hcoe, PowerSeries.gaussNorm_eq]
    refine ciSup_le (fun i => ?_)
    rw [PowerSeries.coeff_monomial, one_pow, mul_one]
    split_ifs with h
    · exact le_refl _
    · simp
  have hlb : ‖r‖ ≤ ‖Restricted.monomial 1 0 r‖ := by
    rw [Restricted.norm_eq, hcoe]
    have h := PowerSeries.le_gaussNorm (norm : R → ℝ) 1 (Restricted.monomial 1 0 r).1
      (Restricted.hasGaussNorm 1 (Restricted.monomial 1 0 r)) 0
    rw [hcoe] at h
    simpa [PowerSeries.coeff_monomial] using h
  have hne : Restricted.monomial 1 0 r ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hr_ne) hlb)
  exact ⟨Restricted.monomial 1 0 r, hne,
    by rw [dist_comm, dist_zero_right]; exact lt_of_le_of_lt hub hr⟩

local instance {S : Type*} [NormedCommRing S] [IsUltrametricDist S] :
    NonarchimedeanRing S where
  is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup).is_nonarchimedean

local instance (S : Type*) [Ring S] [TopologicalSpace S] [NonarchimedeanRing S] :
    IsLinearTopology ℤ S := by
  apply IsLinearTopology.mk_of_hasBasis' (R := ℤ)
    (p := fun U : AddSubgroup S => (U : Set S) ∈ nhds 0)
    (s := fun U : AddSubgroup S => U)
  · refine ⟨fun U => ⟨fun hU => ?_,
      fun ⟨_, hN_mem, hN⟩ => Filter.mem_of_superset hN_mem hN⟩⟩
    obtain ⟨V, hV⟩ := NonarchimedeanRing.is_nonarchimedean U hU
    exact ⟨V.toAddSubgroup, V.mem_nhds_zero, hV⟩
  · intro _ n _ hm
    exact zsmul_mem hm n

omit [Nontrivial R] [CompleteSpace R] in
/-- The reduction-mod-`ε` ring hom `τ_ε : T° →+* R̃[X]` is surjective -/
lemma Restricted.openBall_residueRingHom_surjective {ε : ℝ} (hε : 0 < ε) :
    Function.Surjective (Restricted.openBall_residueRingHom (R := R) ε hε) := by
  exact fun q ↦ ⟨Restricted.pbPoly_to_pbRestricted
    (Polynomial.liftQuot (PowerBounded.openBall_ideal ε hε) q),
    by rw [Restricted.openBall_residueRingHom_pbPoly_to_pbRestricted, Polynomial.liftQuot_map]⟩

omit [Nontrivial R] [CompleteSpace R] in
/-- The kernel of `τ_ε : T° →+* R̃[X]` is the open `ε`-ball ideal of `T°`. -/
lemma Restricted.openBall_residueRingHom_ker {ε : ℝ} (hε : 0 < ε) :
    RingHom.ker (Restricted.openBall_residueRingHom (R := R) ε hε)
      = PowerBounded.openBall_ideal (R := PowerSeries.Restricted R 1) ε hε := by
  ext f
  simpa [RingHom.mem_ker] using ⟨Restricted.openBall_norm_lt_of_residueRingHom_eq_zero hε f,
    Restricted.openBall_residueRingHom_eq_zero_of_norm_lt hε f⟩

-- this should 100% be moved elsewhere
-- also not maybe I want an abbrev for this quotient? openBall_residue?
omit [Nontrivial R] [CompleteSpace R] in
/-- The first-isomorphism-theorem isomorphism `T° ⧸ R_ε ≅ R̃[X]` induced by `τ_ε`. -/
noncomputable def Restricted.openBall_residueEquiv {ε : ℝ} (hε : 0 < ε) :
    (↥(PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)) ⧸
      PowerBounded.openBall_ideal (R := PowerSeries.Restricted R 1) ε hε) ≃+*
    Polynomial (↥(PowerBounded.subring R (S := ℤ)) ⧸ PowerBounded.openBall_ideal (R := R) ε hε) :=
  (Ideal.quotEquivOfEq (Restricted.openBall_residueRingHom_ker hε).symm).trans
    (RingHom.quotientKerEquivOfSurjective (Restricted.openBall_residueRingHom_surjective hε))

omit [Nontrivial R] [CompleteSpace R] in
@[simp]
lemma Restricted.openBall_residueEquiv_mk {ε : ℝ} (hε : 0 < ε)
    (f : ↥(PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ))) :
    Restricted.openBall_residueEquiv hε (Ideal.Quotient.mk _ f)
    = Restricted.openBall_residueRingHom ε hε f := rfl

omit [Nontrivial R] [CompleteSpace R] in
lemma Restricted.openBall_ideal_isUnit_iff
    (f : PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)) :
    IsUnit ((Ideal.Quotient.mk (PowerBounded.openBall_ideal 1 zero_lt_one)) f) ↔
    IsUnit ((openBall_residueRingHom 1 zero_lt_one) f) := by
  refine ⟨fun h => h.map (Restricted.openBall_residueEquiv (R := R) zero_lt_one), fun h ↦ ?_⟩
  have := h.map (Restricted.openBall_residueEquiv (R := R) zero_lt_one).symm
  rwa [← Restricted.openBall_residueEquiv_mk (by simp) f, RingEquiv.symm_apply_apply] at this


omit [Nontrivial R] in
lemma Restricted.PowerBounded_isUnit_iff
    (f : PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)) :
    IsUnit f ↔ (IsUnit (pbCoeff f 0) ∧
    ∀ v, v ≠ 0 → IsTopologicallyNilpotent (PowerSeries.coeff v f.1.1)) := by
  convert IsPowerBounded.PowerBounded_isUnit_iff_res_isUnit f
  rw [PowerBounded.topologicalNilradical_is_openBall_one, Restricted.openBall_ideal_isUnit_iff f,
    openBall_residueRingHom_apply, Polynomial.isUnit_iff_coeff_isUnit_isNilpotent]
  refine and_congr ?_ (forall_congr' fun v => ?_)
  · rw [openBall_residuePolynomial_coeff, ← PowerBounded.topologicalNilradical_is_openBall_one,
      ← IsPowerBounded.PowerBounded_isUnit_iff_res_isUnit]
  · rw [openBall_residuePolynomial_coeff]
    constructor
    · intro h hv0
      refine ⟨1, ?_⟩
      rw [pow_one, Ideal.Quotient.eq_zero_iff_mem, PowerBounded.mem_openBall_ideal, pbCoeff_coe]
      exact IsTopologicallyNilpotent.norm_lt_one (h hv0)
    · intro h hv
      obtain ⟨k, hk⟩ := h hv
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem,
        ← PowerBounded.topologicalNilradical_is_openBall_one,
        IsTopologicallyNilpotent.mem_PowerBounded.topologicalNilradical_iff,
        SubmonoidClass.coe_pow, pbCoeff_coe] at hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [pow_zero] at hk
        exact absurd (IsTopologicallyNilpotent.norm_lt_one hk) (by simp)
      · exact IsTopologicallyNilpotent.of_pow hk0 hk

lemma Restricted.isUnit_subring_iff {A : Type*} [NormedCommRing A] [IsUltrametricDist A]
    [NormMulClass A] [NormOneClass A]
    (a : PowerBounded.subring A (S := ℤ)) (ha : ‖(a : A)‖ = 1) :
    IsUnit a ↔ IsUnit (a : A) := by
  constructor
  · exact fun h ↦ h.map (PowerBounded.subring A (S := ℤ)).subtype
  · rintro ⟨u, hu⟩
    refine isUnit_iff_exists.mpr
      ⟨⟨u.inv, IsPowerBounded.isPowerBounded_of_norm_le_one
        (by rw [← norm_one (α := A), ← u.val_inv]; aesop)⟩, ?_, ?_⟩
    <;> apply Subtype.ext <;> simp [hu]

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] [Nontrivial R] in
lemma Restricted.series_sub_first_term_coeffs {f g : PowerSeries.Restricted R 1}
    (h : g = f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)) :
    ∀ v, PowerSeries.coeff v g.1 = if v = 0 then 0 else PowerSeries.coeff v f.1 := by
  intro v
  rw [h]
  -- this could be an indication that I need a Restricted.coe_sub by rfl lemma
  -- or need better typing to use Submodule.coe_sub
  show PowerSeries.coeff v (f.1 - (PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)).1)
      = if v = 0 then 0 else PowerSeries.coeff v f.1
  rw [map_sub, PowerSeries.Restricted.coeff_C]
  split_ifs with h
  · rw [h, sub_self]
  · rw [sub_zero]

omit [Nontrivial R] [CompleteSpace R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] in
lemma Restricted.series_sub_first_term_norm (f : PowerSeries.Restricted R 1) : (∀ v, v ≠ 0 →
    IsTopologicallyNilpotent (PowerSeries.coeff v f.1)) ↔
    ‖f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)‖ < 1 := by
  set g := f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1) with hg_def
  simp_rw [IsTopologicallyNilpotent.iff_norm_lt_one]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Restricted.gaussNorm_achieved' 1 zero_le_one g
    simp_rw [Restricted.norm_eq, ha.symm, Restricted.series_sub_first_term_coeffs hg_def]
    split_ifs with h0
    · simp
    · simpa using h a h0
  · intro hg v hv
    simpa [Restricted.series_sub_first_term_coeffs hg_def, if_neg hv] using
      lt_of_le_of_lt (PowerSeries.le_gaussNorm _ 1 _ (Restricted.hasGaussNorm 1 g) v) hg

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))]
  [Nontrivial R] in
lemma Restricted.series_sub_first_term_norm_neZero_coeffs (f : PowerSeries.Restricted R 1)
    (hg : ‖f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)‖ < 1) :
    ∀ v, v ≠ 0 → ‖(PowerSeries.coeff v) f.1‖ < 1 := by
  intro v hv
  set g := f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)
  have := Restricted.series_sub_first_term_coeffs (f := f) (g := g) (by rfl) v
  simp [hv] at this
  exact LE.le.trans_lt (by simpa [← this] using
    PowerSeries.le_gaussNorm _ 1 _ (Restricted.hasGaussNorm 1 g) v) hg

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))]
  [Nontrivial R] in
lemma Restricted.norm_coeff_zero_eq_one (f : PowerSeries.Restricted R 1) (hf : ‖f‖ = 1)
    (hg : ‖f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)‖ < 1) :
    ‖PowerSeries.coeff 0 f.1‖ = 1 := by
  refine le_antisymm ?_ ?_
  · simpa [← Restricted.norm_eq, hf] using
      PowerSeries.le_gaussNorm _ 1 _ (Restricted.hasGaussNorm 1 f) 0
  · by_contra hlt
    obtain ⟨a, ha⟩ := gaussNorm_achieved' 1 (by simp) f
    simp only [one_pow, mul_one, ← norm_eq] at ha
    have := Restricted.series_sub_first_term_norm_neZero_coeffs f hg
    grind

-- weakend version of what I want when R is NOT a field
omit [Nontrivial R] in
lemma Restricted.isUnit_iff (f : PowerSeries.Restricted R 1) (hf : ‖f‖ = 1) : IsUnit f ↔
    IsUnit (PowerSeries.coeff 0 f.1) ∧
    ‖f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)‖ < 1 := by
  set g := f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)
  let F : ↥(PowerBounded.subring _ (S := ℤ)) :=
    ⟨f, IsPowerBounded.isPowerBounded_of_norm_le_one hf.le⟩
  -- the show is needed for defeq abuse to work
  rw [show IsUnit f ↔ IsUnit F from (Restricted.isUnit_subring_iff F hf).symm,
      Restricted.PowerBounded_isUnit_iff F]
  constructor
  · rintro ⟨hu, hnil⟩
    refine ⟨?_, (Restricted.series_sub_first_term_norm f).mp hnil⟩
    refine (Restricted.isUnit_subring_iff (pbCoeff F 0) ?_).mp hu
    exact Restricted.norm_coeff_zero_eq_one f hf ((Restricted.series_sub_first_term_norm f).mp hnil)
  · rintro ⟨hu, hg⟩
    refine ⟨?_, (Restricted.series_sub_first_term_norm f).mpr hg⟩
    refine (Restricted.isUnit_subring_iff (pbCoeff F 0) ?_).mpr hu
    exact Restricted.norm_coeff_zero_eq_one f hf hg

section NormedField

-- the BGR lemma I want... this seems inherently weaker
-- and I probably only want to be using the above lemma instead
-- this is stated purely for compeletion
lemma Restricted.isUnit_iff' {R : Type*} [NormedField R] [IsUltrametricDist R] [CompleteSpace R]
    [Filter.NeBot (𝓝[≠] (0 : R))] (f : PowerSeries.Restricted R 1) (hf : ‖f‖ = 1) : IsUnit f ↔
    ‖PowerSeries.coeff 0 f.1‖ = 1 ∧
    ‖f - PowerSeries.Restricted.C 1 (PowerSeries.coeff 0 f.1)‖ < 1 := by
  rw [Restricted.isUnit_iff f hf]
  constructor
  · rintro ⟨_, hg⟩
    exact ⟨Restricted.norm_coeff_zero_eq_one f hf hg, hg⟩
  · rintro ⟨hn, hg⟩
    exact ⟨isUnit_iff_ne_zero.mpr (norm_pos_iff.mp (by rw [hn]; exact one_pos)), hg⟩

end NormedField
