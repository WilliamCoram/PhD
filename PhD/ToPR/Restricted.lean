import Mathlib.RingTheory.PowerSeries.Basic

import PhD.ToPR.MvRestricted
import PhD.ToPR.GaussNorm

import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

namespace PowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R]

abbrev IsRestricted (c :  ℝ) (f : PowerSeries R) :=
  MvPowerSeries.IsRestricted (σ := Unit) (fun _ ↦ c) f

lemma isRestricted_iff (c :  ℝ) (f : PowerSeries R) :
    IsRestricted c f ↔ Tendsto (fun t ↦ ‖coeff t f‖ * c ^ t) cofinite (𝓝 0) := by
  rw [IsRestricted, MvPowerSeries.IsRestricted]
  simp [coeff]


  sorry

@[simp]
lemma isRestricted_abs_iff (c :  ℝ) (f : PowerSeries R) :
    IsRestricted |c| f ↔ IsRestricted c f :=
  MvPowerSeries.isRestricted_abs_iff (fun _ ↦ c) f

lemma isRestricted_zero (c : ℝ) : IsRestricted c (0 : PowerSeries R) :=
 MvPowerSeries.isRestricted_zero (fun _ ↦ c)

lemma isRestricted_monomial (c : ℝ) (n : ℕ) (a : R) : IsRestricted c (monomial n a) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) ((Finsupp.single () n)) a

lemma isRestricted_one (c : ℝ) : IsRestricted c (1 : PowerSeries R) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) 0 1

lemma isRestricted_C (c : ℝ) (a : R) : IsRestricted c (C a) :=
  MvPowerSeries.isRestricted_C (fun _ ↦ c) a

lemma isRestricted.add (c : ℝ) {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g)
    : IsRestricted c (f + g) :=
  MvPowerSeries.isRestricted.add (fun _ ↦ c) hf hg

lemma isRestricted.neg (c : ℝ) {f : PowerSeries R} (hf : IsRestricted c f) :
    IsRestricted c (-f) :=
  MvPowerSeries.isRestricted.neg (fun _ ↦ c) hf

lemma isRestricted.mul [IsUltrametricDist R] (c : ℝ) {f g : PowerSeries R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) :=
  MvPowerSeries.isRestricted.mul (fun _ ↦ c) hf hg

/-- Additive subgroup structure on `MvPowerSeries σ R`. -/
def isAddSubgroup (c : ℝ) : AddSubgroup (PowerSeries R) where
  carrier := IsRestricted c
  zero_mem' := isRestricted_zero c
  add_mem' := isRestricted.add c
  neg_mem' := isRestricted.neg c

variable [IsUltrametricDist R]

/-- Ring structure on `MvPowerSeries σ R`. -/
def isSubring (c : ℝ) :  Subring (PowerSeries R) where
  __ := isAddSubgroup c
  one_mem' := isRestricted_one c
  mul_mem' := isRestricted.mul c

variable (R) in
/-- The type of restricted `MvPowerSeries σ R`. -/
def Restricted (c : ℝ) : Type _ := isSubring (R := R) c

/-- Ring structure on `Restricted R c`. -/
noncomputable
instance (c : ℝ) : Ring (Restricted R c) :=
  Subring.toRing (isSubring c)

end PowerSeries

namespace Restricted

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)

variable (R) in
noncomputable
abbrev gaussNorm (f : PowerSeries.Restricted R c) : ℝ :=
  MvRestricted.gaussNorm R (fun _ ↦ c) f

lemma hasGaussNorm (f : PowerSeries.Restricted R c) :
  PowerSeries.HasGaussNorm norm c f.1 := Filter.Tendsto.bddAbove_range_of_cofinite f.2

noncomputable
instance isRingNorm (hc : 0 < c) :
    RingNorm (PowerSeries.Restricted R c) where
  toFun f := gaussNorm R c f
  __ := MvRestricted.isRingNorm (R := R) (σ := Unit) (fun _ ↦ c) (by grind)

variable (R) in
noncomputable
instance isNormedRing (hc : 0 < c) :
    NormedRing (PowerSeries.Restricted R c) :=
  RingNorm.toNormedRing (isRingNorm c hc)

noncomputable
instance isNonarchimedean (hc : 0 < c) :
    letI := isNormedRing (R := R) c hc
    IsNonarchimedean (R := ℝ) (α := PowerSeries.Restricted R c) norm :=
  fun f g => PowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (Std.le_of_lt hc) norm_nonneg
    IsUltrametricDist.norm_add_le_max (hasGaussNorm c f) (hasGaussNorm c g)

noncomputable
instance isUltrametricDist (hc : 0 < c) :
    letI := isNormedRing (R := R) c hc
    IsUltrametricDist (PowerSeries.Restricted R c) :=
  letI : NormedRing (PowerSeries.Restricted R c) := isNormedRing R c hc
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean (R := R) c hc)

-- note this should be ∃ a, gaussNorm_achieved ... f
-- the using gaussNorm_achieved_iff I can get this as an API lemma...
-- this should probably make achievingPoints_finite immediate to prove...
lemma gaussNorm_achieved (hc : 0 ≤ c) (f : PowerSeries.Restricted R c) :
    ∃ a, ‖PowerSeries.coeff a f.1‖ * c ^ a = gaussNorm R c f := by
  obtain ⟨a, ha⟩ := MvRestricted.gaussNorm_achieved (σ := Unit) (fun _ ↦ c) (fun i ↦ hc) f
  use (a PUnit.unit)
  simp_rw [gaussNorm, ← ha, PowerSeries.coeff, Finsupp.prod_pow, Finset.univ_unique,
    PUnit.default_eq_unit, Finset.prod_singleton,
    show (Finsupp.single () (a PUnit.unit)) = a by aesop]

lemma achievingPoints_finite (hc : 0 ≤ c) (f : PowerSeries.Restricted R c)
    (h : gaussNorm R c f ≠ 0) :
    {a | ‖PowerSeries.coeff a f.1‖ * c ^ a = gaussNorm R c f}.Finite := by
  have := MvRestricted.achievingPoints_finite (fun _ ↦ c) (fun i ↦ hc) f h

  sorry

noncomputable
instance isAbsoluteValue (hc : 0 < c) (hnorm : ∀ a b : R, norm (a * b) = norm a * norm b) :
    IsAbsoluteValue (gaussNorm R c) :=
  MvRestricted.isAbsoluteValue (fun _ ↦ c) (fun _ ↦ hc) hnorm
