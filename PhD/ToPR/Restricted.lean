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

variable [StrongPos (fun _ : Unit ↦ c)]

noncomputable
instance isRingNorm : RingNorm (PowerSeries.Restricted R c) where
  toFun f := gaussNorm R c f
  __ := MvRestricted.isRingNorm (R := R) (σ := Unit) (fun _ ↦ c)

variable (R) in
noncomputable
instance isNormedRing : NormedRing (PowerSeries.Restricted R c) :=
  RingNorm.toNormedRing (isRingNorm c)

noncomputable
instance isNonarchimedean :
    IsNonarchimedean (R := ℝ) (α := PowerSeries.Restricted R c) norm :=
  fun f g => PowerSeries.gaussNorm_add_le_max norm c f.1 g.1
    (Std.le_of_lt (StrongPos_pos (fun _ : Unit ↦ c) 0)) norm_nonneg
    IsUltrametricDist.norm_add_le_max (hasGaussNorm c f) (hasGaussNorm c g)

noncomputable
instance isUltrametricDist :
    IsUltrametricDist (PowerSeries.Restricted R c) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean (R := R) c)


omit [StrongPos fun _ ↦ c] in
lemma gaussNorm_achieved (hc : 0 ≤ c) (f : PowerSeries.Restricted R c) :
    ∃ a, PowerSeries.achievesGaussNorm norm c f.1 a := by
  simp_rw [PowerSeries.achievesGaussNorm]
  obtain ⟨a, _⟩ := MvRestricted.gaussNorm_achieved (σ := Unit) (fun _ ↦ c) (fun i ↦ hc) f
  exact ⟨(a PUnit.unit), by simpa [show Finsupp.single () (a PUnit.unit) = a by grind]⟩

omit [StrongPos fun _ ↦ c] in
lemma gaussNorm_achieved' (hc : 0 ≤ c) (f : PowerSeries.Restricted R c) :
    ∃ a, ‖PowerSeries.coeff a f.1‖ * c ^ a = gaussNorm R c f := by
  have := gaussNorm_achieved c hc f
  simp [PowerSeries.achievesGaussNorm_iff] at this
  exact this

omit [StrongPos fun _ ↦ c] in
lemma achievingPoints_finite (hc : 0 ≤ c) (f : PowerSeries.Restricted R c)
    (h : gaussNorm R c f ≠ 0) :
    {a | PowerSeries.achievesGaussNorm norm c f.1 a}.Finite := by
  have := MvRestricted.achievingPoints_finite (fun _ ↦ c) (fun _ ↦ hc) f h

  sorry

noncomputable
instance isAbsoluteValue (hnorm : ∀ a b : R, norm (a * b) = norm a * norm b) :
    IsAbsoluteValue (gaussNorm R c) :=
  MvRestricted.isAbsoluteValue (fun _ ↦ c) hnorm


end Restricted

section Polynomial

lemma Polynomial.IsRestricted {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)
    (f : Polynomial R) : PowerSeries.IsRestricted c f.toPowerSeries := by
  rw [PowerSeries.isRestricted_iff]
  suffices {t | ¬ (‖(PowerSeries.coeff t) f.toPowerSeries‖ * c ^ t = 0)}.Finite by
    exact tendsto_nhds_of_eventually_eq this
  simp only [coeff_coe, mul_eq_zero, norm_eq_zero, not_or, ← mem_support_iff]
  exact Set.Finite.sep (Finset.finite_toSet _) _

def Polynomial.toRestricted {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)
    (f : Polynomial R) : PowerSeries.Restricted R c :=
  ⟨f.toPowerSeries, Polynomial.IsRestricted c f⟩

end Polynomial
