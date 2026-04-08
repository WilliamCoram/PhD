/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import PhD.RPS.mathlib
import Mathlib.RingTheory.PowerSeries.basic

/-!
# Restricted power series

`IsRestricted` : We say a power series over a normed ring `R` is restricted for a parameter `c` if
`‖coeff R i f‖ * c ^ i → 0`.

-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [NormedRing R] (c : ℝ)

open PowerSeries Filter
open scoped Topology


abbrev IsRestricted' (f : PowerSeries R) := MvPowerSeries.IsRestricted R (Finsupp.single () c) f

def IsRestricted (f : PowerSeries R) :=
  Tendsto (fun t ↦ ‖coeff t f‖ * c ^ t) cofinite (𝓝 0)

lemma IsRestricted_iff_isRestrictedMv (f : PowerSeries R) : IsRestricted c f ↔
    IsRestricted' c (f : MvPowerSeries Unit R) := by
  rw [IsRestricted, IsRestricted', MvPowerSeries.IsRestricted]
  simp_rw [coeff]
  simp only [Finsupp.single_eq_same, Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.prod_singleton]

  -- use Equiv.finsuppUnique
  sorry

lemma IsRestricted_iff_atTop (f : PowerSeries R) :
    IsRestricted c f ↔ Tendsto (fun (i : ℕ) ↦ (norm (coeff i f)) * c ^ i) atTop (𝓝 0) := by
  simp [IsRestricted, Nat.cofinite_eq_atTop]

lemma IsRestricted_iff_epsilon {f : PowerSeries R} : IsRestricted c f ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖‖(coeff n) f‖ * c ^ n‖ < ε := by
  simp [IsRestricted_iff_atTop, NormedAddCommGroup.tendsto_atTop]

lemma isRestricted_iff_abs (f : PowerSeries R) : IsRestricted c f ↔ IsRestricted |c| f := by

  sorry

instance isAddSubgroup : AddSubgroup (PowerSeries R) where
  carrier := IsRestricted c
  zero_mem' := (IsRestricted_iff_isRestrictedMv c 0).mpr (MvPowerSeries.isRestricted_zero R (Finsupp.single () c))
  add_mem' := by
    intro a b ha hb
    exact (IsRestricted_iff_isRestrictedMv c (a + b)).mpr (MvPowerSeries.isRestricted.add R (Finsupp.single () c)
      ((IsRestricted_iff_isRestrictedMv c a).mp ha) ((IsRestricted_iff_isRestrictedMv c b).mp hb))
  neg_mem' := by
    intro f hf
    exact (IsRestricted_iff_isRestrictedMv c (-f)).mpr (MvPowerSeries.isRestricted.neg R (Finsupp.single () c)
      ((IsRestricted_iff_isRestrictedMv c f).mp hf))

instance isSubring [IsUltrametricDist R] : Subring (PowerSeries R) where
  __ := isAddSubgroup c
  one_mem' := (IsRestricted_iff_isRestrictedMv c 1).mpr (MvPowerSeries.isRestricted_one R (Finsupp.single () c))
  mul_mem' := by
    intro a b ha hb
    exact (IsRestricted_iff_isRestrictedMv c (a * b)).mpr (MvPowerSeries.isRestricted.mul R (Finsupp.single () c)
      ((IsRestricted_iff_isRestrictedMv c a).mp ha) ((IsRestricted_iff_isRestrictedMv c b).mp hb))

def Restricted [IsUltrametricDist R] : Type _ := isSubring (R := R) c

noncomputable
instance [IsUltrametricDist R] : Ring (Restricted (R := R) c) :=
  Subring.toRing (isSubring (R := R) c)
