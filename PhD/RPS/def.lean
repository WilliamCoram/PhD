/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import Mathlib

open  PowerSeries

namespace IsRestricted

open IsRestricted

variable {R : Type*} [NormedRing R] (c : ℝ)

lemma nsmul (n : ℕ) (f : PowerSeries R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  have h := IsRestricted.smul c hf (n : R)
  convert h
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_nsmul, nsmul_eq_mul]

lemma zsmul (n : ℤ) (f : PowerSeries R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  have h := IsRestricted.smul c hf (n : R)
  convert h
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_zsmul, zsmul_eq_mul]

end IsRestricted

namespace PowerSeries

variable {R : Type*} [NormedRing R] (c : ℝ)

local instance : AddSubgroup (PowerSeries R) where
  carrier := IsRestricted c
  zero_mem' := IsRestricted.zero c
  add_mem' := IsRestricted.add c
  neg_mem' := IsRestricted.neg c

def  Crestricted : Type _ :=
  Subtype (IsRestricted (R := R) c)

variable (f g : Crestricted (R := R) c)

#check  f + g -- something is not working... do I need to adjust the definition of turning it to a type

namespace Ultrametric

local instance [IsUltrametricDist R] : Subring (PowerSeries R) where
  toAddSubgroup := by infer_instance
  one_mem' := IsRestricted.one c
  mul_mem' := IsRestricted.mul c

/--/
-- Method 2

structure cRestricted where
  series : PowerSeries R
  convergence : IsRestricted c series

noncomputable
instance : AddCommGroup (cRestricted R c) where
  add f g :=⟨f.1 + g.1, IsRestricted.add c f.2 g.2⟩
  add_assoc f g h := by
    rw [cRestricted.mk.injEq]
    exact add_assoc f.1 g.1 h.1
  add_comm f g := by
    rw [cRestricted.mk.injEq]
    exact add_comm f.1 g.1
  zero := ⟨0, IsRestricted.zero c⟩
  zero_add f := by
    rw [cRestricted.mk.injEq]
    exact zero_add f.series
  add_zero f := by
    rw [cRestricted.mk.injEq]
    exact add_zero f.series
  neg f := ⟨-f.1, IsRestricted.neg c f.2⟩
  neg_add_cancel f := by
    rw [cRestricted.mk.injEq]
    exact neg_add_cancel f.1
  nsmul n f := ⟨n • f.1, (IsRestricted.nsmul c n f.1) f.2⟩
  nsmul_zero _ := by
    simp only [zero_nsmul]
    rfl
  nsmul_succ _ _ := by
    simp_rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    rfl
  zsmul n f := ⟨n • f.1, (IsRestricted.zsmul c n f.1) f.2⟩
  zsmul_neg' _ _ := by
    simp only [zsmul_eq_mul, Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev,
      Nat.succ_eq_add_one, Int.cast_add, Int.cast_natCast, Int.cast_one, add_mul, neg_mul, one_mul,
      neg_add_rev]
  zsmul_succ' _ _ := by
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, zsmul_eq_mul, Int.cast_add,
      Int.cast_natCast, Int.cast_one, add_mul, one_mul]
    rfl
  zsmul_zero' _ := by
    simp only [zero_smul]
    rfl

variable [IsUltrametricDist R]

noncomputable
instance : Ring (cRestricted R c) where
  one := ⟨1, IsRestricted.one c⟩
  mul f g := ⟨f.1 * g.1, IsRestricted.mul c f.2 g.2⟩
  zero_mul f := by
    rw [cRestricted.mk.injEq]
    exact zero_mul f.1
  mul_zero f := by
    rw [cRestricted.mk.injEq]
    exact mul_zero f.1
  one_mul f := by
    rw [cRestricted.mk.injEq]
    exact one_mul f.1
  mul_one f := by
    rw [cRestricted.mk.injEq]
    exact mul_one f.1
  mul_assoc f g h := by
    rw [cRestricted.mk.injEq]
    exact mul_assoc f.1 g.1 h.1
  left_distrib f g h := by
    rw [cRestricted.mk.injEq]
    exact left_distrib f.1 g.1 h.1
  right_distrib f g h := by
    rw [cRestricted.mk.injEq]
    exact right_distrib f.1 g.1 h.1
