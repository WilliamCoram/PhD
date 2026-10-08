/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Nonarchimedean groups have a `ℤ`-linear topology

A nonarchimedean additive group has a basis of neighbourhoods of `0` consisting of open additive
subgroups; since additive subgroups are exactly `ℤ`-submodules, its topology is `ℤ`-linear.

This is declared as an instance. Combined with `NonarchimedeanRing.to_nonarchimedeanAddGroup`, it
gives `IsLinearTopology ℤ R` for every nonarchimedean ring `R`.
-/

instance (priority := 100) NonarchimedeanAddGroup.isLinearTopology_int {G : Type*}
    [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G] : IsLinearTopology ℤ G := by
  apply IsLinearTopology.mk_of_hasBasis' (R := ℤ)
    (p := fun U : AddSubgroup G ↦ (U : Set G) ∈ nhds 0) (s := fun U : AddSubgroup G ↦ U)
  · refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨_, hN_mem, hN⟩ ↦ Filter.mem_of_superset hN_mem hN⟩⟩
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
    exact ⟨V.toAddSubgroup, V.mem_nhds_zero, hV⟩
  · exact fun _ n _ hm ↦ zsmul_mem hm n
