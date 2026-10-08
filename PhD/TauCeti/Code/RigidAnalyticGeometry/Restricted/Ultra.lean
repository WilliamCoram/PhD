/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Ultrametric normed rings are nonarchimedean

A seminormed ring whose metric is ultrametric is a nonarchimedean ring: every neighbourhood of
`0` contains an open additive subgroup. This is the ring analogue of
`IsUltrametricDist.nonarchimedeanAddGroup`, declared as an instance.
-/

instance (priority := 100) IsUltrametricDist.nonarchimedeanRing {R : Type*} [SeminormedRing R]
    [IsUltrametricDist R] : NonarchimedeanRing R where
  is_nonarchimedean := IsUltrametricDist.nonarchimedeanAddGroup.is_nonarchimedean
