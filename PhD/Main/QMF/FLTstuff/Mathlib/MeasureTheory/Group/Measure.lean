/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.MeasureTheory.Group.Measure
import PhD.Main.QMF.FLTstuff.Mathlib.MeasureTheory.Group.Action
import PhD.Main.QMF.FLTstuff.Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Measure

Material destined for Mathlib.

PORT (T016f-1) of `FLT.Mathlib.MeasureTheory.Group.Measure`.
-/

open Topology MeasureTheory Measure

-- PORT (v4.33): mathlib now has `MeasureTheory.Measure.IsHaarMeasure.comap` with the same content;
-- the FLT statement (which is the dot-notation form used downstream) is kept verbatim, with its
-- original proof, since mathlib's version takes `MeasurableMul H` as a plain implicit argument.
@[to_additive]
lemma Topology.IsOpenEmbedding.isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [MeasurableMul H] [BorelSpace H]
    {φ : G →* H} (hφ : IsOpenEmbedding φ) (μ : Measure H) [IsHaarMeasure μ] :
    IsHaarMeasure (comap φ μ) where
  map_mul_left_eq_self := (hφ.measurableEmbedding.isMulLeftInvariant_comap μ).map_mul_left_eq_self
  lt_top_of_isCompact := (hφ.isFiniteMeasureOnCompacts_comap μ).lt_top_of_isCompact
  open_pos := (IsOpenPosMeasure.comap μ hφ).open_pos
