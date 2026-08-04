/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Completion

Material destined for Mathlib.

PORT (T016e) of `FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Completion`.
-/

-- TODO upstream

-- no better place to put it really, could go in .Basic but it's about completions
theorem AbsoluteValue.Completion.secondCountableTopology
    {K : Type*} [Field K] {v : AbsoluteValue K ℝ} {L : Type*}
    [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L}
    [SecondCountableTopology L] (h : Isometry f) :
    SecondCountableTopology v.Completion :=
  h.completion_extension.isClosedEmbedding.isInducing.secondCountableTopology

instance NumberField.InfinitePlace.Completion.secondCountableTopology
    {K : Type*} [Field K] (v : InfinitePlace K) :
    SecondCountableTopology (v.Completion) :=
  -- PORT (v4.33): `v.Completion` is now a one-field structure wrapping `v.1.Completion`,
  -- so transfer second countability along the isometry `toCompletion`.
  have : SecondCountableTopology v.1.Completion :=
    AbsoluteValue.Completion.secondCountableTopology v.isometry_embedding
  (isometry_toCompletion v).isEmbedding.isInducing.secondCountableTopology
