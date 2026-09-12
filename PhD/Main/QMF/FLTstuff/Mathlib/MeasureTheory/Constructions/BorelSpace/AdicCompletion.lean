/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun, Kevin Buzzard
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Adic Completion

Material destined for Mathlib.

PORT (T016f-1) of `FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdicCompletion`.
-/

open NumberField

variable (K : Type*) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

noncomputable instance : MeasurableSpace (v.adicCompletion K) := borel _

instance : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
