/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun
-/
import PhD.QMF.FLTstuff.Mathlib.MeasureTheory.Constructions.BorelSpace.InfinitePlace
import PhD.QMF.FLTstuff.Mathlib.MeasureTheory.Constructions.BorelSpace.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.AdeleRing
import PhD.QMF.FLTstuff.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Adele Ring

Material destined for Mathlib.

PORT (T016e) of `FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdeleRing`.
-/

variable (K : Type*) [Field K] [NumberField K]

open NumberField

instance : MeasurableSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (MeasurableSpace (_ × _))

instance : BorelSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (BorelSpace (_ × _))
