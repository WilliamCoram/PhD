/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Japanese rings

An integral domain `A` is *Japanese* if its integral closure in every finite extension of its
fraction field is a finite `A`-module. By a theorem of Dedekind, a noetherian integrally closed
domain has finite integral closure in every finite separable extension of its fraction field; in
particular it is Japanese when its fraction field is perfect.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.4.3 (BGR 4.2/1, 4.3/1–2).
Tau Ceti home: `TauCeti/RingTheory/Japanese.lean`.

## Main definitions

* `IsJapaneseRing A` — BGR 4.3/1.

## Main results

* `isJapaneseRing_of_perfectField` — BGR 4.3/2.
-/

universe u

/-- An integral domain is **Japanese** if its integral closure in every finite extension of its
fraction field is a finite module over it. Source: BGR 4.3/1. -/
def IsJapaneseRing (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L],
    Module.Finite A (integralClosure A L)

/-- **A noetherian integrally closed domain with perfect fraction field is Japanese.**
Source: BGR 4.3/2, from Dedekind's theorem 4.2/1. -/
theorem isJapaneseRing_of_perfectField (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [PerfectField (FractionRing A)] :
    IsJapaneseRing A := by
  intro L _ _ _ _ _
  haveI : Algebra.IsSeparable (FractionRing A) L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact IsIntegralClosure.finite A (FractionRing A) L (integralClosure A L)
