/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Japanese
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Rueckert
import PhD.TauCeti.Code.RigidAnalyticGeometry.WeaklyStable

/-!
# Weak stability of the fraction field of the Tate algebra, in characteristic zero

Over a complete nonarchimedean field `K` of characteristic zero, the fraction field of the Tate
algebra `Tₙ`, with the multiplicative extension of the Gauss norm, is weakly stable, and `Tₙ` is a
Japanese ring. Both statements are instances of facts about perfect fields; they hold in every
characteristic (BGR 5.3.1/1 and 5.3.1/3), and the proof in characteristic `p` is not in this file.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.4.2–0.4.3 (BGR 5.3.1/1,
5.3.1/3, the case `char k = 0`). Tau Ceti home: `TauCeti/RingTheory/TateAlgebra/Stable.lean`.

## Main results

* `Affinoid.TateAlgebra.isWeaklyStable_fractionRing` — BGR 5.3.1/1 in characteristic zero.
* `Affinoid.TateAlgebra.isJapaneseRing` — BGR 5.3.1/3 in characteristic zero.
-/

universe u

namespace Affinoid.TateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

omit [CompleteSpace K] in
/-- **The fraction field of the Tate algebra is weakly stable**, in characteristic zero.
Source: BGR 5.3.1/1 ("All valued fields of characteristic `0` are weakly stable"). -/
theorem isWeaklyStable_fractionRing (n : ℕ) :
    letI := IsFractionRing.normedField (TateAlgebra K n) (FractionRing (TateAlgebra K n))
    IsWeaklyStable (FractionRing (TateAlgebra K n)) := by
  letI := IsFractionRing.normedField (TateAlgebra K n) (FractionRing (TateAlgebra K n))
  haveI := IsFractionRing.isUltrametricDist (TateAlgebra K n) (FractionRing (TateAlgebra K n))
  exact isWeaklyStable_of_perfectField _

/-- **The Tate algebra is Japanese**, in characteristic zero. Source: BGR 5.3.1/3 ("the assertion
follows from Proposition 4.3/2 if `char k = 0`"). -/
theorem isJapaneseRing (n : ℕ) : IsJapaneseRing (TateAlgebra K n) :=
  isJapaneseRing_of_perfectField _

end Affinoid.TateAlgebra
