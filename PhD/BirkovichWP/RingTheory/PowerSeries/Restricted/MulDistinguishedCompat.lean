/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulDistinguished
import PhD.BirkovichWP.RingTheory.PowerSeries.Restricted.Distinguished

/-! # Compatibility: Martin-distinguished vs. the project's `IsDistinguished`

The bridge between the canonical Martin notion `IsMulDistinguished` (multiplicative unit
leading coefficient) and the legacy `IsDistinguished` (unit leading coefficient).  Every
Martin-distinguished series is distinguished, and over a `NormMulClass` coefficient ring the
two coincide.  Kept out of the canonical development (which no longer mentions
`IsDistinguished`) and next to the legacy `IsDistinguished` API it depends on.
-/

namespace PowerSeries

variable {A : Type*} [NormedCommRing A] {c : ℝ} {f : PowerSeries A} {s : ℕ}

/-- Martin-distinguished series are distinguished in the project's sense. -/
lemma IsMulDistinguished.toIsDistinguished (h : IsMulDistinguished c f s) :
    IsDistinguished norm c f s :=
  ⟨h.isNormMulUnit_coeff.isUnit, h.gaussNorm_eq, h.gaussTerm_lt⟩

/-- Over a multiplicatively-normed coefficient ring the two notions of distinguished
coincide: every unit is a multiplicative unit. -/
lemma isMulDistinguished_iff_isDistinguished [NormMulClass A] :
    IsMulDistinguished c f s ↔ IsDistinguished norm c f s :=
  ⟨fun h => h.toIsDistinguished,
    fun h => ⟨h.isUnit_coeff.isNormMulUnit, h.gaussNorm_eq, h.gaussTerm_lt⟩⟩

end PowerSeries
