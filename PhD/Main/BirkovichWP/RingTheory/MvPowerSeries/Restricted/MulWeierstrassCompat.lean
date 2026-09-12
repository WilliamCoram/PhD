/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.MulWeierstrass
import PhD.Main.BirkovichWP.RingTheory.MvPowerSeries.Restricted.Distinguished
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.MulDistinguishedCompat

/-! # Compatibility: multivariate Martin-distinguished vs. `IsDistinguishedX0`

The multivariate bridge.  Over a `NormMulClass` base — in particular a complete nontrivially
normed field — the canonical `IsMulDistinguishedX0` coincides with the legacy
`IsDistinguishedX0`, and the canonical Martin endpoints
(`PhD.Main.ForMathlib.…MvPowerSeries.Restricted.MulWeierstrass`) restate with the field-facing
`IsDistinguishedX0` hypothesis, recovering the endpoints of the Gauss-extension development
in `PhD.Main.BirkovichWP.…MvPowerSeries.Restricted.DivisibleRadius` with no extension machinery.
-/

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {n : ℕ} {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

lemma IsMulDistinguishedX0.toIsDistinguishedX0 {f : Restricted R c} {s : ℕ}
    (h : IsMulDistinguishedX0 f s) : IsDistinguishedX0 f s :=
  PowerSeries.IsMulDistinguished.toIsDistinguished h

/-- Over a multiplicatively-normed base ring the two notions of `X 0`-distinguished
coincide. -/
lemma isMulDistinguishedX0_iff_isDistinguishedX0 [NormMulClass R]
    {f : Restricted R c} {s : ℕ} :
    IsMulDistinguishedX0 f s ↔ IsDistinguishedX0 f s :=
  PowerSeries.isMulDistinguished_iff_isDistinguished

/-- Multivariate Weierstrass division with the project's `IsDistinguishedX0` hypothesis,
over a `NormMulClass` base — recovering the endpoint of `DivisibleRadius` (there proven for
complete nontrivially normed fields via Gauss extensions) with no extension machinery. -/
theorem weierstrassDivision_exists_of_normMulClass [NormMulClass R] [CompleteSpace R]
    {g : Restricted R c} {s : ℕ} (hg : IsDistinguishedX0 g s) (f : Restricted R c) :
    ∃ (q : Restricted R c) (r : Polynomial (Restricted R (Fin.tail c))),
      r.degree < s ∧ f = g * q + Polynomial.toMvRestrictedX0 c r :=
  weierstrassDivision_exists_of_isMulDistinguishedX0
    (isMulDistinguishedX0_iff_isDistinguishedX0.mpr hg) f

/-- Multivariate Weierstrass preparation with the project's `IsDistinguishedX0` hypothesis,
over a `NormMulClass` base. -/
theorem weierstrassPreparation_exists_of_normMulClass [NormMulClass R] [NormOneClass R]
    [CompleteSpace R] {g : Restricted R c} {s : ℕ} (hg : IsDistinguishedX0 g s) :
    ∃ (ω : Polynomial (Restricted R (Fin.tail c))) (e : Restricted R c), ω.Monic ∧
      ω.degree = s ∧ ‖Polynomial.toMvRestrictedX0 c ω‖ = (c 0) ^ s ∧ IsUnit e ∧
      g = e * Polynomial.toMvRestrictedX0 c ω := by
  obtain ⟨ω, e, hm, hd, hn, hu, he⟩ := weierstrassPreparation_exists_of_isMulDistinguishedX0
    (isMulDistinguishedX0_iff_isDistinguishedX0.mpr hg)
  exact ⟨ω, e, hm, hd, hn, hu.isUnit, he⟩

end MvPowerSeries.Restricted
