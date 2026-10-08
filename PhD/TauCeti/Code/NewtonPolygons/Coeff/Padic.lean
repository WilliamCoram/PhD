/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Padic
import PhD.TauCeti.Code.NewtonPolygons.Coeff.NormedAddValuation

/-!
# The normed additive valuation of `ℚ_p`

`Padic.normedAddValuation p : NormedAddValuation ℚ_[p] ℤ` is the discrete member of Layer 1's
family at the uniformiser `p`: the additive valuation is `Padic.addValuation` (Layer 1,
`normAddValZ_padic`), the embedding is `Int.cast`, the base is `p`, and `v p = 1`. This is the
valuation "over `ℚ_p` with `v p = 1`" of the roadmap's examples and acceptance examples: with it the
points of a polygon have integer heights and the slopes of a polynomial are rational numbers.

Roadmap: Layer 2 introduction and Examples. Tau Ceti home:
`TauCeti/NumberTheory/Padics/NewtonPolygon.lean`.
-/

open NormedField

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- **The normed additive valuation of `ℚ_p` with `v p = 1`.** -/
noncomputable def normedAddValuation : NormedAddValuation ℚ_[p] ℤ :=
  NormedAddValuation.ofNormAddValZ ℚ_[p] isUniformizer_p

/-- The additive valuation is Mathlib's `Padic.addValuation`. -/
theorem normedAddValuation_apply (x : ℚ_[p]) : normedAddValuation p x = Padic.addValuation x := by
  sorry

@[simp] theorem normedAddValuation_embed : (normedAddValuation p).embed = Int.castAddHom ℝ := by
  sorry

theorem normedAddValuation_embed_apply (n : ℤ) : (normedAddValuation p).embed n = n := by sorry

@[simp] theorem normedAddValuation_base : (normedAddValuation p).base = p := by sorry

/-- `v p = 1`. -/
theorem normedAddValuation_natCast_prime : normedAddValuation p (p : ℚ_[p]) = 1 := by sorry

/-- The unnormalised member is `log p` times the normalised one (roadmap §2.2.8). -/
theorem scale_normedAddValuation_ofNormAddVal :
    (normedAddValuation p).scale (NormedAddValuation.ofNormAddVal ℚ_[p]) = Real.log p := by sorry

end Padic
