/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Extension
import PhD.TauCeti.Code.NewtonPolygons.Coeff.Polynomial

/-!
# Newton polygons under an isometric extension of the field

The compatible normed additive valuations of roadmap §2.2.7: for an ultrametric normed `K`-algebra
field `L`, the unnormalised member `ofNormAddVal L` restricts to `ofNormAddVal K`, and for `K`
complete and `L/K` algebraic the rational member normalised at `algebraMap K L π` restricts to the
one normalised at `π` (Layer 1, §1.5.1–§1.5.2). The polygon of `f` is therefore unchanged when `f`
is mapped to `L[X]` or `L⟦X⟧` and read with the extended valuation. ⚠ The discrete member is **not**
compatible in general: `normAddValZ L` restricts to `e(L/K)` times `normAddValZ K` (Layer 1,
§1.3.6), so the polygon for `ofNormAddValZ` is scaled by the ramification index.

Roadmap: §2.2.7 (the "isometric scalar extension" clause). Tau Ceti home:
`TauCeti/NumberTheory/NewtonPolygon/Extension.lean`.

## Main results

* `NormedField.NormedAddValuation.ofNormAddVal_algebraMap`,
  `NormedField.NormedAddValuation.ofNormAddValQ_algebraMap` — the compatibilities;
* `Polynomial.newtonPolygon_ofNormAddVal_map`, `PowerSeries.newtonPolygon_ofNormAddVal_map`,
  `Polynomial.newtonPolygon_ofNormAddValQ_map`, `PowerSeries.newtonPolygon_ofNormAddValQ_map` —
  invariance of the polygon.
-/

open NormedField Valuation

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]

namespace NormedField.NormedAddValuation

/-- The unnormalised member restricts along the extension (Layer 1, `normAddVal_algebraMap`). -/
theorem ofNormAddVal_algebraMap (x : K) : ofNormAddVal L (algebraMap K L x) = ofNormAddVal K x := by
  sorry

theorem ofNormAddVal_embed_eq : (ofNormAddVal L).embed = (ofNormAddVal K).embed := by sorry

section Algebraic

variable [CompleteSpace K] [Algebra.IsAlgebraic K L] (π : K) [(valuation (K := K)).IsCommensurable π]

/-- The rational member normalised at `π` restricts along an algebraic extension of a complete
field (Layer 1, `normAddValQ_algebraMap`). -/
theorem ofNormAddValQ_algebraMap (x : K) :
    ofNormAddValQ L (algebraMap K L π) (algebraMap K L x) = ofNormAddValQ K π x := by sorry

theorem ofNormAddValQ_embed_eq :
    (ofNormAddValQ L (algebraMap K L π)).embed = (ofNormAddValQ K π).embed := by sorry

end Algebraic

end NormedField.NormedAddValuation

open NormedField.NormedAddValuation

/-- **The polygon is unchanged under an isometric extension**, for the unnormalised member. -/
theorem Polynomial.newtonPolygon_ofNormAddVal_map (f : Polynomial K) :
    Polynomial.newtonPolygon (ofNormAddVal L) (f.map (algebraMap K L)) =
      Polynomial.newtonPolygon (ofNormAddVal K) f := by sorry

/-- **The polygon is unchanged under an isometric extension**, for the unnormalised member. -/
theorem PowerSeries.newtonPolygon_ofNormAddVal_map (f : PowerSeries K) :
    PowerSeries.newtonPolygon (ofNormAddVal L) (PowerSeries.map (algebraMap K L) f) =
      PowerSeries.newtonPolygon (ofNormAddVal K) f := by sorry

section Algebraic

variable [CompleteSpace K] [Algebra.IsAlgebraic K L] (π : K) [(valuation (K := K)).IsCommensurable π]

/-- **The polygon is unchanged under an algebraic extension of a complete field**, for the rational
member normalised at `π`. -/
theorem Polynomial.newtonPolygon_ofNormAddValQ_map (f : Polynomial K) :
    Polynomial.newtonPolygon (ofNormAddValQ L (algebraMap K L π)) (f.map (algebraMap K L)) =
      Polynomial.newtonPolygon (ofNormAddValQ K π) f := by sorry

/-- **The polygon is unchanged under an algebraic extension of a complete field**, for the rational
member normalised at `π`. -/
theorem PowerSeries.newtonPolygon_ofNormAddValQ_map (f : PowerSeries K) :
    PowerSeries.newtonPolygon (ofNormAddValQ L (algebraMap K L π))
        (PowerSeries.map (algebraMap K L) f) =
      PowerSeries.newtonPolygon (ofNormAddValQ K π) f := by sorry

end Algebraic
