import PhD.ToPR.NewtonPolygon
import PhD.ToPR.GaussNorm
import Mathlib.RingTheory.Valuation.Basic

namespace NewtonPolygon

open Valuation

-- I think the idea should be to start with the additive valuation
-- as for both p-adics the norm and mulVal correspond to first the additive valuation

-- the idea is then to specialize for ANY corresponding multiplicative valuation...
-- as we can then use either the padicNormE or mulValuation
