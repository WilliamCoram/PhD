/-
The project root module.

`lake exe checkdecls` (run by the blueprint CI on `blueprint/lean_decls`) resolves the
`\lean{…}` references of the blueprint against the environment obtained by importing this
module, so every area the blueprint cites must be reachable from here.  `PhD/Test/` and
`PhD/LegacyCode/` are deliberately excluded: they are scratch and history, and still contain
`sorry`.
-/

-- Restricted power series, Gauss norms, Weierstrass division and preparation
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Complete
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Iso
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.PowerBounded
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Residue
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Units
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Complete
import PhD.ForMathlib.RingTheory.PowerSeries.GaussNorm
import PhD.ForMathlib.RingTheory.Polynomial.GaussNorm
import PhD.ForMathlib.RingTheory.MvPolynomial.GaussNorm
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassPrep
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.MulWeierstrass

-- Newton polygons
import PhD.NewtonPolygons.OfSlopes
import PhD.NewtonPolygons.PowerSeriesZeros
import PhD.NewtonPolygons.FirstBreak
import PhD.NewtonPolygons.RadiusOfConvergence
import PhD.NewtonPolygons.PolynomialRoots

-- Compact operators and Fredholm theory
import PhD.TateFredholm.Slopes
import PhD.TateFredholm.TateAlgebra
import PhD.TateFredholm.Riesz
import PhD.TateFredholm.BaseChange

-- Quaternionic modular forms
import PhD.QMF.Weight.Slopes
import PhD.QMF.Weight.HeckeAlgebra
import PhD.QMF.Weight.Pr
import PhD.QMF.Weight.BaseChange
import PhD.QMF.Weight.Quaternionic
import PhD.QMF.Level
import PhD.QMF.Finiteness

-- The Jacobs case
import PhD.JacobsSlash.U3.«10_Eigenforms»
import PhD.JacobsSlash.U3.«2_LevelTopology»
import PhD.JacobsSlash.«4_SlopeReading»
import PhD.JacobsSlash.«5_EigenSlopes»
