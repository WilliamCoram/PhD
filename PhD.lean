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
import PhD.NewtonPolygons.Product

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

-- Entire series, Coleman's resultant and the Riesz--Coleman decomposition
import PhD.TateFredholm.RieszColeman
import PhD.TateFredholm.SlopeFactor
import PhD.TateFredholm.Charpoly
import PhD.TateFredholm.CharpolyPairing
import PhD.TateFredholm.Unitriangular
import PhD.TateFredholm.TwoSidedBound
import PhD.TateFredholm.Conjugation
import PhD.TateFredholm.BlockMap

-- The Liu--Wan--Xiao halo: the estimate, the model seam and the slope theorems
import PhD.LWX.SlopesSeam
import PhD.LWX.SlopeGrowth
import PhD.LWX.TateRiesz
import PhD.LWX.AtkinLehner
import PhD.TateFredholm.FiniteFactor
import PhD.NewtonPolygons.RootFaces
import PhD.TateFredholm.NewtonSlopes

-- The theta layer and the Step I/III skeletons (`.mathlib-quality/lwx-theta/`).
-- `Theta` and `AtkinLehnerInst` still carry five `sorry`s whose statements are known to be
-- **false as written** (the finite part `ν` must be deleted); see the `⚠` notes in those files
-- and `.mathlib-quality/lwx-theta/b2_log.jsonl`.
import PhD.LWX.ConjChar
import PhD.LWX.Theta
import PhD.LWX.StepOne
import PhD.LWX.Degrees
import PhD.LWX.AtkinLehnerInst

-- Bol's identity and the repaired theta equivariance (tranche 4 of the `lwx-theta` board).
import PhD.LWX.Bol

-- Steps I and III of [LWX, Thm 1.3] on the corrected foundation (tranches 5–7 of `lwx-theta`):
-- skeletons, `sorry` only.
import PhD.LWX.Touching
import PhD.LWX.ClassicalPoint
import PhD.LWX.StepThree
-- Board `lwx-theta-h2`: hypothesis H2 discharged, and the theta target at the classical points.
import PhD.LWX.ThetaExact
import PhD.LWX.TargetPoint
import PhD.LWX.DegreeFormula
-- Board `lwx-h1`: hypothesis H1 (Atkin–Lehner) from the classical shapes and the adelic data
-- (complete, sorry-free).
import PhD.LWX.SymPow
import PhD.LWX.NebChar
import PhD.LWX.AtkinLehnerLocal
import PhD.LWX.AtkinLehnerMap
import PhD.LWX.AtkinLehnerIdentity
