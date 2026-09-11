/-
The project root module.

`lake exe checkdecls` (run by the blueprint CI on `blueprint/lean_decls`) resolves the
`\lean{…}` references of the blueprint against the environment obtained by importing this
module, so every area the blueprint cites must be reachable from here.  `PhD/Test/` and
`PhD/LegacyCode/` are deliberately excluded: they are scratch and history, and still contain
`sorry`.
-/

-- Restricted power series, Gauss norms, Weierstrass division and preparation
import PhD.ForMathlib.RingTheory.MvPolynomial.GaussNorm
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Complete
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Iso
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.MulWeierstrass
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.PowerBounded
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Residue
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Units
import PhD.ForMathlib.RingTheory.Polynomial.GaussNorm
import PhD.ForMathlib.RingTheory.PowerSeries.GaussNorm
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Complete
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassPrep

-- Newton polygons
import PhD.NewtonPolygons.FirstBreak
import PhD.NewtonPolygons.OfSlopes
import PhD.NewtonPolygons.PolynomialRoots
import PhD.NewtonPolygons.PowerSeriesZeros
import PhD.NewtonPolygons.Product
import PhD.NewtonPolygons.RadiusOfConvergence

-- Compact operators and Fredholm theory
import PhD.TateFredholm.«04_TateAlgebra»
import PhD.TateFredholm.«06_Slopes»
import PhD.TateFredholm.«08_BaseChange»
import PhD.TateFredholm.«09_Riesz»

-- Quaternionic modular forms
import PhD.QMF.«04_Finiteness»
import PhD.QMF.«04_Level»
import PhD.QMF.Weight.«07_Quaternionic»
import PhD.QMF.Weight.«08_BaseChange»
import PhD.QMF.Weight.«08_HeckeAlgebra»
import PhD.QMF.Weight.«08_Pr»
import PhD.QMF.Weight.«08_Slopes»

-- The Jacobs case
import PhD.JacobsSlash.«4_SlopeReading»
import PhD.JacobsSlash.«5_EigenSlopes»
import PhD.JacobsSlash.U3.«2_LevelTopology»
import PhD.JacobsSlash.U3.«10_Eigenforms»

-- Entire series, Coleman's resultant and the Riesz--Coleman decomposition
import PhD.TateFredholm.«00_Charpoly»
import PhD.TateFredholm.«01_CharpolyPairing»
import PhD.TateFredholm.«06_TwoSidedBound»
import PhD.TateFredholm.«06_Unitriangular»
import PhD.TateFredholm.«07_Conjugation»
import PhD.TateFredholm.«08_BlockMap»
import PhD.TateFredholm.«11_SlopeFactor»
import PhD.TateFredholm.«12_RieszColeman»

-- The Liu--Wan--Xiao halo: the estimate, the model seam and the slope theorems
import PhD.LWX.«05_AtkinLehner»
import PhD.LWX.«05_TateRiesz»
import PhD.LWX.«08_SlopeGrowth»
import PhD.LWX.«13_SlopesSeam»
import PhD.NewtonPolygons.RootFaces
import PhD.TateFredholm.«10_NewtonSlopes»
import PhD.TateFredholm.«13_FiniteFactor»

-- The theta layer and the Step I/III skeletons (`.mathlib-quality/lwx-theta/`).
-- `Theta` and `AtkinLehnerInst` still carry five `sorry`s whose statements are known to be
-- **false as written** (the finite part `ν` must be deleted); see the `⚠` notes in those files
-- and `.mathlib-quality/lwx-theta/b2_log.jsonl`.
import PhD.LWX.«07_ConjChar»
import PhD.LWX.«07_Degrees»
import PhD.LWX.«11_Theta»
import PhD.LWX.«12_StepOne»
import PhD.LWX.«13_AtkinLehnerInst»

-- Bol's identity and the repaired theta equivariance (tranche 4 of the `lwx-theta` board).
import PhD.LWX.«12_Bol»

-- Steps I and III of [LWX, Thm 1.3] on the corrected foundation (tranches 5–7 of `lwx-theta`):
-- skeletons, `sorry` only.
import PhD.LWX.«14_Touching»
import PhD.LWX.«15_ClassicalPoint»
import PhD.LWX.«15_StepThree»
-- Board `lwx-theta-h2`: hypothesis H2 discharged, and the theta target at the classical points.
import PhD.LWX.«16_TargetPoint»
import PhD.LWX.«16_ThetaExact»
import PhD.LWX.«17_DegreeFormula»
-- Board `lwx-h1`: hypothesis H1 (Atkin–Lehner) from the classical shapes and the adelic data
-- (complete, sorry-free).
import PhD.LWX.«10_AtkinLehnerLocal»
import PhD.LWX.«15_SymPow»
import PhD.LWX.«17_NebChar»
import PhD.LWX.«18_AtkinLehnerMap»
import PhD.LWX.«19_AtkinLehnerIdentity»
-- Board `lwx-conductor`: Step I / H1 at conductor `p^{h+1}` (level `h ≥ 1`) and the slope
-- reflection feeding [LWX, Thm 1.5]'s second half — complete, sorry-free.
import PhD.LWX.«11_AtkinLehnerLocalH»
import PhD.LWX.«15_TouchingH»
import PhD.LWX.«17_ClassicalPointH»
import PhD.LWX.«18_TargetPointH»
import PhD.LWX.«19_NebCharH»
import PhD.LWX.«20_AtkinLehnerMapH»
import PhD.LWX.«21_AtkinLehnerIdentityH»
import PhD.LWX.«22_AtkinLehnerFamily»
import PhD.LWX.«23_ConductorSlopes»
-- Board `lwx-degrees`: the degrees of [LWX, Thm 1.3] at every classical weight and
-- [LWX, Cor 1.4] (periodicity modulo `ϕ(q)/2`) — complete, sorry-free.
import PhD.LWX.«24_DegreePeriodicity»
