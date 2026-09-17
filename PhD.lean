/-
The project root module.

`lake exe checkdecls` (run by the blueprint CI on `blueprint/lean_decls`) resolves the
`\lean{…}` references of the blueprint against the environment obtained by importing this
module, so every area the blueprint cites must be reachable from here.  `PhD/Main/Test/` and
`PhD/Main/LegacyCode/` are deliberately excluded: they are scratch and history, and still contain
`sorry`.
-/

-- Restricted power series, Gauss norms, Weierstrass division and preparation
import PhD.Main.ForMathlib.RingTheory.MvPolynomial.GaussNorm
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Complete
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Iso
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.MulWeierstrass
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.PowerBounded
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Residue
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Units
import PhD.Main.ForMathlib.RingTheory.Polynomial.GaussNorm
import PhD.Main.ForMathlib.RingTheory.PowerSeries.GaussNorm
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.Complete
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassPrep

-- Newton polygons
import PhD.Main.NewtonPolygons.FirstBreak
import PhD.Main.NewtonPolygons.OfSlopes
import PhD.Main.NewtonPolygons.PolynomialRoots
import PhD.Main.NewtonPolygons.PowerSeriesZeros
import PhD.Main.NewtonPolygons.Product
import PhD.Main.NewtonPolygons.RadiusOfConvergence

-- Compact operators and Fredholm theory
import PhD.Main.TateFredholm.«04_TateAlgebra»
import PhD.Main.TateFredholm.«06_Slopes»
import PhD.Main.TateFredholm.«08_BaseChange»
import PhD.Main.TateFredholm.«09_Riesz»

-- Quaternionic modular forms
import PhD.Main.QMF.«04_Finiteness»
import PhD.Main.QMF.«04_Level»
import PhD.Main.QMF.Weight.«07_Quaternionic»
import PhD.Main.QMF.Weight.«08_BaseChange»
import PhD.Main.QMF.Weight.«08_HeckeAlgebra»
import PhD.Main.QMF.Weight.«08_Pr»
import PhD.Main.QMF.Weight.«08_Slopes»

-- The Jacobs case
import PhD.Main.JacobsSlash.«4_SlopeReading»
import PhD.Main.JacobsSlash.«5_EigenSlopes»
import PhD.Main.JacobsSlash.U3.«2_LevelTopology»
import PhD.Main.JacobsSlash.U3.«10_Eigenforms»

-- Entire series, Coleman's resultant and the Riesz--Coleman decomposition
import PhD.Main.TateFredholm.«00_Charpoly»
import PhD.Main.TateFredholm.«01_CharpolyPairing»
import PhD.Main.TateFredholm.«06_TwoSidedBound»
import PhD.Main.TateFredholm.«06_Unitriangular»
import PhD.Main.TateFredholm.«07_Conjugation»
import PhD.Main.TateFredholm.«08_BlockMap»
import PhD.Main.TateFredholm.«11_SlopeFactor»
import PhD.Main.TateFredholm.«12_RieszColeman»

-- The Liu--Wan--Xiao halo: the estimate, the model seam and the slope theorems
import PhD.Main.LWX.«05_AtkinLehner»
import PhD.Main.LWX.«05_TateRiesz»
import PhD.Main.LWX.«08_SlopeGrowth»
import PhD.Main.LWX.«13_SlopesSeam»
import PhD.Main.NewtonPolygons.RootFaces
import PhD.Main.TateFredholm.«10_NewtonSlopes»
import PhD.Main.TateFredholm.«13_FiniteFactor»

-- The theta layer and the Step I/III skeletons (`.mathlib-quality/lwx-theta/`).
-- `Theta` and `AtkinLehnerInst` still carry five `sorry`s whose statements are known to be
-- **false as written** (the finite part `ν` must be deleted); see the `⚠` notes in those files
-- and `.mathlib-quality/lwx-theta/b2_log.jsonl`.
import PhD.Main.LWX.«07_ConjChar»
import PhD.Main.LWX.«07_Degrees»
import PhD.Main.LWX.«11_Theta»
import PhD.Main.LWX.«12_StepOne»
import PhD.Main.LWX.«13_AtkinLehnerInst»

-- Bol's identity and the repaired theta equivariance (tranche 4 of the `lwx-theta` board).
import PhD.Main.LWX.«12_Bol»

-- Steps I and III of [LWX, Thm 1.3] on the corrected foundation (tranches 5–7 of `lwx-theta`):
-- skeletons, `sorry` only.
import PhD.Main.LWX.«14_Touching»
import PhD.Main.LWX.«15_ClassicalPoint»
import PhD.Main.LWX.«15_StepThree»
-- Board `lwx-theta-h2`: hypothesis H2 discharged, and the theta target at the classical points.
import PhD.Main.LWX.«16_TargetPoint»
import PhD.Main.LWX.«16_ThetaExact»
import PhD.Main.LWX.«17_DegreeFormula»
-- Board `lwx-h1`: hypothesis H1 (Atkin–Lehner) from the classical shapes and the adelic data
-- (complete, sorry-free).
import PhD.Main.LWX.«10_AtkinLehnerLocal»
import PhD.Main.LWX.«15_SymPow»
import PhD.Main.LWX.«17_NebChar»
import PhD.Main.LWX.«18_AtkinLehnerMap»
import PhD.Main.LWX.«19_AtkinLehnerIdentity»
-- Board `lwx-conductor`: Step I / H1 at conductor `p^{h+1}` (level `h ≥ 1`) and the slope
-- reflection feeding [LWX, Thm 1.5]'s second half — complete, sorry-free.
import PhD.Main.LWX.«11_AtkinLehnerLocalH»
import PhD.Main.LWX.«15_TouchingH»
import PhD.Main.LWX.«17_ClassicalPointH»
import PhD.Main.LWX.«18_TargetPointH»
import PhD.Main.LWX.«19_NebCharH»
import PhD.Main.LWX.«20_AtkinLehnerMapH»
import PhD.Main.LWX.«21_AtkinLehnerIdentityH»
import PhD.Main.LWX.«22_AtkinLehnerFamily»
import PhD.Main.LWX.«23_ConductorSlopes»
-- Board `lwx-degrees`: the degrees of [LWX, Thm 1.3] at every classical weight and
-- [LWX, Cor 1.4] (periodicity modulo `ϕ(q)/2`) — complete, sorry-free.
import PhD.Main.LWX.«24_DegreePeriodicity»
-- Board `lwx-quaternion`: the Atkin–Lehner identity at every neat tame level (the tame central
-- operator), the determinant certificate from normalised representatives, and the adelic data for
-- a definite quaternion algebra over `ℚ`, with its headline theorems — complete, sorry-free.
import PhD.Main.TateFredholm.«02_CharpolyPairingZ»
import PhD.Main.LWX.«23_QuaternionData»
import PhD.Main.LWX.«25_QuaternionSlopes»
