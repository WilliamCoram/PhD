import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Reduction
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

open NormedRing IsLocalRing Subring

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ ι : Type*} [Finite σ] [Fintype ι]

example : IsNoetherianRing (ResidueField (unitClosedBall K)) := inferInstance
example : IsNoetherianRing (MvPolynomial σ (ResidueField (unitClosedBall K))) := inferInstance
example : IsNoetherian (MvPolynomial σ (ResidueField (unitClosedBall K)))
    (ι → MvPolynomial σ (ResidueField (unitClosedBall K))) := inferInstance
