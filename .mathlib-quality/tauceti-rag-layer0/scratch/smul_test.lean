import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Distinguished

open Affinoid

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {n : ℕ}

example (M : Type*) [AddCommGroup M] [Module (TateAlgebra K (n + 1)) M]
    (a b : TateAlgebra K (n + 1)) (m : M) : (a * b) • m = a • b • m := mul_smul a b m

example (M : Type*) [AddCommGroup M] [Module (TateAlgebra K (n + 1)) M]
    (a b : TateAlgebra K (n + 1)) (m : M) : (a * b) • m = a • b • m := by
  letI : Module (TateAlgebra K n) M := Module.compHom M (TateAlgebra.ofTail K n)
  exact mul_smul a b m

example (M : Type*) [AddCommGroup M] [Module (TateAlgebra K (n + 1)) M]
    (a b : TateAlgebra K (n + 1)) (m : M) : (a * b) • m = a • b • m := by
  letI : Module (TateAlgebra K n) M := Module.compHom M (TateAlgebra.ofTail K n)
  exact smul_smul a b m |>.symm
