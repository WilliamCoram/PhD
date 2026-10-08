import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.PowerBounded
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm.FunctionAlgebra

open Affinoid

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A] {ι : Type*} [Fintype ι] (𝔭 : ι → Ideal A)

example (hA : IsAffinoidAlgebra K A) (hcont : Continuous fun f : A ↦ fun i ↦ Ideal.Quotient.mk (𝔭 i) f)
    (hinj : Function.Injective fun f : A ↦ fun i ↦ Ideal.Quotient.mk (𝔭 i) f)
    (hcl : IsClosed (Set.range fun f : A ↦ fun i ↦ Ideal.Quotient.mk (𝔭 i) f)) : True := by
  haveI : ∀ i, IsClosed ((𝔭 i : Ideal A) : Set A) := fun i ↦ hA.isClosed_ideal (𝔭 i)
  let π : A →L[K] (∀ i, A ⧸ 𝔭 i) :=
    ⟨LinearMap.pi fun i ↦ (Ideal.Quotient.mkₐ K (𝔭 i)).toLinearMap, hcont⟩
  obtain ⟨c, hc⟩ := π.antilipschitz_of_injective_of_isClosed_range hinj hcl
  have := hc.le_mul_dist
  trivial
