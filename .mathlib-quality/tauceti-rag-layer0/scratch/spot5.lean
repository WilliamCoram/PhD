import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples

/-! Spot check: the two §0.4 statements about the Tate algebra follow from the general ones in the
planned shape. -/

universe u

open MvPowerSeries MvPowerSeries.Restricted Affinoid Affinoid.TateAlgebra

example (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] (n : ℕ) :
    letI := IsFractionRing.normedField (TateAlgebra K n) (FractionRing (TateAlgebra K n))
    IsWeaklyStable (FractionRing (TateAlgebra K n)) := by
  letI := IsFractionRing.normedField (TateAlgebra K n) (FractionRing (TateAlgebra K n))
  haveI := IsFractionRing.isUltrametricDist (TateAlgebra K n) (FractionRing (TateAlgebra K n))
  exact isWeaklyStable_of_perfectField _

example (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] (n : ℕ) :
    IsJapaneseRing (TateAlgebra K n) :=
  isJapaneseRing_of_perfectField _
