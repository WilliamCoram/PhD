/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.TopologicallyNilpotentIso
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.PowerBoundedIso

/-! # The topological nilradical of a Tate algebra, coefficientwise

Let `R` be a normed commutative ring with ultrametric distance and multiplicative norm, and
write `R°` for its power-bounded subring and `T°` for the power-bounded subring of the Tate
algebra `Restricted R 1`.  This file restates the coefficientwise identification of the
topological nilradical of `T°` from `MvPowerSeries.Restricted` with `ℕ`-indexed coefficients:
under `PowerSeries.Restricted.powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1`, the topological
nilradical of `T°` corresponds to the ideal of restricted power series over `R°` all of whose
coefficients lie in the topological nilradical of `R°`.

* `PowerSeries.Restricted.coeffIdeal c I`: the restricted power series all of whose
  coefficients lie in an ideal `I`, as an ideal of `Restricted S c` (any radius `c`).
* `PowerSeries.Restricted.mem_topologicalNilradical_iff_forall_isTopologicallyNilpotent_coeff`:
  membership in the topological nilradical of `T°` is coefficientwise.
* `PowerSeries.Restricted.map_powerBoundedEquiv_topologicalNilradical`: the image of the
  topological nilradical of `T°` under `powerBoundedEquiv` is
  `coeffIdeal 1 (PowerBounded.topologicalNilradical ℤ)`, with the `comap` version
  `comap_powerBoundedEquiv_coeffIdeal` and the membership version
  `powerBoundedEquiv_mem_coeffIdeal_iff`.
-/

open Filter PowerBounded
open scoped Topology

namespace PowerSeries.Restricted

section CoeffIdeal

variable {S : Type*} [NormedRing S] [IsUltrametricDist S] (c : ℝ) (I : Ideal S)

/-- The restricted power series all of whose coefficients lie in an ideal `I`, as an ideal of
`Restricted S c`; inherited from the multivariate case. -/
def coeffIdeal : Ideal (Restricted S c) :=
  MvPowerSeries.Restricted.coeffIdeal (fun _ ↦ c) I

@[simp]
lemma mem_coeffIdeal {f : Restricted S c} : f ∈ coeffIdeal c I ↔ ∀ n, coeff n f.1 ∈ I :=
  ⟨fun h n ↦ h (Finsupp.single () n), fun h t ↦ by
    obtain ⟨n, rfl⟩ : ∃ n, t = Finsupp.single () n := ⟨t (), Finsupp.unique_single t⟩
    exact h n⟩

end CoeffIdeal

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R]

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)

/-- A power-bounded restricted power series lies in the topological nilradical of `T°` if and
only if all its coefficients are topologically nilpotent. -/
theorem mem_topologicalNilradical_iff_forall_isTopologicallyNilpotent_coeff (f : ↥T°) :
    f ∈ PowerBounded.topologicalNilradical ℤ ↔ ∀ n, IsTopologicallyNilpotent (coeff n f.1.1) :=
  (MvPowerSeries.Restricted.mem_topologicalNilradical_iff_forall_isTopologicallyNilpotent_coeff
    f).trans
    ⟨fun h n ↦ h (Finsupp.single () n), fun h t ↦ by
      obtain ⟨n, rfl⟩ : ∃ n, t = Finsupp.single () n := ⟨t (), Finsupp.unique_single t⟩
      exact h n⟩

section Equiv

variable [NormOneClass R] [NeBot (𝓝[≠] (0 : R))]

/-- Under the isomorphism `powerBoundedEquiv : ↥T° ≃+* Restricted R° 1`, membership in the
ideal of series with topologically nilpotent coefficients corresponds to membership in the
topological nilradical. -/
theorem powerBoundedEquiv_mem_coeffIdeal_iff (f : ↥T°) :
    powerBoundedEquiv f ∈ coeffIdeal 1 (PowerBounded.topologicalNilradical (R := R) ℤ) ↔
      f ∈ PowerBounded.topologicalNilradical ℤ :=
  MvPowerSeries.Restricted.powerBoundedEquiv_mem_coeffIdeal_iff f

/-- The ideal of series with topologically nilpotent coefficients pulls back to the topological
nilradical along `powerBoundedEquiv`. -/
theorem comap_powerBoundedEquiv_coeffIdeal :
    (coeffIdeal 1 (PowerBounded.topologicalNilradical (R := R) ℤ)).comap
        (powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1) =
      PowerBounded.topologicalNilradical ℤ :=
  MvPowerSeries.Restricted.comap_powerBoundedEquiv_coeffIdeal

/-- **The topological nilradical of the Tate algebra consists of the series with topologically
nilpotent coefficients**: its image under `powerBoundedEquiv : ↥T° ≃+* Restricted R° 1` is
`coeffIdeal 1 (PowerBounded.topologicalNilradical ℤ)`. -/
theorem map_powerBoundedEquiv_topologicalNilradical :
    (PowerBounded.topologicalNilradical ℤ).map
        (powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1) =
      coeffIdeal 1 (PowerBounded.topologicalNilradical (R := R) ℤ) :=
  MvPowerSeries.Restricted.map_powerBoundedEquiv_topologicalNilradical

end Equiv

end PowerSeries.Restricted
