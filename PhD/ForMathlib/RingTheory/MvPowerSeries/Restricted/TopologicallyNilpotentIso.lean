/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.PowerBoundedIso

/-! # The topological nilradical of a Tate algebra, coefficientwise

Let `R` be a normed commutative ring with ultrametric distance and multiplicative norm, and
write `R°` for its power-bounded subring and `T°` for the power-bounded subring of the
multivariate Tate algebra `Restricted R 1`.  Every topologically nilpotent element of the Tate
algebra is power-bounded, so the topologically nilpotent elements form the topological
nilradical, an ideal of `T°`.  This file identifies it coefficientwise: a power-bounded
restricted power series is topologically nilpotent if and only if all its coefficients are.

Unlike the power-bounded elements, the topologically nilpotent elements do not form a ring, so
the identification is an ideal correspondence rather than a ring isomorphism: under
`MvPowerSeries.Restricted.powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1`, the topological
nilradical of `T°` corresponds to the ideal of restricted power series over `R°` all of whose
coefficients lie in the topological nilradical of `R°`.

* `MvPowerSeries.Restricted.coeffIdeal c I`: the restricted power series all of whose
  coefficients lie in an ideal `I`, as an ideal of `Restricted S c` (any radii `c`).
* `MvPowerSeries.Restricted.mem_topologicalNilradical_iff_forall_isTopologicallyNilpotent_coeff`:
  membership in the topological nilradical of `T°` is coefficientwise.
* `MvPowerSeries.Restricted.map_powerBoundedEquiv_topologicalNilradical`: the image of the
  topological nilradical of `T°` under `powerBoundedEquiv` is
  `coeffIdeal 1 (PowerBounded.topologicalNilradical ℤ)`, with the `comap` version
  `comap_powerBoundedEquiv_coeffIdeal` and the membership version
  `powerBoundedEquiv_mem_coeffIdeal_iff`.
-/

open Filter PowerBounded
open scoped Topology

namespace MvPowerSeries.Restricted

section CoeffIdeal

variable {S : Type*} [NormedRing S] [IsUltrametricDist S] {σ : Type*} (c : σ → ℝ) (I : Ideal S)

/-- The restricted power series all of whose coefficients lie in an ideal `I`, as an ideal of
`Restricted S c`. -/
def coeffIdeal : Ideal (Restricted S c) where
  carrier := {f | ∀ t, coeff t f.1 ∈ I}
  add_mem' hf hg t := by
    rw [val_add, map_add]
    exact I.add_mem (hf t) (hg t)
  zero_mem' t := by
    rw [val_zero, map_zero]
    exact I.zero_mem
  smul_mem' g f hf t := by
    classical
    rw [smul_eq_mul, val_mul, MvPowerSeries.coeff_mul]
    exact I.sum_mem fun p _ ↦ I.mul_mem_left _ (hf p.2)

@[simp]
lemma mem_coeffIdeal {f : Restricted S c} : f ∈ coeffIdeal c I ↔ ∀ t, coeff t f.1 ∈ I :=
  Iff.rfl

end CoeffIdeal

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {σ : Type*}

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (MvPowerSeries.Restricted R (1 : σ → ℝ)) (S := ℤ)

/-- A power-bounded restricted power series lies in the topological nilradical of `T°` if and
only if all its coefficients are topologically nilpotent. -/
theorem mem_topologicalNilradical_iff_forall_isTopologicallyNilpotent_coeff (f : ↥T°) :
    f ∈ PowerBounded.topologicalNilradical ℤ ↔ ∀ t, IsTopologicallyNilpotent (coeff t f.1.1) :=
  (mem_topologicalNilradical_iff ℤ f).trans
    (isTopologicallyNilpotent_iff_forall_isTopologicallyNilpotent_coeff 1 fun _ ↦ rfl)

section Equiv

variable [NormOneClass R] [NeBot (𝓝[≠] (0 : R))]

/-- Under the isomorphism `powerBoundedEquiv : ↥T° ≃+* Restricted R° 1`, membership in the
ideal of series with topologically nilpotent coefficients corresponds to membership in the
topological nilradical. -/
theorem powerBoundedEquiv_mem_coeffIdeal_iff (f : ↥T°) :
    powerBoundedEquiv f ∈ coeffIdeal 1 (PowerBounded.topologicalNilradical (R := R) ℤ) ↔
      f ∈ PowerBounded.topologicalNilradical ℤ := by
  rw [mem_coeffIdeal, mem_topologicalNilradical_iff_forall_isTopologicallyNilpotent_coeff]
  refine forall_congr' fun t ↦ ?_
  rw [mem_topologicalNilradical_iff, coe_coeff_powerBoundedEquiv]

/-- The ideal of series with topologically nilpotent coefficients pulls back to the topological
nilradical along `powerBoundedEquiv`. -/
theorem comap_powerBoundedEquiv_coeffIdeal :
    (coeffIdeal 1 (PowerBounded.topologicalNilradical (R := R) ℤ)).comap
        (powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° (1 : σ → ℝ)) =
      PowerBounded.topologicalNilradical ℤ := by
  ext f
  rw [Ideal.mem_comap]
  exact powerBoundedEquiv_mem_coeffIdeal_iff f

/-- **The topological nilradical of the Tate algebra consists of the series with topologically
nilpotent coefficients**: its image under `powerBoundedEquiv : ↥T° ≃+* Restricted R° 1` is
`coeffIdeal 1 (PowerBounded.topologicalNilradical ℤ)`. -/
theorem map_powerBoundedEquiv_topologicalNilradical :
    (PowerBounded.topologicalNilradical ℤ).map
        (powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° (1 : σ → ℝ)) =
      coeffIdeal 1 (PowerBounded.topologicalNilradical (R := R) ℤ) := by
  rw [← comap_powerBoundedEquiv_coeffIdeal]
  exact Ideal.map_comap_of_surjective _ powerBoundedEquiv.surjective _

end Equiv

end MvPowerSeries.Restricted
