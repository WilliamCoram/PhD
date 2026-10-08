/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Basic

/-!
# The module and algebra structures on restricted multivariate power series

`MvPowerSeries.Restricted R c` is a `K`-module for every semiring `K` acting on `R` through `R`
(`IsScalarTower K R R`), and a `K`-algebra for every `K`-algebra `R` when `R` is commutative. For
`K = R` these are the instances of mathlib4#42867 (`MvPowerSeries.instModuleRestricted`,
`MvPowerSeries.instAlgebraRestricted`), reproduced here on the restricted-series seam of
`Restricted/Basic.lean`; the general form is needed for `A⟨X⟩` over a normed `K`-algebra `A`
(BGR 3.7.1, 6.1.1/4). If that pull request lands, this file shrinks to the generalisation.

## Main results

* `MvPowerSeries.isRestricted.smul'`: scalars acting through `R` preserve restrictedness.
* `MvPowerSeries.Restricted.val_smul`: scalar multiplication is coefficientwise.
* `MvPowerSeries.Restricted.algebraMap_apply`: the structure map is `Restricted.C`.
* `MvPowerSeries.Restricted.algebraMap_eq_C_comp`: for a `K`-algebra `S`, the structure map
  `K → Restricted S c` is `Restricted.C` after `K → S`.
-/

namespace MvPowerSeries

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*}

omit [IsUltrametricDist R] in
/-- Scalars acting on the coefficients through the ring `R` preserve restrictedness. -/
lemma isRestricted.smul' {K : Type*} [Semiring K] [Module K R] [IsScalarTower K R R]
    (c : σ → ℝ) (k : K) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (k • f) := by
  rw [← smul_one_smul R k f]
  exact isRestricted.smul c _ hf

/-- `K`-module structure on `Restricted R c`, for every ring `K` acting on `R` through `R`; for
`K = R` this is the `R`-module structure of mathlib4#42867. As for polynomials, the general
instance is the only one, so that the `R`-module and `K`-algebra structures share their scalar
multiplication. -/
noncomputable instance (c : σ → ℝ) {K : Type*} [Semiring K] [Module K R]
    [IsScalarTower K R R] : Module K (Restricted R c) where
  smul k f := ⟨k • f.1, isRestricted.smul' c k f.2⟩
  one_smul f := Subtype.ext (one_smul K f.1)
  mul_smul r s f := Subtype.ext (mul_smul r s f.1)
  smul_zero r := Subtype.ext (smul_zero r)
  smul_add r f g := Subtype.ext (smul_add r f.1 g.1)
  add_smul r s f := Subtype.ext (add_smul r s f.1)
  zero_smul f := Subtype.ext (zero_smul K f.1)

instance (c : σ → ℝ) {K : Type*} [Semiring K] [Module K R] [IsScalarTower K R R] :
    IsScalarTower K R (Restricted R c) :=
  ⟨fun k r f ↦ Subtype.ext (smul_assoc k r f.1)⟩

section CommRing

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] (c : σ → ℝ)

/-- `Restricted S c` is a `K`-algebra for every `K` that `S` is an algebra over (through the
constants); for `K = S` this is the `S`-algebra structure of mathlib4#42867. -/
noncomputable instance {K : Type*} [CommSemiring K] [Algebra K S] : Algebra K (Restricted S c) :=
  Algebra.ofModule (fun r f g ↦ Subtype.ext (smul_mul_assoc r f.1 g.1))
    fun r f g ↦ Subtype.ext (mul_smul_comm r f.1 g.1)

end CommRing

namespace Restricted

variable (c : σ → ℝ)

@[simp]
lemma val_smul (r : R) (f : Restricted R c) : (r • f).1 = r • f.1 := rfl

lemma algebraMap_apply {S : Type*} [NormedCommRing S] [IsUltrametricDist S] (a : S) :
    algebraMap S (Restricted S c) a = C c a :=
  Restricted.ext <| by
    simp [Algebra.algebraMap_eq_smul_one, MvPowerSeries.smul_eq_C_mul]

lemma algebraMap_eq_C_comp {S K : Type*} [NormedCommRing S] [IsUltrametricDist S] [CommSemiring K]
    [Algebra K S] : algebraMap K (Restricted S c) = (C c).comp (algebraMap K S) := by
  refine RingHom.ext fun r ↦ Restricted.ext ?_
  change r • (1 : MvPowerSeries σ S) = MvPowerSeries.C (algebraMap K S r)
  rw [← algebraMap_smul S r, MvPowerSeries.smul_eq_C_mul, mul_one]

end Restricted

end MvPowerSeries
