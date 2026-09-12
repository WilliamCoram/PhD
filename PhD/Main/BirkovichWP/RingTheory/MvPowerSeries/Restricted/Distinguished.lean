/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Iso
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.X0Polynomial
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.Distinguished

/-! # Distinguished multivariate restricted power series (in `X 0`)

A restricted multivariate power series is **distinguished in the variable `X 0` of degree
`s`** when its image under the splitting isomorphism
`MvPowerSeries.Restricted.finSuccEquiv` — a univariate restricted series over the Tate
algebra `T = Restricted R (Fin.tail c)` in the remaining variables — is distinguished of
degree `s` at parameter `c 0`.  This is the `IsDistinguished`-based (unit leading
coefficient) notion; the transport dictionary it uses lives in
`MvPowerSeries.Restricted.X0Polynomial`.

## Main definitions

* `MvPowerSeries.Restricted.IsDistinguishedX0`: distinguished in `X 0` of degree `s`.

## Main results

* `MvPowerSeries.Restricted.isDistinguishedX0_toMvRestrictedX0_of_monic`: a monic
  `X 0`-polynomial of degree `s` with `‖ω‖ = (c 0) ^ s` is distinguished in `X 0`.
-/

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {n : ℕ}
  {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

/-- `f` is **distinguished in the variable `X 0` of degree `s`**: its image under the
splitting isomorphism `finSuccEquiv` — a univariate restricted series over the Tate algebra
`Restricted R (Fin.tail c)` of the remaining variables — is distinguished of degree `s` at
parameter `c 0`. -/
def IsDistinguishedX0 (f : Restricted R c) (s : ℕ) : Prop :=
  PowerSeries.IsDistinguished norm (c 0) (finSuccEquiv R c f).1 s

/-- A pulled-back univariate series is distinguished in `X 0` iff it is distinguished at
parameter `c 0`. -/
lemma isDistinguishedX0_finSuccEquiv_symm
    (x : PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0)) (s : ℕ) :
    IsDistinguishedX0 ((finSuccEquiv R c).symm x) s ↔
      PowerSeries.IsDistinguished norm (c 0) x.1 s := by
  unfold IsDistinguishedX0
  rw [RingEquiv.apply_symm_apply]

/-- A monic `X 0`-polynomial of degree `s` with `‖ω‖ = (c 0) ^ s` is distinguished in `X 0`
of degree `s`. -/
lemma isDistinguishedX0_toMvRestrictedX0_of_monic [NormOneClass R]
    {ω : Polynomial (Restricted R (Fin.tail c))} {s : ℕ} (ωm : ω.Monic) (ωd : ω.degree = s)
    (ωn : ‖Polynomial.toMvRestrictedX0 c ω‖ = (c 0) ^ s) :
    IsDistinguishedX0 (Polynomial.toMvRestrictedX0 c ω) s :=
  (isDistinguishedX0_finSuccEquiv_symm (Polynomial.toRestricted (c 0) ω) s).mpr
    (PowerSeries.Restricted.isDistinguished_toRestricted_of_monic ωm ωd
      (by rw [← Polynomial.norm_toMvRestrictedX0]; exact ωn))

end MvPowerSeries.Restricted
