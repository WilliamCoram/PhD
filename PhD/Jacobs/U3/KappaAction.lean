/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3.Setting
import PhD.Jacobs.U3Data

/-!
# The weight-`κ` action of `Σ₁(9)` on the Tate algebra

[Jacobs, Ch. 1 §1.5 Definition 1.27]:

> "The weight κ action of γ = (a b; c d) ∈ Σ_ν on A_p is given by the continuous
> C_p-linear extension of the map sending z^k ↦ κ(cz + d)/(cz + d)^{2ν} ((az+b)/(cz+d))^k"

and [Jacobs, p. 29 + Proposition 2.6]: on the matrices in play (`c ≡ 0`, `d ≡ 1 mod 9`)
the character is `κ(cx+d) = (cx+d)^t = exp₃(t·log(cx+d))`, and

> "The generating function of the operator |κ (a b; c d) is given by
> κ(cx + d) / ((cx + d)(cx + d − axy − by))."

**Design** (records the AG-B glue noted in `.mathlib-quality/jacobs/decomposition.md`):
the action of a matrix is *defined* as `Jacobs.ofGenFun` of *`Jacobs.weightGenFun`* — the
transcription `PhD.Jacobs.U3Data` already uses — so Proposition 2.6 holds by construction
(`matrixCoeff_kappaOp` below is `Jacobs.matrixCoeff_ofGenFun`), and the mathematical
content moves to where it belongs: the action laws (`kappaOp_mul`), Jacobs's "easy check
that `|κ` is a right-action" (Def 1.27) made honest.  The model of the Tate algebra `A₃`
is `TateFredholm`'s coefficient space `c(ℕ, K₃)` (basis `e_k ↔ z^k`).

The library acts on the *left* (`Sigma0` conventions); a left-form matrix `g` acts as
Jacobs's `|κ (adj g)`, and the adjugate anti-homomorphism turns the right-action law into
the left one.  `weightGenFun` takes the Jacobs-form (right-convention) matrix, so the
translation appears below as `adjParams`.
-/

open TateFredholm Jacobs
open scoped TateFredholm

namespace Jacobs.U3

variable (t : K₃) (ht : ‖t‖ < 1)

/-- The Jacobs-form parameter matrix of a left-form `g`: the adjugate `(d −b; −c a)`,
read as the `2×2` array over `K₃` that `Jacobs.weightGenFun` consumes. -/
noncomputable def adjParams (g : Matrix (Fin 2) (Fin 2) K₃) : Matrix (Fin 2) (Fin 2) K₃ :=
  Matrix.adjugate g

/-- Integrality of the weight generating function for `g ∈ Σ₁(9)` ([Jacobs, p. 29]:
"exp₃(t log(cx + d)) converges to an element of `𝒪₃[[x]]`", extended over the geometric
factor): every coefficient has norm `≤ 1`.

NOT the `‖3‖ ^ m` row decay: that stronger bound is false for general `g ∈ Σ₁(9)`
(`g = 1` gives `weightGenFun = 1/(1−xy)`, with `(m,m)`-coefficient `1`) and is special
to the `η`-composed block matrices ([Jacobs, Lemma 2.7] = `Jacobs.norm_coeff_h02_le` and
AG-W's `rowInt` family) — recorded adversarial finding, `decomposition.md` L5.2. -/
theorem norm_coeff_weightGenFun_le_one (g : Sigma1) (m r : ℕ) :
    ‖MvPowerSeries.coeff (idx m r) (weightGenFun t (adjParams g.1))‖ ≤ 1 := sorry

/-- Column decay: each column of the weight generating function is a Tate-algebra
element — the action of `g` sends `z^r` into `A₃` ([Jacobs, (2.1.3)]: "`= ∑ a_m^{(r)} z^m`
with `a_m^{(r)} ∈ ℂ₃`", coefficients tending to `0`).  Together with
`norm_coeff_weightGenFun_le_one` this is exactly the input pair of `Jacobs.ofGenFun`. -/
theorem tendsto_coeff_weightGenFun (g : Sigma1) (r : ℕ) :
    Filter.Tendsto (fun m => MvPowerSeries.coeff (idx m r) (weightGenFun t (adjParams g.1)))
      Filter.atTop (nhds 0) := sorry

/-- The weight-`κ` action of a single `g ∈ Σ₁(9)` on the Tate algebra `c(ℕ, K₃)`:
`Jacobs.ofGenFun` of the weight generating function of the adjugate.
[Jacobs, Def 1.27 + (2.1.3): the operator whose `(m,r)` matrix entry is `a_m^{(r)}`.] -/
noncomputable def kappaOp (ht : ‖t‖ < 1) (g : Sigma1) : c(ℕ, K₃) →L[K₃] c(ℕ, K₃) := by
  sorry

/-- **[Jacobs, Proposition 2.6]** (by design): the matrix of `kappaOp g` is the
coefficient array of the generating function `κ(cx+d)/((cx+d)(cx+d−axy−by))` at the
Jacobs-form parameters of `g`. -/
theorem matrixCoeff_kappaOp (g : Sigma1) (j i : ℕ) :
    matrixCoeff (kappaOp t ht g) j i
      = MvPowerSeries.coeff (idx j i) (weightGenFun t (adjParams g.1)) := sorry

/-- **The action law** ([Jacobs, Def 1.27]: "It is an easy check that … `|κ` is a
right-action of `Σ_ν` on `A_p`", left-composed form): `kappaOp` is multiplicative. -/
theorem kappaOp_mul (g h : Sigma1) :
    kappaOp t ht (g * h) = (kappaOp t ht g).comp (kappaOp t ht h) := sorry

theorem kappaOp_one : kappaOp t ht 1 = ContinuousLinearMap.id K₃ c(ℕ, K₃) := sorry

/-- The Tate algebra `c(ℕ, K₃)` as a distributive `Σ₁(9)`-module via `kappaOp`. -/
noncomputable def kappaModuleAction (t : K₃) (ht : ‖t‖ < 1) :
    DistribMulAction Sigma1 c(ℕ, K₃) := sorry

end Jacobs.U3
