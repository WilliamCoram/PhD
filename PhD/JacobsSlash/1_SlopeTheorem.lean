/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Slopes

/-!
# The Jacobs normalisation `ϖ₃`

The abstract slope theorem — [Jacobs, *Slopes of Compact Hecke Operators*, Theorem 2.12]: row
divisibility `‖matrixCoeff u j i‖ ≤ ‖ϖ‖ ^ j` plus unit top-left minors of the rescaled matrix
force `‖c_m(u)‖ = ‖ϖ‖ ^ (m.choose 2)` — is proved at an arbitrary `ϖ` in
`PhD.TateFredholm.Slopes` (`TateFredholm.norm_charCoeff_of_unit_minors`,
`TateFredholm.val_charCoeff_of_unit_minors`); it was generalised out of this file on 2026-09-01,
having been pinned at `ϖ = 3` here.

What remains is the fork's **choice of normalisation**: `ϖ₃`, the element `3` viewed as a
pseudo-uniformizer of `K`, which makes `PseudoUniformizer.val` the thesis's `v₃` with
`v₃(3) = 1`.  The slope readings of `PhD.JacobsSlash.«4_SlopeReading»` and the applications in
`PhD.JacobsSlash.«3_Slopes»` consume the general theorems at `ϖ₃`.

`3` need not be a *uniformizer* of `K`, and under `hω : ω ^ 2 + ω + 1 = 0` (case B) it is not —
`K` is then ramified over `ℚ₃` with `v₃(K^×) = (1/2)ℤ`; see the `PhD.JacobsSlash.U3Data` module
header.  `PseudoUniformizer` asks only for a topologically nilpotent unit with multiplicative
norm, which is all the valuation needs, and `[CharZero K]` supplies `(3 : K) ≠ 0`.
-/

open TateFredholm
open scoped TateFredholm

namespace JacobsSlash

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The normalisation.**  `3` as a pseudo-uniformizer of `K`: the choice that makes
`PseudoUniformizer.val` the thesis's `v₃`, normalised by `v₃(3) = 1`.

Defining this instead of assuming `(ϖ : PseudoUniformizer K) (hϖ : (ϖ : K) = 3)` is what keeps
the normalisation out of every downstream signature: a normalisation is a choice, not a
hypothesis. -/
def ϖ₃ [CharZero K] (h3 : ‖(3 : K)‖ < 1) : PseudoUniformizer K :=
  PseudoUniformizer.ofNormLtOne three_ne_zero h3

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem coe_ϖ₃ [CharZero K] (h3 : ‖(3 : K)‖ < 1) :
    ((ϖ₃ h3 : PseudoUniformizer K) : K) = 3 := rfl

-- NOTE(cleanup): `charCoeff_smul` below is `3`-free and field-general; a differently-shaped
-- `TateFredholm.charCoeff_smul` (over a Tate ring, with a compactoid hypothesis) already exists
-- in `PhD/TateFredholm/Riesz.lean`, so hoisting this one means resolving that name collision —
-- deferred to the cleanup pass.

/-- Scalars scale the characteristic coefficients geometrically:
`c_m (λ • u) = λ^m c_m (u)` (each `m × m` minor is `m`-homogeneous). -/
theorem charCoeff_smul (lam : K) (u : c(ℕ, K) →L[K] c(ℕ, K)) (m : ℕ) :
    charCoeff (lam • u) m = lam ^ m * charCoeff u m := by
  have hmc : ∀ j i : ℕ, matrixCoeff (lam • u) j i = lam * matrixCoeff u j i := fun _ _ => rfl
  have hminor : ∀ S : {S : Finset ℕ // S.card = m},
      minor (lam • u) (S : Finset ℕ) = lam ^ m * minor u (S : Finset ℕ) := by
    rintro ⟨S, hS⟩
    have hmat : (Matrix.of fun j i : S => matrixCoeff (lam • u) (j : ℕ) (i : ℕ)) =
        lam • Matrix.of fun j i : S => matrixCoeff u (j : ℕ) (i : ℕ) := by
      ext j i
      exact hmc _ _
    show (Matrix.of fun j i : S => matrixCoeff (lam • u) (j : ℕ) (i : ℕ)).det = _
    rw [hmat, Matrix.det_smul, Fintype.card_coe, hS]
    rfl
  rw [charCoeff, charCoeff, tsum_congr hminor, tsum_mul_left]
  ring

end JacobsSlash
