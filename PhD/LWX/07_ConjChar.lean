/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«06_Vertices»

/-!
# The conjugate nebentypus `ω⁻¹` — SKELETON

[LWX, §3.23 Step I] runs the whole argument at a *pair* of characters: the lower bound polygon of
Corollary 3.18 is applied "for each of `T_{(k,χ)}` and `T_{(k,χ⁻¹)}`" (`lwx.txt:1826–1830`), and
Proposition 3.22 pins the total of the two.  Everything in the halo layer is already stated for an
arbitrary `ω`, so the second instance costs nothing once `ω⁻¹` exists as a term — but it does not
exist anywhere in the project.  This file supplies it.

Note that the *same* `UpDatum` serves both characters: `03_UpMatrix.lean`'s `UpDatum` carries only the
coset data (`tgt`, `mat`), and the nebentypus enters at `UpDatum.matrix D ω` through `entry ω`.  So
the `ψ⁻¹`-space is `D` at `invChar ω`, not a different datum — which is why this file is small.

## Main declarations

* `LWX.invChar` — the conjugate character `u ↦ (ω u)⁻¹`.
* `LWX.invChar_apply`, `LWX.invChar_invChar` — the API.
-/

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The conjugate nebentypus** `ω⁻¹ : u ↦ (ω u)⁻¹`.  A monoid hom because `ℤ_[p]ˣ` is
commutative. -/
def invChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : (ZMod p)ˣ →* ℤ_[p]ˣ where
  toFun u := (ω u)⁻¹
  map_one' := by simp
  map_mul' u v := by simp [mul_comm]

@[simp]
theorem invChar_apply (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (u : (ZMod p)ˣ) : invChar ω u = (ω u)⁻¹ := rfl

@[simp]
theorem invChar_invChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : invChar (invChar ω) = ω := by
  ext u
  simp

end LWX
