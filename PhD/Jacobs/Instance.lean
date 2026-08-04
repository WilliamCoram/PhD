/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.SlopeReading
import Mathlib.NumberTheory.Padics.Complex

/-!
# Non-vacuity: the Jacobs parameters exist over `ℂ₃`

The case-B development (`PhD.Jacobs.Slopes`, `PhD.Jacobs.SlopeReading`) is stated over an
abstract complete ultrametric field `K` carrying parameters `ω, ν, t` subject to
`hω : ω² + ω + 1 = 0`, `hν2 : ν² = −2`, `hνc : ‖ν − 2695‖ ≤ ‖3‖¹⁰`, `ht : ‖t‖ < 1` and
`h3 : ‖3‖ < 1`.  Nothing there proves that this parameter class is *inhabited* — and if it
were empty, every case-B theorem would be vacuously true and the build would still be green.

This file closes that gap: it exhibits `K = ℂ₃` together with parameters satisfying every
hypothesis, so the slope statements have content.  `slopes_nonvacuous` is the certificate in
its strongest form — it instantiates the case-B headline itself.

## Why `ℂ₃`

Two reasons, one negative and one positive.

*Cheap*: `Mathlib.NumberTheory.Padics.Complex` gives `ℂ₃ = ℂ_[3]` (the completion of an
algebraic closure of `ℚ₃`, normed by the spectral norm) with `NontriviallyNormedField`,
`IsUltrametricDist`, `CompleteSpace`, `CharZero` and `IsAlgClosed` all as instances, so the
four typeclass hypotheses are `inferInstance` and `hω`/`hν2` follow from algebraic closure.

*Right*: the eventual statement of [Jacobs, Cor 2.16] is about the **eigenvalues** of `U₃`,
not merely about the slopes of its characteristic series.  Eigenvalues are roots of
`charPowerSeries`, and those need an algebraically closed complete field to live in — over the
minimal field (below) the characteristic series need not split.  So `ℂ₃` is the natural home
for the eigenvalue statement, not a compromise made for convenience.

## What this certificate does *not* see

`ℂ₃` is far larger than necessary, and its value group is all of `ℚ` (it is divisible, every
element having roots of every order).  Two things are therefore invisible here:

* **The minimal field is quadratic.**  `ν` already lies in `ℤ₃`: `−2 ≡ 1 mod 3` and the squares
  in `𝔽₃ˣ` are `{1}`, so `−2` is a square in `ℤ₃ˣ` — which is why [Jacobs, p. 22] writes
  `ν₃ ∈ ℤ₃` (`508² + 2 = 3⁷ · 118`, and `2695 ≡ 508 mod 3⁷`).  Only `ω` needs an extension, so
  the smallest admissible `K` is `ℚ₃(ζ₃) = ℚ₃(√−3)`, of degree `2` over `ℚ₃`.
* **The half-integer slopes are forced there, not here.**  Over `ℚ₃(ζ₃)` the extension is
  totally ramified with `e = 2`, so `v₃(Kˣ) = (1/2)ℤ` and the slopes `1/2, 3/2, 5/2, …` of
  [Jacobs, Cor 2.16] are *compelled* to be half-integers (see the `PhD.Jacobs.U3Data` module
  header).  Over `ℂ₃`, with value group `ℚ`, that is no constraint at all.

Neither point weakens any theorem — the abstract statements over `K` remain the canonical
ones, and they are what will compose with the AG-B identification, which happens over Jacobs'
own coefficient field rather than over `ℂ₃`.  But a reader should not conclude from this file
that the result needs an infinite-dimensional coefficient field.

## The cyclotomic certificate (not done here)

A second witness at the minimal field `ℚ₃(ζ₃)` would certify exactly the two facts above.  It
is plumbing rather than missing theory: mathlib has no *instance* `NormedField L` for a finite
extension `L/ℚ₃` (there cannot be one — it would be a diamond), but it does have the
constructions.  The recipe:

* `L := CyclotomicField 3 ℚ_[3]` (or `AdjoinRoot (X ^ 2 + X + 1 : ℚ_[3][X])`);
* `letI : NormedField L := spectralNorm.normedField ℚ_[3] L`
  (`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`);
* `CompleteSpace L` is then free from that file's `instance completeSpace [FiniteDimensional …]`;
* `IsUltrametricDist L` from `isNonarchimedean_spectralNorm`, as
  `PadicAlgCl.isUltrametricDist` does it for the algebraic closure;
* `ν` from `ℤ₃ ⊆ ℚ₃ ⊆ L` — the argument of `exists_sqrt_neg_two_near` below transports
  verbatim, since it uses only the ultrametric law and multiplicativity.

The one genuine addition would be `IsAlgClosed`-free constructions of `ω` (immediate: `ζ₃`
generates `L`) — no Hensel argument is needed anywhere, for the reason explained below.

## Why no Hensel lemma is needed

The obvious route to `hνc` is Hensel's lemma at `a = 2695`.  It is not necessary, and mathlib's
`hensels_lemma` would in any case give only `‖z − a‖ < ‖f'(a)‖ = 1`, far short of `‖3‖¹⁰`.
Instead, take *any* square root `ν` of `−2` (algebraic closure) and let the ultrametric choose
the sign:

`(ν − 2695)(ν + 2695) = ν² − 2695² = −2 − 7263025 = −(3¹¹ · 41)`,

so `‖ν − 2695‖ · ‖ν + 2695‖ = ‖3‖¹¹`.  Both factors have norm `≤ 1` (as `‖ν‖ = 1 = ‖2695‖`),
while their difference is `−5390`, of norm `1`, so by the ultrametric law the larger of the two
is exactly `1` — whence the smaller is exactly `‖3‖¹¹`.  Replacing `ν` by `−ν` if necessary
makes `ν − 2695` the smaller one.  This gives `‖ν − 2695‖ = ‖3‖¹¹`, one power *stronger* than
`hνc` requires.
-/

open TateFredholm NewtonPolygon₀

namespace Jacobs

namespace Instance

noncomputable section

/-! ### `ℂ₃` carries the four typeclass hypotheses -/

example : NontriviallyNormedField ℂ_[3] := inferInstance
example : IsUltrametricDist ℂ_[3] := inferInstance
example : CompleteSpace ℂ_[3] := inferInstance
example : CharZero ℂ_[3] := inferInstance

/-! ### The parameters -/

/-- `h3 : ‖(3 : K)‖ < 1` over `ℂ₃`: the norm extends the `3`-adic norm of `ℚ₃`, where
`‖3‖ = 1/3`. -/
theorem norm_three_lt_one : ‖(3 : ℂ_[3])‖ < 1 := by
  have h : ‖(3 : ℂ_[3])‖ = ‖((3 : ℕ) : ℚ_[3])‖ := by
    rw [← PadicComplex.norm_extends' 3 ((3 : ℕ) : ℚ_[3])]
    congr 1
    rw [map_natCast, PadicComplex.coe_natCast]
    norm_num
  rw [h, Padic.norm_p]
  norm_num

/-- `hω : ω ^ 2 + ω + 1 = 0` — a primitive cube root of unity exists in `ℂ₃`. -/
theorem exists_omega : ∃ ω : ℂ_[3], ω ^ 2 + ω + 1 = 0 := by
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℂ_[3]).degree = 2 := by
    compute_degree!
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (k := ℂ_[3])
    (Polynomial.X ^ 2 + Polynomial.X + 1) (by rw [hdeg]; decide)
  exact ⟨ω, by simpa [Polynomial.IsRoot] using hω⟩

/-- `ht : ‖t‖ < 1` — the weight disc is nonempty (its centre will do). -/
theorem exists_t : ∃ t : ℂ_[3], ‖t‖ < 1 := ⟨0, by simp⟩

/-- **`hν2` and `hνc` together.**  A square root of `−2` sitting `3`-adically at `2695`, i.e.
Jacobs' Hensel root `ν₃ = √−2` with its refined `p. 39` location.

The proof needs no Hensel lemma (module header): algebraic closure supplies *some* `ν` with
`ν² = −2`, and the ultrametric law forces one of `ν ∓ 2695` to have norm exactly `‖3‖¹¹`; we
pick the sign making it `ν − 2695`.  The bound obtained is `‖3‖¹¹`, one power stronger than
`hνc` asks for — the slack is real, and matches the thesis's own consistency check
`2695² + 2 = 3¹¹ · 41`. -/
theorem exists_sqrt_neg_two_near :
    ∃ ν : ℂ_[3], ν ^ 2 = -2 ∧ ‖ν - 2695‖ ≤ ‖(3 : ℂ_[3])‖ ^ 10 := by
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq (-2 : ℂ_[3]) (n := 2) two_pos
  set h3 := norm_three_lt_one
  -- Numerals prime to `3` have norm `1`.
  have h41 : ‖(41 : ℂ_[3])‖ = 1 :=
    norm_ofNat_eq_one h3 (n := 41) (by norm_num) (by norm_num)
  have h2695 : ‖(2695 : ℂ_[3])‖ = 1 :=
    norm_ofNat_eq_one h3 (n := 2695) (by norm_num) (by norm_num)
  have h5390 : ‖(5390 : ℂ_[3])‖ = 1 :=
    norm_ofNat_eq_one h3 (n := 5390) (by norm_num) (by norm_num)
  -- `‖ν‖ = 1`, since `‖ν‖² = ‖−2‖ = 1`.
  have hνnorm : ‖ν‖ = 1 := by
    have hsq : ‖ν‖ ^ 2 = 1 := by
      rw [← norm_pow, hν, norm_neg]
      exact norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
    nlinarith [norm_nonneg ν, hsq]
  -- The factorisation `(ν − 2695)(ν + 2695) = −(3¹¹ · 41)`.
  have key : (ν - 2695) * (ν + 2695) = -((3 : ℂ_[3]) ^ 11 * 41) := by
    linear_combination hν
  have hprod : ‖ν - 2695‖ * ‖ν + 2695‖ = ‖(3 : ℂ_[3])‖ ^ 11 := by
    rw [← norm_mul, key, norm_neg, norm_mul, norm_pow, h41, mul_one]
  -- Both factors are integral.
  have hA : ‖ν - 2695‖ ≤ 1 := by
    refine (norm_sub_le_max' ν (2695 : ℂ_[3])).trans ?_
    simp [hνnorm, h2695]
  have hB : ‖ν + 2695‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max ν (2695 : ℂ_[3])).trans ?_
    simp [hνnorm, h2695]
  -- Their difference is `−5390`, of norm `1`, so the larger factor has norm exactly `1`.
  have hdiff : (ν - 2695) - (ν + 2695) = -(5390 : ℂ_[3]) := by ring
  have hmax : 1 ≤ max ‖ν - 2695‖ ‖ν + 2695‖ := by
    have h := norm_sub_le_max' (ν - 2695) (ν + 2695)
    rw [hdiff, norm_neg, h5390] at h
    exact h
  have hpow : ‖(3 : ℂ_[3])‖ ^ 11 ≤ ‖(3 : ℂ_[3])‖ ^ 10 :=
    pow_le_pow_of_le_one (norm_nonneg _) h3.le (by norm_num)
  rcases le_total ‖ν - 2695‖ ‖ν + 2695‖ with h | h
  · -- `ν + 2695` is the larger factor, hence of norm `1`; so `‖ν − 2695‖ = ‖3‖¹¹`.
    refine ⟨ν, hν, ?_⟩
    have hB1 : ‖ν + 2695‖ = 1 := le_antisymm hB (by rwa [max_eq_right h] at hmax)
    rw [hB1, mul_one] at hprod
    exact hprod.le.trans hpow
  · -- `ν − 2695` is the larger factor; swap the sign of `ν`.
    refine ⟨-ν, by rwa [neg_pow, even_two.neg_one_pow, one_mul], ?_⟩
    have hA1 : ‖ν - 2695‖ = 1 := le_antisymm hA (by rwa [max_eq_left h] at hmax)
    rw [hA1, one_mul] at hprod
    have hswap : ‖-ν - 2695‖ = ‖ν + 2695‖ := by
      rw [show -ν - (2695 : ℂ_[3]) = -(ν + 2695) by ring, norm_neg]
    rw [hswap]
    exact hprod.le.trans hpow

/-! ### The certificate -/

set_option linter.unusedVariables false in
/-- **Non-vacuity of [Jacobs, Cor 2.16].**  There are parameters over `ℂ₃` satisfying every
hypothesis of the case-B development, and for them the case-B headline
(`unitSlope_newtonPolygon₀OfPowerSeries_M22op`) says what it is meant to say: the Newton
polygon of `det(1 − T·M₂,₂)` has unit slopes `1/2, 3/2, 5/2, …`.

This is the statement that rules out the failure mode the abstract development cannot rule out
on its own — an unsatisfiable hypothesis pack making every case-B theorem vacuously true.

(`hν2` is bound but unused in the body: `M22op` does not take it, yet asserting it is part of
what this certificate is for, so the binder stays.) -/
theorem slopes_nonvacuous :
    ∃ (ω ν t : ℂ_[3]) (hω : ω ^ 2 + ω + 1 = 0) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
      (hνc : ‖ν - 2695‖ ≤ ‖(3 : ℂ_[3])‖ ^ 10),
      ∀ j : ℕ,
        (newtonPolygon₀OfPowerSeries (ϖ₃ norm_three_lt_one).val
            (charPowerSeries (M22op ω hω norm_three_lt_one ht hνc))).unitSlope j
          = (((j : ℝ) + 1 / 2 : ℝ) : WithBotTop ℝ) := by
  obtain ⟨ω, hω⟩ := exists_omega
  obtain ⟨ν, hν2, hνc⟩ := exists_sqrt_neg_two_near
  obtain ⟨t, ht⟩ := exists_t
  exact ⟨ω, ν, t, hω, ht, hν2, hνc, fun j =>
    unitSlope_newtonPolygon₀OfPowerSeries_M22op ω hω norm_three_lt_one ht hν2 hνc j⟩

end

end Instance

end Jacobs
