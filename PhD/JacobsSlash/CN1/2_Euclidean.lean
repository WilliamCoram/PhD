/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.U3.«1_Hurwitz»
import Mathlib.Data.Rat.Floor

/-!
# The Hurwitz order is norm-Euclidean; its right ideals are principal

Part 1 of the class-number-one chain (board `.mathlib-quality/hurwitz-cn1/`), replacing
the cancelled FLT deferral of `hClassNumberOne` (user decision 2026-08-10).

Sources ([Voight, *Quaternion algebras*, GTM 288]):

* 11.3.1 (p. 169): rounding a rational quaternion to the nearer of `ℤ⁴` and `(ℤ+½)⁴`
  leaves squared distance `< 1` — and in fact `≤ 1/2` (Exercise 11.7).
* Lemma 11.3.2 (p. 169): the right Euclidean algorithm `α = βμ + ρ`, `nrd ρ < nrd β`.
* Proposition 11.3.4 (p. 169): every right ideal of `𝓞` is right principal, by norm
  descent on a minimal-norm nonzero element.

Right ideals are `Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder` (mathlib's
`Semiring.toOppositeModule`: `op s • y = y * s`), and `Submodule.span 𝓞ᵐᵒᵖ {x} = x𝓞`.

**Sidedness warning.**  The division must place the quotient to the RIGHT of the
divisor, `a = b * q + r`: only then is the remainder `r = a - b * q` of two elements of
a right ideal again in the ideal.  (The unimported legacy skeleton
`PhD/Jacobs/U3/ClassNumberOneFallback.lean` stated `a = q * b + r`, which descends left
ideals — a planning catch recorded on the board.)
-/

open Quaternion

namespace JacobsSlash

/-- Halved coordinates that differ by an even amount have equal parity: the side condition
in `ofTuple_mem_of_parity` for the tuples produced by coordinatewise rounding. -/
private theorem two_mul_add_emod_two (m n e : ℤ) : (2 * m + e) % 2 = (2 * n + e) % 2 := by omega

/-- The one-coordinate inequality behind the covering bound: two rationals at distance
`≤ 1/2` from the origin whose difference is `1/2 - n` with `n` an integer have squares
summing to `≤ 1/4`.  The bounds force `n = 0` or `n = 1`; geometrically, on the segment
from `(0, -1/2)` to `(1/2, 0)` the squared distance to the origin is maximised at the
endpoints. -/
private theorem sq_add_sq_le_quarter {f g : ℚ} (n : ℤ) (hf1 : -(1 / 2) ≤ f) (hf2 : f ≤ 1 / 2)
    (hg1 : -(1 / 2) ≤ g) (hg2 : g ≤ 1 / 2) (h : f - g = 1 / 2 - n) :
    f ^ 2 + g ^ 2 ≤ 1 / 4 := by
  have hn : n = 0 ∨ n = 1 := by
    have hlow : (-1 : ℤ) < n := by exact_mod_cast (by linarith : (-1 : ℚ) < (n : ℚ))
    have hhigh : n < 2 := by exact_mod_cast (by linarith : (n : ℚ) < 2)
    omega
  rcases hn with rfl | rfl <;> push_cast at h
  · obtain rfl : g = f - 1 / 2 := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ f) (by linarith : (0 : ℚ) ≤ 1 / 2 - f)]
  · obtain rfl : f = g - 1 / 2 := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ g) (by linarith : (0 : ℚ) ≤ 1 / 2 - g)]

/-- **The two roundings of one coordinate are complementary**: rounding `c` to `ℤ` and
rounding `c` to `ℤ + 1/2` leave errors whose squares sum to `≤ 1/4`.  Both errors are
`≤ 1/2` in absolute value (`abs_sub_round`) and they differ by `1/2 - n` for the integer
`n = round c - round (c - 1/2)`. -/
private theorem sq_add_sq_round_le (c : ℚ) :
    (c - (round c : ℚ)) ^ 2 + (c - 1 / 2 - (round (c - 1 / 2) : ℚ)) ^ 2 ≤ 1 / 4 := by
  obtain ⟨hf1, hf2⟩ := abs_le.mp (abs_sub_round c)
  obtain ⟨hg1, hg2⟩ := abs_le.mp (abs_sub_round (c - 1 / 2))
  refine sq_add_sq_le_quarter (round c - round (c - 1 / 2)) hf1 hf2 hg1 hg2 ?_
  push_cast
  ring

/-- Rounding each coordinate of `γ` into the shifted lattice `(ℤ + s)⁴`, where `2s = e` is an
integer, lands in the Hurwitz order: the four halved coordinates are all congruent to `e`
mod `2`, and the squared error is the sum of the four coordinate errors. -/
private theorem exists_normSq_sub_eq (γ : ℍ[ℚ]) (s : ℚ) (e : ℤ) (he : (e : ℚ) = 2 * s) :
    ∃ μ ∈ hurwitzOrder, normSq (γ - μ)
      = (γ.re - s - (round (γ.re - s) : ℚ)) ^ 2 + (γ.imI - s - (round (γ.imI - s) : ℚ)) ^ 2
        + (γ.imJ - s - (round (γ.imJ - s) : ℚ)) ^ 2
        + (γ.imK - s - (round (γ.imK - s) : ℚ)) ^ 2 := by
  refine ⟨ofTuple (2 * round (γ.re - s) + e, 2 * round (γ.imI - s) + e,
    2 * round (γ.imJ - s) + e, 2 * round (γ.imK - s) + e),
    ofTuple_mem_of_parity ⟨two_mul_add_emod_two .., two_mul_add_emod_two ..,
      two_mul_add_emod_two ..⟩, ?_⟩
  rw [normSq_def']
  simp only [re_sub, imI_sub, imJ_sub, imK_sub, ofTuple_re, ofTuple_imI, ofTuple_imJ,
    ofTuple_imK]
  push_cast [he]
  ring

/-- **The Hurwitz covering bound** [Voight 11.3.1 + Exercise 11.7]: every rational
quaternion is within squared distance `≤ 1/2` of a Hurwitz quaternion — round each
coordinate, and if the integer rounding is bad (all four fractional parts near `1/2`),
round instead to the half-integer lattice `(ℤ+½)⁴ ⊆ 𝓞`. -/
theorem exists_normSq_sub_le_half (γ : ℍ[ℚ]) :
    ∃ μ ∈ hurwitzOrder, normSq (γ - μ) ≤ 1 / 2 := by
  obtain ⟨μ₁, hμ₁mem, hμ₁⟩ := exists_normSq_sub_eq γ 0 0 (by norm_num)
  obtain ⟨μ₂, hμ₂mem, hμ₂⟩ := exists_normSq_sub_eq γ (1 / 2) 1 (by norm_num)
  simp only [sub_zero] at hμ₁
  have hsum : normSq (γ - μ₁) + normSq (γ - μ₂) ≤ 1 := by
    rw [hμ₁, hμ₂]
    linarith [sq_add_sq_round_le γ.re, sq_add_sq_round_le γ.imI, sq_add_sq_round_le γ.imJ,
      sq_add_sq_round_le γ.imK]
  rcases le_total (normSq (γ - μ₁)) (normSq (γ - μ₂)) with h | h
  · exact ⟨μ₁, hμ₁mem, by linarith⟩
  · exact ⟨μ₂, hμ₂mem, by linarith⟩

/-- **The Hurwitz order is right norm-Euclidean** [Voight, Lemma 11.3.2]: for `a b : 𝓞`
with `b ≠ 0` there are `q r : 𝓞` with `a = b * q + r` and `N(r) < N(b)`.  Here `q` is the
Hurwitz rounding of `b⁻¹ * a`, and multiplicativity of the norm gives the strict drop. -/
theorem exists_div_rem (a b : hurwitzOrder) (hb : b ≠ 0) :
    ∃ q r : hurwitzOrder, a = b * q + r ∧ hnorm r < hnorm b := by
  have hb' : (b : ℍ[ℚ]) ≠ 0 := fun h => hb (Subtype.ext h)
  obtain ⟨μ, hμmem, hμ⟩ := exists_normSq_sub_le_half ((b : ℍ[ℚ])⁻¹ * (a : ℍ[ℚ]))
  refine ⟨⟨μ, hμmem⟩, a - b * ⟨μ, hμmem⟩, by abel, ?_⟩
  have hcoe : ((a - b * ⟨μ, hμmem⟩ : hurwitzOrder) : ℍ[ℚ])
      = (b : ℍ[ℚ]) * ((b : ℍ[ℚ])⁻¹ * (a : ℍ[ℚ]) - μ) := by
    push_cast
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hb', one_mul]
  have hnb : 0 < normSq (b : ℍ[ℚ]) := normSq_nonneg.lt_of_ne' (normSq_ne_zero.mpr hb')
  rw [← Nat.cast_lt (α := ℚ), hnorm_coe, hnorm_coe, hcoe, map_mul]
  nlinarith [mul_le_mul_of_nonneg_left hμ hnb.le]

/-- **Every right ideal of the Hurwitz order is principal**
[Voight, Proposition 11.3.4]: descent on `hnorm` from `exists_div_rem`, generated by a
nonzero element of minimal norm (or `x = 0` for the zero ideal). -/
theorem right_ideal_principal (I : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder) :
    ∃ x : hurwitzOrder, I = Submodule.span (hurwitzOrder)ᵐᵒᵖ {x} := by
  by_cases hI : I = ⊥
  · exact ⟨0, hI.trans (Submodule.span_zero_singleton _).symm⟩
  obtain ⟨y, hyI, hy0⟩ := I.ne_bot_iff.mp hI
  have hSne : {n : ℕ | ∃ z ∈ I, z ≠ 0 ∧ hnorm z = n}.Nonempty := ⟨hnorm y, y, hyI, hy0, rfl⟩
  obtain ⟨x, hxI, hx0, hxn⟩ := Nat.sInf_mem hSne
  refine ⟨x, le_antisymm (fun c hcI => ?_) ((Submodule.span_singleton_le_iff_mem ..).mpr hxI)⟩
  obtain ⟨q, r, hqr, hr⟩ := exists_div_rem c x hx0
  have hrI : r ∈ I := by
    rw [eq_sub_of_add_eq' hqr.symm]
    exact I.sub_mem hcI (I.smul_mem (MulOpposite.op q) hxI)
  have hr0 : r = 0 := by
    by_contra hne
    have hle : sInf {n : ℕ | ∃ z ∈ I, z ≠ 0 ∧ hnorm z = n} ≤ hnorm r :=
      Nat.sInf_le ⟨r, hrI, hne, rfl⟩
    omega
  rw [hqr, hr0, add_zero]
  exact Submodule.mem_span_singleton.mpr ⟨MulOpposite.op q, rfl⟩

end JacobsSlash
