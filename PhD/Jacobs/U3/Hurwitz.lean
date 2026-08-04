/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Hurwitz order of `ℍ[ℚ]` and its right-ideal theory

[Jacobs, p. 22]:

> "Recall that in D = Q(i,j), our maximal order O_D is Z⟨i, j, ½(1+i+j+k)⟩, and so
> O_D^× = {±1, ±i, ±j, ±k, ±u₁, …, ±u₈}"  (the 24 Hurwitz units).

The thesis derives its class-set input (1.4.4), `D_f^× = D^× U₀(1)`, from the
Jacquet–Langlands correspondence [Jacobs, Lemma 1.22] — out of scope for this
formalisation.  The classical replacement route ([Voight, *Quaternion algebras*,
GTM 288]) is: the Hurwitz order is norm-Euclidean (Voight 11.3.1), hence every right
ideal is principal (11.1.8-style descent), hence the idelic class set is trivial
(27.6.8 dictionary; `PhD.Jacobs.U3.Level` / `ClassSet`).

**Status note (user decision 2026-08-05)**: FLT states the same surjectivity
(`FLT/Data/HurwitzRatHat.lean`, `completed_units`, currently `sorry`) and is expected
to cover it upstream — the class-number-one chain (`exists_div_rem`,
`right_ideal_principal`, the dictionary) is **deferred** and lives OFF the live chain in
`PhD/Jacobs/U3/ClassNumberOneFallback.lean`; the single live dependency is the interface
`Jacobs.U3.hClassNumberOne` (`Level.lean`).  Everything in THIS file IS scheduled work:
the order, its norm and its 24 units feed Theorem 2.1's orbit computation and Lemma 2.2
regardless of how (1.4.4) is eventually discharged.

Everything is stated for mathlib's `ℍ[ℚ]` (no bespoke quaternion structure; contrast
FLT's standalone `Hurwitz` type).
-/

open Quaternion

namespace Jacobs.U3

/-- Membership predicate for the Hurwitz order, in **halved-coordinate parity form**:
`x ∈ 𝓞` iff `2x` has integer coordinates all of the same parity.  Equivalent to Jacobs's
"`ℤ⟨i, j, ½(1+i+j+k)⟩`" description ("all four coordinates integers, or all four
half-odd-integers"), but a *single* branch with a parity side condition — one computation
per ring axiom instead of a four-way case split.

Stated through the coordinate projections rather than an anonymous-constructor literal:
`Quaternion` is a `def` (not an `abbrev`), so a literal at expected type `ℍ[ℚ]`
elaborates at `QuaternionAlgebra ℚ (-1) 0 (-1)` with *that* type's ring instances, and
neither `rw` nor `simp` will then connect it to the `ℍ[ℚ]` operations appearing in the
`Subring` obligations.  Projections avoid the whole seam: `re_add`, `re_mul`, … are
`@[simp]` and fire on any element. -/
def IsHurwitz (x : ℍ[ℚ]) : Prop :=
  ∃ A B C D : ℤ, x.re = (A : ℚ) / 2 ∧ x.imI = (B : ℚ) / 2 ∧ x.imJ = (C : ℚ) / 2 ∧
    x.imK = (D : ℚ) / 2 ∧ A % 2 = B % 2 ∧ B % 2 = C % 2 ∧ C % 2 = D % 2

/-- The Hurwitz order `𝓞 = ℤ⟨i, j, ½(1+i+j+k)⟩ ⊆ ℍ[ℚ]` [Jacobs p. 22]. -/
def hurwitzOrder : Subring ℍ[ℚ] where
  carrier := {x | IsHurwitz x}
  zero_mem' := ⟨0, 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩
  one_mem' := ⟨2, 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩
  add_mem' := by
    rintro x y ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
      ⟨A', B', C', D', hr', hi', hj', hk', hAB', hBC', hCD'⟩
    exact ⟨A + A', B + B', C + C', D + D',
      by simp [hr, hr']; ring,
      by simp [hi, hi']; ring,
      by simp [hj, hj']; ring,
      by simp [hk, hk']; ring,
      by omega, by omega, by omega⟩
  neg_mem' := by
    rintro x ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
    exact ⟨-A, -B, -C, -D,
      by simp [hr]; ring,
      by simp [hi]; ring,
      by simp [hj]; ring,
      by simp [hk]; ring,
      by omega, by omega, by omega⟩
  mul_mem' := by
    rintro x y ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
      ⟨A', B', C', D', hr', hi', hj', hk', hAB', hBC', hCD'⟩
    -- Extract the shared parity: `A = 2a + r`, …, `D = 2d + r` with the same `r`.
    obtain ⟨a, b, c, d, r, hA, hB, hC, hD⟩ :
        ∃ a b c d r : ℤ, A = 2 * a + r ∧ B = 2 * b + r ∧ C = 2 * c + r ∧ D = 2 * d + r :=
      ⟨A / 2, B / 2, C / 2, D / 2, A % 2, by omega, by omega, by omega, by omega⟩
    obtain ⟨a', b', c', d', r', hA', hB', hC', hD'⟩ :
        ∃ a' b' c' d' r' : ℤ, A' = 2 * a' + r' ∧ B' = 2 * b' + r' ∧ C' = 2 * c' + r' ∧
          D' = 2 * d' + r' :=
      ⟨A' / 2, B' / 2, C' / 2, D' / 2, A' % 2, by omega, by omega, by omega, by omega⟩
    subst hA hB hC hD hA' hB' hC' hD'
    refine ⟨2 * (a * a' - b * b' - c * c' - d * d') + r' * (a - b - c - d)
              + r * (a' - b' - c' - d') - r * r',
            2 * (a * b' + b * a' + c * d' - d * c') + r' * (a + b + c - d)
              + r * (a' + b' + d' - c') + r * r',
            2 * (a * c' - b * d' + c * a' + d * b') + r' * (a - b + c + d)
              + r * (a' + b' + c' - d') + r * r',
            2 * (a * d' + b * c' - c * b' + d * a') + r' * (a + b - c + d)
              + r * (a' - b' + c' + d') + r * r', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hr, hi, hj, hk, hr', hi', hj', hk']; ring
    · simp [hr, hi, hj, hk, hr', hi', hj', hk']; ring
    · simp [hr, hi, hj, hk, hr', hi', hj', hk']; ring
    · simp [hr, hi, hj, hk, hr', hi', hj', hk']; ring
    -- The four witnesses have equal parity: each pairwise difference is visibly `2 * _`
    -- (`ring`), which makes the `% 2` goals linear and so reachable by `omega`.
    · have h : (2 * (a * a' - b * b' - c * c' - d * d') + r' * (a - b - c - d)
              + r * (a' - b' - c' - d') - r * r')
            - (2 * (a * b' + b * a' + c * d' - d * c') + r' * (a + b + c - d)
              + r * (a' + b' + d' - c') + r * r')
          = 2 * ((a * a' - b * b' - c * c' - d * d') - (a * b' + b * a' + c * d' - d * c')
              - r' * (b + c) - r * (b' + d') - r * r') := by ring
      omega
    · have h : (2 * (a * b' + b * a' + c * d' - d * c') + r' * (a + b + c - d)
              + r * (a' + b' + d' - c') + r * r')
            - (2 * (a * c' - b * d' + c * a' + d * b') + r' * (a - b + c + d)
              + r * (a' + b' + c' - d') + r * r')
          = 2 * ((a * b' + b * a' + c * d' - d * c') - (a * c' - b * d' + c * a' + d * b')
              + r' * (b - d) + r * (d' - c')) := by ring
      omega
    · have h : (2 * (a * c' - b * d' + c * a' + d * b') + r' * (a - b + c + d)
              + r * (a' + b' + c' - d') + r * r')
            - (2 * (a * d' + b * c' - c * b' + d * a') + r' * (a + b - c + d)
              + r * (a' - b' + c' + d') + r * r')
          = 2 * ((a * c' - b * d' + c * a' + d * b') - (a * d' + b * c' - c * b' + d * a')
              + r' * (c - b) + r * (b' - d')) := by ring
      omega

/-- The reduced norm of a Hurwitz quaternion is a non-negative integer.  In the shared
parity form `A = 2a + r`, … the halved coordinates give
`N = (a² + b² + c² + d²) + r(a + b + c + d) + r²`, visibly an integer, and it is
non-negative because `normSq` is a sum of squares. -/
theorem exists_norm_eq_natCast (x : hurwitzOrder) :
    ∃ n : ℕ, (normSq (x : ℍ[ℚ]) : ℚ) = n := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := x.2
  obtain ⟨a, b, c, d, r, hA, hB, hC, hD⟩ :
      ∃ a b c d r : ℤ, A = 2 * a + r ∧ B = 2 * b + r ∧ C = 2 * c + r ∧ D = 2 * d + r :=
    ⟨A / 2, B / 2, C / 2, D / 2, A % 2, by omega, by omega, by omega, by omega⟩
  subst hA hB hC hD
  refine ⟨((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + r * (a + b + c + d) + r ^ 2).toNat, ?_⟩
  have hNQ : normSq (x : ℍ[ℚ])
      = (((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + r * (a + b + c + d) + r ^ 2 : ℤ) : ℚ) := by
    rw [normSq_def', hr, hi, hj, hk]; push_cast; ring
  have hnn : (0 : ℤ) ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + r * (a + b + c + d) + r ^ 2 := by
    have h : (0 : ℚ)
        ≤ (((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + r * (a + b + c + d) + r ^ 2 : ℤ) : ℚ) := by
      rw [← hNQ, normSq_def']; positivity
    exact_mod_cast h
  rw [hNQ]
  exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (Int.toNat_of_nonneg hnn).symm

/-- The Hurwitz order is closed under conjugation (`star` negates the imaginary
coordinates, which preserves the shared parity). -/
theorem star_mem {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) : star x ∈ hurwitzOrder := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := hx
  exact ⟨A, -B, -C, -D,
    by simpa using hr, by simp [hi]; ring,
    by simp [hj]; ring, by simp [hk]; ring,
    by omega, by omega, by omega⟩

/-- The integer norm of a Hurwitz quaternion. -/
noncomputable def hnorm (x : hurwitzOrder) : ℕ := (exists_norm_eq_natCast x).choose

/-- The defining property of `hnorm`: it is the reduced norm, read in `ℚ`. -/
@[simp] theorem hnorm_coe (x : hurwitzOrder) : (hnorm x : ℚ) = normSq (x : ℍ[ℚ]) :=
  (exists_norm_eq_natCast x).choose_spec.symm

/-- The integer norm is multiplicative — inherited from `normSq` being a
`MonoidWithZeroHom`.  This is what makes the norm a Euclidean-style size function. -/
theorem hnorm_mul (x y : hurwitzOrder) : hnorm (x * y) = hnorm x * hnorm y := by
  have h : ((hnorm (x * y) : ℕ) : ℚ) = ((hnorm x * hnorm y : ℕ) : ℚ) := by
    push_cast
    rw [hnorm_coe, hnorm_coe, hnorm_coe]
    exact map_mul normSq (x : ℍ[ℚ]) (y : ℍ[ℚ])
  exact_mod_cast h

/-- Only `0` has norm `0` (`ℍ[ℚ]` is a division ring, so `normSq` is nondegenerate). -/
@[simp] theorem hnorm_eq_zero_iff {x : hurwitzOrder} : hnorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h0 : normSq (x : ℍ[ℚ]) = 0 := by rw [← hnorm_coe, h]; norm_num
    exact Subtype.ext (normSq_eq_zero.mp h0)
  · rintro rfl
    have h0 : ((hnorm (0 : hurwitzOrder) : ℕ) : ℚ) = 0 := by
      rw [hnorm_coe]
      simp
    exact_mod_cast h0

/-- A Hurwitz quaternion is a unit of the order iff its norm is `1`
[Jacobs p. 22; Voight 11.1.9]. -/
theorem isUnit_iff_hnorm_eq_one {x : hurwitzOrder} : IsUnit x ↔ hnorm x = 1 := by
  constructor
  · -- a unit has `N(x)·N(x⁻¹) = 1` in `ℕ`, so `N(x) = 1`
    rintro ⟨u, rfl⟩
    have hmul : (u : hurwitzOrder) * ((u⁻¹ : (hurwitzOrder)ˣ) : hurwitzOrder) = 1 := by
      exact_mod_cast u.mul_inv
    have h1 : hnorm (1 : hurwitzOrder) = 1 := by
      have : ((hnorm (1 : hurwitzOrder) : ℕ) : ℚ) = ((1 : ℕ) : ℚ) := by
        rw [hnorm_coe]; simp
      exact_mod_cast this
    have h : hnorm (u : hurwitzOrder) * hnorm ((u⁻¹ : (hurwitzOrder)ˣ) : hurwitzOrder) = 1 := by
      rw [← hnorm_mul, hmul, h1]
    exact Nat.eq_one_of_mul_eq_one_right h
  · -- conversely `star x` is a two-sided inverse, and it lies in the order
    intro h
    have hn : normSq (x : ℍ[ℚ]) = 1 := by rw [← hnorm_coe, h]; norm_num
    have hstar : (star (x : ℍ[ℚ])) ∈ hurwitzOrder := star_mem x.2
    have hxx : (x : ℍ[ℚ]) * star (x : ℍ[ℚ]) = 1 := by
      rw [Quaternion.mul_star_eq_coe]
      rw [show ((x : ℍ[ℚ]) * star (x : ℍ[ℚ])).re = normSq (x : ℍ[ℚ]) from rfl, hn]
      simp
    have hxx' : (star (x : ℍ[ℚ])) * (x : ℍ[ℚ]) = 1 := by
      rw [Quaternion.star_mul_eq_coe]
      rw [show (star (x : ℍ[ℚ]) * (x : ℍ[ℚ])).re = normSq (x : ℍ[ℚ]) from by
        rw [← Quaternion.normSq_star, normSq_def]; simp, hn]
      simp
    exact ⟨⟨x, ⟨star (x : ℍ[ℚ]), hstar⟩, Subtype.ext hxx, Subtype.ext hxx'⟩, rfl⟩

/-- Norm-one in `ℕ` is the same as norm-one in `ℚ`; the bridge used to move between the
integer norm and `normSq` when characterising units. -/
theorem hnorm_eq_one_iff {x : hurwitzOrder} : hnorm x = 1 ↔ normSq (x : ℍ[ℚ]) = 1 := by
  constructor
  · intro h; rw [← hnorm_coe, h]; norm_num
  · intro h
    have hq : ((hnorm x : ℕ) : ℚ) = ((1 : ℕ) : ℚ) := by rw [hnorm_coe, h]; norm_num
    exact_mod_cast hq

/-- **The norm-one equation in halved coordinates.**  Writing `x = (A + Bi + Cj + Dk)/2`,
`N(x) = (A² + B² + C² + D²)/4`, so the units of `𝓞` are exactly the `x ∈ 𝓞` whose
halved coordinates satisfy `A² + B² + C² + D² = 4`.  This bounds every coordinate by
`|A| ≤ 2`, turning the unit enumeration into a finite check on `[-2, 2]⁴`. -/
theorem hnorm_eq_one_iff_coords {x : hurwitzOrder} {A B C D : ℤ}
    (hr : (x : ℍ[ℚ]).re = (A : ℚ) / 2) (hi : (x : ℍ[ℚ]).imI = (B : ℚ) / 2)
    (hj : (x : ℍ[ℚ]).imJ = (C : ℚ) / 2) (hk : (x : ℍ[ℚ]).imK = (D : ℚ) / 2) :
    hnorm x = 1 ↔ A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 := by
  rw [hnorm_eq_one_iff]
  constructor
  · intro h
    have hq : ((A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
      have := h
      rw [normSq_def', hr, hi, hj, hk] at this
      push_cast
      linarith [this]
    exact_mod_cast hq
  · intro h
    have hq : ((A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by exact_mod_cast h
    rw [normSq_def', hr, hi, hj, hk]
    push_cast at hq ⊢
    linarith [hq]

/-- Every coordinate of a unit is bounded: `|A| ≤ 2`. -/
theorem abs_le_two_of_hnorm_eq_one {A B C D : ℤ} (h : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4) :
    A ^ 2 ≤ 4 := by nlinarith [sq_nonneg B, sq_nonneg C, sq_nonneg D]

/-- The halved-coordinate tuples of the units: `(A,B,C,D) ∈ [-2,2]⁴` with
`A² + B² + C² + D² = 4` and all four of the same parity.  The box is justified by
`abs_le_two_of_hnorm_eq_one`. -/
noncomputable def unitTuples : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2) ×ˢ
    (Finset.Icc (-2 : ℤ) 2)).filter
    (fun t => t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = 4 ∧
      t.1 % 2 = t.2.1 % 2 ∧ t.2.1 % 2 = t.2.2.1 % 2 ∧ t.2.2.1 % 2 = t.2.2.2 % 2)

/-- The quaternion with halved coordinates `(A,B,C,D)`.  The inverse direction of
`IsHurwitz`: `x ∈ 𝓞` iff `x = ofTuple t` for a same-parity `t`. -/
def ofTuple (t : ℤ × ℤ × ℤ × ℤ) : ℍ[ℚ] :=
  ⟨(t.1 : ℚ) / 2, (t.2.1 : ℚ) / 2, (t.2.2.1 : ℚ) / 2, (t.2.2.2 : ℚ) / 2⟩

@[simp] theorem ofTuple_re (t : ℤ × ℤ × ℤ × ℤ) : (ofTuple t).re = (t.1 : ℚ) / 2 := rfl
@[simp] theorem ofTuple_imI (t : ℤ × ℤ × ℤ × ℤ) : (ofTuple t).imI = (t.2.1 : ℚ) / 2 := rfl
@[simp] theorem ofTuple_imJ (t : ℤ × ℤ × ℤ × ℤ) : (ofTuple t).imJ = (t.2.2.1 : ℚ) / 2 := rfl
@[simp] theorem ofTuple_imK (t : ℤ × ℤ × ℤ × ℤ) : (ofTuple t).imK = (t.2.2.2 : ℚ) / 2 := rfl

/-- Distinct halved-coordinate tuples give distinct quaternions. -/
theorem ofTuple_injective : Function.Injective ofTuple := by
  rintro ⟨A, B, C, D⟩ ⟨A', B', C', D'⟩ h
  have h1 : (A : ℚ) / 2 = (A' : ℚ) / 2 := congrArg QuaternionAlgebra.re h
  have h2 : (B : ℚ) / 2 = (B' : ℚ) / 2 := congrArg QuaternionAlgebra.imI h
  have h3 : (C : ℚ) / 2 = (C' : ℚ) / 2 := congrArg QuaternionAlgebra.imJ h
  have h4 : (D : ℚ) / 2 = (D' : ℚ) / 2 := congrArg QuaternionAlgebra.imK h
  have e1 : (A : ℚ) = A' := by linarith
  have e2 : (B : ℚ) = B' := by linarith
  have e3 : (C : ℚ) = C' := by linarith
  have e4 : (D : ℚ) = D' := by linarith
  simp only [Prod.mk.injEq]
  exact ⟨by exact_mod_cast e1, by exact_mod_cast e2, by exact_mod_cast e3,
    by exact_mod_cast e4⟩

/-- Membership in `unitTuples` puts the quaternion in the order. -/
theorem ofTuple_mem_of_parity {t : ℤ × ℤ × ℤ × ℤ}
    (hp : t.1 % 2 = t.2.1 % 2 ∧ t.2.1 % 2 = t.2.2.1 % 2 ∧ t.2.2.1 % 2 = t.2.2.2 % 2) :
    ofTuple t ∈ hurwitzOrder :=
  ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, rfl, rfl, rfl, rfl, hp.1, hp.2.1, hp.2.2⟩

/-- **The count is 24** — machine-checked, independently of [Jacobs p. 22]'s list:
`8` all-even tuples (the permutations of `(±2,0,0,0)`, i.e. the Lipschitz units
`±1, ±i, ±j, ±k`) and `16` all-odd tuples (`{±1}⁴`, i.e. the half-units
`(±1±i±j±k)/2`). -/
theorem card_unitTuples : unitTuples.card = 24 := by
  simp [unitTuples]
  decide

/-- The unit group of the Hurwitz order has exactly `24` elements
[Jacobs p. 22: `{±1, ±i, ±j, ±k, ±u₁, …, ±u₈}`].

Route (recorded): by `isUnit_iff_hnorm_eq_one` + `hnorm_eq_one_iff_coords`, units
correspond to integer tuples `(A,B,C,D)` with `A²+B²+C²+D² = 4` and all four of the same
parity.  `abs_le_two_of_hnorm_eq_one` bounds the box to `[-2,2]⁴`, so the count is a
finite check: the all-even solutions are the `8` permutations of `(±2,0,0,0)` (the
Lipschitz units `±1, ±i, ±j, ±k`) and the all-odd ones are the `16` tuples in `{±1}⁴`
(the half-units `(±1±i±j±k)/2`).  The bijection below sends a tuple to the
corresponding unit; the counting step itself is `decide` (`card_unitTuples`). -/
theorem card_units_hurwitzOrder : Nat.card (hurwitzOrder)ˣ = 24 := by
  classical
  -- Every tuple in `unitTuples` names an element of the order …
  have hmem : ∀ t ∈ unitTuples, ofTuple t ∈ hurwitzOrder := by
    intro t ht
    simp only [unitTuples, Finset.mem_filter] at ht
    exact ofTuple_mem_of_parity ⟨ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
  -- … and that element is a unit.
  have hunit : ∀ (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ unitTuples),
      IsUnit (⟨ofTuple t, hmem t ht⟩ : hurwitzOrder) := by
    intro t ht
    simp only [unitTuples, Finset.mem_filter] at ht
    exact isUnit_iff_hnorm_eq_one.mpr
      ((hnorm_eq_one_iff_coords (x := ⟨ofTuple t, hmem t (by
        simp only [unitTuples, Finset.mem_filter]; exact ht)⟩)
        rfl rfl rfl rfl).mpr ht.2.1)
  -- The tuple-to-unit map.
  refine (Nat.card_eq_of_bijective
    (fun s : {t : ℤ × ℤ × ℤ × ℤ // t ∈ unitTuples} => (hunit s.1 s.2).unit) ?_).symm.trans ?_
  · constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have : ofTuple t = ofTuple t' := by
        have := congrArg (fun u : (hurwitzOrder)ˣ => ((u : hurwitzOrder) : ℍ[ℚ])) h
        simpa [IsUnit.unit_spec] using this
      exact Subtype.ext (ofTuple_injective this)
    · intro u
      obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := (u : hurwitzOrder).2
      have hn : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 :=
        (hnorm_eq_one_iff_coords hr hi hj hk).mp
          (isUnit_iff_hnorm_eq_one.mp ⟨u, rfl⟩)
      have hbox : ∀ z : ℤ, z ^ 2 ≤ 4 → z ∈ Finset.Icc (-2 : ℤ) 2 := by
        intro z hz; simp only [Finset.mem_Icc]; constructor <;> nlinarith
      have ht : (A, B, C, D) ∈ unitTuples := by
        simp only [unitTuples, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨hbox A (by nlinarith [sq_nonneg B, sq_nonneg C, sq_nonneg D]),
          hbox B (by nlinarith [sq_nonneg A, sq_nonneg C, sq_nonneg D]),
          hbox C (by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg D]),
          hbox D (by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C])⟩,
          hn, hAB, hBC, hCD⟩
      refine ⟨⟨(A, B, C, D), ht⟩, ?_⟩
      have hx : ofTuple (A, B, C, D) = ((u : hurwitzOrder) : ℍ[ℚ]) := by
        refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [hr, hi, hj, hk]
      exact Units.ext (Subtype.ext (by simpa [IsUnit.unit_spec] using hx))
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_unitTuples]

end Jacobs.U3
