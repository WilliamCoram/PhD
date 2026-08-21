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
GTM 288]) — the Hurwitz order is norm-Euclidean (Voight 11.3.2), hence every right
ideal is principal (11.3.4), hence the idelic class set is trivial (27.6.8
dictionary) — is fully formalised in `PhD/JacobsSlash/CN1/` (board
`.mathlib-quality/hurwitz-cn1/`), culminating in `JacobsSlash.hClassNumberOne`
(`CN1/«4_Dictionary»`, sorry-free, standard axioms).

**Status note**: the 2026-08-05 deferral of that chain to FLT's `completed_units` was
cancelled on 2026-08-10 (the FLT project dropped its Hurwitz material), and the in-repo
proof was completed the same day.  The order, its norm and its 24 units defined here
also feed Theorem 2.1's orbit computation and Lemma 2.2.

Everything is stated for mathlib's `ℍ[ℚ]` (no bespoke quaternion structure; contrast
FLT's standalone `Hurwitz` type).

## Main definitions

* `JacobsSlash.IsHurwitz`: membership in the Hurwitz order, in halved-coordinate parity form.
* `JacobsSlash.hurwitzOrder`: the Hurwitz order `𝓞 = ℤ⟨i, j, ½(1+i+j+k)⟩ ⊆ ℍ[ℚ]`.
* `JacobsSlash.hnorm`: the reduced norm of a Hurwitz quaternion, as a natural number.
* `JacobsSlash.ofTuple`, `JacobsSlash.unitTuples`: the quaternion named by a halved-coordinate
  tuple, and the `24` tuples that name the units.

## Main results

* `JacobsSlash.star_mem`: the order is closed under conjugation.
* `JacobsSlash.hnorm_mul`: the integer norm is multiplicative.
* `JacobsSlash.isUnit_iff_hnorm_eq_one`: `x` is a unit of `𝓞` iff `hnorm x = 1`.
* `JacobsSlash.exists_unit_of_tuple`, `JacobsSlash.exists_tuple_of_unit`: the unit group of `𝓞`
  is exactly the image of `unitTuples` under `ofTuple`.
* `JacobsSlash.card_units_hurwitzOrder`: [Jacobs p. 22] — `𝓞^×` has exactly `24` elements.

## Implementation notes

`IsHurwitz` is stated through the coordinate projections rather than an
anonymous-constructor literal: `Quaternion` is a `def` (not an `abbrev`), so a literal at
expected type `ℍ[ℚ]` elaborates at `QuaternionAlgebra ℚ (-1) 0 (-1)` with *that* type's
ring instances, and neither `rw` nor `simp` will then connect it to the `ℍ[ℚ]` operations
appearing in the `Subring` obligations.  Projections avoid the whole seam: `re_add`,
`re_mul`, … are `@[simp]` and fire on any element.
-/

open Quaternion

namespace JacobsSlash

/-- Membership predicate for the Hurwitz order, in **halved-coordinate parity form**:
`x ∈ 𝓞` iff `2x` has integer coordinates all of the same parity.  Equivalent to Jacobs's
"`ℤ⟨i, j, ½(1+i+j+k)⟩`" description ("all four coordinates integers, or all four
half-odd-integers"), but a *single* branch with a parity side condition — one computation
per ring axiom instead of a four-way case split. -/
def IsHurwitz (x : ℍ[ℚ]) : Prop :=
  ∃ A B C D : ℤ, x.re = (A : ℚ) / 2 ∧ x.imI = (B : ℚ) / 2 ∧ x.imJ = (C : ℚ) / 2 ∧
    x.imK = (D : ℚ) / 2 ∧ A % 2 = B % 2 ∧ B % 2 = C % 2 ∧ C % 2 = D % 2

/-- The Hurwitz order `𝓞 = ℤ⟨i, j, ½(1+i+j+k)⟩ ⊆ ℍ[ℚ]` [Jacobs p. 22]. -/
def hurwitzOrder : Subring ℍ[ℚ] where
  carrier := {x | IsHurwitz x}
  zero_mem' := by refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  one_mem' := by refine ⟨2, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  add_mem' := by
    rintro x y ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
      ⟨A', B', C', D', hr', hi', hj', hk', hAB', hBC', hCD'⟩
    refine ⟨A + A', B + B', C + C', D + D', ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
      simp only [re_add, imI_add, imJ_add, imK_add, hr, hi, hj, hk, hr', hi', hj', hk'] <;>
      push_cast <;>
      ring
  neg_mem' := by
    rintro x ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
    refine ⟨-A, -B, -C, -D, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
      simp only [re_neg, imI_neg, imJ_neg, imK_neg, hr, hi, hj, hk] <;>
      push_cast <;>
      ring
  mul_mem' := by
    rintro x y ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
      ⟨A', B', C', D', hr', hi', hj', hk', hAB', hBC', hCD'⟩
    obtain ⟨a, b, c, d, r, hA, hB, hC, hD⟩ :
        ∃ a b c d r : ℤ, A = 2 * a + r ∧ B = 2 * b + r ∧ C = 2 * c + r ∧ D = 2 * d + r :=
      ⟨A / 2, B / 2, C / 2, D / 2, A % 2, by omega, by omega, by omega, by omega⟩
    obtain ⟨a', b', c', d', r', hA', hB', hC', hD'⟩ :
        ∃ a' b' c' d' r' : ℤ, A' = 2 * a' + r' ∧ B' = 2 * b' + r' ∧ C' = 2 * c' + r' ∧
          D' = 2 * d' + r' :=
      ⟨A' / 2, B' / 2, C' / 2, D' / 2, A' % 2, by omega, by omega, by omega, by omega⟩
    subst hA hB hC hD hA' hB' hC' hD'
    obtain ⟨s, hs⟩ :
        ∃ s : ℤ, s = r' * (a + b + c + d) + r * (a' + b' + c' + d') + r * r' := ⟨_, rfl⟩
    refine ⟨2 * (a * a' - b * b' - c * c' - d * d' - r' * (b + c + d)
              - r * (b' + c' + d') - r * r') + s,
            2 * (a * b' + b * a' + c * d' - d * c' - r' * d - r * c') + s,
            2 * (a * c' - b * d' + c * a' + d * b' - r' * b - r * d') + s,
            2 * (a * d' + b * c' - c * b' + d * a' - r' * c - r * b') + s,
            ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
      simp only [re_mul, imI_mul, imJ_mul, imK_mul, hr, hi, hj, hk, hr', hi', hj', hk', hs] <;>
      push_cast <;>
      ring

/-- The reduced norm of a Hurwitz quaternion is a non-negative integer. -/
theorem exists_norm_eq_natCast (x : hurwitzOrder) :
    ∃ n : ℕ, (normSq (x : ℍ[ℚ]) : ℚ) = n := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := x.2
  obtain ⟨a, b, c, d, r, hA, hB, hC, hD⟩ :
      ∃ a b c d r : ℤ, A = 2 * a + r ∧ B = 2 * b + r ∧ C = 2 * c + r ∧ D = 2 * d + r :=
    ⟨A / 2, B / 2, C / 2, D / 2, A % 2, by omega, by omega, by omega, by omega⟩
  subst hA hB hC hD
  have hNQ : normSq (x : ℍ[ℚ])
      = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + r * (a + b + c + d) + r ^ 2 : ℤ) : ℚ) := by
    rw [normSq_def', hr, hi, hj, hk]
    push_cast
    ring
  have hnn : (0 : ℤ) ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + r * (a + b + c + d) + r ^ 2 := by
    have h : (0 : ℚ) ≤ normSq (x : ℍ[ℚ]) := normSq_nonneg
    rw [hNQ] at h
    exact_mod_cast h
  exact ⟨_, hNQ.trans (by exact_mod_cast (Int.toNat_of_nonneg hnn).symm)⟩

/-- The Hurwitz order is closed under conjugation (`star` negates the imaginary
coordinates, which preserves the shared parity). -/
theorem star_mem {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) : star x ∈ hurwitzOrder := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := hx
  refine ⟨A, -B, -C, -D, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
    simp only [re_star, imI_star, imJ_star, imK_star, hr, hi, hj, hk] <;>
    push_cast <;>
    ring

/-- The integer norm of a Hurwitz quaternion. -/
noncomputable def hnorm (x : hurwitzOrder) : ℕ := (exists_norm_eq_natCast x).choose

/-- The defining property of `hnorm`: it is the reduced norm, read in `ℚ`. -/
@[simp] theorem hnorm_coe (x : hurwitzOrder) : (hnorm x : ℚ) = normSq (x : ℍ[ℚ]) :=
  (exists_norm_eq_natCast x).choose_spec.symm

/-- The integer norm is multiplicative — inherited from `normSq` being a
`MonoidWithZeroHom`.  This is what makes the norm a Euclidean-style size function. -/
theorem hnorm_mul (x y : hurwitzOrder) : hnorm (x * y) = hnorm x * hnorm y := by
  have h : ((hnorm (x * y) : ℕ) : ℚ) = ((hnorm x * hnorm y : ℕ) : ℚ) := by
    push_cast [hnorm_coe]
    exact map_mul normSq (x : ℍ[ℚ]) (y : ℍ[ℚ])
  exact_mod_cast h

/-- Only `0` has norm `0` (`ℍ[ℚ]` is a division ring, so `normSq` is nondegenerate). -/
@[simp] theorem hnorm_eq_zero_iff {x : hurwitzOrder} : hnorm x = 0 ↔ x = 0 := by
  rw [← Nat.cast_inj (R := ℚ), hnorm_coe, Nat.cast_zero, normSq_eq_zero]
  exact ⟨fun h => Subtype.ext (by simpa using h), fun h => by simp [h]⟩

/-- Norm-one in `ℕ` is the same as norm-one in `ℚ`; the bridge used to move between the
integer norm and `normSq` when characterising units. -/
theorem hnorm_eq_one_iff {x : hurwitzOrder} : hnorm x = 1 ↔ normSq (x : ℍ[ℚ]) = 1 := by
  rw [← hnorm_coe]
  norm_cast

/-- A Hurwitz quaternion is a unit of the order iff its norm is `1`
[Jacobs p. 22; Voight 11.1.9].  The inverse of a norm-one `x` is its conjugate `star x`,
which `star_mem` puts back in the order. -/
theorem isUnit_iff_hnorm_eq_one {x : hurwitzOrder} : IsUnit x ↔ hnorm x = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    refine Nat.eq_one_of_mul_eq_one_right (n := hnorm ((u⁻¹ : (hurwitzOrder)ˣ) : hurwitzOrder)) ?_
    rw [← hnorm_mul, u.mul_inv, hnorm_eq_one_iff]
    simp
  · intro h
    have hn : normSq (x : ℍ[ℚ]) = 1 := hnorm_eq_one_iff.mp h
    exact ⟨⟨x, ⟨star (x : ℍ[ℚ]), star_mem x.2⟩,
      Subtype.ext (by simp [self_mul_star, hn]),
      Subtype.ext (by simp [star_mul_self, hn])⟩, rfl⟩

/-- **The norm-one equation in halved coordinates.**  Writing `x = (A + Bi + Cj + Dk)/2`,
`N(x) = (A² + B² + C² + D²)/4`, so the units of `𝓞` are exactly the `x ∈ 𝓞` whose
halved coordinates satisfy `A² + B² + C² + D² = 4`.  This bounds every coordinate by
`|A| ≤ 2`, turning the unit enumeration into a finite check on `[-2, 2]⁴`. -/
theorem hnorm_eq_one_iff_coords {x : hurwitzOrder} {A B C D : ℤ}
    (hr : (x : ℍ[ℚ]).re = (A : ℚ) / 2) (hi : (x : ℍ[ℚ]).imI = (B : ℚ) / 2)
    (hj : (x : ℍ[ℚ]).imJ = (C : ℚ) / 2) (hk : (x : ℍ[ℚ]).imK = (D : ℚ) / 2) :
    hnorm x = 1 ↔ A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 := by
  have key : normSq (x : ℍ[ℚ]) = ((A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 : ℤ) : ℚ) / 4 := by
    rw [normSq_def', hr, hi, hj, hk]
    push_cast
    ring
  rw [hnorm_eq_one_iff, key, div_eq_one_iff_eq (by norm_num : (4 : ℚ) ≠ 0)]
  norm_cast

/-- If four integer squares sum to `4` then each of them is at most `4`; equivalently, every
coordinate of a unit is bounded by `|A| ≤ 2`. -/
theorem abs_le_two_of_hnorm_eq_one {A B C D : ℤ} (h : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4) :
    A ^ 2 ≤ 4 := by nlinarith [sq_nonneg B, sq_nonneg C, sq_nonneg D]

/-- The halved-coordinate tuples of the units: `(A,B,C,D) ∈ [-2,2]⁴` with
`A² + B² + C² + D² = 4` and all four of the same parity.  The box is justified by
`abs_le_two_of_hnorm_eq_one`. -/
def unitTuples : Finset (ℤ × ℤ × ℤ × ℤ) :=
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
  obtain ⟨h1, h2, h3, h4⟩ := QuaternionAlgebra.ext_iff.mp h
  simp only [ofTuple_re, ofTuple_imI, ofTuple_imJ, ofTuple_imK] at h1 h2 h3 h4
  simp only [Prod.mk.injEq]
  exact ⟨by exact_mod_cast (by linarith : (A : ℚ) = A'),
    by exact_mod_cast (by linarith : (B : ℚ) = B'),
    by exact_mod_cast (by linarith : (C : ℚ) = C'),
    by exact_mod_cast (by linarith : (D : ℚ) = D')⟩

/-- A same-parity tuple names an element of the Hurwitz order. -/
theorem ofTuple_mem_of_parity {t : ℤ × ℤ × ℤ × ℤ}
    (hp : t.1 % 2 = t.2.1 % 2 ∧ t.2.1 % 2 = t.2.2.1 % 2 ∧ t.2.2.1 % 2 = t.2.2.2 % 2) :
    ofTuple t ∈ hurwitzOrder :=
  ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, rfl, rfl, rfl, rfl, hp.1, hp.2.1, hp.2.2⟩

/-- **The count is 24** — machine-checked, independently of [Jacobs p. 22]'s list:
`8` all-even tuples (the permutations of `(±2,0,0,0)`, i.e. the Lipschitz units
`±1, ±i, ±j, ±k`) and `16` all-odd tuples (`{±1}⁴`, i.e. the half-units
`(±1±i±j±k)/2`). -/
theorem card_unitTuples : unitTuples.card = 24 := by decide

/-- A tuple in `unitTuples` names an element of the Hurwitz order. -/
theorem ofTuple_mem_of_mem_unitTuples {t : ℤ × ℤ × ℤ × ℤ} (ht : t ∈ unitTuples) :
    ofTuple t ∈ hurwitzOrder := by
  simp only [unitTuples, Finset.mem_filter] at ht
  exact ofTuple_mem_of_parity ⟨ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩

private theorem isUnit_ofTuple {t : ℤ × ℤ × ℤ × ℤ} (ht : t ∈ unitTuples) :
    IsUnit (⟨ofTuple t, ofTuple_mem_of_mem_unitTuples ht⟩ : hurwitzOrder) := by
  simp only [unitTuples, Finset.mem_filter] at ht
  exact isUnit_iff_hnorm_eq_one.mpr ((hnorm_eq_one_iff_coords rfl rfl rfl rfl).mpr ht.2.1)

/-- **Conversely, every tuple in `unitTuples` names a unit.**  Together with
`exists_tuple_of_unit` this is the `24`-element enumeration in usable form. -/
theorem exists_unit_of_tuple {t : ℤ × ℤ × ℤ × ℤ} (ht : t ∈ unitTuples) :
    ∃ u : (hurwitzOrder)ˣ, ((u : hurwitzOrder) : ℍ[ℚ]) = ofTuple t :=
  ⟨(isUnit_ofTuple ht).unit, by simp [IsUnit.unit_spec]⟩

/-- **Every unit of the Hurwitz order is `ofTuple t` for a tuple in `unitTuples`.**
The enumeration behind `card_units_hurwitzOrder`, exposed so that the `mod 9` orbit
computation (`PhD/Jacobs/U3/ClassSet.lean`, B09) can case on the 24 units. -/
theorem exists_tuple_of_unit (u : (hurwitzOrder)ˣ) :
    ∃ t ∈ unitTuples, ofTuple t = ((u : hurwitzOrder) : ℍ[ℚ]) := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := (u : hurwitzOrder).2
  have hn : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 :=
    (hnorm_eq_one_iff_coords hr hi hj hk).mp (isUnit_iff_hnorm_eq_one.mp ⟨u, rfl⟩)
  have hbox : ∀ z : ℤ, z ^ 2 ≤ 4 → z ∈ Finset.Icc (-2 : ℤ) 2 := fun z hz =>
    Finset.mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩
  refine ⟨(A, B, C, D), ?_, ?_⟩
  · simp only [unitTuples, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hbox A (by nlinarith [sq_nonneg B, sq_nonneg C, sq_nonneg D]),
      hbox B (by nlinarith [sq_nonneg A, sq_nonneg C, sq_nonneg D]),
      hbox C (by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg D]),
      hbox D (by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C])⟩,
      hn, hAB, hBC, hCD⟩
  · refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [hr, hi, hj, hk]

/-- The unit group of the Hurwitz order has exactly `24` elements
[Jacobs p. 22: `{±1, ±i, ±j, ±k, ±u₁, …, ±u₈}`] — the `8` Lipschitz units `±1, ±i, ±j, ±k`
and the `16` half-units `(±1±i±j±k)/2`. -/
theorem card_units_hurwitzOrder : Nat.card (hurwitzOrder)ˣ = 24 := by
  classical
  refine (Nat.card_eq_of_bijective (fun s : {t : ℤ × ℤ × ℤ × ℤ // t ∈ unitTuples} =>
    (isUnit_ofTuple s.2).unit) ⟨?_, ?_⟩).symm.trans ?_
  · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
    refine Subtype.ext (ofTuple_injective ?_)
    simpa [IsUnit.unit_spec] using
      congrArg (fun u : (hurwitzOrder)ˣ => ((u : hurwitzOrder) : ℍ[ℚ])) h
  · intro u
    obtain ⟨t, ht, hx⟩ := exists_tuple_of_unit u
    exact ⟨⟨t, ht⟩, Units.ext (Subtype.ext (by simpa [IsUnit.unit_spec] using hx))⟩
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_unitTuples]

end JacobsSlash
