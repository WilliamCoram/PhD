/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Quaternion.Definite

/-!
# The Hurwitz order

The Hurwitz order `𝒪 = ℤ + ℤi + ℤj + ℤω ⊆ ℍ[ℚ]`, `ω = (1 + i + j + k)/2`: the quaternions whose
coordinates are all integers or all half-integers. It is a maximal order, its unit group has `24`
elements, it is right (and left) norm Euclidean, and consequently every right ideal is principal.

[Voi21, Lemma 11.1.2]: "The lattice `O = ℤ + ℤi + ℤj + ℤω` in `B` is the unique order that properly
contains `ℤ⟨i, j⟩`, and `O` is maximal." [Voi21, Lemma 11.3.2]: "For all `α, β ∈ O` with `β ≠ 0`,
there exists `μ, ρ ∈ O` such that `α = βμ + ρ` and `nrd(ρ) < nrd(β)`." [Voi21, Proposition 11.3.4]:
"Every right ideal `I ⊆ O` is right principal."

## Main definitions

* `Quaternion.IsHurwitz`: membership in halved-coordinate parity form.
* `Quaternion.hurwitzOrder`: the Hurwitz order, a subring of `ℍ[ℚ]`.
* `Quaternion.hurwitzOmega`: `ω = (1 + i + j + k)/2`.

## Main results

* `Quaternion.mem_hurwitzOrder_iff_exists_int`: `𝒪 = ℤ + ℤi + ℤj + ℤω`.
* `Quaternion.star_mem_hurwitzOrder`: `𝒪` is closed under conjugation.
* `Quaternion.exists_nrd_eq_natCast`, `Quaternion.exists_trd_eq_intCast`: the reduced norm and
  trace of a Hurwitz quaternion are a natural number and an integer.
* `Quaternion.isUnit_hurwitzOrder_iff`: the units are the elements of reduced norm `1`.
* `Quaternion.card_units_hurwitzOrder`: `|𝒪^×| = 24`.
* `Quaternion.exists_nrd_sub_le_half`: the covering bound behind the Euclidean algorithm.
* `Quaternion.exists_div_rem_right`, `Quaternion.exists_div_rem_left`: the Euclidean algorithm.
* `Quaternion.right_ideal_principal`.
* `Quaternion.eq_hurwitzOrder_of_le`: maximality.

## Implementation notes

`ℍ[ℚ]` is `Quaternion ℚ`, a non-reducible `def` for `ℍ[ℚ,-1,-1]`, so the `QuaternionAlgebra`-level
component lemmas do not fire on its terms, and an anonymous constructor written at type `ℍ[ℚ]`
elaborates at `ℍ[ℚ,-1,-1]`, straddling that seam. Every quaternion constant used here is therefore
a named `ℍ[ℚ]`-level definition (`qI`, `qJ`, `qK`, `hurwitzOmega`, `ofTuple`) kept opaque and
equipped with `rfl` component lemmas; component computations use a curated `simp only` over those
lemmas rather than `simp`, whose cast lemmas would split casts at quaternion level. Statements
about `nrd` are converted to `Quaternion.normSq` before any rewriting.

Roadmap: §0.1.4. Tau Ceti home: `TauCeti/Algebra/QuaternionAlgebra/Hurwitz.lean`.
-/

open scoped Quaternion
open QuaternionAlgebra

noncomputable section

namespace Quaternion

/-- The coordinates of `x` are all integers or all half-integers. -/
def IsHurwitz (x : ℍ[ℚ]) : Prop :=
  ∃ A B C D : ℤ, x.re = (A : ℚ) / 2 ∧ x.imI = (B : ℚ) / 2 ∧ x.imJ = (C : ℚ) / 2 ∧
    x.imK = (D : ℚ) / 2 ∧ A % 2 = B % 2 ∧ B % 2 = C % 2 ∧ C % 2 = D % 2

/-- **The Hurwitz order** `ℤ⟨i, j, (1 + i + j + k)/2⟩ ⊆ ℍ[ℚ]`. -/
def hurwitzOrder : Subring ℍ[ℚ] where
  carrier := {x | IsHurwitz x}
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
  one_mem' := by refine ⟨2, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  add_mem' := by
    rintro x y ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
      ⟨A', B', C', D', hr', hi', hj', hk', hAB', hBC', hCD'⟩
    refine ⟨A + A', B + B', C + C', D + D', ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
      simp only [re_add, imI_add, imJ_add, imK_add, hr, hi, hj, hk, hr', hi', hj', hk'] <;>
      push_cast <;>
      ring
  zero_mem' := by refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  neg_mem' := by
    rintro x ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
    refine ⟨-A, -B, -C, -D, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
      simp only [re_neg, imI_neg, imJ_neg, imK_neg, hr, hi, hj, hk] <;>
      push_cast <;>
      ring

theorem mem_hurwitzOrder_iff {x : ℍ[ℚ]} : x ∈ hurwitzOrder ↔ IsHurwitz x := Iff.rfl

/-- `ω = (1 + i + j + k)/2`. -/
def hurwitzOmega : ℍ[ℚ] := ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩

@[simp] private theorem hurwitzOmega_re : hurwitzOmega.re = 1 / 2 := rfl
@[simp] private theorem hurwitzOmega_imI : hurwitzOmega.imI = 1 / 2 := rfl
@[simp] private theorem hurwitzOmega_imJ : hurwitzOmega.imJ = 1 / 2 := rfl
@[simp] private theorem hurwitzOmega_imK : hurwitzOmega.imK = 1 / 2 := rfl

@[simp] private theorem intCast_re (n : ℤ) : ((n : ℍ[ℚ])).re = (n : ℚ) := rfl
@[simp] private theorem intCast_imI (n : ℤ) : ((n : ℍ[ℚ])).imI = 0 := rfl
@[simp] private theorem intCast_imJ (n : ℤ) : ((n : ℍ[ℚ])).imJ = 0 := rfl
@[simp] private theorem intCast_imK (n : ℤ) : ((n : ℍ[ℚ])).imK = 0 := rfl

@[simp] private theorem ofNat_re (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℍ[ℚ]).re = OfNat.ofNat n := rfl
@[simp] private theorem ofNat_imI (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℍ[ℚ]).imI = 0 := rfl
@[simp] private theorem ofNat_imJ (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℍ[ℚ]).imJ = 0 := rfl
@[simp] private theorem ofNat_imK (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℍ[ℚ]).imK = 0 := rfl

private def qI : ℍ[ℚ] := ⟨0, 1, 0, 0⟩

private def qJ : ℍ[ℚ] := ⟨0, 0, 1, 0⟩

@[simp] private theorem qI_re : qI.re = 0 := rfl
@[simp] private theorem qI_imI : qI.imI = 1 := rfl
@[simp] private theorem qI_imJ : qI.imJ = 0 := rfl
@[simp] private theorem qI_imK : qI.imK = 0 := rfl
@[simp] private theorem qJ_re : qJ.re = 0 := rfl
@[simp] private theorem qJ_imI : qJ.imI = 0 := rfl
@[simp] private theorem qJ_imJ : qJ.imJ = 1 := rfl
@[simp] private theorem qJ_imK : qJ.imK = 0 := rfl

private def qK : ℍ[ℚ] := ⟨0, 0, 0, 1⟩

@[simp] private theorem qK_re : qK.re = 0 := rfl
@[simp] private theorem qK_imI : qK.imI = 0 := rfl
@[simp] private theorem qK_imJ : qK.imJ = 0 := rfl
@[simp] private theorem qK_imK : qK.imK = 1 := rfl

/-- **`𝒪 = ℤ + ℤi + ℤj + ℤω`.** -/
theorem mem_hurwitzOrder_iff_exists_int {x : ℍ[ℚ]} :
    x ∈ hurwitzOrder ↔ ∃ n₀ n₁ n₂ n₃ : ℤ,
      x = (n₀ : ℍ[ℚ]) + (n₁ : ℍ[ℚ]) * ⟨0, 1, 0, 0⟩ + (n₂ : ℍ[ℚ]) * ⟨0, 0, 1, 0⟩ +
        (n₃ : ℍ[ℚ]) * hurwitzOmega := by
  simp only [show (⟨0, 1, 0, 0⟩ : ℍ[ℚ]) = qI from rfl, show (⟨0, 0, 1, 0⟩ : ℍ[ℚ]) = qJ from rfl]
  constructor
  · rintro ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩
    obtain ⟨a, b, c, d, r, hA, hB, hC, hD⟩ :
        ∃ a b c d r : ℤ, A = 2 * a + r ∧ B = 2 * b + r ∧ C = 2 * c + r ∧ D = 2 * d + r :=
      ⟨A / 2, B / 2, C / 2, D / 2, A % 2, by omega, by omega, by omega, by omega⟩
    subst hA hB hC hD
    refine ⟨a - d, b - d, c - d, 2 * d + r, ?_⟩
    ext <;>
      simp only [re_add, imI_add, imJ_add, imK_add, re_mul, imI_mul, imJ_mul, imK_mul,
        intCast_re, intCast_imI, intCast_imJ, intCast_imK, qI_re, qI_imI, qI_imJ, qI_imK,
        qJ_re, qJ_imI, qJ_imJ, qJ_imK, hurwitzOmega_re, hurwitzOmega_imI, hurwitzOmega_imJ,
        hurwitzOmega_imK, hr, hi, hj, hk] <;>
      push_cast <;> ring
  · rintro ⟨n₀, n₁, n₂, n₃, rfl⟩
    refine ⟨2 * n₀ + n₃, 2 * n₁ + n₃, 2 * n₂ + n₃, n₃, ?_, ?_, ?_, ?_, by omega, by omega,
      by omega⟩ <;>
      simp only [re_add, imI_add, imJ_add, imK_add, re_mul, imI_mul, imJ_mul, imK_mul,
        intCast_re, intCast_imI, intCast_imJ, intCast_imK, qI_re, qI_imI, qI_imJ, qI_imK,
        qJ_re, qJ_imI, qJ_imJ, qJ_imK, hurwitzOmega_re, hurwitzOmega_imI, hurwitzOmega_imJ,
        hurwitzOmega_imK] <;>
      push_cast <;> ring

theorem star_mem_hurwitzOrder {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) : star x ∈ hurwitzOrder := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := hx
  refine ⟨A, -B, -C, -D, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
    simp only [re_star, imI_star, imJ_star, imK_star, hr, hi, hj, hk] <;>
    push_cast <;>
    ring

/-- The reduced norm of a Hurwitz quaternion is a natural number. -/
theorem exists_nrd_eq_natCast {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) : ∃ n : ℕ, nrd x = (n : ℚ) := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := hx
  obtain ⟨a, b, c, d, r, hA, hB, hC, hD⟩ :
      ∃ a b c d r : ℤ, A = 2 * a + r ∧ B = 2 * b + r ∧ C = 2 * c + r ∧ D = 2 * d + r :=
    ⟨A / 2, B / 2, C / 2, D / 2, A % 2, by omega, by omega, by omega, by omega⟩
  subst hA hB hC hD
  have hNQ : nrd x = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + r * (a + b + c + d) + r ^ 2 : ℤ) : ℚ) := by
    rw [nrd_eq_normSq, normSq_def', hr, hi, hj, hk]
    push_cast
    ring
  have hnn : (0 : ℤ) ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + r * (a + b + c + d) + r ^ 2 := by
    have h : (0 : ℚ) ≤ nrd x := by
      rw [nrd_eq_normSq]
      exact normSq_nonneg
    rw [hNQ] at h
    exact_mod_cast h
  exact ⟨_, hNQ.trans (by exact_mod_cast (Int.toNat_of_nonneg hnn).symm)⟩

/-- The reduced trace of a Hurwitz quaternion is an integer. -/
theorem exists_trd_eq_intCast {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) : ∃ n : ℤ, trd x = (n : ℚ) := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := hx
  refine ⟨A, ?_⟩
  have h2 : trd x = 2 * x.re := rfl
  rw [h2, hr]
  ring

/-- **A Hurwitz quaternion is a unit of the order exactly when its reduced norm is `1`.** -/
theorem isUnit_hurwitzOrder_iff {x : hurwitzOrder} : IsUnit x ↔ nrd (x : ℍ[ℚ]) = 1 := by
  rw [nrd_eq_normSq]
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨n, hn⟩ := exists_nrd_eq_natCast (u : hurwitzOrder).2
    obtain ⟨m, hm⟩ := exists_nrd_eq_natCast ((u⁻¹ : (hurwitzOrder)ˣ) : hurwitzOrder).2
    rw [nrd_eq_normSq] at hn hm
    have h1 : normSq ((u : hurwitzOrder) : ℍ[ℚ])
        * normSq (((u⁻¹ : (hurwitzOrder)ˣ) : hurwitzOrder) : ℍ[ℚ]) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, u.mul_inv, Subring.coe_one, map_one]
    rw [hn, hm] at h1
    have hnm : n * m = 1 := by exact_mod_cast h1
    rw [hn, Nat.eq_one_of_mul_eq_one_right hnm]
    norm_num
  · intro h
    refine ⟨⟨x, ⟨star (x : ℍ[ℚ]), star_mem_hurwitzOrder x.2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · rw [Subring.coe_mul, Subring.coe_one, self_mul_star, h, coe_one]
    · rw [Subring.coe_mul, Subring.coe_one, star_mul_self, h, coe_one]

/-- The quaternion `(A + Bi + Cj + Dk)/2` of a tuple of integers. -/
def ofTuple (t : ℤ × ℤ × ℤ × ℤ) : ℍ[ℚ] :=
  ⟨(t.1 : ℚ) / 2, (t.2.1 : ℚ) / 2, (t.2.2.1 : ℚ) / 2, (t.2.2.2 : ℚ) / 2⟩

@[simp] theorem ofTuple_re (t : ℤ × ℤ × ℤ × ℤ) : (ofTuple t).re = (t.1 : ℚ) / 2 := rfl

@[simp] theorem ofTuple_imI (t : ℤ × ℤ × ℤ × ℤ) : (ofTuple t).imI = (t.2.1 : ℚ) / 2 := rfl

@[simp] theorem ofTuple_imJ (t : ℤ × ℤ × ℤ × ℤ) :
    (ofTuple t).imJ = (t.2.2.1 : ℚ) / 2 := rfl

@[simp] theorem ofTuple_imK (t : ℤ × ℤ × ℤ × ℤ) :
    (ofTuple t).imK = (t.2.2.2 : ℚ) / 2 := rfl

private theorem ofTuple_mem_of_parity {t : ℤ × ℤ × ℤ × ℤ}
    (hp : t.1 % 2 = t.2.1 % 2 ∧ t.2.1 % 2 = t.2.2.1 % 2 ∧ t.2.2.1 % 2 = t.2.2.2 % 2) :
    ofTuple t ∈ hurwitzOrder :=
  ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, rfl, rfl, rfl, rfl, hp.1, hp.2.1, hp.2.2⟩

/-- Distinct tuples give distinct quaternions. -/
theorem ofTuple_injective : Function.Injective ofTuple := by
  rintro ⟨A, B, C, D⟩ ⟨A', B', C', D'⟩ h
  obtain ⟨h1, h2, h3, h4⟩ := QuaternionAlgebra.ext_iff.mp h
  simp only [ofTuple] at h1 h2 h3 h4
  simp only [Prod.mk.injEq]
  exact ⟨by exact_mod_cast (by linarith : (A : ℚ) = A'),
    by exact_mod_cast (by linarith : (B : ℚ) = B'),
    by exact_mod_cast (by linarith : (C : ℚ) = C'),
    by exact_mod_cast (by linarith : (D : ℚ) = D')⟩

private theorem nrd_eq_one_iff_coords {x : ℍ[ℚ]} {A B C D : ℤ} (hr : x.re = (A : ℚ) / 2)
    (hi : x.imI = (B : ℚ) / 2) (hj : x.imJ = (C : ℚ) / 2) (hk : x.imK = (D : ℚ) / 2) :
    nrd x = 1 ↔ A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 := by
  have key : nrd x = ((A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 : ℤ) : ℚ) / 4 := by
    rw [nrd_eq_normSq, normSq_def', hr, hi, hj, hk]
    push_cast
    ring
  rw [key, div_eq_one_iff_eq (by norm_num : (4 : ℚ) ≠ 0)]
  norm_cast

/-- The `24` tuples `(A, B, C, D)` of the Hurwitz units `(A + Bi + Cj + Dk)/2`. -/
def unitTuples : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2) ×ˢ
    (Finset.Icc (-2 : ℤ) 2)).filter
    (fun t => t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = 4 ∧
      t.1 % 2 = t.2.1 % 2 ∧ t.2.1 % 2 = t.2.2.1 % 2 ∧ t.2.2.1 % 2 = t.2.2.2 % 2)

private theorem card_unitTuples : unitTuples.card = 24 := by decide

/-- The unit tuples give Hurwitz quaternions. -/
theorem ofTuple_mem_of_mem_unitTuples {t : ℤ × ℤ × ℤ × ℤ} (ht : t ∈ unitTuples) :
    ofTuple t ∈ hurwitzOrder := by
  simp only [unitTuples, Finset.mem_filter] at ht
  exact ofTuple_mem_of_parity ⟨ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩

/-- The unit tuples give Hurwitz units. -/
theorem isUnit_ofTuple {t : ℤ × ℤ × ℤ × ℤ} (ht : t ∈ unitTuples) :
    IsUnit (⟨ofTuple t, ofTuple_mem_of_mem_unitTuples ht⟩ : hurwitzOrder) := by
  simp only [unitTuples, Finset.mem_filter] at ht
  exact isUnit_hurwitzOrder_iff.mpr ((nrd_eq_one_iff_coords rfl rfl rfl rfl).mpr ht.2.1)

/-- Every Hurwitz unit comes from a unit tuple. -/
theorem exists_tuple_of_unit (u : (hurwitzOrder)ˣ) :
    ∃ t ∈ unitTuples, ofTuple t = ((u : hurwitzOrder) : ℍ[ℚ]) := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := (u : hurwitzOrder).2
  have hn : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 :=
    (nrd_eq_one_iff_coords hr hi hj hk).mp (isUnit_hurwitzOrder_iff.mp ⟨u, rfl⟩)
  have hbox : ∀ z : ℤ, z ^ 2 ≤ 4 → z ∈ Finset.Icc (-2 : ℤ) 2 := fun z hz =>
    Finset.mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩
  refine ⟨(A, B, C, D), ?_, ?_⟩
  · simp only [unitTuples, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hbox A (by nlinarith [sq_nonneg B, sq_nonneg C, sq_nonneg D]),
      hbox B (by nlinarith [sq_nonneg A, sq_nonneg C, sq_nonneg D]),
      hbox C (by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg D]),
      hbox D (by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C])⟩, hn, hAB, hBC, hCD⟩
  · exact QuaternionAlgebra.ext hr.symm hi.symm hj.symm hk.symm

/-- **The Hurwitz order has exactly `24` units**: `±1, ±i, ±j, ±k, (±1 ± i ± j ± k)/2`. -/
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

private theorem sq_add_sq_round_le (c : ℚ) :
    (c - (round c : ℚ)) ^ 2 + (c - 1 / 2 - (round (c - 1 / 2) : ℚ)) ^ 2 ≤ 1 / 4 := by
  obtain ⟨hf1, hf2⟩ := abs_le.mp (abs_sub_round c)
  obtain ⟨hg1, hg2⟩ := abs_le.mp (abs_sub_round (c - 1 / 2))
  refine sq_add_sq_le_quarter (round c - round (c - 1 / 2)) hf1 hf2 hg1 hg2 ?_
  push_cast
  ring

private theorem parity_two_mul_add (u v e : ℤ) : (2 * u + e) % 2 = (2 * v + e) % 2 := by omega

private theorem exists_normSq_sub_eq (γ : ℍ[ℚ]) (s : ℚ) (e : ℤ) (he : (e : ℚ) = 2 * s) :
    ∃ μ ∈ hurwitzOrder, normSq (γ - μ)
      = (γ.re - s - (round (γ.re - s) : ℚ)) ^ 2 + (γ.imI - s - (round (γ.imI - s) : ℚ)) ^ 2
        + (γ.imJ - s - (round (γ.imJ - s) : ℚ)) ^ 2
        + (γ.imK - s - (round (γ.imK - s) : ℚ)) ^ 2 := by
  refine ⟨ofTuple (2 * round (γ.re - s) + e, 2 * round (γ.imI - s) + e,
    2 * round (γ.imJ - s) + e, 2 * round (γ.imK - s) + e),
    ofTuple_mem_of_parity ⟨parity_two_mul_add _ _ _, parity_two_mul_add _ _ _,
      parity_two_mul_add _ _ _⟩, ?_⟩
  rw [normSq_def']
  simp only [re_sub, imI_sub, imJ_sub, imK_sub, ofTuple_re, ofTuple_imI, ofTuple_imJ,
    ofTuple_imK]
  push_cast [he]
  ring

/-- Every rational quaternion is within reduced norm `1/2` of a Hurwitz quaternion. -/
theorem exists_nrd_sub_le_half (γ : ℍ[ℚ]) : ∃ μ ∈ hurwitzOrder, nrd (γ - μ) ≤ 1 / 2 := by
  obtain ⟨μ₁, hμ₁mem, hμ₁⟩ := exists_normSq_sub_eq γ 0 0 (by norm_num)
  obtain ⟨μ₂, hμ₂mem, hμ₂⟩ := exists_normSq_sub_eq γ (1 / 2) 1 (by norm_num)
  simp only [sub_zero] at hμ₁
  have hsum : normSq (γ - μ₁) + normSq (γ - μ₂) ≤ 1 := by
    rw [hμ₁, hμ₂]
    linarith [sq_add_sq_round_le γ.re, sq_add_sq_round_le γ.imI, sq_add_sq_round_le γ.imJ,
      sq_add_sq_round_le γ.imK]
  rcases le_total (normSq (γ - μ₁)) (normSq (γ - μ₂)) with h | h
  · exact ⟨μ₁, hμ₁mem, by rw [nrd_eq_normSq]; linarith⟩
  · exact ⟨μ₂, hμ₂mem, by rw [nrd_eq_normSq]; linarith⟩

private theorem normSq_pos_of_ne_zero {x : ℍ[ℚ]} (hx : x ≠ 0) : 0 < normSq x :=
  normSq_nonneg.lt_of_ne' (normSq_ne_zero.mpr hx)

/-- **The Hurwitz order is right norm Euclidean.** -/
theorem exists_div_rem_right (α β : hurwitzOrder) (hβ : β ≠ 0) :
    ∃ μ ρ : hurwitzOrder, α = β * μ + ρ ∧ nrd (ρ : ℍ[ℚ]) < nrd (β : ℍ[ℚ]) := by
  have hβ' : (β : ℍ[ℚ]) ≠ 0 := fun h => hβ (Subtype.ext h)
  obtain ⟨μ, hμmem, hμ⟩ := exists_nrd_sub_le_half ((β : ℍ[ℚ])⁻¹ * (α : ℍ[ℚ]))
  rw [nrd_eq_normSq] at hμ
  refine ⟨⟨μ, hμmem⟩, α - β * ⟨μ, hμmem⟩, by abel, ?_⟩
  have hcoe : ((α - β * ⟨μ, hμmem⟩ : hurwitzOrder) : ℍ[ℚ])
      = (β : ℍ[ℚ]) * ((β : ℍ[ℚ])⁻¹ * (α : ℍ[ℚ]) - μ) := by
    push_cast
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hβ', one_mul]
  have hnb : 0 < normSq (β : ℍ[ℚ]) := normSq_pos_of_ne_zero hβ'
  rw [nrd_eq_normSq, nrd_eq_normSq, hcoe, map_mul]
  nlinarith [mul_le_mul_of_nonneg_left hμ hnb.le]

/-- **The Hurwitz order is left norm Euclidean.** -/
theorem exists_div_rem_left (α β : hurwitzOrder) (hβ : β ≠ 0) :
    ∃ μ ρ : hurwitzOrder, α = μ * β + ρ ∧ nrd (ρ : ℍ[ℚ]) < nrd (β : ℍ[ℚ]) := by
  have hβ' : (β : ℍ[ℚ]) ≠ 0 := fun h => hβ (Subtype.ext h)
  obtain ⟨μ, hμmem, hμ⟩ := exists_nrd_sub_le_half ((α : ℍ[ℚ]) * (β : ℍ[ℚ])⁻¹)
  rw [nrd_eq_normSq] at hμ
  refine ⟨⟨μ, hμmem⟩, α - ⟨μ, hμmem⟩ * β, by abel, ?_⟩
  have hcoe : ((α - ⟨μ, hμmem⟩ * β : hurwitzOrder) : ℍ[ℚ])
      = ((α : ℍ[ℚ]) * (β : ℍ[ℚ])⁻¹ - μ) * (β : ℍ[ℚ]) := by
    push_cast
    rw [sub_mul, mul_assoc, inv_mul_cancel₀ hβ', mul_one]
  have hnb : 0 < normSq (β : ℍ[ℚ]) := normSq_pos_of_ne_zero hβ'
  rw [nrd_eq_normSq, nrd_eq_normSq, hcoe, map_mul]
  nlinarith [mul_le_mul_of_nonneg_right hμ hnb.le]

private noncomputable def hnorm (x : hurwitzOrder) : ℕ := (exists_nrd_eq_natCast x.2).choose

private theorem hnorm_coe (x : hurwitzOrder) : (hnorm x : ℚ) = nrd (x : ℍ[ℚ]) :=
  (exists_nrd_eq_natCast x.2).choose_spec.symm

private theorem hnorm_coe' (x : hurwitzOrder) : (hnorm x : ℚ) = normSq (x : ℍ[ℚ]) := by
  rw [hnorm_coe, nrd_eq_normSq]

/-- **Every right ideal of the Hurwitz order is principal.** -/
theorem right_ideal_principal (I : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder) :
    ∃ x : hurwitzOrder, I = Submodule.span (hurwitzOrder)ᵐᵒᵖ {x} := by
  by_cases hI : I = ⊥
  · exact ⟨0, hI.trans (Submodule.span_zero_singleton _).symm⟩
  obtain ⟨y, hyI, hy0⟩ := I.ne_bot_iff.mp hI
  have hSne : {n : ℕ | ∃ z ∈ I, z ≠ 0 ∧ hnorm z = n}.Nonempty := ⟨hnorm y, y, hyI, hy0, rfl⟩
  obtain ⟨x, hxI, hx0, hxn⟩ := Nat.sInf_mem hSne
  refine ⟨x, le_antisymm (fun c hcI => ?_) ((Submodule.span_singleton_le_iff_mem ..).mpr hxI)⟩
  obtain ⟨q, r, hqr, hr⟩ := exists_div_rem_right c x hx0
  have hrI : r ∈ I := by
    rw [eq_sub_of_add_eq' hqr.symm]
    exact I.sub_mem hcI (I.smul_mem (MulOpposite.op q) hxI)
  have hr0 : r = 0 := by
    by_contra hne
    have hlt : hnorm r < hnorm x := by
      rw [← Nat.cast_lt (α := ℚ), hnorm_coe, hnorm_coe]
      exact hr
    have hle : sInf {n : ℕ | ∃ z ∈ I, z ≠ 0 ∧ hnorm z = n} ≤ hnorm r :=
      Nat.sInf_le ⟨r, hrI, hne, rfl⟩
    omega
  rw [hqr, hr0, add_zero]
  exact Submodule.mem_span_singleton.mpr ⟨MulOpposite.op q, rfl⟩

private theorem mem_hurwitzOrder_qI : qI ∈ hurwitzOrder :=
  ⟨0, 2, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by omega, by omega, by omega⟩

private theorem mem_hurwitzOrder_qJ : qJ ∈ hurwitzOrder :=
  ⟨0, 0, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num, by omega, by omega, by omega⟩

private theorem mem_hurwitzOrder_qK : qK ∈ hurwitzOrder :=
  ⟨0, 0, 0, 2, by norm_num, by norm_num, by norm_num, by norm_num, by omega, by omega, by omega⟩

private theorem parity_of_sq_add_sq {A B C D n : ℤ}
    (h : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 * n) :
    A % 2 = B % 2 ∧ B % 2 = C % 2 ∧ C % 2 = D % 2 := by
  obtain ⟨a, pa, hpa, rfl⟩ : ∃ a p, (p = 0 ∨ p = 1) ∧ A = 2 * a + p :=
    ⟨A / 2, A % 2, by omega, by omega⟩
  obtain ⟨b, pb, hpb, rfl⟩ : ∃ b p, (p = 0 ∨ p = 1) ∧ B = 2 * b + p :=
    ⟨B / 2, B % 2, by omega, by omega⟩
  obtain ⟨c, pc, hpc, rfl⟩ : ∃ c p, (p = 0 ∨ p = 1) ∧ C = 2 * c + p :=
    ⟨C / 2, C % 2, by omega, by omega⟩
  obtain ⟨d, pd, hpd, rfl⟩ : ∃ d p, (p = 0 ∨ p = 1) ∧ D = 2 * d + p :=
    ⟨D / 2, D % 2, by omega, by omega⟩
  obtain ⟨m, key⟩ : ∃ m : ℤ, pa + pb + pc + pd = 4 * m := by
    refine ⟨n - (a ^ 2 + a * pa + b ^ 2 + b * pb + c ^ 2 + c * pc + d ^ 2 + d * pd), ?_⟩
    rcases hpa with rfl | rfl <;> rcases hpb with rfl | rfl <;> rcases hpc with rfl | rfl <;>
      rcases hpd with rfl | rfl <;> linarith
  rcases hpa with rfl | rfl <;> rcases hpb with rfl | rfl <;> rcases hpc with rfl | rfl <;>
    rcases hpd with rfl | rfl <;> omega

/-- **The Hurwitz order is a maximal order.** -/
theorem eq_hurwitzOrder_of_le {S : Subring ℍ[ℚ]} (hS : S.toAddSubgroup.FG)
    (hle : hurwitzOrder ≤ S) : S = hurwitzOrder := by
  refine le_antisymm (fun α hα => ?_) hle
  obtain ⟨A, hA⟩ := exists_int_trd_of_fg hS hα
  obtain ⟨B, hB⟩ := exists_int_trd_of_fg hS (S.mul_mem hα (hle mem_hurwitzOrder_qI))
  obtain ⟨C, hC⟩ := exists_int_trd_of_fg hS (S.mul_mem hα (hle mem_hurwitzOrder_qJ))
  obtain ⟨D, hD⟩ := exists_int_trd_of_fg hS (S.mul_mem hα (hle mem_hurwitzOrder_qK))
  obtain ⟨n, hn⟩ := exists_int_nrd_of_fg hS hα
  have e0 : ∀ y : ℍ[ℚ], trd y = 2 * y.re := fun _ ↦ rfl
  rw [e0] at hA hB hC hD
  simp only [re_mul, qI_re, qI_imI, qI_imJ, qI_imK, qJ_re, qJ_imI, qJ_imJ, qJ_imK, qK_re,
    qK_imI, qK_imJ, qK_imK, mul_zero, mul_one, sub_zero, zero_sub] at hB hC hD
  rw [nrd_eq_normSq, normSq_def'] at hn
  have hre : α.re = (A : ℚ) / 2 := by linarith
  have hi : α.imI = ((-B : ℤ) : ℚ) / 2 := by push_cast; linarith
  have hj : α.imJ = ((-C : ℤ) : ℚ) / 2 := by push_cast; linarith
  have hk : α.imK = ((-D : ℤ) : ℚ) / 2 := by push_cast; linarith
  have hsq : A ^ 2 + (-B) ^ 2 + (-C) ^ 2 + (-D) ^ 2 = 4 * n := by
    rw [hre, hi, hj, hk] at hn
    field_simp at hn
    exact_mod_cast hn
  obtain ⟨p1, p2, p3⟩ := parity_of_sq_add_sq hsq
  exact ⟨A, -B, -C, -D, hre, hi, hj, hk, p1, p2, p3⟩


end Quaternion
