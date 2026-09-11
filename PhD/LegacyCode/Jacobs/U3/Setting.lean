/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.«03_Quaternionic»
import PhD.Jacobs.U3Data
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis

/-!
# The Jacobs setting: `D = ℚ(i,j)`, the place `3`, `√−2`, and the rigidification `θ₃`

[Jacobs, *Slopes of Compact Hecke Operators*, Ch. 1 §1.4 pp. 13–14 and Ch. 2 §2.1 p. 22]:

> "Let D be the discriminant 2 quaternion algebra over Q and write D = Q(i,j)."

> "One easily verifies that for all odd primes q the map D_q → M₂(Q_q) given by
> a + bi + cj + dk ↦ (a + bν_q + dξ_q, bξ_q − c − dν_q; bξ_q + c − dν_q, a − bν_q − dξ_q)
> is an isomorphism where ν_q, ξ_q ∈ Z_q satisfy ν_q² + ξ_q² = −1."

> "we choose our elements ν₃, ξ₃ of Z₃ such that ν₃² + ξ₃² = −1 as follows: take ν₃ to be
> the square root of −2 in Z₃ that is 508 mod 3⁷ and ξ₃ = 1."

This file fixes, once for the whole AG-B development, the objects below.

## Main definitions

* `QMF.U3.D := ℍ[ℚ]` — mathlib's quaternions over `ℚ` (Hamilton = discriminant-2 algebra),
  a division ring since `ℚ` is a linearly ordered field;
* `QMF.U3.v₃ : HeightOneSpectrum (𝓞 ℚ)` — the place `3`;
* `QMF.U3.K₃ := v₃.adicCompletion ℚ` with its mathlib `NormedField` structure, and the
  Jacobs typeclass pack (`IsUltrametricDist`, `‖3‖ < 1`, …) needed to instantiate
  `PhD.Jacobs.U3Data` at `K₃`;
* `QMF.U3.ν₃ : K₃` — the Hensel square root of `−2` located at `2695 mod 3¹⁰`
  (existence via mathlib's `hensels_lemma` over `ℤ_[3]` transported along mathlib's
  `padicEquiv : ℚ_[3] ≃A[ℚ] K₃`; the sign is pinned by `ν₃ ≡ 1 mod 3` and the location
  by the ultrametric factorisation `(ν−2695)(ν+2695) = −3¹¹·41` — the argument of
  `Jacobs.Instance.exists_sqrt_neg_two_near`, which transports verbatim);
* `QMF.U3.theta : (D ⊗[ℚ] K₃) ≃ₐ[ℚ] M₂(K₃)` — the isomorphism above at `q = 3`, and the
  `RigidificationAt ℚ D v₃` instance it provides;
* `QMF.U3.γ₉ : ℤᵐ⁰` — the wild-level threshold `v(9)`, and `Sigma1`, the submonoid of
  `Sigma0 K₃ γ₉` of matrices whose `(0,0)`-entry is `≡ 1 mod 9` (the left-handed form of
  Jacobs's "`c ≡ 0, d ≡ 1 mod 9`" congruence: the adjugate swaps `d` into the `(0,0)`
  slot).  On `Sigma1` the character `κ` is `u ↦ u^t` with no Teichmüller correction,
  which is what makes the weight action of `PhD.Jacobs.U3Data` apply.

## Main results

* `Jacobs.U3.theta_tmul_one`: the explicit matrix of `θ₃` on a quaternion, read off the
  four coordinates against `1, i, j, k` — the computational heart of every local check.
* `Jacobs.U3.sq_ν₃`, `Jacobs.U3.ν₃_near`: `ν₃² = −2` and its `3`-adic location
  `ν₃ ≡ 2695 mod 3¹⁰`, the two facts every entry-valuation downstream rests on.
* `Jacobs.U3.valued_three_eq`, `Jacobs.U3.valued_nine_eq`: `3` is a uniformizer at `v₃`
  and `v(9) = γ₉`, so the mod-`9` threshold really is reached by `9`.
* `Jacobs.U3.sigma1_of_mul_eq_one`: `Σ₁(9)` is closed under inversion *inside* the
  integral matrices — read off `MN = NM = 1` without ever forming `M⁻¹`.
* `Jacobs.U3.valuation_three_eq_one_of_ne`,
  `Jacobs.U3.inv_three_mem_adicCompletionIntegers`: away from `3`, both `3` and `3⁻¹` are
  `w`-adic integers — the away-from-`3` input for the certificate memberships.
-/

open Quaternion IsDedekindDomain NumberField QMF
open scoped TensorProduct

namespace Jacobs.U3

/-- Jacobs's `D = ℚ(i,j)`: the quaternion algebra over `ℚ` ramified exactly at `{2, ∞}`
[Jacobs, p. 13].  Mathlib's `ℍ[ℚ]` with its division-ring structure. -/
abbrev D : Type := ℍ[ℚ]

/-- The place `3` of `ℚ`, as a height-one prime of `𝓞 ℚ`. -/
noncomputable def v₃ : HeightOneSpectrum (RingOfIntegers ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩

/-- The local field `ℚ₃`, in its adic-completion incarnation (the `v`-component field of
the `QMF` framework).  Mathlib provides `NormedField K₃`. -/
abbrev K₃ : Type := v₃.adicCompletion ℚ

/- `Algebra ℚ K₃` has two instance paths in scope: `DivisionRing.toRatAlgebra` (from the
field structure of `K₃`) and `HeightOneSpectrum.instAlgebraAdicCompletion` (from the adic
construction).  They are equal — `Subsingleton (Algebra ℚ A)` — but not syntactically, and
the `QMF` framework (`RigidificationAt`, `toLocal`, `toMatrix`) is stated for a *generic*
base field, so it always sees the adic one.  Pinning the adic path here makes `theta`'s
type match the framework's on the nose, which is what lets the rigidification instance be
`⟨theta ν₃ sq_ν₃⟩` with no `Subsingleton.elim` transport — and, downstream, what lets
`θ₃` actually be *computed* on generators (`PhD/Jacobs/U3/Level.lean`). -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

/- The Jacobs typeclass pack at `K₃`.  These instances let every abstract-`K` result of
`PhD.Jacobs.{PadicAnalytic, U3Data, Slopes}` be instantiated at `K = K₃`.
`IsUltrametricDist` and `CompleteSpace` are found by mathlib (`Valued.toNormedField`'s
ultrametric instance; completion completeness); `CharZero` comes from the `ℚ`-algebra
structure, and
`NontriviallyNormedField` is built *on top of* mathlib's `NormedField` instance — same
norm, no diamond — with nontriviality witnessed by `‖3⁻¹‖ > 1`. -/

example : IsUltrametricDist K₃ := inferInstance
example : CompleteSpace K₃ := inferInstance

instance : CharZero K₃ := charZero_of_injective_algebraMap (algebraMap ℚ K₃).injective

/-- The place `v₃` is generated by `3`. -/
private theorem natGenerator_v₃ : Rat.HeightOneSpectrum.natGenerator v₃ = 3 :=
  congrArg Subtype.val
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply (⟨3, Nat.prime_three⟩ : Nat.Primes))

/-- `3` lies in the prime `v₃`. -/
private theorem three_mem_v₃ : (3 : RingOfIntegers ℚ) ∈ v₃.asIdeal := by
  have h : ((3 : ℕ) : ℤ) ∈ v₃.asIdeal.map (Rat.IsIntegralClosure.intEquiv (RingOfIntegers ℚ)) :=
    (Rat.HeightOneSpectrum.natGenerator_dvd_iff v₃).mp (by rw [natGenerator_v₃])
  have hb := (Rat.IsIntegralClosure.intEquiv (RingOfIntegers ℚ)).bijective
  rw [← v₃.asIdeal.comap_map_of_bijective _ hb, Ideal.mem_comap, map_ofNat]
  exact_mod_cast h

/-- The residue-characteristic hypothesis `h3` of the Jacobs development, at `K₃`:
the norm of `3` is `< 1` because `3` generates the place. -/
theorem norm_three_lt_one : ‖(3 : K₃)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  -- Pass to the underlying `UniformSpace.Completion` through the ring isomorphism
  -- `adicCompletion.equiv` (unambiguous — no algebra-instance path involved), where the
  -- valuation of a coerced element is `Valued.valuedCompletion_apply`.
  have h1 : Valued.v (3 : K₃) = Valued.v (3 : (v₃.valuation ℚ).Completion) := by
    rw [← IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_toCompletion (K := ℚ) v₃,
      show ((3 : K₃).toCompletion)
          = IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv ℚ v₃ (3 : K₃) from rfl,
      map_ofNat]
  have h2 : (3 : (v₃.valuation ℚ).Completion)
      = ((3 : WithVal (v₃.valuation ℚ)) : (v₃.valuation ℚ).Completion) :=
    (map_ofNat (UniformSpace.Completion.coeRingHom (α := WithVal (v₃.valuation ℚ))) 3).symm
  have h3 : Valued.v ((3 : WithVal (v₃.valuation ℚ)) : (v₃.valuation ℚ).Completion)
      = v₃.valuation ℚ (3 : ℚ) := Valued.valuedCompletion_apply _
  rw [h1, h2, h3,
    show (3 : ℚ) = algebraMap (RingOfIntegers ℚ) ℚ 3 from (map_ofNat _ 3).symm]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mpr three_mem_v₃

noncomputable instance : NontriviallyNormedField K₃ :=
  { (inferInstance : NormedField K₃) with
    non_trivial := by
      refine ⟨(3 : K₃)⁻¹, ?_⟩
      have h0 : (0 : ℝ) < ‖(3 : K₃)‖ :=
        norm_pos_iff.mpr (three_ne_zero : (3 : K₃) ≠ 0)
      rw [norm_inv]
      exact one_lt_inv_iff₀.mpr ⟨h0, norm_three_lt_one⟩ }

/-- The Hensel square root of `−2` in `ℤ_[3]` with `z ≡ 1 mod 3`: `hensels_lemma` at
`F = X² + 2`, `a = 1` (`‖F(1)‖ = ‖3‖ < 1 = ‖F′(1)‖²`). -/
private theorem exists_padic_sqrt_neg_two :
    ∃ z : ℤ_[3], z ^ 2 = -2 ∧ ‖z - 1‖ < 1 := by
  have h2 : ‖((2 : ℤ) : ℤ_[3])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp fun h => (by decide : ¬ ((3:ℤ) ∣ 2))
        ((PadicInt.norm_int_lt_one_iff_dvd 2).mp h))
  have h2' : ‖((2 : ℕ) : ℤ_[3])‖ = 1 := by
    rw [show ((2 : ℕ) : ℤ_[3]) = ((2 : ℤ) : ℤ_[3]) by push_cast; ring]
    exact h2
  have h3 : ‖((3 : ℕ) : ℤ_[3])‖ = (3 : ℝ)⁻¹ := PadicInt.norm_p (p := 3)
  have hder : ‖(Polynomial.X ^ 2 + Polynomial.C 2 :
      Polynomial ℤ_[3]).derivative.aeval (1 : ℤ_[3])‖ = 1 := by
    simp only [Polynomial.derivative_add, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, add_zero, map_mul, map_pow, Polynomial.aeval_X, one_pow,
      mul_one, map_natCast]
    simpa using h2'
  have hnorm : ‖(Polynomial.X ^ 2 + Polynomial.C 2 : Polynomial ℤ_[3]).aeval (1 : ℤ_[3])‖
      < ‖(Polynomial.X ^ 2 + Polynomial.C 2 :
        Polynomial ℤ_[3]).derivative.aeval (1 : ℤ_[3])‖ ^ 2 := by
    rw [hder]
    simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, one_pow,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (1 : ℤ_[3]) + 2 = ((3 : ℕ) : ℤ_[3]) by norm_num, h3]
    norm_num
  obtain ⟨z, hz0, hznear, -, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_, ?_⟩
  · simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply] at hz0
    linear_combination hz0
  · rw [hder] at hznear
    exact hznear

/-- Some square root of `−2` in `K₃`: the Hensel root of `ℤ_[3]`, transported through
mathlib's comparison equivalence `Padic.adicCompletionEquiv : ℚ_[3] ≃A[ℚ] K₃` (only the
ring structure of the transport is used; the sign is renormalised below). -/
private theorem exists_sqrt_neg_two : ∃ x : K₃, x ^ 2 = -2 := by
  obtain ⟨z, hz, -⟩ := exists_padic_sqrt_neg_two
  refine ⟨Padic.adicCompletionEquiv (R := RingOfIntegers ℚ) ⟨3, Nat.prime_three⟩
    (z : ℚ_[3]), ?_⟩
  have h' : ((z : ℚ_[3])) ^ 2 = -2 := by
    rw [show ((z : ℚ_[3])) ^ 2 = ((z ^ 2 : ℤ_[3]) : ℚ_[3]) by push_cast; ring, hz]
    push_cast
    norm_cast
  calc (Padic.adicCompletionEquiv (R := RingOfIntegers ℚ) ⟨3, Nat.prime_three⟩
        (z : ℚ_[3])) ^ 2
      = (Padic.adicCompletionEquiv (R := RingOfIntegers ℚ) ⟨3, Nat.prime_three⟩)
        ((z : ℚ_[3]) ^ 2) := (map_pow _ _ 2).symm
    _ = -2 := by rw [h', map_neg]; exact congrArg Neg.neg (map_ofNat _ 2)

/-- The square root of `−2` in `K₃` selected by Jacobs [p. 22]: the root that is
`≡ 1 mod 3` (equivalently `≡ 508 mod 3⁷`, `≡ 2695 mod 3¹⁰` — note `508 ≡ 1 mod 3`).
Constructed by sign-normalising an arbitrary root: exactly one of `±ν′` satisfies
`‖ν − 1‖ < 1`, by the factorisation `(ν′−1)(ν′+1) = −3` whose factors differ by the
unit `2`. -/
noncomputable def ν₃ : K₃ :=
  if ‖exists_sqrt_neg_two.choose - 1‖ < 1 then exists_sqrt_neg_two.choose
  else -exists_sqrt_neg_two.choose

@[simp] theorem sq_ν₃ : ν₃ ^ 2 = -2 := by
  unfold ν₃
  split <;> [skip; rw [neg_pow, (by norm_num : (-1 : K₃) ^ 2 = 1), one_mul]] <;>
    exact exists_sqrt_neg_two.choose_spec

/-- The sign normalisation: `‖ν₃ − 1‖ ≤ ‖3‖` (`ν₃ ≡ 1 mod 3`).  From
`(ν₃−1)(ν₃+1) = ν₃² − 1 = −3` with `(ν₃+1) − (ν₃−1) = 2` a unit, the ultrametric forces
`{‖ν₃−1‖, ‖ν₃+1‖} = {‖3‖, 1}`, and the `if` in the definition selects the small
`ν₃ − 1`. -/
private theorem norm_ν₃_sub_one_le : ‖ν₃ - 1‖ ≤ ‖(3 : K₃)‖ := by
  have h3 : ‖(3 : K₃)‖ < 1 := norm_three_lt_one
  have h2 : ‖(2 : K₃)‖ = 1 :=
    Jacobs.norm_ofNat_eq_one h3 (n := 2) (by norm_num) (by norm_num)
  set x := exists_sqrt_neg_two.choose with hxdef
  have hx : x ^ 2 = -2 := exists_sqrt_neg_two.choose_spec
  -- `‖x‖ = 1` from `‖x‖² = ‖−2‖ = 1`
  have hnx : ‖x‖ = 1 := by
    have hsq : ‖x‖ ^ 2 = 1 := by
      rw [← norm_pow, hx, norm_neg, h2]
    nlinarith [norm_nonneg x, hsq]
  -- both factors are integral
  have hm : ‖x - 1‖ ≤ 1 := by
    refine (Jacobs.norm_sub_le_max' x 1).trans ?_
    simp [hnx]
  have hp : ‖x + 1‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max x 1).trans ?_
    simp [hnx]
  -- the factorisation `(x−1)(x+1) = −3`
  have hprod : ‖x - 1‖ * ‖x + 1‖ = ‖(3 : K₃)‖ := by
    rw [← norm_mul, show (x - 1) * (x + 1) = -3 by linear_combination hx, norm_neg]
  -- the two factors differ by the unit `2`, so the larger is exactly `1`
  have hmax : (1 : ℝ) ≤ max ‖x + 1‖ ‖x - 1‖ := by
    calc (1:ℝ) = ‖(x + 1) - (x - 1)‖ := by
          rw [show (x + 1) - (x - 1) = 2 by ring, h2]
      _ ≤ max ‖x + 1‖ ‖x - 1‖ := Jacobs.norm_sub_le_max' _ _
  unfold ν₃
  by_cases hif : ‖exists_sqrt_neg_two.choose - 1‖ < 1
  · rw [if_pos hif]
    rw [← hxdef] at hif ⊢
    -- `‖x−1‖ < 1` forces `‖x+1‖ = 1`, hence `‖x−1‖ = ‖3‖`
    have hplus : ‖x + 1‖ = 1 := by
      rcases max_cases ‖x + 1‖ ‖x - 1‖ with ⟨heq, -⟩ | ⟨heq, hcmp⟩
      · exact le_antisymm hp (heq ▸ hmax)
      · exact absurd (le_trans hmax (le_of_eq heq)) (not_le.mpr hif)
    rw [show ‖x - 1‖ = ‖x - 1‖ * ‖x + 1‖ by rw [hplus, mul_one], hprod]
  · rw [if_neg hif]
    rw [← hxdef] at hif ⊢
    -- `‖x−1‖ = 1` is forced, hence `‖x+1‖ = ‖3‖`, and `−x − 1 = −(x+1)`
    have hm1 : ‖x - 1‖ = 1 := le_antisymm hm (not_lt.mp hif)
    have hplus : ‖x + 1‖ = ‖(3 : K₃)‖ := by
      rw [← hprod, hm1, one_mul]
    rw [show -x - 1 = -(x + 1) by ring, norm_neg, hplus]

/-- The 3-adic location `ν₃ ≡ 2695 mod 3¹⁰` [Jacobs p. 39 substitution]: the hypothesis
`hνc` of `PhD.Jacobs.U3Data` at `K₃`.  (The proof gives `‖3‖¹¹`, one power stronger:
`(ν₃−2695)(ν₃+2695) = −3¹¹·41` with the second factor a unit since
`ν₃ + 2695 ≡ 1 + 2695 ≡ 2 mod 3`.) -/
theorem ν₃_near : ‖ν₃ - 2695‖ ≤ ‖(3 : K₃)‖ ^ 10 := by
  have h3 : ‖(3 : K₃)‖ < 1 := norm_three_lt_one
  have h41 : ‖(41 : K₃)‖ = 1 :=
    Jacobs.norm_ofNat_eq_one h3 (n := 41) (by norm_num) (by norm_num)
  have h2696 : ‖(2696 : K₃)‖ = 1 :=
    Jacobs.norm_ofNat_eq_one h3 (n := 2696) (by norm_num) (by norm_num)
  have key : (ν₃ - 2695) * (ν₃ + 2695) = -((3 : K₃) ^ 11 * 41) := by
    linear_combination sq_ν₃
  have hprod : ‖ν₃ - 2695‖ * ‖ν₃ + 2695‖ = ‖(3 : K₃)‖ ^ 11 := by
    rw [← norm_mul, key, norm_neg, norm_mul, norm_pow, h41, mul_one]
  have hplus : ‖ν₃ + 2695‖ = 1 := by
    have hsub : ‖(ν₃ + 2695) - 2696‖ < ‖(2696 : K₃)‖ := by
      rw [show (ν₃ + 2695) - 2696 = ν₃ - 1 by ring, h2696]
      exact lt_of_le_of_lt norm_ν₃_sub_one_le h3
    rw [Jacobs.norm_eq_of_sub_lt hsub, h2696]
  rw [show ‖ν₃ - 2695‖ = ‖ν₃ - 2695‖ * ‖ν₃ + 2695‖ by rw [hplus, mul_one], hprod]
  exact pow_le_pow_of_le_one (norm_nonneg _) h3.le (by norm_num)

/-- `2` is a unit at `3`. -/
theorem norm_two_eq_one : ‖(2 : K₃)‖ = 1 :=
  Jacobs.norm_ofNat_eq_one norm_three_lt_one (n := 2) (by norm_num) (by norm_num)

/-- `ν₃` is a unit: `‖ν₃‖² = ‖−2‖ = ‖2‖ = 1`. -/
@[simp] theorem norm_ν₃ : ‖ν₃‖ = 1 := by
  have hsq : ‖ν₃‖ ^ 2 = 1 := by rw [← norm_pow, sq_ν₃, norm_neg, norm_two_eq_one]
  nlinarith [norm_nonneg ν₃, hsq]

/-- Half-integers are `3`-integral: `‖A/2‖ ≤ 1` in `K₃` for `A : ℤ`, because `2` is a unit
at `3`.  This is what makes the Hurwitz order — which has half-integral coordinates —
integral at `3` (`PhD/Jacobs/U3/Level.lean`). -/
theorem norm_algebraMap_half_le_one (A : ℤ) : ‖algebraMap ℚ K₃ ((A : ℚ) / 2)‖ ≤ 1 := by
  rw [map_div₀, map_intCast, map_ofNat, norm_div, norm_two_eq_one, div_one]
  exact IsUltrametricDist.norm_intCast_le_one (R := K₃) A

/-- The quaternion generators `i`, `j`, `k` of `D`, named so that every statement below
uses one syntactic form (the anonymous constructor elaborates at the *unfolded*
`ℍ[ℚ,-1,-1]`, which `rw` will not match against `D`). -/
def qi : D := ⟨0, 1, 0, 0⟩
def qj : D := ⟨0, 0, 1, 0⟩
def qk : D := ⟨0, 0, 0, 1⟩

@[simp] theorem qi_re : qi.re = 0 := rfl
@[simp] theorem qi_imI : qi.imI = 1 := rfl
@[simp] theorem qi_imJ : qi.imJ = 0 := rfl
@[simp] theorem qi_imK : qi.imK = 0 := rfl
@[simp] theorem qj_re : qj.re = 0 := rfl
@[simp] theorem qj_imI : qj.imI = 0 := rfl
@[simp] theorem qj_imJ : qj.imJ = 1 := rfl
@[simp] theorem qj_imK : qj.imK = 0 := rfl
@[simp] theorem qk_re : qk.re = 0 := rfl
@[simp] theorem qk_imI : qk.imI = 0 := rfl
@[simp] theorem qk_imJ : qk.imJ = 0 := rfl
@[simp] theorem qk_imK : qk.imK = 1 := rfl

/-- The images of the quaternion generators under `θ` [Jacobs p. 14, at `ξ = 1`]:
`i ↦ (ν 1; 1 −ν)`, `j ↦ (0 −1; 1 0)`, `k ↦ (1 −ν; −ν −1)`, as a
`QuaternionAlgebra.Basis` of `M₂(K₃)` (the relations are `i² = j² = −1`, `ij = k = −ji`,
using `ν² = −2`). -/
private noncomputable def thetaBasis (ν : K₃) (hν : ν ^ 2 = -2) :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) K₃) (-1 : ℚ) 0 (-1) where
  i := !![ν, 1; 1, -ν]
  j := !![0, -1; 1, 0]
  k := !![1, -ν; -ν, -1]
  i_mul_i := by
    have h1 : ν * ν + 1 = -1 := by linear_combination hν
    have h4 : (1 : K₃) + ν * ν = -1 := by linear_combination hν
    refine Matrix.ext fun r c => ?_
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h4]
  j_mul_j := by
    refine Matrix.ext fun r c => ?_
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  i_mul_j := by
    refine Matrix.ext fun r c => ?_
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    refine Matrix.ext fun r c => ?_
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The quaternion side of `θ`: the `ℚ`-algebra map `ℍ[ℚ] → M₂(K₃)` determined by the
generator images. -/
private noncomputable def thetaHom (ν : K₃) (hν : ν ^ 2 = -2) :
    D →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₃ :=
  (thetaBasis ν hν).liftHom

/-- The base-changed splitting as a **`K₃`-algebra** map `K₃ ⊗[ℚ] D → M₂(K₃)`:
quaternions through `thetaHom`, scalars through the (central) scalar matrices.  Working
on this side — `K₃` on the *left* — is what makes `Algebra.TensorProduct.basis` and the
`K₃`-linear dimension count available; the `ℚ`-form required by `RigidificationAt` is
recovered at the end through `Algebra.TensorProduct.comm`. -/
private noncomputable def thetaK (ν : K₃) (hν : ν ^ 2 = -2) :
    (K₃ ⊗[ℚ] D) →ₐ[K₃] Matrix (Fin 2) (Fin 2) K₃ :=
  Algebra.TensorProduct.lift (Algebra.ofId K₃ (Matrix (Fin 2) (Fin 2) K₃)) (thetaHom ν hν)
    (fun x y => Algebra.commutes x (thetaHom ν hν y))

/-- The `K₃`-basis `1⊗1, 1⊗i, 1⊗j, 1⊗k` of `K₃ ⊗[ℚ] D`, from `basisOneIJK`. -/
private noncomputable def tensorBasis : Module.Basis (Fin 4) K₃ (K₃ ⊗[ℚ] D) :=
  Algebra.TensorProduct.basis K₃ (QuaternionAlgebra.basisOneIJK (-1 : ℚ) 0 (-1))

private theorem finrank_tensor : Module.finrank K₃ (K₃ ⊗[ℚ] D) = 4 := by
  rw [Module.finrank_eq_card_basis tensorBasis, Fintype.card_fin]

private theorem finrank_matrix₂ : Module.finrank K₃ (Matrix (Fin 2) (Fin 2) K₃) = 4 := by
  rw [Module.finrank_matrix]
  simp

/-- **Surjectivity of `thetaK`**, by Jacobs's explicit inverse [§B.1 p. 44 `th1`, at
`ξ = 1`]: the preimage of `(m₀₀ m₀₁; m₁₀ m₁₁)` is `a⊗1 + b⊗i + c⊗j + d⊗k` with
`a = (m₀₀+m₁₁)/2`, `b = ((m₁₁−m₀₀)ν − (m₀₁+m₁₀))/2`, `c = (m₁₀−m₀₁)/2`,
`d = ((m₁₁−m₀₀) + (m₀₁+m₁₀)ν)/2`.  Verified entrywise using `ν² = −2` only. -/
private theorem thetaK_one_tmul (ν : K₃) (hν : ν ^ 2 = -2) (q : D) :
    thetaK ν hν (1 ⊗ₜ[ℚ] q) = thetaHom ν hν q := by
  show algebraMap K₃ (Matrix (Fin 2) (Fin 2) K₃) 1 * thetaHom ν hν q = _
  rw [map_one, one_mul]

private theorem thetaK_tmul_one (ν : K₃) (hν : ν ^ 2 = -2) (z : K₃) :
    thetaK ν hν (z ⊗ₜ[ℚ] (1 : D)) = algebraMap K₃ (Matrix (Fin 2) (Fin 2) K₃) z := by
  show algebraMap K₃ (Matrix (Fin 2) (Fin 2) K₃) z * thetaHom ν hν 1 = _
  rw [map_one, mul_one]

private theorem thetaK_surjective (ν : K₃) (hν : ν ^ 2 = -2) :
    Function.Surjective (thetaK ν hν) := by
  have hone : ∀ q : D, thetaK ν hν (1 ⊗ₜ[ℚ] q) = thetaHom ν hν q := thetaK_one_tmul ν hν
  have h1 : thetaK ν hν (1 ⊗ₜ[ℚ] (1 : D)) = 1 := by rw [hone, map_one]
  have hi : thetaK ν hν (1 ⊗ₜ[ℚ] qi) = !![ν, 1; 1, -ν] := by
    rw [hone]; show (thetaBasis ν hν).lift _ = _
    simp [QuaternionAlgebra.Basis.lift, thetaBasis, qi]
  have hj : thetaK ν hν (1 ⊗ₜ[ℚ] qj) = !![0, -1; 1, 0] := by
    rw [hone]; show (thetaBasis ν hν).lift _ = _
    simp [QuaternionAlgebra.Basis.lift, thetaBasis, qj]
  have hk : thetaK ν hν (1 ⊗ₜ[ℚ] qk) = !![1, -ν; -ν, -1] := by
    rw [hone]; show (thetaBasis ν hν).lift _ = _
    simp [QuaternionAlgebra.Basis.lift, thetaBasis, qk]
  intro m
  refine ⟨((m 0 0 + m 1 1) / 2) • (1 ⊗ₜ[ℚ] (1 : D))
      + (((m 1 1 - m 0 0) * ν - (m 0 1 + m 1 0)) / 2) • (1 ⊗ₜ[ℚ] qi)
      + ((m 1 0 - m 0 1) / 2) • (1 ⊗ₜ[ℚ] qj)
      + (((m 1 1 - m 0 0) + (m 0 1 + m 1 0) * ν) / 2) • (1 ⊗ₜ[ℚ] qk), ?_⟩
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, hi, hj, hk]
  -- `Matrix.ext` (rather than the `ext` tactic) keeps the goals at `K₃` level: `ext`
  -- would also apply `adicCompletion.ext` and push them through the structure-eta,
  -- where `hν` no longer matches.
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul, Matrix.one_apply, Fin.zero_eta, Fin.mk_one,
      reduceIte, Fin.reduceEq, mul_zero, add_zero, zero_add, mul_one, mul_neg, if_true]
  · linear_combination (m 1 1 - m 0 0) / 2 * hν
  · linear_combination (-(m 0 1) - m 1 0) / 2 * hν
  · linear_combination (-(m 0 1) - m 1 0) / 2 * hν
  · linear_combination (m 0 0 - m 1 1) / 2 * hν

noncomputable def theta (ν : K₃) (hν : ν ^ 2 = -2) :
    (D ⊗[ℚ] K₃) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₃ :=
  (Algebra.TensorProduct.comm ℚ D K₃).trans
    ((AlgEquiv.ofBijective (thetaK ν hν)
      (by
        have hfin : Module.finrank K₃ (K₃ ⊗[ℚ] D)
            = Module.finrank K₃ (Matrix (Fin 2) (Fin 2) K₃) := by
          rw [finrank_tensor, finrank_matrix₂]
        exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
            (f := (thetaK ν hν).toLinearMap) hfin).mpr (thetaK_surjective ν hν),
          thetaK_surjective ν hν⟩)).restrictScalars ℚ)

/-- **`θ` on a quaternion**, the explicit matrix of [Jacobs §B.1 p. 44 `th1`] (at `ξ = 1`):
`θ(d ⊗ 1)` reads off the four coordinates of `d` against `1, i, j, k`.  Every entry is a
`ℚ`-combination of `1` and `ν` with denominators dividing those of the coordinates — the
form used to check integrality of the local order (`PhD/Jacobs/U3/Level.lean`). -/
theorem theta_tmul_one (ν : K₃) (hν : ν ^ 2 = -2) (d : D) :
    theta ν hν (d ⊗ₜ[ℚ] (1 : K₃)) =
      !![algebraMap ℚ K₃ d.re + algebraMap ℚ K₃ d.imI * ν + algebraMap ℚ K₃ d.imK,
          algebraMap ℚ K₃ d.imI - algebraMap ℚ K₃ d.imJ - algebraMap ℚ K₃ d.imK * ν;
         algebraMap ℚ K₃ d.imI + algebraMap ℚ K₃ d.imJ - algebraMap ℚ K₃ d.imK * ν,
          algebraMap ℚ K₃ d.re - algebraMap ℚ K₃ d.imI * ν - algebraMap ℚ K₃ d.imK] := by
  show thetaK ν hν (Algebra.TensorProduct.comm ℚ D K₃ (d ⊗ₜ[ℚ] (1 : K₃))) = _
  rw [Algebra.TensorProduct.comm_tmul, thetaK_one_tmul]
  show (thetaBasis ν hν).lift d = _
  simp only [QuaternionAlgebra.Basis.lift, thetaBasis]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;>
    (simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.algebraMap_matrix_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
        Fin.mk_one, Fin.reduceEq, reduceIte, if_true]
     simp only [Algebra.smul_def]
     ring)

/-- **`θ` on a scalar**: `θ(1 ⊗ z)` is the scalar matrix `z·1`.  (The right-hand tensor
factor is central, and `θ` is a `K₃`-algebra map on that side by construction.) -/
theorem theta_one_tmul (ν : K₃) (hν : ν ^ 2 = -2) (z : K₃) :
    theta ν hν ((1 : D) ⊗ₜ[ℚ] z) = !![z, 0; 0, z] := by
  show thetaK ν hν (Algebra.TensorProduct.comm ℚ D K₃ ((1 : D) ⊗ₜ[ℚ] z)) = _
  rw [Algebra.TensorProduct.comm_tmul, thetaK_tmul_one]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c <;> simp [Matrix.algebraMap_matrix_apply]

/-- The fixed rigidification of `D` at `3` [Jacobs p. 14]: `theta` at Jacobs's root `ν₃`.
This is the `RigidificationAt` instance the whole `QMF` framework consumes at `v₃`. -/
noncomputable instance : RigidificationAt ℚ D v₃ := ⟨theta ν₃ sq_ν₃⟩

/-- The threshold `v(9) = v(3)²`: elements of value group `ℤᵐ⁰` at exponent `−2`. -/
def γ₉ : WithZero (Multiplicative ℤ) := (Multiplicative.ofAdd (-2 : ℤ) : Multiplicative ℤ)

/-- The prime `v₃` is generated by `3`. -/
private theorem asIdeal_v₃ : v₃.asIdeal = Ideal.span {(3 : RingOfIntegers ℚ)} := by
  have hb := (Rat.IsIntegralClosure.intEquiv (RingOfIntegers ℚ)).bijective
  have h : v₃.asIdeal.map (Rat.IsIntegralClosure.intEquiv (RingOfIntegers ℚ))
      = Ideal.span {((3 : ℕ) : ℤ)} := by
    rw [← natGenerator_v₃]
    exact (Rat.HeightOneSpectrum.span_natGenerator v₃).symm
  have h2 : (Ideal.span {(3 : RingOfIntegers ℚ)}).map
      (Rat.IsIntegralClosure.intEquiv (RingOfIntegers ℚ)) = Ideal.span {((3 : ℕ) : ℤ)} := by
    rw [Ideal.map_span]
    simp [map_ofNat]
  rw [← v₃.asIdeal.comap_map_of_bijective _ hb, h, ← h2,
    Ideal.comap_map_of_bijective _ hb]

/-- `3 ∉ v₃²`: the prime `v₃` is generated by `3`, and `9 ∤ 3`. -/
private theorem three_notMem_sq_v₃ : (3 : RingOfIntegers ℚ) ∉ v₃.asIdeal ^ 2 := by
  rw [asIdeal_v₃, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro h
  have hd := map_dvd Rat.ringOfIntegersEquiv h
  simp [map_ofNat] at hd

/-- **`3` is a uniformizer at `v₃`**: `v(3) = exp(−1)`.  Needed for the *strict* side of
the level conditions (`v(3c) > γ₉` for a unit `c`) — the `≤` side only needs
`valued_three_le`. -/
theorem valued_three_eq :
    Valued.v (3 : K₃) = (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) := by
  have hle : v₃.intValuation (3 : RingOfIntegers ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₃ 3 1).mpr
      (by simpa using three_mem_v₃)
  have hnle : ¬ (v₃.intValuation (3 : RingOfIntegers ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ))) :=
    fun h => three_notMem_sq_v₃
      ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₃ 3 2).mp h)
  have hint : v₃.intValuation (3 : RingOfIntegers ℚ)
      = (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) := by
    rcases eq_or_ne (v₃.intValuation (3 : RingOfIntegers ℚ)) 0 with h0 | h0
    · exact absurd (h0 ▸ (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ _)) hnle
    · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
      have hae : v₃.intValuation (3 : RingOfIntegers ℚ)
          = WithZero.exp (Multiplicative.toAdd a) := by
        rw [← ha, WithZero.exp_eq_coe_ofAdd]
        simp
      rw [hae] at hle hnle ⊢
      rw [WithZero.exp_le_exp] at hle
      rw [WithZero.exp_le_exp] at hnle
      congr 1
      omega
  have key : Valued.v (algebraMap ℚ K₃ (3 : ℚ)) = v₃.valuation ℚ (3 : ℚ) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v₃) (3 : ℚ)
  rw [show (3 : K₃) = algebraMap ℚ K₃ (3 : ℚ) from (map_ofNat _ 3).symm, key,
    show (3 : ℚ) = algebraMap (RingOfIntegers ℚ) ℚ 3 from (map_ofNat _ 3).symm,
    HeightOneSpectrum.valuation_of_algebraMap, hint]

/-- Away from `3`, the rational `3` is a `w`-adic unit: its valuation at any finite place
`w ≠ v₃` is `1`.  (`v₃.asIdeal = (3)` is maximal, so no other prime contains `3`.) -/
theorem valuation_three_eq_one_of_ne {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) : w.valuation ℚ (3 : ℚ) = 1 := by
  rw [show (3 : ℚ) = algebraMap (RingOfIntegers ℚ) ℚ 3 from (map_ofNat _ 3).symm,
    HeightOneSpectrum.valuation_eq_one_iff_notMem]
  refine fun hmem => hw (HeightOneSpectrum.ext ?_)
  have hle : v₃.asIdeal ≤ w.asIdeal :=
    asIdeal_v₃ ▸ (Ideal.span_singleton_le_iff_mem _).mpr hmem
  exact ((Ring.DimensionLEOne.maximalOfPrime v₃.ne_bot v₃.isPrime).eq_of_le
    w.isPrime.ne_top hle).symm

/-- Away from `3`, `3⁻¹` is a `w`-adic integer — the input certifying that global
quaternions of reduced norm `±3^k` are integrally invertible at every place `≠ v₃`
(consumed by the certificate memberships in `Factorisations.lean`). -/
theorem inv_three_mem_adicCompletionIntegers {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    algebraMap ℚ (w.adicCompletion ℚ) (3 : ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  have hval : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (3 : ℚ)⁻¹)
      = w.valuation ℚ (3 : ℚ)⁻¹ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) _
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval, map_inv₀,
    valuation_three_eq_one_of_ne hw, inv_one]

/-- `v(3) ≤ (ofAdd (-1))`: the value group of `K₃` is discrete, so `v(3) < 1` already
forces one full step down. -/
theorem valued_three_le : Valued.v (3 : K₃)
    ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v (3 : K₃) < 1 := Valued.toNormedField.norm_lt_one_iff.mp norm_three_lt_one
  rcases eq_or_ne (Valued.v (3 : K₃)) 0 with h0 | h0
  · rw [h0]; exact zero_le
  · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
    rw [← ha] at h ⊢
    rw [WithZero.coe_le_coe]
    have h1 : a < 1 := by exact_mod_cast h
    have h2 : Multiplicative.toAdd a < (0 : ℤ) := h1
    have h3 : Multiplicative.toAdd a ≤ (-1 : ℤ) := by omega
    exact h3

/-- `v(9) = γ₉` exactly: the mod-`9` threshold *is* the valuation of `9`. -/
theorem valued_nine_eq : Valued.v (9 : K₃) = γ₉ := by
  rw [show (9 : K₃) = 3 * 3 by norm_num, map_mul, valued_three_eq, γ₉,
    ← WithZero.exp_eq_coe_ofAdd, ← WithZero.exp_add]
  norm_num

/-- `v(9) ≤ γ₉`: the mod-`9` threshold really is reached by `9`. -/
theorem valued_nine_le_γ₉ : Valued.v (9 : K₃) ≤ γ₉ := by
  have h : (9 : K₃) = 3 * 3 := by norm_num
  rw [h, map_mul, γ₉]
  calc Valued.v (3 : K₃) * Valued.v (3 : K₃)
      ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
        mul_le_mul' valued_three_le valued_three_le
    _ = ((Multiplicative.ofAdd (-2 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.coe_mul]
        norm_cast

theorem γ₉_lt_one : γ₉ < 1 := by decide

/-- `Σ₁(9) ⊆ Σ₀(v(9))`: the submonoid of matrices with `(0,0)`-entry `≡ 1 mod 9`
(valuatively: `v(g₀₀ − 1) ≤ v(9)`).  Left-handed form of Jacobs's monoid of matrices with
`c ≡ 0`, `d ≡ 1 mod 9` — the natural domain of the weight-`κ` action, since `g₀₀` is then
a `1`-unit and `κ(g₀₀) = g₀₀ᵗ` needs no Teichmüller factor. -/
def Sigma1 : Submonoid (Matrix (Fin 2) (Fin 2) K₃) where
  carrier := {g | g ∈ Sigma0 K₃ γ₉ γ₉_lt_one ∧ Valued.v (g 0 0 - 1) ≤ γ₉}
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    simp only [Matrix.one_apply_eq, sub_self, map_zero]
    exact zero_le
  mul_mem' := by
    intro a b ha hb
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    -- `(ab)₀₀ − 1 = (a₀₀−1)·b₀₀ + (b₀₀−1) + a₀₁·b₁₀`, all three of value `≤ γ₉`
    have hexp : (a * b) 0 0 - 1
        = (a 0 0 - 1) * b 0 0 + (b 0 0 - 1) + a 0 1 * b 1 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hexp]
    refine le_trans (Valued.v.map_add _ _) (max_le (le_trans (Valued.v.map_add _ _)
      (max_le ?_ ?_)) ?_)
    · rw [map_mul]
      calc Valued.v (a 0 0 - 1) * Valued.v (b 0 0)
          ≤ γ₉ * 1 := mul_le_mul' ha.2 (Sigma0.entry_le_one ⟨b, hb.1⟩ 0 0)
        _ = γ₉ := mul_one _
    · exact hb.2
    · rw [map_mul]
      calc Valued.v (a 0 1) * Valued.v (b 1 0)
          ≤ 1 * γ₉ := mul_le_mul' (Sigma0.entry_le_one ⟨a, ha.1⟩ 0 1)
            (Sigma0.v_c_le ⟨b, hb.1⟩)
        _ = γ₉ := one_mul _

/-- `Σ₁(9)` is closed under taking inverses *inside the integral matrices*: if `M ∈ Σ₁(9)`
and `N` is an integral two-sided inverse of `M`, then `N ∈ Σ₁(9)`.

The proof reads the four conditions off the two identities `MN = 1` and `NM = 1` without
ever forming `M⁻¹`: `N₁₀α = −N₁₁γ` gives the lower-left congruence (since `v(α) = 1`);
`αN₀₀ = 1 − βN₁₀` forces `v(N₀₀) = 1`; and `N₀₀ − 1 = N₀₀(1−α) − βN₁₀` is `≤ γ₉` because
both summands are. -/
theorem sigma1_of_mul_eq_one {M N : Matrix (Fin 2) (Fin 2) K₃} (hM : M ∈ Sigma1)
    (hN : ∀ i j, Valued.v (N i j) ≤ 1) (h1 : M * N = 1) (h2 : N * M = 1) :
    N ∈ Sigma1 := by
  obtain ⟨⟨hMint, hMc, hMa, hMdet⟩, hMa1⟩ := hM
  have e1 : M 0 0 * N 0 0 + M 0 1 * N 1 0 = 1 := by
    have := congrFun (congrFun h1 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at this
  have e2 : N 1 0 * M 0 0 + N 1 1 * M 1 0 = 0 := by
    have := congrFun (congrFun h2 1) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
      at this
  -- lower-left: `N₁₀ α = −N₁₁ γ`
  have hNc : Valued.v (N 1 0) ≤ γ₉ := by
    have hkey : N 1 0 * M 0 0 = -(N 1 1 * M 1 0) := by linear_combination e2
    have hv : Valued.v (N 1 0) = Valued.v (N 1 1 * M 1 0) := by
      have := congrArg Valued.v hkey
      rwa [map_mul, hMa, mul_one, Valuation.map_neg] at this
    rw [hv, map_mul]
    exact le_trans (mul_le_mul' (hN 1 1) hMc) (by rw [one_mul])
  -- `v(N₀₀) = 1`
  have hbn : Valued.v (M 0 1 * N 1 0) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (le_trans (mul_le_mul' (hMint 0 1) hNc) (by rw [one_mul])) γ₉_lt_one
  have hNa : Valued.v (N 0 0) = 1 := by
    have hlt : Valued.v (-(M 0 1 * N 1 0)) < Valued.v (1 : K₃) := by
      rw [Valuation.map_neg, map_one]
      exact hbn
    have h : Valued.v (M 0 0 * N 0 0) = 1 := by
      have hsum : M 0 0 * N 0 0 = 1 + -(M 0 1 * N 1 0) := by linear_combination e1
      rw [hsum, Valuation.map_add_eq_of_lt_left _ hlt, map_one]
    rwa [map_mul, hMa, one_mul] at h
  refine ⟨⟨hN, hNc, hNa, ?_⟩, ?_⟩
  · intro hdet
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, hdet, mul_zero, Matrix.det_one] at this
    exact one_ne_zero this.symm
  · have hsub : N 0 0 - 1 = N 0 0 * (1 - M 0 0) + -(M 0 1 * N 1 0) := by
      linear_combination e1
    rw [hsub]
    refine le_trans (Valued.v.map_add _ _) (max_le ?_ ?_)
    · rw [map_mul]
      refine le_trans (mul_le_mul' (le_of_eq hNa) ?_) (by rw [one_mul])
      rw [show (1 : K₃) - M 0 0 = -(M 0 0 - 1) by ring, Valuation.map_neg]
      exact hMa1
    · rw [Valuation.map_neg, map_mul]
      exact le_trans (mul_le_mul' (hMint 0 1) hNc) (by rw [one_mul])

theorem sigma1_le_sigma0 : Sigma1 ≤ Sigma0 K₃ γ₉ γ₉_lt_one := fun _ hg => hg.1

/-- Membership in `Σ₁(9)`: the `Σ₀` conditions plus `v(g₀₀ − 1) ≤ v(9)`. -/
theorem mem_sigma1_iff {g : Matrix (Fin 2) (Fin 2) K₃} :
    g ∈ Sigma1 ↔ g ∈ Sigma0 K₃ γ₉ γ₉_lt_one ∧
      Valued.v (g 0 0 - 1) ≤ γ₉ := Iff.rfl

/-- **`ℕ` is dense in the unit ball of `K₃`.**  `K₃` is the completion of `ℚ` at `3`, so
`𝓞₃ ≅ ℤ₃` (`PadicInt.adicCompletionIntegersEquiv`, a CONTINUOUS `ℤ`-algebra equivalence)
and `PadicInt.denseRange_natCast` transports.  This is the density hypothesis of
`Jacobs.tsum_binomialCoeff_eq_unitPow`, i.e. what licenses the exponent-density proof of
the `p`-adic binomial theorem at `K₃`. -/
theorem exists_natCast_close {t : K₃} (ht : ‖t‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ‖t - ((m : ℕ) : K₃)‖ < ε := by
  have ht' : t ∈ v₃.adicCompletionIntegers ℚ :=
    Valued.toNormedField.norm_le_one_iff.mp ht
  set e := PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ) ⟨3, Nat.prime_three⟩ with he
  set U : Set (v₃.adicCompletionIntegers ℚ) := {y | ‖(y : K₃) - t‖ < ε} with hU
  have hUopen : IsOpen U := by
    refine isOpen_induced_iff.mpr ⟨{z : K₃ | ‖z - t‖ < ε}, ?_, rfl⟩
    exact isOpen_lt (by fun_prop) continuous_const
  have hx : e.symm ⟨t, ht'⟩ ∈ e ⁻¹' U := by
    show e (e.symm ⟨t, ht'⟩) ∈ U
    rw [e.apply_symm_apply]
    show ‖((⟨t, ht'⟩ : v₃.adicCompletionIntegers ℚ) : K₃) - t‖ < ε
    simpa using hε
  obtain ⟨m, hm⟩ := PadicInt.denseRange_natCast.exists_mem_open
    (hUopen.preimage e.continuous) ⟨_, hx⟩
  refine ⟨m, ?_⟩
  have hnat : e ((m : ℕ) : ℤ_[(⟨3, Nat.prime_three⟩ : Nat.Primes)])
      = ((m : ℕ) : v₃.adicCompletionIntegers ℚ) := map_natCast e m
  have hmem : ‖((((m : ℕ) : v₃.adicCompletionIntegers ℚ) : K₃)) - t‖ < ε := by
    have h2 : e ((m : ℕ) : ℤ_[(⟨3, Nat.prime_three⟩ : Nat.Primes)]) ∈ U := hm
    rwa [hnat] at h2
  rw [norm_sub_rev]
  refine lt_of_le_of_lt (le_of_eq (congrArg (fun y : K₃ => ‖y - t‖) ?_)) hmem
  exact (map_natCast (algebraMap (v₃.adicCompletionIntegers ℚ) K₃) m).symm

end Jacobs.U3
