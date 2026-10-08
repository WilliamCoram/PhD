/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Hamilton.Splitting
import PhD.TauCeti.Code.OverconvergentForms.Adelic.Components
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Hamilton's quaternions at `p = 3`: the place, the local field and the rigidification `θ₃`

The place `v₃` of `ℚ`, the local field `K₃ = ℚ_3` as an adic completion, the square root
`ν₃ = √−2 ∈ ℤ_3` with `ν₃ ≡ 1 mod 3`, and the rigidification `θ₃` of `ℍ[ℚ]` at `3` attached to
`ν = ν₃`, `ξ = 1`. Every odd prime carries a rigidification.

[Jac03, §1.4, p. 14]: "One easily verifies that for all odd primes `q` the map `D_q → M₂(ℚ_q)` given
by `a + bi + cj + dk ↦ ((a + bν_q + dξ_q, bξ_q − c − dν_q), (bξ_q + c − dν_q, a − bν_q − dξ_q))` is
an isomorphism."

## Main definitions

* `Hamilton.padicPlace`, `Hamilton.v₃`, `Hamilton.K₃`, `Hamilton.ν₃`.
* `Hamilton.theta3`: the rigidification of `ℍ[ℚ]` at `3`.
* `Hamilton.rigidificationOfOdd`: a rigidification at every odd prime.

## Main results

* `Hamilton.valued_ratCast`: the valuation of a rational in `ℚ_w` is its `w`-adic valuation.
* `Hamilton.valued_natCast_padicPlace`, `Hamilton.valued_intCast_eq_one`, `Hamilton.valued_three`,
  `Hamilton.valued_ofNat_eq_one`.
* `Hamilton.exists_sq_add_sq_eq_neg_one_adicCompletion`, `Hamilton.exists_sqrt_neg_two`.
* `Hamilton.sq_ν₃`, `Hamilton.valued_ν₃`, `Hamilton.valued_ν₃_sub_one`,
  `Hamilton.valued_ν₃_sub_twentyTwo`: `ν₃² = −2`, `ν₃ ≡ 1 mod 3`, `ν₃ ≡ 22 mod 27`.
* `Hamilton.isUnit_two`, `Hamilton.sq_ν₃_add_one_sq`: the hypotheses of the splitting at `3`.
* `Hamilton.charZero_K₃`: `ℚ_3` has characteristic zero (a local instance, not a global one).
* `Hamilton.toMatrix_unitsIncl`: `θ₃` on global quaternions.

Roadmap: §0.1.3, §0.5. Tau Ceti home: `TauCeti/NumberTheory/AutomorphicForm/Hamilton/Setting.lean`.
-/

open scoped Quaternion TensorProduct WithZero
open IsDedekindDomain NumberField AdelicAlgebra

noncomputable section

namespace Hamilton

open scoped AdelicAlgebra.RightAlgebra

/-- The place of `ℚ` at a prime `q`. -/
def padicPlace (q : ℕ) [Fact q.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨q, Fact.out⟩

/-- The place `3` of `ℚ`. -/
abbrev v₃ : HeightOneSpectrum (𝓞 ℚ) := padicPlace 3

/-- The local field `ℚ_3`, as the adic completion at `v₃`. -/
abbrev K₃ : Type := v₃.adicCompletion ℚ

private theorem natGenerator_padicPlace (q : ℕ) [Fact q.Prime] :
    Rat.HeightOneSpectrum.natGenerator (padicPlace q) = q :=
  congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨q, Fact.out⟩)

private theorem asIdeal_padicPlace (q : ℕ) [Fact q.Prime] :
    (padicPlace q).asIdeal = Ideal.span {(q : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (padicPlace q)
  rw [natGenerator_padicPlace] at h
  rw [← (padicPlace q).asIdeal.comap_map_of_bijective _
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective, ← h, ← Ideal.map_symm, Ideal.map_span,
    Set.image_singleton, map_natCast]

/-- **The valuation of a rational in `ℚ_w` is its `w`-adic valuation**: the cast `ℚ → ℚ_w` is the
adic embedding, both being ring homomorphisms out of `ℚ`. -/
theorem valued_ratCast (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (r : w.adicCompletion ℚ) = w.valuation ℚ r := by
  have e := congrFun
    (HeightOneSpectrum.algebraMap_adicCompletion (R := 𝓞 ℚ) (S := ℚ) (K := ℚ) (v := w)) r
  rw [eq_ratCast] at e
  rw [e]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

/-- `q` is a uniformiser at the place `q`. -/
theorem valued_natCast_padicPlace (q : ℕ) [Fact q.Prime] :
    Valued.v ((q : ℚ) : (padicPlace q).adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [valued_ratCast, show (q : ℚ) = algebraMap (𝓞 ℚ) ℚ (q : 𝓞 ℚ) from (map_natCast _ q).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine (padicPlace q).intValuation_singleton (fun h => ?_) (asIdeal_padicPlace q)
  exact (Fact.out : q.Prime).ne_zero (by simpa using congrArg (algebraMap (𝓞 ℚ) ℚ) h)

/-- An integer prime to `q` is a unit at the place `q`. -/
theorem valued_intCast_eq_one {q : ℕ} [Fact q.Prime] {n : ℤ} (hn : ¬ (q : ℤ) ∣ n) :
    Valued.v ((n : ℚ) : (padicPlace q).adicCompletion ℚ) = 1 := by
  rw [valued_ratCast, show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_intCast _ n).symm,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff,
    asIdeal_padicPlace, Ideal.mem_span_singleton]
  intro hdvd
  apply hn
  have h := map_dvd (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hdvd
  rwa [map_natCast, map_intCast] at h

/-- `ν² + ξ² = −1` is solvable in `ℚ_q`, read in the adic completion, for `q` odd. -/
theorem exists_sq_add_sq_eq_neg_one_adicCompletion (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    ∃ ν ξ : (padicPlace q).adicCompletion ℚ, ν ^ 2 + ξ ^ 2 = -1 ∧ Valued.v ν ≤ 1 ∧
      Valued.v ξ ≤ 1 := by
  obtain ⟨ν, ξ, h⟩ := Quaternion.exists_sq_add_sq_eq_neg_one q hq
  let E : ℤ_[q] ≃A[ℤ] (padicPlace q).adicCompletionIntegers ℚ :=
    PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨q, Fact.out⟩
  exact ⟨(E ν).1, (E ξ).1, by simpa using congrArg (fun z => (E z).1) h, (E ν).2, (E ξ).2⟩

/-- `2` is a unit of every completion of `ℚ` (it is one in `ℚ`). -/
theorem isUnit_two (w : HeightOneSpectrum (𝓞 ℚ)) : IsUnit (2 : w.adicCompletion ℚ) := by
  simpa using (IsUnit.mk0 (2 : ℚ) two_ne_zero).map (algebraMap ℚ (w.adicCompletion ℚ))

/-- **`ℍ[ℚ]` is split at every odd prime.** -/
abbrev rigidificationOfOdd (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    RigidificationAt ℚ ℍ[ℚ] (padicPlace q) :=
  ⟨Quaternion.splitEquiv (exists_sq_add_sq_eq_neg_one_adicCompletion q hq).choose
    (exists_sq_add_sq_eq_neg_one_adicCompletion q hq).choose_spec.choose
    (exists_sq_add_sq_eq_neg_one_adicCompletion q hq).choose_spec.choose_spec.1 (isUnit_two _)⟩

-- Hensel for `X² + 2` at `1`: `‖1 + 2‖ = ‖3‖ < 1 = ‖2‖²`
private theorem exists_padicInt_sqrt_neg_two : ∃ z : ℤ_[3], z ^ 2 = -2 ∧ ‖z - 1‖ < 1 := by
  set P : Polynomial ℤ_[3] := Polynomial.X ^ 2 + Polynomial.C 2 with hP
  have hPe : ∀ z : ℤ_[3], P.aeval z = z ^ 2 + 2 := fun z => by simp [hP]
  have hP' : P.derivative.aeval (1 : ℤ_[3]) = 2 := by simp [hP, one_add_one_eq_two]
  have h2 : ‖(2 : ℤ_[3])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
    have h := (PadicInt.norm_int_lt_one_iff_dvd 2).mp (by exact_mod_cast hlt)
    omega
  have hnorm : ‖P.aeval (1 : ℤ_[3])‖ < ‖P.derivative.aeval (1 : ℤ_[3])‖ ^ 2 := by
    rw [hP', h2, one_pow, hPe, one_pow,
      show (1 : ℤ_[3]) + 2 = ((3 : ℕ) : ℤ_[3]) by norm_num, PadicInt.norm_p]
    norm_num
  obtain ⟨z, hz, hz1, -⟩ := hensels_lemma hnorm
  refine ⟨z, by linear_combination (hPe z).symm.trans hz, ?_⟩
  rwa [hP', h2] at hz1

/-- `v(3) = exp(−1)`: `3` is a uniformiser of `K₃`. -/
theorem valued_three : Valued.v (3 : K₃) = WithZero.exp (-1 : ℤ) := by
  rw [← valued_natCast_padicPlace 3, Rat.cast_natCast, Nat.cast_ofNat]

/-- There is a square root of `−2` in `K₃` congruent to `1` modulo `3`. -/
theorem exists_sqrt_neg_two : ∃ x : K₃, x ^ 2 = -2 ∧ Valued.v (x - 1) < 1 := by
  obtain ⟨z, hz, hz1⟩ := exists_padicInt_sqrt_neg_two
  obtain ⟨w, hw⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp hz1
  let E : ℤ_[3] ≃A[ℤ] v₃.adicCompletionIntegers ℚ :=
    PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨3, Nat.prime_three⟩
  -- transport to `K₃` (literals as sums of `1`, which the equivalence carries), where `z − 1 = 3w`
  -- has `v(3w) ≤ v(3) < 1`
  have hz' : z ^ 2 + (1 + 1) = 0 := by rw [one_add_one_eq_two]; linear_combination hz
  have hw' : z - 1 = (1 + 1 + 1) * w := by rw [hw]; norm_num
  have h1 := congrArg (fun a => (E a).1) hz'
  have h2 := congrArg (fun a => (E a).1) hw'
  simp at h1 h2
  obtain ⟨x, hx, y, hy1, hxy⟩ : ∃ x : K₃, x ^ 2 = -2 ∧ ∃ y : K₃, Valued.v y ≤ 1 ∧ x - 1 = 3 * y :=
    ⟨(E z).1, by linear_combination h1, (E w).1, (E w).2, by linear_combination h2⟩
  refine ⟨x, hx, ?_⟩
  rw [hxy, map_mul]
  calc Valued.v (3 : K₃) * Valued.v y ≤ Valued.v (3 : K₃) * 1 := mul_le_mul' le_rfl hy1
    _ < 1 := by
      rw [mul_one, valued_three, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num

/-- **`ν₃ = √−2 ∈ ℤ_3`**, the root congruent to `1` modulo `3`. -/
def ν₃ : K₃ := exists_sqrt_neg_two.choose

/-- `ν₃² = −2`. -/
@[simp]
theorem sq_ν₃ : ν₃ ^ 2 = -2 := exists_sqrt_neg_two.choose_spec.1

/-- `ν₃ ≡ 1 mod 3`. -/
theorem valued_ν₃_sub_one : Valued.v (ν₃ - 1) < 1 := exists_sqrt_neg_two.choose_spec.2

/-- `ν₃` is a unit of `ℤ_3`. -/
theorem valued_ν₃ : Valued.v ν₃ = 1 := by
  have h : Valued.v (ν₃ - 1) < Valued.v (1 : K₃) := by rw [map_one]; exact valued_ν₃_sub_one
  rw [show ν₃ = (ν₃ - 1) + 1 by ring, Valuation.map_add_eq_of_lt_right _ h, map_one]

/-- A literal prime to `3` is a unit of `K₃`. -/
theorem valued_ofNat_eq_one (n : ℕ) [n.AtLeastTwo] (hn : ¬ (3 : ℤ) ∣ n) :
    Valued.v (OfNat.ofNat n : K₃) = 1 := by
  have h := valued_intCast_eq_one (q := 3) (n := n) (by exact_mod_cast hn)
  rw [Int.cast_natCast, Rat.cast_natCast] at h
  exact h

/-- `ν₃ ≡ 22 mod 27`. -/
theorem valued_ν₃_sub_twentyTwo : Valued.v (ν₃ - 22) ≤ Valued.v ((27 : ℚ) : K₃) := by
  have h2 : Valued.v (2 : K₃) = 1 := valued_ofNat_eq_one 2 (by norm_num)
  have h23 : Valued.v (23 : K₃) = 1 := valued_ofNat_eq_one 23 (by norm_num)
  -- `ν₃ + 22 = (ν₃ − 1) + 23` is a unit
  have hsum : Valued.v (ν₃ + 22) = 1 := by
    have h : Valued.v (ν₃ - 1) < Valued.v (23 : K₃) := by rw [h23]; exact valued_ν₃_sub_one
    rw [show ν₃ + 22 = (ν₃ - 1) + 23 by ring, Valuation.map_add_eq_of_lt_right _ h, h23]
  -- `(ν₃ − 22)(ν₃ + 22) = ν₃² − 484 = −2 · 3⁵`
  have hprod : (ν₃ - 22) * (ν₃ + 22) = -2 * 3 ^ 5 := by linear_combination sq_ν₃
  have hv : Valued.v (ν₃ - 22) = WithZero.exp (-1 : ℤ) ^ 5 := by
    have h := congrArg Valued.v hprod
    rwa [map_mul, map_mul, hsum, mul_one, Valuation.map_neg, h2, one_mul, map_pow,
      valued_three] at h
  rw [hv, show ((27 : ℚ) : K₃) = 3 ^ 3 by
      rw [Rat.cast_ofNat]; norm_num,
    map_pow, valued_three, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_le_exp]
  norm_num

/-- `ν₃² + 1² = −1`: the pair `(ν₃, 1)` splits `ℍ[ℚ]` at `3`. -/
theorem sq_ν₃_add_one_sq : ν₃ ^ 2 + (1 : K₃) ^ 2 = -1 := by
  rw [sq_ν₃]
  norm_num

/-- `K₃` has characteristic zero. Not an instance: globally it would loop with
`DivisionRing.toRatAlgebra`. Use it locally (`haveI := charZero_K₃`) right before `ring` or
`field_simp`, never before elaborating a statement mentioning `algebraMap ℚ K₃`. -/
theorem charZero_K₃ : CharZero K₃ := algebraRat.charZero K₃

/-- **The rigidification `θ₃`** of `ℍ[ℚ]` at `3`, attached to `ν = ν₃`, `ξ = 1`. -/
instance theta3 : RigidificationAt ℚ ℍ[ℚ] v₃ where
  equiv := Quaternion.splitEquiv ν₃ 1 sq_ν₃_add_one_sq (isUnit_two v₃)

/-- `θ₃` on a global quaternion. -/
theorem toMatrix_unitsIncl (x : (ℍ[ℚ])ˣ) :
    toMatrix ℚ ℍ[ℚ] v₃ (unitsIncl ℚ ℍ[ℚ] x) =
      Quaternion.splitHom (R := ℚ) ν₃ (1 : K₃) sq_ν₃_add_one_sq (x : ℍ[ℚ]) := by
  rw [toMatrix_apply, coe_unitsIncl,
    show (x : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = incl ℚ ℍ[ℚ] (x : ℍ[ℚ]) from rfl,
    toLocal_incl]
  exact (Quaternion.splitEquiv_tmul ν₃ 1 _ _ (x : ℍ[ℚ]) 1).trans (one_smul _ _)

end Hamilton
