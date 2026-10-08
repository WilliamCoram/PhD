/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Quaternion.BaseChange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Splittings of Hamilton's quaternions

Over a commutative ring `S` with `ν² + ξ² = −1`, Hamilton's quaternions split:
`a + bi + cj + dk ↦ ((a + bν + dξ, bξ − c − dν), (bξ + c − dν, a − bν − dξ))` is an algebra
homomorphism `ℍ[R] → M₂(S)`, and an isomorphism `ℍ[R] ⊗_R S ≃ M₂(S)` when `2` is invertible. Such
`ν, ξ` exist in `ℤ_q` for every odd prime `q`, and do not exist in `ℚ_2`, where the reduced norm is
anisotropic: `ℍ[ℚ]` is split at every odd prime and ramified at `2`.

[Jac03, Lemma 1.18]: "Suppose `L` is a field of characteristic zero. Then `D ⊗_ℚ L = M₂(L)` if and
only if there exist `ν, ξ ∈ L` such that `ν² + ξ² = −1`." [Jac03, Lemma 1.19]: "There are no
elements `ν, ξ ∈ ℚ_2` such that `ν² + ξ² = −1`."

## Main definitions

* `Quaternion.splitHom`, `Quaternion.splitEquiv`, with `Quaternion.splitHom_apply`,
  `Quaternion.splitEquiv_tmul` and the explicit inverse `Quaternion.splitEquiv_symm_apply`.

## Main results

* `Quaternion.exists_sq_add_sq_eq_neg_one`: `ν² + ξ² = −1` is solvable in `ℤ_q`, `q` odd.
* `Quaternion.nrd_eq_zero_iff_of_padic_two`: the reduced norm of `ℍ[ℚ_2]` is anisotropic, and
  `Quaternion.not_exists_sq_add_sq_eq_neg_one_padic_two`.

Roadmap: §0.1.2, §0.1.3, Examples. Tau Ceti home:
`TauCeti/Algebra/QuaternionAlgebra/Splitting.lean`.
-/

open scoped Quaternion TensorProduct

noncomputable section

namespace Quaternion

open scoped AdelicAlgebra.RightAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

private def splitBasis (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) S) (-1 : R) 0 (-1) where
  i := !![ν, ξ; ξ, -ν]
  j := !![0, -1; 1, 0]
  k := !![ξ, -ν; -ν, -ξ]
  i_mul_i := by
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h
  j_mul_j := by
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  i_mul_j := by
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The splitting of Hamilton's quaternions** attached to `ν² + ξ² = −1`. -/
def splitHom (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) : ℍ[R] →ₐ[R] Matrix (Fin 2) (Fin 2) S :=
  (splitBasis ν ξ h).liftHom

/-- The splitting in coordinates. -/
theorem splitHom_apply (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (x : ℍ[R]) :
    splitHom ν ξ h x =
      !![algebraMap R S x.re + algebraMap R S x.imI * ν + algebraMap R S x.imK * ξ,
        algebraMap R S x.imI * ξ - algebraMap R S x.imJ - algebraMap R S x.imK * ν;
        algebraMap R S x.imI * ξ + algebraMap R S x.imJ - algebraMap R S x.imK * ν,
        algebraMap R S x.re - algebraMap R S x.imI * ν - algebraMap R S x.imK * ξ] := by
  change algebraMap R (Matrix (Fin 2) (Fin 2) S) x.re + x.imI • !![ν, ξ; ξ, -ν] +
    x.imJ • !![0, -1; 1, 0] + x.imK • !![ξ, -ν; -ν, -ξ] = _
  refine Matrix.ext fun a b => ?_
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.algebraMap_matrix_apply, Algebra.smul_def (A := S)] <;> ring

private def splitTensorHomR (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) :
    ℍ[R] ⊗[R] S →ₐ[R] Matrix (Fin 2) (Fin 2) S :=
  Algebra.TensorProduct.lift (splitHom ν ξ h)
    ((Algebra.ofId S (Matrix (Fin 2) (Fin 2) S)).restrictScalars R)
    fun _ y => (Algebra.commutes y _).symm

private theorem splitTensorHomR_tmul (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (x : ℍ[R]) (s : S) :
    splitTensorHomR (R := R) ν ξ h (x ⊗ₜ[R] s) = s • splitHom ν ξ h x := by
  show splitHom ν ξ h x * algebraMap S (Matrix (Fin 2) (Fin 2) S) s = _
  rw [Algebra.smul_def]
  exact (Algebra.commutes s (splitHom ν ξ h x)).symm

private def splitTensorHom (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) :
    ℍ[R] ⊗[R] S →ₐ[S] Matrix (Fin 2) (Fin 2) S :=
  { splitTensorHomR ν ξ h with
    commutes' := fun s => by
      rw [show algebraMap S (ℍ[R] ⊗[R] S) s = (1 : ℍ[R]) ⊗ₜ[R] s from
        Algebra.TensorProduct.right_algebraMap_apply s]
      show splitTensorHomR (R := R) ν ξ h ((1 : ℍ[R]) ⊗ₜ[R] s) = _
      rw [splitTensorHomR_tmul, map_one, Algebra.algebraMap_eq_smul_one] }

private theorem splitTensorHom_tmul (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (x : ℍ[R]) (s : S) :
    splitTensorHom (R := R) ν ξ h (x ⊗ₜ[R] s) = s • splitHom ν ξ h x :=
  splitTensorHomR_tmul ν ξ h x s

-- the explicit preimage `a + bi + cj + dk` of `m`, with `t = 1/2`: `a = t(m₀₀ + m₁₁)`,
-- `c = t(m₁₀ − m₀₁)`, and `b`, `d` solving `bν + dξ = t(m₀₀ − m₁₁)`, `bξ − dν = t(m₀₁ + m₁₀)`
-- by `ν² + ξ² = −1`; the quaternions sit in a vector so that they have type `ℍ[R]`
private theorem splitTensorHom_preimage (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) {t : S}
    (ht : 2 * t = 1) (m : Matrix (Fin 2) (Fin 2) S) :
    splitTensorHom (R := R) ν ξ h (∑ n : Fin 4,
      ![(1 : ℍ[R]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] n ⊗ₜ[R]
        ![t * (m 0 0 + m 1 1), -(t * (m 0 0 - m 1 1) * ν + t * (m 0 1 + m 1 0) * ξ),
          t * (m 1 0 - m 0 1), t * (m 0 1 + m 1 0) * ν - t * (m 0 0 - m 1 1) * ξ] n) = m := by
  simp only [map_sum, splitTensorHom_tmul, splitHom_apply]
  refine Matrix.ext fun a b => ?_
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_four]
  · linear_combination (-t * (m 0 0 - m 1 1)) * h + m 0 0 * ht
  · linear_combination (-t * (m 0 1 + m 1 0)) * h + m 0 1 * ht
  · linear_combination (-t * (m 0 1 + m 1 0)) * h + m 1 0 * ht
  · linear_combination (t * (m 0 0 - m 1 1)) * h + m 1 1 * ht

private theorem splitTensorHom_surjective (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1)
    (h2 : IsUnit (2 : S)) : Function.Surjective (splitTensorHom (R := R) ν ξ h) := by
  obtain ⟨t, ht⟩ : ∃ t : S, 2 * t = 1 := ⟨_, h2.mul_val_inv⟩
  exact fun m => ⟨_, splitTensorHom_preimage ν ξ h ht m⟩

-- a surjection between free modules of the same finite rank is injective (Orzech)
private theorem splitTensorHom_injective (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1)
    (h2 : IsUnit (2 : S)) : Function.Injective (splitTensorHom (R := R) ν ξ h) := by
  let b₁ : Module.Basis (Fin 4) S (ℍ[R] ⊗[R] S) :=
    AdelicAlgebra.rightBasis (QuaternionAlgebra.basisOneIJK (-1 : R) 0 (-1))
  let e : ℍ[R] ⊗[R] S ≃ₗ[S] Matrix (Fin 2) (Fin 2) S :=
    b₁.equiv (Matrix.stdBasis S (Fin 2) (Fin 2))
      ((finProdFinEquiv (m := 2) (n := 2)).symm : Fin 4 ≃ Fin 2 × Fin 2)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap
    (splitTensorHom ν ξ h).toLinearMap e.injective (splitTensorHom_surjective ν ξ h h2)

/-- **`ℍ[R] ⊗_R S ≃ M₂(S)`** when `ν² + ξ² = −1` and `2` is invertible in `S`. -/
def splitEquiv (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (h2 : IsUnit (2 : S)) :
    ℍ[R] ⊗[R] S ≃ₐ[S] Matrix (Fin 2) (Fin 2) S :=
  AlgEquiv.ofBijective (splitTensorHom ν ξ h)
    ⟨splitTensorHom_injective ν ξ h h2, splitTensorHom_surjective ν ξ h h2⟩

/-- The splitting on pure tensors. -/
@[simp]
theorem splitEquiv_tmul (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (h2 : IsUnit (2 : S)) (x : ℍ[R])
    (s : S) : splitEquiv (R := R) ν ξ h h2 (x ⊗ₜ s) = s • splitHom ν ξ h x :=
  splitTensorHom_tmul ν ξ h x s

/-- **The inverse of the splitting**, for any `t` with `2t = 1`. -/
theorem splitEquiv_symm_apply (ν ξ : S) (h : ν ^ 2 + ξ ^ 2 = -1) (h2 : IsUnit (2 : S)) {t : S}
    (ht : 2 * t = 1) (m : Matrix (Fin 2) (Fin 2) S) :
    (splitEquiv (R := R) ν ξ h h2).symm m = ∑ n : Fin 4,
      ![(1 : ℍ[R]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] n ⊗ₜ[R]
        ![t * (m 0 0 + m 1 1), -(t * (m 0 0 - m 1 1) * ν + t * (m 0 1 + m 1 0) * ξ),
          t * (m 1 0 - m 0 1), t * (m 0 1 + m 1 0) * ν - t * (m 0 0 - m 1 1) * ξ] n :=
  (AlgEquiv.symm_apply_eq _).mpr (splitTensorHom_preimage ν ξ h ht m).symm

private theorem norm_lt_one_iff_toZMod_eq_zero {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) :
    ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]

-- a solution `a² + b² = −1` modulo `q` with `a ≠ 0` lifts: Hensel for `X² + (ξ₀² + 1)` at `ν₀`,
-- whose derivative `2ν₀` is a unit
private theorem exists_lift_of_ne_zero {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) {a b : ZMod q}
    (ha : a ≠ 0) (hab : a ^ 2 + b ^ 2 = -1) : ∃ ν ξ : ℤ_[q], ν ^ 2 + ξ ^ 2 = -1 := by
  have hν₀ : PadicInt.toZMod ((a.val : ℕ) : ℤ_[q]) = a := by simp
  have hξ₀ : PadicInt.toZMod ((b.val : ℕ) : ℤ_[q]) = b := by simp
  set ν₀ : ℤ_[q] := ((a.val : ℕ) : ℤ_[q])
  set ξ₀ : ℤ_[q] := ((b.val : ℕ) : ℤ_[q])
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[q], c = ξ₀ ^ 2 + 1 := ⟨_, rfl⟩
  set P : Polynomial ℤ_[q] := Polynomial.X ^ 2 + Polynomial.C c with hP
  have hPe : ∀ z : ℤ_[q], P.aeval z = z ^ 2 + (ξ₀ ^ 2 + 1) := fun z => by simp [hP, hc]
  have hP' : P.derivative.aeval ν₀ = 2 * ν₀ := by simp [hP, one_add_one_eq_two]
  have h2 : (2 : ZMod q) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hq)
  have hd : ‖P.derivative.aeval ν₀‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
    rw [hP', norm_lt_one_iff_toZMod_eq_zero, map_mul, hν₀, map_ofNat] at hlt
    exact mul_ne_zero h2 ha hlt
  have hnorm : ‖P.aeval ν₀‖ < ‖P.derivative.aeval ν₀‖ ^ 2 := by
    rw [hd, one_pow, norm_lt_one_iff_toZMod_eq_zero, hPe, map_add, map_add, map_pow, map_pow,
      map_one, hν₀, hξ₀]
    linear_combination hab
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  exact ⟨z, ξ₀, by linear_combination (hPe z).symm.trans hz⟩

/-- **`ν² + ξ² = −1` is solvable in `ℤ_q` for every odd prime `q`**: solvable modulo `q` by
counting squares, and lifted by Hensel's lemma. -/
theorem exists_sq_add_sq_eq_neg_one (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    ∃ ν ξ : ℤ_[q], ν ^ 2 + ξ ^ 2 = -1 := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq q (-1)
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      rintro rfl
      rw [ha] at hab
      simp at hab
    obtain ⟨ν, ξ, h⟩ := exists_lift_of_ne_zero hq hb (by rw [add_comm]; exact hab)
    exact ⟨ξ, ν, by rw [add_comm]; exact h⟩
  · exact exists_lift_of_ne_zero hq ha hab

-- a sum of four squares in `ℤ_2` with one term `1` is nonzero modulo `8`
private theorem one_add_sq_add_sq_add_sq_ne_zero (y₁ y₂ y₃ : ℤ_[2]) :
    1 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 ≠ 0 := by
  intro h
  have h8 := congrArg (PadicInt.toZModPow 3) h
  rw [map_zero, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow] at h8
  have key : ∀ a b c : ZMod 8, 1 + a ^ 2 + b ^ 2 + c ^ 2 ≠ 0 := by decide
  exact key _ _ _ h8

-- dividing by the coordinate of largest norm gives integral coordinates, one of them `1`
private theorem sq_add_sq_add_sq_add_sq_ne_zero {x₀ x₁ x₂ x₃ : ℚ_[2]} (h₀ : x₀ ≠ 0)
    (h₁ : ‖x₁‖ ≤ ‖x₀‖) (h₂ : ‖x₂‖ ≤ ‖x₀‖) (h₃ : ‖x₃‖ ≤ ‖x₀‖) :
    x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 ≠ 0 := by
  intro h
  have hn : ∀ {x : ℚ_[2]}, ‖x‖ ≤ ‖x₀‖ → ‖x / x₀‖ ≤ 1 := fun hx => by
    rw [norm_div]
    exact div_le_one_of_le₀ hx (norm_nonneg _)
  obtain ⟨y₁, hy₁⟩ : ∃ y : ℤ_[2], (y : ℚ_[2]) = x₁ / x₀ := ⟨⟨x₁ / x₀, hn h₁⟩, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : ℤ_[2], (y : ℚ_[2]) = x₂ / x₀ := ⟨⟨x₂ / x₀, hn h₂⟩, rfl⟩
  obtain ⟨y₃, hy₃⟩ : ∃ y : ℤ_[2], (y : ℚ_[2]) = x₃ / x₀ := ⟨⟨x₃ / x₀, hn h₃⟩, rfl⟩
  refine one_add_sq_add_sq_add_sq_ne_zero y₁ y₂ y₃ (PadicInt.ext ?_)
  push_cast
  rw [hy₁, hy₂, hy₃, show (1 : ℚ_[2]) + (x₁ / x₀) ^ 2 + (x₂ / x₀) ^ 2 + (x₃ / x₀) ^ 2 =
      (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) / x₀ ^ 2 by field_simp, h, zero_div]

/-- **Hamilton's quaternions are ramified at `2`**: the reduced norm of `ℍ[ℚ_2]` is anisotropic, a
sum of four squares in `ℤ_2`, one of them odd, being nonzero modulo `8`. -/
theorem nrd_eq_zero_iff_of_padic_two (x : ℍ[ℚ_[2]]) : QuaternionAlgebra.nrd x = 0 ↔ x = 0 := by
  refine ⟨fun hx => ?_, fun hx => by rw [hx]; exact map_zero _⟩
  have hsum : x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 = 0 := by
    have h := QuaternionAlgebra.nrd_apply x
    rw [hx] at h
    linear_combination -h
  by_contra hne
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ
    (fun n => ‖![x.re, x.imI, x.imJ, x.imK] n‖) Finset.univ_nonempty
  have hm' : ∀ n, ‖![x.re, x.imI, x.imJ, x.imK] n‖ ≤ ‖![x.re, x.imI, x.imJ, x.imK] m‖ :=
    fun n => hm n (Finset.mem_univ n)
  have hm0 : ![x.re, x.imI, x.imJ, x.imK] m ≠ 0 := by
    intro h0
    have hz : ∀ n, ![x.re, x.imI, x.imJ, x.imK] n = 0 := fun n =>
      norm_le_zero_iff.mp ((hm' n).trans (by rw [h0, norm_zero]))
    exact hne (QuaternionAlgebra.ext (hz 0) (hz 1) (hz 2) (hz 3))
  have h0 := hm' 0
  have h1 := hm' 1
  have h2 := hm' 2
  have h3 := hm' 3
  fin_cases m <;> simp at hm0 h0 h1 h2 h3
  · exact sq_add_sq_add_sq_add_sq_ne_zero hm0 h1 h2 h3 hsum
  · exact sq_add_sq_add_sq_add_sq_ne_zero hm0 h0 h2 h3 (by linear_combination hsum)
  · exact sq_add_sq_add_sq_add_sq_ne_zero hm0 h0 h1 h3 (by linear_combination hsum)
  · exact sq_add_sq_add_sq_add_sq_ne_zero hm0 h0 h1 h2 (by linear_combination hsum)

/-- There are no `ν, ξ ∈ ℚ_2` with `ν² + ξ² = −1`. -/
theorem not_exists_sq_add_sq_eq_neg_one_padic_two : ¬ ∃ ν ξ : ℚ_[2], ν ^ 2 + ξ ^ 2 = -1 := by
  rintro ⟨ν, ξ, h⟩
  have hx : QuaternionAlgebra.nrd (⟨1, ν, ξ, 0⟩ : ℍ[ℚ_[2]]) = 0 := by
    rw [QuaternionAlgebra.nrd_apply]
    linear_combination h
  have h0 := congrArg QuaternionAlgebra.re ((nrd_eq_zero_iff_of_padic_two _).mp hx)
  exact one_ne_zero h0

end Quaternion
