/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination

/-!
# The reduced norm and reduced trace of `ℍ[R,a,b]`

For Mathlib's quaternion algebra `ℍ[R,a,b] = (a, b / R)` over a commutative ring, with its canonical
involution `star`: the reduced trace `trd x = x + x̄ = 2 x.re`, the reduced norm
`nrd x = x x̄ = re² − a·imI² − b·imJ² + ab·imK²`, the quadratic relation
`x² − trd(x) x + nrd(x) = 0`, and the characterisation of units. The reduced norm and trace are the
determinant and trace in **every** splitting: for an `R`-algebra homomorphism
`φ : ℍ[R,a,b] → M₂(S)` with `2`, `a`, `b` invertible in `S`, `det (φ x) = nrd x` and
`tr (φ x) = trd x`.

[Voi21, 3.2.9]: "Suppose `char F ≠ 2` and let `B = (a, b | F)`. Then the map
`α = t + xi + yj + zk ↦ ᾱ = t − xi − yj − zk` defines a standard involution on `B`."

## Main definitions

* `QuaternionAlgebra.trd`: the reduced trace, an `R`-linear map.
* `QuaternionAlgebra.nrd`: the reduced norm, a monoid-with-zero homomorphism.
* `QuaternionAlgebra.mapRingHom`: change of coefficients `ℍ[R,a,b] →+* ℍ[S,f a,f b]` along a ring
  homomorphism `f : R →+* S`.

## Main results

* `QuaternionAlgebra.coe_nrd`, `QuaternionAlgebra.coe_trd`: `nrd x = x * star x`,
  `trd x = x + star x`.
* `QuaternionAlgebra.nrd_add`: the polarisation `nrd (x + y) = nrd x + nrd y + trd (x ȳ)`.
* `QuaternionAlgebra.mul_self_eq`: the quadratic relation.
* `QuaternionAlgebra.isUnit_iff_isUnit_nrd`.
* `QuaternionAlgebra.det_map_eq_nrd`, `QuaternionAlgebra.trace_map_eq_trd`: independence of the
  splitting.
* `Quaternion.nrd_eq_normSq`: for Hamilton's quaternions the reduced norm is `normSq`.

Roadmap: §0.1.1. Tau Ceti home: `TauCeti/Algebra/QuaternionAlgebra/ReducedNorm.lean`.
-/

open scoped Quaternion

noncomputable section

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- **The reduced trace** `trd x = x + x̄ = 2 x.re`. -/
def trd : ℍ[R,a,b] →ₗ[R] R where
  toFun x := 2 * x.re
  map_add' x y := by simp [mul_add]
  map_smul' r x := by simp [mul_left_comm]

/-- **The reduced norm** `nrd x = x x̄ = re² − a·imI² − b·imJ² + ab·imK²`. -/
def nrd : ℍ[R,a,b] →*₀ R where
  toFun x := x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp only [re_mul, imI_mul, imJ_mul, imK_mul]; ring

theorem trd_apply (x : ℍ[R,a,b]) : trd x = 2 * x.re := rfl

theorem nrd_apply (x : ℍ[R,a,b]) :
    nrd x = x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 := rfl

/-- `nrd x = x x̄`. -/
theorem coe_nrd (x : ℍ[R,a,b]) : ((nrd x : R) : ℍ[R,a,b]) = x * star x := by
  rw [mul_star_eq_coe]
  congr 1
  simp only [nrd_apply, re_mul, re_star, imI_star, imJ_star, imK_star]
  ring

theorem coe_nrd' (x : ℍ[R,a,b]) : ((nrd x : R) : ℍ[R,a,b]) = star x * x :=
  (coe_nrd x).trans (star_comm_self' x).symm

/-- `trd x = x + x̄`. -/
theorem coe_trd (x : ℍ[R,a,b]) : ((trd x : R) : ℍ[R,a,b]) = x + star x := by
  rw [self_add_star', trd_apply]
  simp

@[simp]
theorem nrd_star (x : ℍ[R,a,b]) : nrd (star x) = nrd x := by
  simp [nrd_apply]

@[simp]
theorem trd_star (x : ℍ[R,a,b]) : trd (star x) = trd x := by
  simp [trd_apply]

@[simp]
theorem nrd_coe (r : R) : nrd (r : ℍ[R,a,b]) = r ^ 2 := by
  simp [nrd_apply]

@[simp]
theorem trd_coe (r : R) : trd (r : ℍ[R,a,b]) = 2 * r := by
  simp [trd_apply]

theorem nrd_smul (r : R) (x : ℍ[R,a,b]) : nrd (r • x) = r ^ 2 * nrd x := by
  simp only [nrd_apply, re_smul, imI_smul, imJ_smul, imK_smul, smul_eq_mul]
  ring

/-- The polarisation of the reduced norm. -/
theorem nrd_add (x y : ℍ[R,a,b]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  simp only [nrd_apply, trd_apply, re_add, imI_add, imJ_add, imK_add, re_mul, re_star, imI_star,
    imJ_star, imK_star]
  ring

/-- **The quadratic relation** `x² = trd(x) x − nrd(x)`. -/
theorem mul_self_eq (x : ℍ[R,a,b]) : x * x = trd x • x - nrd x • (1 : ℍ[R,a,b]) := by
  ext <;> simp [trd_apply, nrd_apply] <;> ring

/-- **`x` is a unit exactly when `nrd x` is**, with inverse `(nrd x)⁻¹ x̄`. -/
theorem isUnit_iff_isUnit_nrd {x : ℍ[R,a,b]} : IsUnit x ↔ IsUnit (nrd x) := by
  refine ⟨fun h ↦ h.map nrd, fun h ↦ ?_⟩
  obtain ⟨u, hu⟩ := h
  refine ⟨⟨x, (↑u⁻¹ : R) • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, ← coe_nrd, ← hu, smul_coe, Units.inv_mul, coe_one]
  · rw [smul_mul_assoc, ← coe_nrd', ← hu, smul_coe, Units.inv_mul, coe_one]

section Splitting

variable {S : Type*} [CommRing S] [Algebra R S]

private theorem algebraMap_matrix_eq_smul_one (r : R) :
    algebraMap R (Matrix (Fin 2) (Fin 2) S) r =
      algebraMap R S r • (1 : Matrix (Fin 2) (Fin 2) S) := by
  rw [Algebra.algebraMap_eq_smul_one, algebraMap_smul]

private theorem mul_self_eq_trace_smul_sub_det_smul (M : Matrix (Fin 2) (Fin 2) S) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two, Fin.sum_univ_succ] <;> ring

private theorem exists_mul_eq_one_of_mul_self_eq_smul_one {M : Matrix (Fin 2) (Fin 2) S} {c : S}
    (hc : IsUnit c) (h : M * M = c • (1 : Matrix (Fin 2) (Fin 2) S)) :
    ∃ N, M * N = 1 ∧ N * M = 1 := by
  obtain ⟨u, rfl⟩ := hc
  refine ⟨(↑u⁻¹ : S) • M, ?_, ?_⟩
  · rw [mul_smul_comm, h, smul_smul, Units.inv_mul, one_smul]
  · rw [smul_mul_assoc, h, smul_smul, Units.inv_mul, one_smul]

private theorem trace_eq_zero_of_anticommute (h2 : IsUnit (2 : S))
    {M N N' : Matrix (Fin 2) (Fin 2) S} (hNN' : N * N' = 1) (hN'N : N' * N = 1)
    (h : N * M = -(M * N)) : M.trace = 0 := by
  have key : M.trace = -M.trace :=
    calc M.trace = (N' * N * M).trace := by rw [hN'N, Matrix.one_mul]
      _ = (N * M * N').trace := by rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = (-(M * (N * N'))).trace := by rw [h, neg_mul, Matrix.mul_assoc]
      _ = -M.trace := by rw [hNN', Matrix.mul_one, Matrix.trace_neg]
  exact h2.mul_right_eq_zero.mp (by linear_combination key)

private theorem trace_map_eq_zero_of_anticommute (φ : ℍ[R,a,b] →ₐ[R] Matrix (Fin 2) (Fin 2) S)
    (h2 : IsUnit (2 : S)) {p q : ℍ[R,a,b]} {c : R} (hc : IsUnit (algebraMap R S c))
    (hq : q * q = algebraMap R ℍ[R,a,b] c) (hpq : q * p = -(p * q)) : (φ p).trace = 0 := by
  have hN : φ q * φ q = algebraMap R S c • (1 : Matrix (Fin 2) (Fin 2) S) := by
    rw [← map_mul, hq, AlgHom.commutes, algebraMap_matrix_eq_smul_one]
  obtain ⟨N', hN', hN'q⟩ := exists_mul_eq_one_of_mul_self_eq_smul_one hc hN
  exact trace_eq_zero_of_anticommute h2 hN' hN'q (by rw [← map_mul, ← map_mul, hpq, map_neg])

/-- **The reduced trace is the trace in every splitting.** -/
theorem trace_map_eq_trd (φ : ℍ[R,a,b] →ₐ[R] Matrix (Fin 2) (Fin 2) S) (h2 : IsUnit (2 : S))
    (ha : IsUnit (algebraMap R S a)) (hb : IsUnit (algebraMap R S b)) (x : ℍ[R,a,b]) :
    (φ x).trace = algebraMap R S (trd x) := by
  have hi : (⟨0, 1, 0, 0⟩ : ℍ[R,a,b]) * ⟨0, 1, 0, 0⟩ = algebraMap R ℍ[R,a,b] a := by
    ext <;> simp [algebraMap_eq]
  have hj : (⟨0, 0, 1, 0⟩ : ℍ[R,a,b]) * ⟨0, 0, 1, 0⟩ = algebraMap R ℍ[R,a,b] b := by
    ext <;> simp [algebraMap_eq]
  have hI : (φ ⟨0, 1, 0, 0⟩).trace = 0 :=
    trace_map_eq_zero_of_anticommute φ h2 hb hj (by ext <;> simp)
  have hJ : (φ ⟨0, 0, 1, 0⟩).trace = 0 :=
    trace_map_eq_zero_of_anticommute φ h2 ha hi (by ext <;> simp)
  have hK : (φ ⟨0, 0, 0, 1⟩).trace = 0 :=
    trace_map_eq_zero_of_anticommute φ h2 ha hi (by ext <;> simp)
  have hx : x = algebraMap R ℍ[R,a,b] x.re + x.imI • (⟨0, 1, 0, 0⟩ : ℍ[R,a,b]) +
      x.imJ • (⟨0, 0, 1, 0⟩ : ℍ[R,a,b]) + x.imK • (⟨0, 0, 0, 1⟩ : ℍ[R,a,b]) := by
    ext <;> simp [algebraMap_eq]
  rw [hx]
  simp only [map_add, map_smul, AlgHom.commutes, Matrix.trace_add, Matrix.trace_smul, hI, hJ, hK,
    smul_zero, add_zero, algebraMap_matrix_eq_smul_one, Matrix.trace_one, trd_apply]
  simp [map_ofNat, mul_comm]

/-- **The reduced norm is the determinant in every splitting.** -/
theorem det_map_eq_nrd (φ : ℍ[R,a,b] →ₐ[R] Matrix (Fin 2) (Fin 2) S) (h2 : IsUnit (2 : S))
    (ha : IsUnit (algebraMap R S a)) (hb : IsUnit (algebraMap R S b)) (x : ℍ[R,a,b]) :
    (φ x).det = algebraMap R S (nrd x) := by
  have hCH := mul_self_eq_trace_smul_sub_det_smul (φ x)
  rw [← map_mul, mul_self_eq, map_sub, map_smul, map_smul, map_one,
    algebra_compatible_smul S (trd x), algebra_compatible_smul S (nrd x),
    trace_map_eq_trd φ h2 ha hb x] at hCH
  simpa using (congrFun (congrFun (sub_right_inj.mp hCH) 0) 0).symm

end Splitting

section Map

variable {S : Type*} [CommRing S]

/-- **Change of coefficients** `ℍ[R,a,b] → ℍ[S,f a,f b]` along a ring homomorphism `f`. -/
def mapRingHom (f : R →+* S) (a b : R) : ℍ[R,a,b] →+* ℍ[S,f a,f b] where
  toFun x := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp]
theorem nrd_mapRingHom (f : R →+* S) (x : ℍ[R,a,b]) : nrd (mapRingHom f a b x) = f (nrd x) := by
  simp [nrd_apply, mapRingHom]

@[simp]
theorem trd_mapRingHom (f : R →+* S) (x : ℍ[R,a,b]) : trd (mapRingHom f a b x) = f (trd x) := by
  simp [trd_apply, mapRingHom, map_ofNat]

end Map

end QuaternionAlgebra

namespace Quaternion

variable {R : Type*} [CommRing R]

/-- For Hamilton's quaternions the reduced norm is `Quaternion.normSq`. -/
theorem nrd_eq_normSq (x : ℍ[R]) : QuaternionAlgebra.nrd x = normSq x := by
  have hx : QuaternionAlgebra.nrd x
      = x.re ^ 2 - (-1) * x.imI ^ 2 - (-1) * x.imJ ^ 2 + (-1) * (-1) * x.imK ^ 2 := rfl
  rw [hx, normSq_def']
  ring

end Quaternion
