/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Quaternion.ReducedNorm
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Totally definite quaternion algebras

`(a, b / F)` is *totally definite* if `σ a < 0` and `σ b < 0` for every real embedding `σ` of `F`:
the reduced norm is then a positive definite quadratic form at every real place. A totally definite
quaternion algebra over a field with a real embedding is a division algebra, and the reduced norm of
a nonzero element is totally positive.

[Buz07, §9, p. 67]: "let `D` be a quaternion algebra over `F` ramified at all infinite places."

## Main definitions

* `QuaternionAlgebra.IsTotallyDefinite`.
* `QuaternionAlgebra.IsTotallyDefinite.divisionRing`.

## Main results

* `QuaternionAlgebra.IsTotallyDefinite.nrd_pos`: the reduced norm of a nonzero element is
  positive at every real embedding.
* `QuaternionAlgebra.isTotallyDefinite_iff_nrd_pos`.
* `QuaternionAlgebra.IsTotallyDefinite.isUnit_iff`: every nonzero element is a unit.
* `QuaternionAlgebra.exists_int_trd_of_fg`, `QuaternionAlgebra.exists_int_nrd_of_fg`: elements of
  an order are integral.
* `QuaternionAlgebra.nonempty_ringHom_real`: a totally real number field has a real embedding.
* `QuaternionAlgebra.isTotallyDefinite_hamilton`: Hamilton's quaternions over `ℚ`.

Roadmap: §0.1.2. Tau Ceti home: `TauCeti/Algebra/QuaternionAlgebra/Definite.lean`.
-/

open scoped Quaternion

noncomputable section

namespace QuaternionAlgebra

variable {F : Type*} [Field F] {a b : F}

/-- **`(a, b / F)` is totally definite**: `a` and `b` are negative at every real embedding. -/
def IsTotallyDefinite (a b : F) : Prop :=
  ∀ σ : F →+* ℝ, σ a < 0 ∧ σ b < 0

/-- The reduced norm of a nonzero element is positive at every real embedding. -/
theorem IsTotallyDefinite.nrd_pos (h : IsTotallyDefinite a b) (σ : F →+* ℝ) {x : ℍ[F,a,b]}
    (hx : x ≠ 0) : 0 < σ (nrd x) := by
  obtain ⟨ha, hb⟩ := h σ
  have hsq : ∀ y : F, y ≠ 0 → 0 < σ y ^ 2 := fun y hy ↦
    lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 fun hh ↦ hy (σ.injective (by simpa using hh))))
  have key : σ (nrd x) = σ x.re ^ 2 + -σ a * σ x.imI ^ 2 + -σ b * σ x.imJ ^ 2 +
      σ a * σ b * σ x.imK ^ 2 := by
    simp only [nrd_apply, map_add, map_sub, map_mul, map_pow]
    ring
  have hab : 0 < σ a * σ b := mul_pos_of_neg_of_neg ha hb
  have h2 : 0 ≤ -σ a * σ x.imI ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ -σ b * σ x.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 ≤ σ a * σ b * σ x.imK ^ 2 := mul_nonneg hab.le (sq_nonneg _)
  have hcomp : x.re ≠ 0 ∨ x.imI ≠ 0 ∨ x.imJ ≠ 0 ∨ x.imK ≠ 0 := by
    by_contra hc
    simp only [not_or, ne_eq, not_not] at hc
    exact hx (by ext <;> simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2])
  rw [key]
  rcases hcomp with hc | hc | hc | hc
  · linarith [hsq _ hc]
  · linarith [mul_pos (neg_pos.mpr ha) (hsq _ hc), sq_nonneg (σ x.re)]
  · linarith [mul_pos (neg_pos.mpr hb) (hsq _ hc), sq_nonneg (σ x.re)]
  · linarith [mul_pos hab (hsq _ hc), sq_nonneg (σ x.re)]

/-- **Total definiteness is the positivity of the reduced norm at every real embedding.** -/
theorem isTotallyDefinite_iff_nrd_pos :
    IsTotallyDefinite a b ↔ ∀ σ : F →+* ℝ, ∀ x : ℍ[F,a,b], x ≠ 0 → 0 < σ (nrd x) := by
  refine ⟨fun h σ x hx ↦ h.nrd_pos σ hx, fun h σ ↦ ⟨?_, ?_⟩⟩
  · have hi := h σ ⟨0, 1, 0, 0⟩ (by simp [QuaternionAlgebra.ext_iff])
    rw [show nrd (⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) = -a from by simp [nrd_apply]] at hi
    simpa using hi
  · have hj := h σ ⟨0, 0, 1, 0⟩ (by simp [QuaternionAlgebra.ext_iff])
    rw [show nrd (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) = -b from by simp [nrd_apply]] at hj
    simpa using hj

/-- The reduced norm of a nonzero element of a totally definite algebra is nonzero. -/
theorem IsTotallyDefinite.nrd_ne_zero [Nonempty (F →+* ℝ)] (h : IsTotallyDefinite a b)
    {x : ℍ[F,a,b]} (hx : x ≠ 0) : nrd x ≠ 0 := by
  obtain ⟨σ⟩ := ‹Nonempty (F →+* ℝ)›
  exact fun hn ↦ (h.nrd_pos σ hx).ne' (by rw [hn, map_zero])

/-- **In a totally definite quaternion algebra every nonzero element is a unit.** -/
theorem IsTotallyDefinite.isUnit_iff [Nonempty (F →+* ℝ)] (h : IsTotallyDefinite a b)
    {x : ℍ[F,a,b]} : IsUnit x ↔ x ≠ 0 := by
  refine ⟨fun hu ↦ ?_, fun hx ↦ isUnit_iff_isUnit_nrd.mpr (h.nrd_ne_zero hx).isUnit⟩
  rintro rfl
  exact zero_ne_one (isUnit_zero_iff.mp hu)

/-- **A totally definite quaternion algebra is a division ring**, with `x⁻¹ = (nrd x)⁻¹ x̄`. -/
abbrev IsTotallyDefinite.divisionRing [Nonempty (F →+* ℝ)] (h : IsTotallyDefinite a b) :
    DivisionRing ℍ[F,a,b] :=
  { (inferInstance : Ring ℍ[F,a,b]) with
    inv := fun x ↦ (nrd x)⁻¹ • star x
    exists_pair_ne := ⟨0, 1, zero_ne_one⟩
    mul_inv_cancel := by
      intro x hx
      show x * ((nrd x)⁻¹ • star x) = 1
      rw [mul_smul_comm, ← coe_nrd, smul_coe, inv_mul_cancel₀ (h.nrd_ne_zero hx), coe_one]
    inv_zero := by
      show (nrd (0 : ℍ[F,a,b]))⁻¹ • star (0 : ℍ[F,a,b]) = 0
      simp
    nnqsmul := _
    nnqsmul_def := fun _ _ ↦ rfl
    qsmul := _
    qsmul_def := fun _ _ ↦ rfl }

private theorem isIntegral_of_mem_of_fg {S : Subring ℍ[F,a,b]} (hS : S.toAddSubgroup.FG)
    {x : ℍ[F,a,b]} (hx : x ∈ S) : IsIntegral ℤ x := by
  refine IsIntegral.of_mem_of_fg (subalgebraOfSubring S) ?_ x hx
  rw [Submodule.fg_iff_addSubgroup_fg]
  exact hS

private theorem isIntegral_star {x : ℍ[F,a,b]} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) := by
  obtain ⟨p, hpm, hp⟩ := hx
  refine ⟨p, hpm, ?_⟩
  have key : ∀ q : Polynomial ℤ, Polynomial.eval₂ (algebraMap ℤ ℍ[F,a,b]) (star x) q
      = star (Polynomial.eval₂ (algebraMap ℤ ℍ[F,a,b]) x q) := by
    intro q
    refine Polynomial.induction_on' q ?_ ?_
    · intro u v hu hv
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add, hu, hv, star_add]
    · intro n c
      simp only [Polynomial.eval₂_monomial, star_mul, star_pow, algebraMap_int_eq, eq_intCast,
        star_intCast]
      exact (Int.cast_commute c _).eq
  rw [key, hp, star_zero]

open scoped IsMulCommutative in
private theorem isIntegral_of_mem_closure_pair {x y z : ℍ[F,a,b]} (hxy : x * y = y * x)
    (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y)
    (hz : z ∈ Subring.closure ({x, y} : Set ℍ[F,a,b])) : IsIntegral ℤ z := by
  have hcomm : ∀ u ∈ ({x, y} : Set ℍ[F,a,b]), ∀ v ∈ ({x, y} : Set ℍ[F,a,b]), u * v = v * u := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro u (rfl | rfl) v (rfl | rfl)
    exacts [rfl, hxy, hxy.symm, rfl]
  haveI := Subring.isMulCommutative_closure hcomm
  have hiff : ∀ w : Subring.closure ({x, y} : Set ℍ[F,a,b]),
      IsIntegral ℤ w ↔ IsIntegral ℤ (w : ℍ[F,a,b]) := fun w ↦
    (isIntegral_algHom_iff
      (RingHom.toIntAlgHom (Subring.subtype (Subring.closure ({x, y} : Set ℍ[F,a,b]))))
      Subtype.val_injective).symm
  refine (hiff ⟨z, hz⟩).mp ?_
  induction hz using Subring.closure_induction with
  | mem u hu =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    exacts [(hiff _).mpr hx, (hiff _).mpr hy]
  | zero => exact isIntegral_zero
  | one => exact isIntegral_one
  | add u v hu hv ihu ihv => exact ihu.add ihv
  | neg u hu ihu => exact ihu.neg
  | mul u v hu hv ihu ihv => exact ihu.mul ihv

private theorem isIntegral_of_coe {r : F} (h : IsIntegral ℤ ((r : F) : ℍ[F,a,b])) :
    IsIntegral ℤ r :=
  (isIntegral_algHom_iff ((Algebra.ofId F ℍ[F,a,b]).restrictScalars ℤ) algebraMap_injective).mp h

private theorem isIntegral_of_mem_closure_star {x z : ℍ[F,a,b]} (hx : IsIntegral ℤ x)
    (hz : z ∈ Subring.closure ({x, star x} : Set ℍ[F,a,b])) : IsIntegral ℤ z :=
  isIntegral_of_mem_closure_pair ((coe_nrd x).symm.trans (coe_nrd' x)) hx (isIntegral_star hx) hz

private theorem isIntegral_trd {x : ℍ[F,a,b]} (hx : IsIntegral ℤ x) : IsIntegral ℤ (trd x) :=
  isIntegral_of_coe <| (coe_trd x).symm ▸ isIntegral_of_mem_closure_star hx
    (Subring.add_mem _ (Subring.subset_closure (by simp)) (Subring.subset_closure (by simp)))

private theorem isIntegral_nrd {x : ℍ[F,a,b]} (hx : IsIntegral ℤ x) : IsIntegral ℤ (nrd x) :=
  isIntegral_of_coe <| (coe_nrd x).symm ▸ isIntegral_of_mem_closure_star hx
    (Subring.mul_mem _ (Subring.subset_closure (by simp)) (Subring.subset_closure (by simp)))

/-- **Elements of an order are integral**: an element of a subring of `ℍ[ℚ,a,b]` that is finitely
generated as an abelian group has integral reduced trace. -/
theorem exists_int_trd_of_fg {a b : ℚ} {S : Subring ℍ[ℚ,a,b]}
    (hS : S.toAddSubgroup.FG) {x : ℍ[ℚ,a,b]} (hx : x ∈ S) : ∃ t : ℤ, trd x = (t : ℚ) := by
  obtain ⟨t, ht⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trd (isIntegral_of_mem_of_fg hS hx))
  exact ⟨t, by simpa using ht.symm⟩

/-- The reduced norm of an element of an order is an integer. -/
theorem exists_int_nrd_of_fg {a b : ℚ} {S : Subring ℍ[ℚ,a,b]}
    (hS : S.toAddSubgroup.FG) {x : ℍ[ℚ,a,b]} (hx : x ∈ S) : ∃ n : ℤ, nrd x = (n : ℚ) := by
  obtain ⟨n, hn⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_nrd (isIntegral_of_mem_of_fg hS hx))
  exact ⟨n, by simpa using hn.symm⟩

/-- A totally real number field has a real embedding. -/
theorem nonempty_ringHom_real [NumberField F] [NumberField.IsTotallyReal F] :
    Nonempty (F →+* ℝ) := by
  obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
  exact ⟨(NumberField.IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

/-- **Hamilton's quaternions `(−1, −1 / ℚ)` are totally definite.** -/
theorem isTotallyDefinite_hamilton : IsTotallyDefinite (-1 : ℚ) (-1) := by
  intro σ
  constructor <;> norm_num

end QuaternionAlgebra
