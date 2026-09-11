/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.U3.«2_Level»

/-!
# Almost-everywhere integrality and denominators in `D ⊗ 𝔸_f`

Part 3 of the class-number-one chain (board `.mathlib-quality/hurwitz-cn1/`).

The finite adele ring is the restricted product `Πʳ_v [K_v, 𝓞_v]` [Voight 27.6.1;
mathlib `IsDedekindDomain.FiniteAdeleRing`], so an element of `D ⊗[ℚ] 𝔸_f` — a finite
sum of pure tensors — is integral (lands in `localOrder w`) at all but finitely many
places, and some nonzero integer multiple of it is integral everywhere.  These are the
two facts the idelic dictionary consumes; both are proved by `TensorProduct` induction
from their scalar analogues (`a.2 : ∀ᶠ v, a v ∈ 𝓞_v` for a finite adele `a`, and
per-place denominator clearing via the adic valuation).

Note the FLT-repo counterpart `FLT/Data/HurwitzRatHat.lean: canonicalForm` states the
denominator-clearing fact in the `ẐHat` formulation, with `sorry`; the FLT project is
dropping that file (2026-08-10), so it is proven here instead, in the live
`FiniteAdeleRing` framework.  The direct induction sufficed, so the restricted-product
tensor machinery of `PhD/QMF/FLTstuff/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`
was not needed.
-/

open Quaternion IsDedekindDomain NumberField QMF
open scoped TensorProduct

/- See `Setting.lean`: pin the adic `Algebra ℚ K_w` instance path used by the `QMF`
framework, keeping statements syntactically aligned with `04_Level.lean`'s. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/-- Denominator clearing in `ℚ`: any integer multiple of `q.den` turns `q` into an
integer. -/
private theorem exists_intCast_eq_of_den_dvd {q : ℚ} {m : ℤ} (h : (q.den : ℤ) ∣ m) :
    ∃ a : ℤ, (m : ℚ) * q = (a : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨c * q.num, ?_⟩
  push_cast
  linear_combination (c : ℚ) * Rat.mul_den_eq_num q

/-- A common multiple `m` of the four coordinate denominators clears them all at once:
`m • d` has integer coordinates, hence is `IsHurwitz` with all four parities even. -/
private theorem intCast_smul_mem_hurwitzOrder {d : D} {m : ℤ} (hre : (d.re.den : ℤ) ∣ m)
    (himI : (d.imI.den : ℤ) ∣ m) (himJ : (d.imJ.den : ℤ) ∣ m) (himK : (d.imK.den : ℤ) ∣ m) :
    (m : ℚ) • d ∈ hurwitzOrder := by
  obtain ⟨a, ha⟩ := exists_intCast_eq_of_den_dvd hre
  obtain ⟨b, hb⟩ := exists_intCast_eq_of_den_dvd himI
  obtain ⟨c, hc⟩ := exists_intCast_eq_of_den_dvd himJ
  obtain ⟨e, he⟩ := exists_intCast_eq_of_den_dvd himK
  have half : ∀ z : ℤ, ((2 * z : ℤ) : ℚ) / 2 = (z : ℚ) := by
    intro z
    push_cast
    ring
  refine ⟨2 * a, 2 * b, 2 * c, 2 * e, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩
  · rw [half, Quaternion.re_smul, smul_eq_mul, ha]
  · rw [half, Quaternion.imI_smul, smul_eq_mul, hb]
  · rw [half, Quaternion.imJ_smul, smul_eq_mul, hc]
  · rw [half, Quaternion.imK_smul, smul_eq_mul, he]

/-- Every rational quaternion has a nonzero integer multiple in the Hurwitz order: the
product of the four coordinate denominators makes every coordinate an integer, which is
`IsHurwitz` with all parities even. -/
theorem exists_intCast_smul_mem_hurwitzOrder (d : D) :
    ∃ M : ℤ, M ≠ 0 ∧ (M : ℚ) • d ∈ hurwitzOrder :=
  ⟨(d.re.den : ℤ) * d.imI.den * d.imJ.den * d.imK.den, by simp,
    intCast_smul_mem_hurwitzOrder (((dvd_mul_right _ _).mul_right _).mul_right _)
      (((dvd_mul_left _ _).mul_right _).mul_right _) ((dvd_mul_left _ _).mul_right _)
      (dvd_mul_left _ _)⟩

/-- Per-place denominator clearing: every element of the completion `K_v` has a nonzero
integer multiple in `𝓞_v` (an element of `v.asIdeal ^ k` for large `k`, read through
the adic valuation). -/
theorem exists_intCast_mul_mem_adicCompletionIntegers
    {v : HeightOneSpectrum (RingOfIntegers ℚ)} (x : v.adicCompletion ℚ) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨r, hr, hrx⟩ :=
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hr' : ((Rat.ringOfIntegersEquiv r : ℤ) : RingOfIntegers ℚ) = r :=
    (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* _) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply r)
  refine ⟨Rat.ringOfIntegersEquiv r, by simpa using nonZeroDivisors.ne_zero hr, ?_⟩
  rwa [← map_intCast (algebraMap (RingOfIntegers ℚ) (v.adicCompletion ℚ)), hr', mul_comm]

/-- Global denominator clearing for a finite adele: some nonzero integer multiple is
integral at every place.  (The bad set is finite by the restricted-product structure;
multiply the per-place clearings of `exists_intCast_mul_mem_adicCompletionIntegers`,
the remaining factors being integers hence integral.) -/
theorem exists_intCast_mul_mem_adicCompletionIntegers_forall
    (a : FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ v, (N : v.adicCompletion ℚ) * a v ∈ v.adicCompletionIntegers ℚ := by
  classical
  choose n hn0 hn using fun v : HeightOneSpectrum (RingOfIntegers ℚ) =>
    exists_intCast_mul_mem_adicCompletionIntegers (v := v) (a v)
  have hS : {v : HeightOneSpectrum (RingOfIntegers ℚ) |
      a v ∉ v.adicCompletionIntegers ℚ}.Finite := Filter.eventually_cofinite.mp a.2
  refine ⟨∏ v ∈ hS.toFinset, n v, Finset.prod_ne_zero_iff.mpr fun v _ => hn0 v, fun v => ?_⟩
  by_cases hv : v ∈ hS.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, Int.cast_mul,
      mul_comm (n v : v.adicCompletion ℚ), mul_assoc]
    exact mul_mem (intCast_mem _ _) (hn v)
  · exact mul_mem (intCast_mem _ _) (not_not.mp fun h => hv (hS.mem_toFinset.mpr h))

/-- Multiplying by an integer preserves local integrality: `(k : ℚ) • ξ` is the `ℤ`-smul
`k • ξ`, and a subring is closed under `ℤ`-smul. -/
private theorem intCast_smul_mem_localOrder {w : HeightOneSpectrum (RingOfIntegers ℚ)} (k : ℤ)
    {ξ : D ⊗[ℚ] w.adicCompletion ℚ} (hξ : ξ ∈ localOrder w) : (k : ℚ) • ξ ∈ localOrder w :=
  (Int.cast_smul_eq_zsmul ℚ k ξ).symm ▸ zsmul_mem hξ k

/-- **Almost-everywhere integrality** in `D ⊗ 𝔸_f`: every element is in the local order
at all but finitely many places.  `TensorProduct` induction: for a pure tensor `d ⊗ a`,
away from the (finitely many) places where `a` is not integral or the denominator of
`d` is not a unit, `d ⊗ a_w ∈ localOrder w`. -/
theorem eventually_toLocal_mem_localOrder
    (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    ∀ᶠ w in Filter.cofinite, toLocal ℚ D w x ∈ localOrder w := by
  induction x using TensorProduct.induction_on with
  | zero => exact .of_forall fun w => (map_zero (toLocal ℚ D w)).symm ▸ zero_mem _
  | tmul d a =>
    obtain ⟨M, hM0, hM⟩ := exists_intCast_smul_mem_hurwitzOrder d
    filter_upwards [a.2,
      (algebraMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ) (M : ℚ)⁻¹).2] with w ha hb
    have key : ((M : ℚ) • d) ⊗ₜ[ℚ]
        (algebraMap ℚ (w.adicCompletion ℚ) (M : ℚ)⁻¹ * a w) = d ⊗ₜ[ℚ] a w := by
      rw [TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul,
        mul_inv_cancel₀ (Int.cast_ne_zero.mpr hM0), one_smul]
    rw [toLocal_tmul, evalAlgHom_apply, ← key]
    exact tmul_mem_localOrder hM ⟨_, mul_mem hb ha⟩
  | add x y hx hy =>
    filter_upwards [hx, hy] with w h1 h2
    rw [map_add]
    exact add_mem h1 h2

/-- **Denominator clearing** in `D ⊗ 𝔸_f`: some nonzero integer multiple of any element
is in the local order at every place.  (`TensorProduct` induction from
`exists_intCast_smul_mem_hurwitzOrder` and
`exists_intCast_mul_mem_adicCompletionIntegers_forall`; this is the live-framework
statement of FLT's `canonicalForm`.) -/
theorem exists_intCast_smul_toLocal_mem
    (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ w, toLocal ℚ D w ((N : ℚ) • x) ∈ localOrder w := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, fun w => by
      rw [smul_zero, map_zero]
      exact zero_mem _⟩
  | tmul d a =>
    obtain ⟨M, hM0, hM⟩ := exists_intCast_smul_mem_hurwitzOrder d
    obtain ⟨N, hN0, hN⟩ := exists_intCast_mul_mem_adicCompletionIntegers_forall a
    refine ⟨M * N, mul_ne_zero hM0 hN0, fun w => ?_⟩
    have hNa : (N : w.adicCompletion ℚ) * a w = (N : ℚ) • a w := by
      rw [Algebra.smul_def, map_intCast]
    have key : ((M * N : ℤ) : ℚ) • (d ⊗ₜ[ℚ] a w) =
        ((M : ℚ) • d) ⊗ₜ[ℚ] ((N : w.adicCompletion ℚ) * a w) := by
      rw [hNa, TensorProduct.smul_tmul_smul, Int.cast_mul]
    rw [map_smul, toLocal_tmul, evalAlgHom_apply, key]
    exact tmul_mem_localOrder hM ⟨_, hN w⟩
  | add x y hx hy =>
    obtain ⟨N₁, h₁0, h₁⟩ := hx
    obtain ⟨N₂, h₂0, h₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero h₁0 h₂0, fun w => ?_⟩
    have key : toLocal ℚ D w (((N₁ * N₂ : ℤ) : ℚ) • (x + y)) =
        (N₂ : ℚ) • toLocal ℚ D w ((N₁ : ℚ) • x) + (N₁ : ℚ) • toLocal ℚ D w ((N₂ : ℚ) • y) := by
      simp only [map_add, map_smul, smul_add, smul_smul]
      push_cast
      rw [mul_comm (N₂ : ℚ) (N₁ : ℚ)]
    rw [key]
    exact add_mem (intCast_smul_mem_localOrder _ (h₁ w)) (intCast_smul_mem_localOrder _ (h₂ w))

end JacobsSlash
