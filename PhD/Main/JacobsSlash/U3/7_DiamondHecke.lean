/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.JacobsSlash.U3.«6_Matrix»

/-!
# The diamond operator `W = [U₁(9)·μ·U₁(9)]` and its matrix

The `W`-side of the identification, in the thesis's own convention.  `μ = diag(1,4)` at
`3` [Jacobs, Lemma 2.9] — the thesis's own element: in the fork's d-form `U₁(9)` the trap
is `diag(4,1)` (its `(1,1)`-entry is `1`, so it lies in `U₁(9)` and would make
`[U₁(9)μU₁(9)]` the identity), the mirror image of the left-handed library's situation.

`μ` lies in the acting monoid `Δ₁(3)` of `«6_Matrix»` but *not* in `U₁(9)`, and it
normalises `U₁(9)`, so `U₁(9)·μ·U₁(9)` is a single right coset and `heckeW` is the same
`heckeOperatorSlash` construction as `heckeU3` — **on the same space `kappaForms`**, at
`μ` instead of `η₃`.  (The wide `κ`-layer that this file used to carry now lives at its
proper depth in `«1_Setting»` and `«4_KappaColumn»`; `Σ₁(3)` is the single acting monoid.)

## Main definitions

* `JacobsSlash.mu3`: the adelic `μ`, trivial away from `3` and `diag(1,4)` at `3`.
* `JacobsSlash.uTableW`: the three certificates (oracle `certificate_search_w.py`).
* `JacobsSlash.heckeW`: the Hecke operator `W = [U₁(9)·μ·U₁(9)]` on `kappaForms`.

## Main statements

* `JacobsSlash.bijOn_muRep`: `U₁(9)·μ·U₁(9)` is the single right coset `U₁(9)·μ`.
* `JacobsSlash.kappaSlash_acting_eq_delta`: each certificate acting operator IS the
  transcribed `δ` — **twist-free**, no coboundary scalar.
* `JacobsSlash.heckeW_apply_classRep_eq_delta`: `(Wφ)(cᵢ) = δᵢ(φ(c_{σ_W(i)}))` — with
  `«4_DiamondW»`'s `Wop_eq_blockOp_deltaOf`, this says `Wop` is the matrix of the
  genuine `W`.
-/

open Quaternion IsDedekindDomain NumberField QMF TateFredholm AbstractHeckeOperatorSlash RightSlashAction
open scoped TateFredholm PowerSeries Pointwise TensorProduct

/- See `«1_Setting»`: pin the adic `Algebra ℚ K₃` path. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/-! ### The adelic diamond element `μ = diag(1,4)` and its single right coset

The fork uses the **thesis's own** `μ = diag(1,4)` at `3`.  (Handedness note, oracle
record `certificate_search_w.py`: in the fork's d-form `U₁(9)` the trap element is
`diag(4,1)` — its `(1,1)`-entry is `1`, so it lies in `U₁(9)` and would make `[U₁(9)μU₁(9)]`
the identity; `diag(1,4)` has `v(4 − 1) = v(3) > γ₉`, so it is genuinely outside.  The
left-handed library had these roles reversed.) -/

section Diamond

/-- The adelic diamond element `μ`: trivial away from `3`, and the thesis's `diag(1,4)`
at `3` [Jacobs, Lemma 2.9]. -/
noncomputable def mu3 : Dfx ℚ D :=
  unitAt ℚ D v₃ (diagUnit (1 : K₃) (4 : K₃) one_ne_zero (by norm_num))

@[simp] theorem toMatrix_mu3 :
    toMatrix ℚ D v₃ mu3 = Matrix.of ![![(1 : K₃), 0], ![0, 4]] := by
  rw [mu3, toMatrix_unitAt, diagUnit_val]

@[simp] theorem toMatrix_mu3_inv :
    toMatrix ℚ D v₃ mu3⁻¹ = Matrix.of ![![(1 : K₃), 0], ![0, (4 : K₃)⁻¹]] := by
  rw [mu3, unitAt_inv, toMatrix_unitAt, diagUnit_inv, inv_one]

@[simp] theorem toLocal_mu3_ne {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w ((mu3 : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) = 1 :=
  toLocal_unitAt_ne ℚ D v₃ _ hw

@[simp] theorem toLocal_mu3_inv_ne {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((mu3⁻¹ : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) = 1 := by
  rw [mu3, unitAt_inv]
  exact toLocal_unitAt_ne ℚ D v₃ _ hw

/-- `‖4‖ = 1`: `4` is a `3`-adic unit. -/
theorem norm_four_eq_one : ‖(4 : K₃)‖ = 1 :=
  norm_ofNat_eq_one norm_three_lt_one (n := 4) (by norm_num) (by norm_num)

/-- `v(4) = 1`: `4` is a `3`-adic unit, valuation-side. -/
theorem valued_four_eq_one : Valued.v (4 : K₃) = 1 := by
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.mp norm_four_eq_one.le) ?_
  by_contra hlt
  exact absurd (Valued.toNormedField.norm_lt_one_iff.mpr (not_le.mp hlt))
    (by rw [norm_four_eq_one]; exact lt_irrefl 1)

/-- `v(4⁻¹) = 1`. -/
theorem valued_inv_four_eq_one : Valued.v ((4 : K₃)⁻¹) = 1 := by
  rw [map_inv₀, valued_four_eq_one, inv_one]

/-- The entries of the `μ`-conjugate of a matrix: `(a b; c d) ↦ (a b/4; 4c d)`. -/
theorem conj_mu3_entries (M : Matrix (Fin 2) (Fin 2) K₃) :
    Matrix.of ![![(1 : K₃), 0], ![0, 4]] * M * Matrix.of ![![(1 : K₃), 0], ![0, (4 : K₃)⁻¹]]
      = Matrix.of ![![M 0 0, M 0 1 * (4 : K₃)⁻¹], ![4 * M 1 0, M 1 1]] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      mul_comm, ← mul_assoc]

/-- The `3`-component of the `μ`-conjugate. -/
theorem toMatrix_conj_mu3 (u : Dfx ℚ D) :
    toMatrix ℚ D v₃ (mu3 * u * mu3⁻¹)
      = Matrix.of ![![toMatrix ℚ D v₃ u 0 0, toMatrix ℚ D v₃ u 0 1 * (4 : K₃)⁻¹],
                    ![4 * toMatrix ℚ D v₃ u 1 0, toMatrix ℚ D v₃ u 1 1]] := by
  rw [map_mul, map_mul, toMatrix_mu3, toMatrix_mu3_inv, conj_mu3_entries]

/-- **`μ` normalises `U₁(9)`** (right-coset orientation): diagonal conjugation scales the
off-diagonal entries by the `3`-unit `4^{±1}` and fixes both congruence conditions, so
`U₁(9)·μ·U₁(9) = U₁(9)·μ` is a single right coset [Jacobs, Lemma 2.9's coset content]. -/
theorem mu3_mul_mem_U1_9 {u : Dfx ℚ D} (hu : u ∈ U1_9) : mu3 * u * mu3⁻¹ ∈ U1_9 := by
  have hconj : ∀ v : Dfx ℚ D, v ∈ U1_9 →
      toMatrix ℚ D v₃ (mu3 * v * mu3⁻¹) ∈ Sigma1 ∧
        toMatrix ℚ D v₃ (mu3 * v * mu3⁻¹) ∈ integralMatrices := by
    intro v hv
    obtain ⟨⟨hint, hc, hd, hdet⟩, hd1⟩ := toMatrix_mem_sigma1_of_mem_U1_9 hv
    set M := toMatrix ℚ D v₃ v with hM
    have hentry : ∀ i j : Fin 2,
        Valued.v (toMatrix ℚ D v₃ (mu3 * v * mu3⁻¹) i j) ≤ 1 := by
      intro i j
      rw [toMatrix_conj_mu3]
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue,
          Fin.zero_eta, Fin.mk_one, map_mul, valued_four_eq_one, valued_inv_four_eq_one,
          one_mul, mul_one]
      · exact hint 0 0
      · exact hint 0 1
      · exact hint 1 0
      · exact hint 1 1
    have hc' : Valued.v (toMatrix ℚ D v₃ (mu3 * v * mu3⁻¹) 1 0) ≤ γ₉ := by
      rw [toMatrix_conj_mu3]
      simpa [map_mul, valued_four_eq_one] using hc
    have hd' : Valued.v (toMatrix ℚ D v₃ (mu3 * v * mu3⁻¹) 1 1) = 1 := by
      rw [toMatrix_conj_mu3]
      simpa using hd
    have hd1' : Valued.v (toMatrix ℚ D v₃ (mu3 * v * mu3⁻¹) 1 1 - 1) ≤ γ₉ := by
      rw [toMatrix_conj_mu3]
      simpa using hd1
    have hdet' : (toMatrix ℚ D v₃ (mu3 * v * mu3⁻¹)).det ≠ 0 := by
      rw [map_mul, map_mul, Matrix.det_mul, Matrix.det_mul]
      refine mul_ne_zero (mul_ne_zero ?_ hdet) ?_ <;>
        · rw [Matrix.det_fin_two]
          norm_num
    exact ⟨⟨⟨hentry, hc', hd', hdet'⟩, hd1'⟩,
      fun i j => Valued.toNormedField.norm_le_one_iff.mpr (hentry i j)⟩
  refine mem_U1_9_of_toMatrix (fun w hw => ?_) (hconj u hu).2 ?_ (hconj u hu).1 ?_
  · constructor
    · have h := (hu.1 w).1
      rw [show ((mu3 * u * mu3⁻¹ : Dfx ℚ D) :
          D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
          = (mu3 : Dfx ℚ D) * (u : Dfx ℚ D) * (mu3⁻¹ : Dfx ℚ D) by
        push_cast
        ring, map_mul, map_mul, toLocal_mu3_ne hw, toLocal_mu3_inv_ne hw, one_mul,
        mul_one]
      exact h
    · have h := (hu.1 w).2
      rw [show (((mu3 * u * mu3⁻¹)⁻¹ : Dfx ℚ D) :
          D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
          = (mu3 : Dfx ℚ D) * (u⁻¹ : Dfx ℚ D) * (mu3⁻¹ : Dfx ℚ D) by
        rw [show (mu3 * u * mu3⁻¹)⁻¹ = mu3 * u⁻¹ * mu3⁻¹ by group]
        push_cast
        ring, map_mul, map_mul, toLocal_mu3_ne hw, toLocal_mu3_inv_ne hw, one_mul,
        mul_one]
      exact h
  · rw [show (mu3 * u * mu3⁻¹)⁻¹ = mu3 * u⁻¹ * mu3⁻¹ by group]
    exact (hconj u⁻¹ (U1_9.inv_mem hu)).2
  · rw [show (mu3 * u * mu3⁻¹)⁻¹ = mu3 * u⁻¹ * mu3⁻¹ by group]
    exact (hconj u⁻¹ (U1_9.inv_mem hu)).1

/-- `U₁(9)·μ·U₁(9)` is the single right coset `U₁(9)·μ`: the `Fin 1`-family `_ ↦ μ` is a
bijective system of representatives. -/
theorem bijOn_muRep :
    Set.BijOn (Quotient.mk'' : Dfx ℚ D → RightCosets U1_9)
      (Set.range (fun _ : Fin 1 => mu3))
      (((Quotient.mk'' : Dfx ℚ D → RightCosets U1_9) ''
        (({mu3} : Set (Dfx ℚ D)) * (U1_9 : Set (Dfx ℚ D)))) :
        Set (RightCosets U1_9)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨-, rfl⟩
    exact ⟨mu3, ⟨mu3, rfl, 1, U1_9.one_mem, mul_one mu3⟩, rfl⟩
  · rintro _ ⟨-, rfl⟩ _ ⟨-, rfl⟩ -
    rfl
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨e, he, u, hu, rfl⟩ := hg
    rw [Set.mem_singleton_iff] at he
    subst he
    refine ⟨mu3, ⟨0, rfl⟩, Quotient.eq''.mpr ?_⟩
    rw [QuotientGroup.rightRel_apply]
    exact mu3_mul_mem_U1_9 hu

/-- The finiteness input for `heckeOperatorSlash` at `μ` (a single coset). -/
theorem finite_image_mu3 :
    (((Quotient.mk'' : Dfx ℚ D → RightCosets U1_9) ''
      (({mu3} : Set (Dfx ℚ D)) * (U1_9 : Set (Dfx ℚ D)))) :
      Set (RightCosets U1_9)).Finite := by
  rw [← bijOn_muRep.image_eq]
  exact (Set.finite_range _).image _

/-- `μ` lies in the **wide** acting monoid `Δ₁(3)` — and NOT in the narrow `Δ₁(9)`:
`v(4 − 1) = v(3) = γ₃ > γ₉`.  This rejection is precisely why `Σ₁(3)` exists. -/
theorem mu3_mem_levelMonoid1₃ : mu3 ∈ levelMonoid1₃ := by
  refine Submonoid.mem_comap.mpr ?_
  rw [toMatrix_mu3]
  refine ⟨⟨fun i j => ?_, ?_, ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      simp [valued_four_eq_one]
  · simp
  · simpa using valued_four_eq_one
  · rw [Matrix.det_fin_two]
    norm_num
  · have h : (4 : K₃) - 1 = 3 := by norm_num
    simpa [h] using le_of_eq valued_three_eq_γ₃

/-! ### The three `W`-certificates

Computed by the fork oracle `PhD/Main/JacobsSlash/U3/certificate_search_w.py` (unique hit per
class over 312 candidates): `σ_W = (1,2,0)`, central signs `d_W = (−1,−1,+1)`, and the
`3`-components `u(i) = diag(−1/5,−1/8), diag(−5/7,−1/8), diag(7,1)` — all *rational
diagonal* (no `ν₃`), unlike the `η`-certificates. -/


/-- The certificate factors: central signs `−1, −1, +1`. -/
noncomputable def dTableW : Fin 3 → Dˣ := ![-1, -1, 1]

theorem dTableW_mem (i : Fin 3) : unitsIncl ℚ D (dTableW i) ∈ globalUnits ℚ D :=
  ⟨dTableW i, rfl⟩

/-- The `U₁(9)`-factor, defined by the factorisation equation. -/
noncomputable def uCandW (i : Fin 3) : Dfx ℚ D :=
  (unitsIncl ℚ D (dTableW i) * classRep (sigmaW i))⁻¹ * (classRep i * mu3⁻¹)

theorem factorisationW (i : Fin 3) :
    classRep i * mu3⁻¹
      = unitsIncl ℚ D (dTableW i) * classRep (sigmaW i) * uCandW i := by
  rw [uCandW]
  group

/-- A diagonal matrix with unit entries and `d ≡ 1 mod 9` lies in `Σ₁(9)`. -/
private theorem mem_sigma1_diag {a d : K₃} (ha : ‖a‖ = 1) (hd : ‖d‖ = 1)
    (hd1 : Valued.v (d - 1) ≤ γ₉) :
    Matrix.of ![![a, 0], ![0, d]] ∈ Sigma1 := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hd0 : d ≠ 0 := fun h => by simp [h] at hd
  refine ⟨⟨fun i j => ?_, ?_, ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j <;>
      simp [valued_eq_one_of_norm_eq_one ha, valued_eq_one_of_norm_eq_one hd]
  · simp
  · simpa using valued_eq_one_of_norm_eq_one hd
  · rw [Matrix.det_fin_two]
    simpa using mul_ne_zero ha0 hd0
  · simpa using hd1

/-- A diagonal matrix with integral entries is integral. -/
private theorem mem_integralMatrices_diag {a d : K₃} (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    Matrix.of ![![a, 0], ![0, d]] ∈ integralMatrices := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simp
  · simp
  · simpa using hd

/-- The certificate element factored so that every `toMatrix` is a known one. -/
private theorem uCandW_eq (i : Fin 3) :
    uCandW i = (classRep (sigmaW i))⁻¹ * unitsIncl ℚ D (dTableW i)⁻¹
      * classRep i * mu3⁻¹ := by
  rw [uCandW, mul_inv_rev, map_inv]
  group

private theorem toMatrix_unitsIncl_dTableW_inv (i : Fin 3) :
    toMatrix ℚ D v₃ (unitsIncl ℚ D (dTableW i)⁻¹)
      = (![(-1 : K₃), -1, 1] i) • (1 : Matrix (Fin 2) (Fin 2) K₃) := by
  fin_cases i <;>
    · rw [dTableW]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk]
      rw [toMatrix_unitsIncl]
      refine Matrix.ext fun a b => ?_
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.smul_apply]

/-- The `3`-components of the three certificates: `diag(−1/5,−1/8)`, `diag(−5/7,−1/8)`,
`diag(7,1)` (oracle `certificate_search_w.py`). -/
theorem toMatrix_uCandW (i : Fin 3) :
    toMatrix ℚ D v₃ (uCandW i)
      = Matrix.of ![![![(-1/5 : K₃), -5/7, 7] i, 0], ![0, ![(-1/8 : K₃), -1/8, 1] i]] := by
  rw [uCandW_eq, map_mul, map_mul, map_mul, toMatrix_classRep_inv,
    toMatrix_unitsIncl_dTableW_inv, toMatrix_classRep, toMatrix_mu3_inv]
  fin_cases i <;>
    · refine Matrix.ext fun a b => ?_
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, classDiag, sigmaW] <;>
        norm_num

/-- The `3`-components of the inverse certificates. -/
theorem toMatrix_uCandW_inv (i : Fin 3) :
    toMatrix ℚ D v₃ (uCandW i)⁻¹
      = Matrix.of ![![![(-5 : K₃), -7/5, 1/7] i, 0], ![0, ![(-8 : K₃), -8, 1] i]] := by
  have hmul : toMatrix ℚ D v₃ (uCandW i)⁻¹ * toMatrix ℚ D v₃ (uCandW i) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hmul2 : toMatrix ℚ D v₃ (uCandW i)
      * Matrix.of ![![![(-5 : K₃), -7/5, 1/7] i, 0], ![0, ![(-8 : K₃), -8, 1] i]] = 1 := by
    rw [toMatrix_uCandW]
    fin_cases i <;>
      · refine Matrix.ext fun a b => ?_
        fin_cases a <;> fin_cases b <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  calc toMatrix ℚ D v₃ (uCandW i)⁻¹
      = toMatrix ℚ D v₃ (uCandW i)⁻¹ * (toMatrix ℚ D v₃ (uCandW i)
          * Matrix.of ![![![(-5 : K₃), -7/5, 1/7] i, 0],
              ![0, ![(-8 : K₃), -8, 1] i]]) := by rw [hmul2, mul_one]
    _ = _ := by rw [← mul_assoc, hmul, one_mul]

private theorem toLocal_classRepW_ne (j : Fin 3)
    {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w ((classRep j : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) = 1 := by
  simp [classRep, hw]

private theorem toLocal_classRepW_inv_ne (j : Fin 3)
    {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w (((classRep j)⁻¹ : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) = 1 := by
  simp [classRep, hw]

private theorem dTableW_val_mem (i : Fin 3) : ((dTableW i : Dˣ) : D) ∈ hurwitzOrder := by
  fin_cases i <;>
    · rw [dTableW]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Units.val_neg, Units.val_one]
      first
        | exact hurwitzOrder.neg_mem hurwitzOrder.one_mem
        | exact hurwitzOrder.one_mem

private theorem dTableW_inv_val_mem (i : Fin 3) :
    (((dTableW i)⁻¹ : Dˣ) : D) ∈ hurwitzOrder := by
  fin_cases i <;>
    · rw [dTableW]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, inv_neg, inv_one, Units.val_neg, Units.val_one]
      first
        | exact hurwitzOrder.neg_mem hurwitzOrder.one_mem
        | exact hurwitzOrder.one_mem

/-- Away from `3` the certificates are the central signs, hence integral. -/
private theorem uCandW_away (i : Fin 3) {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((uCandW i : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w ∧
      toLocal ℚ D w (((uCandW i)⁻¹ : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w := by
  have hcoe : ∀ x y z u : Dfx ℚ D,
      ((x * y * z * u : Dfx ℚ D) : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
        = (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) * y * z * u := by
    intro x y z u
    push_cast
    ring
  constructor
  · rw [uCandW_eq, hcoe, map_mul, map_mul, map_mul,
      toLocal_classRepW_inv_ne (sigmaW i) hw, toLocal_classRepW_ne i hw,
      toLocal_mu3_inv_ne hw, one_mul, mul_one, mul_one, toLocal_unitsIncl]
    simpa using tmul_mem_localOrder (dTableW_inv_val_mem i) 1
  · rw [show (uCandW i)⁻¹ = mu3 * (classRep i)⁻¹ * unitsIncl ℚ D (dTableW i)
        * classRep (sigmaW i) by
      simp only [uCandW, mul_inv_rev, inv_inv]
      group, hcoe, map_mul, map_mul, map_mul, toLocal_mu3_ne hw,
      toLocal_classRepW_inv_ne i hw, toLocal_classRepW_ne (sigmaW i) hw,
      one_mul, mul_one, toLocal_unitsIncl]
    simpa using tmul_mem_localOrder (dTableW_val_mem i) 1

theorem uCandW_mem (i : Fin 3) : uCandW i ∈ U1_9 := by
  have h5 : ‖(5 : K₃)‖ = 1 :=
    norm_ofNat_eq_one norm_three_lt_one (n := 5) (by norm_num) (by norm_num)
  have h7 : ‖(7 : K₃)‖ = 1 :=
    norm_ofNat_eq_one norm_three_lt_one (n := 7) (by norm_num) (by norm_num)
  have h8 : ‖(8 : K₃)‖ = 1 :=
    norm_ofNat_eq_one norm_three_lt_one (n := 8) (by norm_num) (by norm_num)
  have h8eight : ‖(8 : K₃)‖ = 1 → Valued.v ((-1/8 : K₃) - 1) ≤ γ₉ := fun h8' => by
    rw [show (-1/8 : K₃) - 1 = 9 * (-1/8) by ring, map_mul, valued_nine_eq,
      valued_eq_one_of_norm_eq_one (by simp [norm_div, norm_neg, h8']), mul_one]
  have hneg8 : Valued.v ((-8 : K₃) - 1) ≤ γ₉ := by
    rw [show (-8 : K₃) - 1 = 9 * (-1) by ring, map_mul, valued_nine_eq,
      valued_eq_one_of_norm_eq_one (by simp), mul_one]
  refine mem_U1_9_of_toMatrix (fun w hw => uCandW_away i hw) ?_ ?_ ?_ ?_
  · rw [toMatrix_uCandW]
    refine mem_integralMatrices_diag ?_ ?_ <;> fin_cases i <;>
      simp [norm_div, norm_neg, h5, h7, h8]
  · rw [toMatrix_uCandW_inv]
    refine mem_integralMatrices_diag ?_ ?_ <;> fin_cases i <;>
      simp [norm_div, norm_neg, h5, h7, h8]
  · rw [toMatrix_uCandW]
    fin_cases i
    · exact mem_sigma1_diag (by simp [norm_div, norm_neg, h5])
        (by simp [norm_div, norm_neg, h8]) (h8eight h8)
    · exact mem_sigma1_diag (by simp [norm_div, norm_neg, h5, h7])
        (by simp [norm_div, norm_neg, h8]) (h8eight h8)
    · exact mem_sigma1_diag (by simp [h7]) (by simp) (by show Valued.v ((1 : K₃) - 1) ≤ γ₉; simp)
  · rw [toMatrix_uCandW_inv]
    fin_cases i
    · exact mem_sigma1_diag (by simp [h5]) (by simp [h8]) hneg8
    · exact mem_sigma1_diag (by simp [norm_div, norm_neg, h5, h7]) (by simp [h8]) hneg8
    · exact mem_sigma1_diag (by simp [h7]) (by simp)
        (by show Valued.v ((1 : K₃) - 1) ≤ γ₉; simp)

/-- The certificate table as `U₁(9)`-elements. -/
noncomputable def uTableW : Fin 3 → U1_9 := fun i => ⟨uCandW i, uCandW_mem i⟩

@[simp] theorem uTableW_coe (i : Fin 3) : ((uTableW i : U1_9) : Dfx ℚ D) = uCandW i := rfl

/-- The acting matrices `θ₃(u(i)·μ) = diag(−1/5,−1/2), diag(−5/7,−1/2), diag(7,4)` — the
thesis's `δ`-data ON THE NOSE (oracle verdict: **twist-free**). -/
theorem toMatrix_uTableW_mul_mu3 (i : Fin 3) :
    toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3)
      = Matrix.of ![![![(-1/5 : K₃), -5/7, 7] i, 0], ![0, ![(-1/2 : K₃), -1/2, 4] i]] := by
  rw [uTableW_coe, map_mul, toMatrix_uCandW, toMatrix_mu3]
  fin_cases i <;>
    · refine Matrix.ext fun a b => ?_
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem toMatrix_uTableW_mul_mu3_mem_sigma1₃ (i : Fin 3) :
    toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3) ∈ Sigma1₃ := by
  rw [map_mul]
  exact Sigma1₃.mul_mem (sigma1_le_sigma1₃ (toMatrix_mem_sigma1_of_mem_U1_9 (uTableW i).2))
    (Submonoid.mem_comap.mp mu3_mem_levelMonoid1₃)

/-! ### The `δ`-identification — twist-free

`weightGenFun` at a diagonal matrix is the geometric diagonal scaled by `κ(d)·d⁻²`, and
at the three certificate acting matrices those data are the thesis's `δ`-operators
**exactly**: the fork carries no `classWeight` coboundary (oracle verdict, mirroring the
`ε`-side of `«5_Factorisations»`). -/

section DeltaIdentification

variable {t : K₃}

/-- `weightGenFun` of a diagonal matrix: the `(m,r)` coefficient is `κ(d)·d⁻²·(a/d)^m`
on the diagonal `m = r`, and `0` off it. -/
theorem coeff_weightGenFun_diagonal (t : K₃) (a d : K₃) (hd : d ≠ 0) (m r : ℕ) :
    MvPowerSeries.coeff (idx m r) (weightGenFun t (Matrix.of ![![a, 0], ![0, d]]))
      = if m = r then unitPow t d * d⁻¹ * d⁻¹ * (a / d) ^ m else 0 := by
  have h11 : (Matrix.of ![![a, 0], ![0, d]] : Matrix (Fin 2) (Fin 2) K₃) 1 1 = d := rfl
  have h10 : (Matrix.of ![![a, 0], ![0, d]] : Matrix (Fin 2) (Fin 2) K₃) 1 0 = 0 := rfl
  have h01 : (Matrix.of ![![a, 0], ![0, d]] : Matrix (Fin 2) (Fin 2) K₃) 0 1 = 0 := rfl
  have h00 : (Matrix.of ![![a, 0], ![0, d]] : Matrix (Fin 2) (Fin 2) K₃) 0 0 = a := rfl
  have hlin : QMF.linX (Matrix.of ![![a, 0], ![0, d]]) = PowerSeries.C d := by
    rw [QMF.linX, h11, h10, map_zero, zero_mul, add_zero]
  have hlininv : (QMF.linX (Matrix.of ![![a, 0], ![0, d]]))⁻¹ = PowerSeries.C d⁻¹ := by
    rw [hlin, PowerSeries.C_inv]
  have hnum : QMF.numX (Matrix.of ![![a, 0], ![0, d]]) = PowerSeries.C a * PowerSeries.X := by
    rw [QMF.numX, h01, h00, map_zero, zero_add]
  have hmob : QMF.mobius (Matrix.of ![![a, 0], ![0, d]])
      = PowerSeries.C (a / d) * PowerSeries.X := by
    rw [QMF.mobius, hnum, hlininv, mul_comm (PowerSeries.C a) PowerSeries.X, mul_assoc,
      ← map_mul, mul_comm a d⁻¹, ← div_eq_inv_mul, mul_comm PowerSeries.X]
  have hcol : (PowerSeries.mk fun n => unitPow t
        ((Matrix.of ![![a, 0], ![0, d]] : Matrix (Fin 2) (Fin 2) K₃) 1 1)
        * (binomialCoeff t n
          * ((Matrix.of ![![a, 0], ![0, d]] : Matrix (Fin 2) (Fin 2) K₃) 1 0
            / (Matrix.of ![![a, 0], ![0, d]] : Matrix (Fin 2) (Fin 2) K₃) 1 1) ^ n))
      = PowerSeries.C (unitPow t d) := by
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_mk, h10, h11, PowerSeries.coeff_C]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne', zero_div, zero_pow hn.ne', mul_zero, mul_zero]
  rw [← QMF.coeff_yCoeff, weightGenFun, kappaSeries₂_eq_yExtend,
    QMF.WeightSeries.yCoeff_yExtend_mul_inv _ (by rw [h11]; exact hd) r, hcol, hlininv, hmob,
    mul_pow, ← map_pow, ← map_pow, ← map_mul, ← mul_assoc, ← map_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases eq_or_ne m r with rfl | hmr
  · rw [if_pos rfl, if_pos rfl, mul_one, sq]; ring
  · rw [if_neg hmr, if_neg hmr, mul_zero]

/-- **The `δ`-identification — TWIST-FREE**: each certificate acting operator IS the
transcribed `δ`, with no coboundary scalar (the fork's counterpart of
`blockEntry_eq_epsOp`). -/
theorem kappaSlash_acting_eq_delta (ht : ‖t‖ < 1) (i : Fin 3) :
    (jacobsWeight t ht).kappaSlash ⟨toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3),
        toMatrix_uTableW_mul_mu3_mem_sigma1₃ i⟩
      = deltaOf norm_three_lt_one ht i := by
  refine TateFredholm.ext_matrixCoeff fun m r => ?_
  rw [matrixCoeff_kappaSlash_jacobsWeight]
  simp only [toMatrix_uTableW_mul_mu3, deltaOf]
  fin_cases i <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, JacobsSlash.delta01, JacobsSlash.delta12, JacobsSlash.delta20,
      TateFredholm.matrixCoeff_smul, TateFredholm.matrixCoeff_diagOp]
  · rw [coeff_weightGenFun_diagonal t (-1/5 : K₃) (-1/2 : K₃) (by norm_num) m r]
    rcases eq_or_ne m r with rfl | hmr
    · rw [if_pos rfl, if_pos rfl, show ((-1/5 : K₃) / (-1/2 : K₃)) = 2/5 by norm_num]
      ring_nf
    · rw [if_neg hmr, if_neg hmr, mul_zero]
  · rw [coeff_weightGenFun_diagonal t (-5/7 : K₃) (-1/2 : K₃) (by norm_num) m r]
    rcases eq_or_ne m r with rfl | hmr
    · rw [if_pos rfl, if_pos rfl, show ((-5/7 : K₃) / (-1/2 : K₃)) = 10/7 by norm_num]
      ring_nf
    · rw [if_neg hmr, if_neg hmr, mul_zero]
  · rw [coeff_weightGenFun_diagonal t (7 : K₃) (4 : K₃) (by norm_num) m r]
    rcases eq_or_ne m r with rfl | hmr
    · rw [if_pos rfl, if_pos rfl]
      ring_nf
    · rw [if_neg hmr, if_neg hmr, mul_zero]

end DeltaIdentification


/-! ### `W = [U₁(9)·μ·U₁(9)]` and its matrix

The wide-monoid counterpart of `«6_Matrix»`: the same `slashFixedPointsOfLE`/
`heckeOperatorSlash` construction at `Δ₁(3)` and `μ`, with the single-coset (`Fin 1`)
instance of the S11 matrix recipe. -/

section HeckeW


/-- **The genuine diamond operator** `W = [U₁(9)·μ·U₁(9)]` on weight-`κ` forms. -/
noncomputable def heckeW (t : K₃) (ht : ‖t‖ < 1) :
    kappaForms t ht →ₗ[K₃] kappaForms t ht :=
  Weight.heckeOperator (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃
    mu3_mem_levelMonoid1₃ finite_image_mu3

theorem uTableW_mul_mu3_mem_levelMonoid1₃ (i : Fin 3) :
    ((uTableW i : Dfx ℚ D) * mu3) ∈ levelMonoid1₃ :=
  Submonoid.mem_comap.mpr (toMatrix_uTableW_mul_mu3_mem_sigma1₃ i)

/-- **AG-W-ID headline (unconditional)**: the diamond operator evaluated at the class
representatives is the single-certificate action
`(Wφ)(cᵢ) = φ(c_{σ(i)}) ∣κ (u(i)·μ)` — the `W`-analogue of `heckeU3_apply_classRep`,
via the S11 recipe at the `Fin 1` coset family. -/
theorem heckeW_apply_classRep (t : K₃) (ht : ‖t‖ < 1) (φ : kappaForms t ht)
    (i : Fin 3) :
    (heckeW t ht φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
        (classRep i)
      = (jacobsWeight t ht).kappaSlash
          ⟨toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3),
            toMatrix_uTableW_mul_mu3_mem_sigma1₃ i⟩
          ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
            (classRep (sigmaW i))) := by
  letI := Weight.kappaLevelSlashActionTwisted (toMatrix ℚ D v₃) (jacobsWeight t ht) 1
  haveI := Weight.kappaLevelSMulSlashClassTwisted (toMatrix ℚ D v₃) (jacobsWeight t ht) 1
  have key := AutomorphicFunction.heckeOperatorSlash_apply_rep (Γ := globalUnits ℚ D)
    K₃ U1_9_subset_levelMonoid1₃ mu3_mem_levelMonoid1₃ finite_image_mu3 φ
    (fun _ : Fin 1 => mu3) (fun _ => mu3_mem_levelMonoid1₃) bijOn_muRep
    (fun _ _ _ => Subsingleton.elim _ _)
    (classRep i) (fun _ => classRep (sigmaW i))
    (fun _ => unitsIncl ℚ D (dTableW i)) (fun _ => dTableW_mem i)
    (fun _ => uTableW i)
    (fun _ => by rw [uTableW_coe]; exact factorisationW i)
    (fun _ => uTableW_mul_mu3_mem_levelMonoid1₃ i)
  refine key.trans ?_
  rw [Finset.univ_unique, Finset.sum_singleton,
    Weight.kappaLevelSlashActionTwisted_slash, MonoidHom.one_apply, one_smul]

/-- **`Wop` is the matrix of the genuine `W`** — twist-free: on the `i`-th
representative, `W` acts by the transcribed `δ`-operator of the block layout of
`JacobsSlash.Wop` [Jacobs, (2.1.10), p. 32]. -/
theorem heckeW_apply_classRep_eq_delta (t : K₃) (ht : ‖t‖ < 1)
    (φ : kappaForms t ht) (i : Fin 3) :
    (heckeW t ht φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
        (classRep i)
      = deltaOf norm_three_lt_one ht i ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
          (classRep (sigmaW i))) := by
  rw [heckeW_apply_classRep, kappaSlash_acting_eq_delta ht i]

end HeckeW

end Diamond

end JacobsSlash
