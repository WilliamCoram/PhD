/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.Padics.RingHoms
import PhD.Jacobs.U3.Level
import PhD.Main.QMF.«04_UpiElement»

/-!
# Theorem 2.1: the class set of `U₁(9)`, and Lemma 2.2: trivial stabilisers

[Jacobs, Theorem 2.1 p. 23]:

> "D_f^× = D^× c₀ U₁(9) ⊔ D^× c₁ U₁(9) ⊔ D^× c₂ U₁(9), where c₀,p = 1 ∀p;
> c₁,p = 1 if p ≠ 3, (5 0; 0 2) if p = 3; c₂,p = 1 if p ≠ 3, (7 0; 0 4) if p = 3."

[Jacobs, Lemma 2.2 p. 24]:  "Γᵢ = {1} for all i = 0, 1, 2."

The proof route is the thesis's own chain [(1.4.5)–(1.4.12) pp. 16–18]: given (1.4.4)
(`HClassNumberOne`), the class set reduces to the orbit space of the 24-unit image
`𝓞_D^× → SL₂(ℤ/9)` acting on the 72 primitive vectors of `(ℤ/9)²`, a finite computation
("an unilluminating calculation shows that O_D^×\G·x consists of three elements").
Every statement below that mentions the class set takes `HClassNumberOne` as an explicit
hypothesis (discharged by `hClassNumberOne`).

## Main definitions

* `Jacobs.U3.classRep`: the three adelic representatives `c₀, c₁, c₂`.
* `Jacobs.U3.redMod9`, `Jacobs.U3.redMat`: reduction of `𝓞₃` and of an integral matrix
  modulo `9`.
* `Jacobs.U3.unitsMod9`: the image of a Hurwitz unit in `GL₂(ℤ/9)`.

## Main results

* `Jacobs.U3.orbits_unitsMod9`: the `𝓞_D^×`-orbits of the primitive vectors of `(ℤ/9)²`
  are exactly three, with representatives `(1,0), (5,0), (7,0)`.
* `Jacobs.U3.classRep_complete`: [Jacobs, Theorem 2.1] — every `g ∈ D_f^×` lies in
  `D^× · cᵢ · U₁(9)` for a unique `i`.
* `Jacobs.U3.exists_classRep_section`: the double-coset section form the
  `AutomorphicFunction` framework consumes.
* `Jacobs.U3.stabilizerAt_classRep`: [Jacobs, Lemma 2.2] — the stabilisers `Γᵢ` are
  trivial.

## Implementation notes

The `set_option maxRecDepth` lines guard kernel `decide` calls over the 24 Hurwitz units
and the 72 primitive vectors; they are load-bearing, and are scoped to the single
declaration that needs them.
-/

open Quaternion IsDedekindDomain NumberField QMF
open scoped TensorProduct

/- See `Setting.lean`: pin the adic `Algebra ℚ K₃` path, the one the `QMF` framework uses. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace Jacobs.U3

/-- The adelic representative `cᵢ` [Jacobs, Thm 2.1]: trivial away from `3`, and the
diagonal matrix `θ₃⁻¹ (dᵢ 0; 0 eᵢ)` at `3`, for `(d,e) = (1,1), (5,2), (7,4)`.
(Constructed through the rigidification and the `v₃`-component splitting of
`PhD.Main.QMF.«04_UpiElement»`; `det = dᵢeᵢ ∈ {1, 10, 28}` is a `3`-adic unit, so this is a unit
of the local order and defines an element of `D_f^×`.) -/
noncomputable def diagUnit (a b : K₃) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Matrix (Fin 2) (Fin 2) K₃)ˣ where
  val := Matrix.of ![![a, 0], ![0, b]]
  inv := Matrix.of ![![a⁻¹, 0], ![0, b⁻¹]]
  val_inv := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb]
  inv_val := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb]

@[simp] theorem diagUnit_val (a b : K₃) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((diagUnit a b ha hb : (Matrix (Fin 2) (Fin 2) K₃)ˣ) : Matrix (Fin 2) (Fin 2) K₃)
      = Matrix.of ![![a, 0], ![0, b]] := rfl

@[simp] theorem diagUnit_inv (a b : K₃) (ha : a ≠ 0) (hb : b ≠ 0) :
    (((diagUnit a b ha hb)⁻¹ : (Matrix (Fin 2) (Fin 2) K₃)ˣ) : Matrix (Fin 2) (Fin 2) K₃)
      = Matrix.of ![![a⁻¹, 0], ![0, b⁻¹]] := rfl

/-- The diagonal entries `(dᵢ, eᵢ) = (1,1), (5,2), (7,4)` of the representatives. -/
def classDiag : Fin 3 → ℤ × ℤ := ![(1, 1), (5, 2), (7, 4)]

theorem classDiag_fst_ne_zero (i : Fin 3) : (((classDiag i).1 : ℤ) : K₃) ≠ 0 := by
  fin_cases i <;> simp [classDiag]

theorem classDiag_snd_ne_zero (i : Fin 3) : (((classDiag i).2 : ℤ) : K₃) ≠ 0 := by
  fin_cases i <;> simp [classDiag]

noncomputable def classRep : Fin 3 → Dfx ℚ D := fun i =>
  unitAt ℚ D v₃ (diagUnit (((classDiag i).1 : ℤ) : K₃) (((classDiag i).2 : ℤ) : K₃)
    (classDiag_fst_ne_zero i) (classDiag_snd_ne_zero i))

/-- The `3`-component matrices of the representatives are the thesis's `(1 0; 0 1)`,
`(5 0; 0 2)`, `(7 0; 0 4)`. -/
theorem toMatrix_classRep (i : Fin 3) :
    toMatrix ℚ D v₃ (classRep i)
      = Matrix.of ![![((![1, 5, 7] : Fin 3 → ℤ) i : K₃), 0],
                    ![0, ((![1, 2, 4] : Fin 3 → ℤ) i : K₃)]] := by
  rw [classRep, toMatrix_unitAt, diagUnit_val]
  fin_cases i <;> rfl

/-- The `3`-component matrix of `cᵢ⁻¹`: the inverse diagonal. -/
theorem toMatrix_classRep_inv (i : Fin 3) :
    toMatrix ℚ D v₃ (classRep i)⁻¹
      = Matrix.of ![![((((classDiag i).1 : ℤ) : K₃))⁻¹, 0],
                    ![0, ((((classDiag i).2 : ℤ) : K₃))⁻¹]] := by
  rw [classRep, unitAt_inv, toMatrix_unitAt, diagUnit_inv]

/-- The entries `1, 5, 7, 2, 4` of the class representatives are `3`-units, so both
`cᵢ` and `cᵢ⁻¹` have integral `3`-component. -/
theorem norm_classDiag_eq_one (i : Fin 3) :
    ‖(((classDiag i).1 : ℤ) : K₃)‖ = 1 ∧ ‖(((classDiag i).2 : ℤ) : K₃)‖ = 1 := by
  have h3 : ‖(3 : K₃)‖ < 1 := norm_three_lt_one
  have h2 : ‖(2 : K₃)‖ = 1 := norm_two_eq_one
  have h4 : ‖(4 : K₃)‖ = 1 :=
    Jacobs.norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have h5 : ‖(5 : K₃)‖ = 1 :=
    Jacobs.norm_ofNat_eq_one h3 (n := 5) (by norm_num) (by norm_num)
  have h7 : ‖(7 : K₃)‖ = 1 :=
    Jacobs.norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  fin_cases i
  · exact ⟨by simp [classDiag], by simp [classDiag]⟩
  · exact ⟨by simpa [classDiag] using h5, by simpa [classDiag] using h2⟩
  · exact ⟨by simpa [classDiag] using h7, by simpa [classDiag] using h4⟩

/-- A diagonal matrix with integral entries is integral. -/
theorem diag_mem_integralMatrices {a b : K₃} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    (Matrix.of ![![a, 0], ![0, b]] : Matrix (Fin 2) (Fin 2) K₃) ∈ integralMatrices := by
  intro p q
  fin_cases p <;> fin_cases q
  · simpa using ha
  · simp
  · simp
  · simpa using hb

theorem classDiag_fst_eq (i : Fin 3) :
    ((classDiag i).1 : ℤ) = (![1, 5, 7] : Fin 3 → ℤ) i := by fin_cases i <;> rfl

theorem classDiag_snd_eq (i : Fin 3) :
    ((classDiag i).2 : ℤ) = (![1, 2, 4] : Fin 3 → ℤ) i := by fin_cases i <;> rfl

/-- Both `cᵢ` and `cᵢ⁻¹` have integral `3`-component: the diagonal entries `1, 5, 7, 2, 4`
are `3`-units, so their inverses are integral too.  This is why conjugation by `cᵢ`
preserves integrality — the step the trivial-stabiliser argument needs. -/
theorem classRep_mem_integralMatrices (i : Fin 3) :
    toMatrix ℚ D v₃ (classRep i) ∈ integralMatrices ∧
      toMatrix ℚ D v₃ (classRep i)⁻¹ ∈ integralMatrices := by
  obtain ⟨hn1, hn2⟩ := norm_classDiag_eq_one i
  refine ⟨?_, ?_⟩
  · rw [toMatrix_classRep, ← classDiag_fst_eq, ← classDiag_snd_eq]
    exact diag_mem_integralMatrices (le_of_eq hn1) (le_of_eq hn2)
  · rw [toMatrix_classRep_inv]
    exact diag_mem_integralMatrices (by rw [norm_inv, hn1, inv_one])
      (by rw [norm_inv, hn2, inv_one])

theorem valued_classDiag_eq_one (i : Fin 3) :
    Valued.v ((((classDiag i).1 : ℤ) : K₃)) = 1 ∧
      Valued.v ((((classDiag i).2 : ℤ) : K₃)) = 1 :=
  ⟨valued_eq_one_of_norm_eq_one (norm_classDiag_eq_one i).1,
    valued_eq_one_of_norm_eq_one (norm_classDiag_eq_one i).2⟩

/-- Conjugating by a diagonal matrix fixes the `(0,0)` entry and scales the `(1,0)` entry
by a unit.  This is why the trivial-stabiliser check never has to see `cᵢ`: both `Σ₁(9)`
conditions are invariant. -/
theorem diag_conj_entries {a b : K₃} (ha : a ≠ 0) (_hb : b ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) K₃) :
    (Matrix.of ![![a, 0], ![0, b]] * M * Matrix.of ![![a⁻¹, 0], ![0, b⁻¹]]) 0 0 = M 0 0 ∧
      (Matrix.of ![![a, 0], ![0, b]] * M * Matrix.of ![![a⁻¹, 0], ![0, b⁻¹]]) 1 0
        = b * M 1 0 * a⁻¹ := by
  constructor <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      field_simp
      ring

/-- Reduction `𝓞₃ →+* ℤ/9`, through the identification `𝓞₃ ≅ ℤ_[3]` of
`PadicInt.adicCompletionIntegersEquiv` (the same one B08's `exists_fin3_approx` uses) and
`PadicInt.toZModPow 2`. -/
noncomputable def redMod9 : v₃.adicCompletionIntegers ℚ →+* ZMod 9 :=
  (PadicInt.toZModPow 2).comp
    ((PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ)
      ⟨3, Nat.prime_three⟩).symm : _ ≃A[ℤ] _).toRingEquiv.toRingHom

/- The ring-hom laws for `redMod9` in the "element plus membership proof" form the matrix
construction below needs.  Routing through `congr 1` rather than letting `Subtype` defeq
do the work is essential: the direct route times out at `whnf`, because
`adicCompletionIntegers` is a `ValuationSubring` whose instances unfold expensively. -/
private theorem redMod9_one' (h : (1 : K₃) ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨1, h⟩ = 1 := by
  rw [← map_one redMod9]; congr 1

private theorem redMod9_zero' (h : (0 : K₃) ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨0, h⟩ = 0 := by
  rw [← map_zero redMod9]; congr 1

private theorem redMod9_add' {x y : K₃} (hx : x ∈ v₃.adicCompletionIntegers ℚ)
    (hy : y ∈ v₃.adicCompletionIntegers ℚ) (hxy : x + y ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨x + y, hxy⟩ = redMod9 ⟨x, hx⟩ + redMod9 ⟨y, hy⟩ := by
  rw [← map_add redMod9]; congr 1

private theorem redMod9_mul' {x y : K₃} (hx : x ∈ v₃.adicCompletionIntegers ℚ)
    (hy : y ∈ v₃.adicCompletionIntegers ℚ) (hxy : x * y ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨x * y, hxy⟩ = redMod9 ⟨x, hx⟩ * redMod9 ⟨y, hy⟩ := by
  rw [← map_mul redMod9]; congr 1

/-- Reduction mod `9` is surjective: `𝓞₃ ↠ ℤ/9`.  (`PadicInt.toZModPow` is surjective —
witness `(z.val : ℤ_[3])` — and the identification `𝓞₃ ≅ ℤ_[3]` is bijective.)  This is the
lifting input for [Jacobs, (1.4.6)] `GL₂(ℤ₃) ↠ GL₂(ℤ/9)`. -/
theorem redMod9_surjective : Function.Surjective redMod9 := by
  have hA : Function.Surjective (PadicInt.toZModPow 2 : ℤ_[3] →+* ZMod (3 ^ 2)) := fun z =>
    ⟨(z.val : ℤ_[3]), by simp [PadicInt.toZModPow]⟩
  have hB : Function.Surjective
      (((PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ)
        ⟨3, Nat.prime_three⟩).symm : _ ≃A[ℤ] _).toRingEquiv.toRingHom) :=
    (PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ)
      ⟨3, Nat.prime_three⟩).symm.surjective
  exact hA.comp hB

/-- **The kernel of reduction is exactly `9·𝓞₃`**, stated as DIVISIBILITY inside the
subtype.  Transporting divisibility (rather than an equation through coercions into `K₃`)
is what makes this provable: the coercion route runs into the fact that `v₃` is a plain
`def`, so `adicCompletion ℚ v₃` and `adicCompletion ℚ (primesEquiv.symm ⟨3,_⟩)` are defeq
but not syntactically equal and no `rw` will fire. -/
theorem redMod9_eq_zero_iff_dvd (x : v₃.adicCompletionIntegers ℚ) :
    redMod9 x = 0 ↔ (9 : v₃.adicCompletionIntegers ℚ) ∣ x := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp
      (by rw [← PadicInt.ker_toZModPow (p := 3) 2]; exact h :
        (PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ)
          ⟨3, Nat.prime_three⟩).symm x ∈ Ideal.span {((3 : ℕ) : ℤ_[3]) ^ 2})
    refine ⟨(PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ)
      ⟨3, Nat.prime_three⟩) z, ?_⟩
    have hc := congrArg (PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ)
      ⟨3, Nat.prime_three⟩) hz
    rw [map_mul, show ((3 : ℕ) : ℤ_[3]) ^ 2 = (9 : ℤ_[3]) by norm_num, map_ofNat] at hc
    have hrt : (PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ) ⟨3, Nat.prime_three⟩)
        ((PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ)
          ⟨3, Nat.prime_three⟩).symm x) = x :=
      ContinuousAlgEquiv.apply_symm_apply _ _
    rw [hrt] at hc
    rw [← hc]
    exact mul_comm _ _
  · rintro ⟨z, rfl⟩
    rw [map_mul]
    have h9 : redMod9 9 = 0 := by rw [map_ofNat]; decide
    rw [h9, zero_mul]

/-- The converse of `redMod9_eq_zero_of_le`: vanishing mod `9` forces valuation `≤ v(9)`.
This is what turns "fixes `e₁` mod `9`" back into the `Σ₁(9)` valuation conditions. -/
theorem valued_le_of_redMod9_eq_zero {y : K₃} (hy : y ∈ v₃.adicCompletionIntegers ℚ)
    (h : redMod9 ⟨y, hy⟩ = 0) : Valued.v y ≤ Valued.v (9 : K₃) := by
  obtain ⟨z, hz⟩ := (redMod9_eq_zero_iff_dvd ⟨y, hy⟩).mp h
  have hyv : y = ((9 : v₃.adicCompletionIntegers ℚ) : K₃)
      * ((z : v₃.adicCompletionIntegers ℚ) : K₃) := by
    have hcast := congrArg (fun w : v₃.adicCompletionIntegers ℚ => (w : K₃)) hz
    simpa using hcast
  have h9c : ((9 : v₃.adicCompletionIntegers ℚ) : K₃) = (9 : K₃) := by norm_cast
  rw [h9c] at hyv
  rw [hyv, map_mul]
  exact le_trans (mul_le_mul' le_rfl z.2) (by rw [mul_one])

/-- Entrywise reduction of an integral matrix mod `9`. -/
noncomputable def redMat : integralMatrices →+* Matrix (Fin 2) (Fin 2) (ZMod 9) where
  toFun M := Matrix.of fun i j => redMod9 ⟨M.1 i j, mem_integralMatrices_iff.mp M.2 i j⟩
  map_one' := by
    refine Matrix.ext fun i j => ?_
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.of_apply, OneMemClass.coe_one, Matrix.one_apply_eq]
      exact redMod9_one' _
    · simp only [Matrix.of_apply, OneMemClass.coe_one, Matrix.one_apply_ne hij]
      exact redMod9_zero' _
  map_zero' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, ZeroMemClass.coe_zero, Matrix.zero_apply]
    exact redMod9_zero' _
  map_add' M N := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Subring.coe_add, Matrix.add_apply]
    exact redMod9_add' _ _ _
  map_mul' M N := by
    refine Matrix.ext fun i j => ?_
    have hM0 := mem_integralMatrices_iff.mp M.2 i 0
    have hM1 := mem_integralMatrices_iff.mp M.2 i 1
    have hN0 := mem_integralMatrices_iff.mp N.2 0 j
    have hN1 := mem_integralMatrices_iff.mp N.2 1 j
    simp only [Matrix.of_apply, Subring.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [redMod9_add' (mul_mem hM0 hN0) (mul_mem hM1 hN1)
        (add_mem (mul_mem hM0 hN0) (mul_mem hM1 hN1)),
      redMod9_mul' hM0 hN0 (mul_mem hM0 hN0),
      redMod9_mul' hM1 hN1 (mul_mem hM1 hN1)]

/-- A Hurwitz quaternion, viewed in the local order at `3`. -/
noncomputable def hurwitzToLocal : hurwitzOrder →+* localOrder v₃ where
  toFun d := ⟨(d : D) ⊗ₜ[ℚ] (1 : K₃), by
    simpa using tmul_mem_localOrder (w := v₃) d.2 1⟩
  map_one' := Subtype.ext (by simp [Algebra.TensorProduct.one_def])
  map_zero' := Subtype.ext (by simp)
  map_add' d e := Subtype.ext (by simp [TensorProduct.add_tmul])
  map_mul' d e := Subtype.ext (by simp [Algebra.TensorProduct.tmul_mul_tmul])

/-- **`M₂(𝓞₃) ↠ M₂(ℤ/9)`** [Jacobs, (1.4.6)]: entrywise lifting.  Together with the
determinant bookkeeping this is what lets a `mod 9` matrix be realised by an element of
the local order. -/
theorem redMat_surjective : Function.Surjective redMat := by
  classical
  intro N
  choose f hf using redMod9_surjective
  refine ⟨⟨Matrix.of fun i j => ((f (N i j) : v₃.adicCompletionIntegers ℚ) : K₃), ?_⟩, ?_⟩
  · intro a b
    exact Valued.toNormedField.norm_le_one_iff.mpr (f (N a b)).2
  · refine Matrix.ext fun i j => ?_
    show redMod9 ⟨((f (N i j) : v₃.adicCompletionIntegers ℚ) : K₃), _⟩ = N i j
    rw [show (⟨((f (N i j) : v₃.adicCompletionIntegers ℚ) : K₃), _⟩ :
        v₃.adicCompletionIntegers ℚ) = f (N i j) from Subtype.ext rfl]
    exact hf (N i j)

/-- `θ₃` as a ring homomorphism from the local order to the integral matrices (B07a). -/
noncomputable def thetaOnOrder : localOrder v₃ →+* integralMatrices :=
  RingHom.codRestrict (theta3.toRingHom.comp (localOrder v₃).subtype) integralMatrices
    fun x => theta_localOrder_subset x.1 x.2

/-- Reduction of the Hurwitz units to `GL₂(ℤ/9)` along `θ₃` and `𝓞₃ → ℤ/9`. -/
noncomputable def unitsMod9 : (hurwitzOrder)ˣ →* GL (Fin 2) (ZMod 9) :=
  Units.map ((redMat.comp (thetaOnOrder.comp hurwitzToLocal)) : _ →+* _).toMonoidHom

/-- Norm-to-valuation comparison (the direction the `ν₃ mod 9` computation needs). -/
theorem valued_le_of_norm_le {x y : K₃} (hy : y ≠ 0) (h : ‖x‖ ≤ ‖y‖) :
    Valued.v x ≤ Valued.v y := by
  have hy0 : Valued.v y ≠ 0 := by
    simpa using (Valuation.ne_zero_iff Valued.v).mpr hy
  have hn : ‖x / y‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hy)]
    exact h
  have hv : Valued.v (x / y) ≤ 1 := Valued.toNormedField.norm_le_one_iff.mp hn
  rwa [map_div₀, div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm hy0))] at hv

/-- Anything of valuation at most `v(9)` reduces to `0` mod `9`. -/
theorem redMod9_eq_zero_of_le {y : K₃} (hy : y ∈ v₃.adicCompletionIntegers ℚ)
    (h : Valued.v y ≤ Valued.v (9 : K₃)) : redMod9 ⟨y, hy⟩ = 0 := by
  have h9 : (9 : K₃) ≠ 0 := by norm_num
  have h90 : Valued.v (9 : K₃) ≠ 0 := by
    simp
  have hz : y / 9 ∈ v₃.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀,
      div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm h90))]
    exact h
  have h9m : (9 : K₃) ∈ v₃.adicCompletionIntegers ℚ := by
    have : ‖(9 : K₃)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (R := K₃) 9
    exact Valued.toNormedField.norm_le_one_iff.mp (by simpa using this)
  have h9e : (⟨(9 : K₃), h9m⟩ : v₃.adicCompletionIntegers ℚ) = 9 :=
    Subtype.ext (by norm_cast)
  rw [show (⟨y, hy⟩ : v₃.adicCompletionIntegers ℚ) = ⟨9, h9m⟩ * ⟨y / 9, hz⟩ from
      Subtype.ext (by show y = (9 : K₃) * (y / 9); field_simp), map_mul, h9e, map_ofNat,
    show (9 : ZMod 9) = 0 from by decide, zero_mul]

/-- **`ν₃ ≡ 4 mod 9`** [Jacobs p. 23]: from `ν₃ ≡ 2695 mod 3¹⁰` and `2695 ≡ 4 mod 9`.
This is what makes the `mod 9` unit images computable. -/
theorem redMod9_ν₃ (h : ν₃ ∈ v₃.adicCompletionIntegers ℚ) : redMod9 ⟨ν₃, h⟩ = 4 := by
  have h9 : (9 : K₃) ≠ 0 := by norm_num
  have hn9 : ‖(9 : K₃)‖ = ‖(3 : K₃)‖ ^ 2 := by
    rw [show (9 : K₃) = 3 * 3 by norm_num, norm_mul, sq]
  have hsub : Valued.v (ν₃ - 2695) ≤ Valued.v (9 : K₃) := by
    refine valued_le_of_norm_le h9 ?_
    rw [hn9]
    refine ν₃_near.trans (pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le ?_)
    norm_num
  have hm : (2695 : K₃) ∈ v₃.adicCompletionIntegers ℚ := by
    have : ‖(2695 : K₃)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (R := K₃) 2695
    exact Valued.toNormedField.norm_le_one_iff.mp (by simpa using this)
  have hd : ν₃ - 2695 ∈ v₃.adicCompletionIntegers ℚ := sub_mem h hm
  have hz := redMod9_eq_zero_of_le hd hsub
  rw [show (⟨ν₃ - 2695, hd⟩ : v₃.adicCompletionIntegers ℚ) = ⟨ν₃, h⟩ - ⟨2695, hm⟩ from
      Subtype.ext (by simp), map_sub, sub_eq_zero] at hz
  have h2695e : (⟨(2695 : K₃), hm⟩ : v₃.adicCompletionIntegers ℚ) = 2695 :=
    Subtype.ext (by norm_cast)
  rw [hz, h2695e, map_ofNat]
  decide

/-- The primitive vectors: pairs with at least one coordinate a unit ([Jacobs,
Prop 1.25]: "G·x = {(x₁, x₂) ∈ X : at least one of x₁, x₂ ∈ (ℤ/pⁿ)^×}"); there are
`72` of them. -/
def primitiveVectors : Finset ((ZMod 9) × (ZMod 9)) :=
  {v | IsUnit v.1 ∨ IsUnit v.2}

theorem card_primitiveVectors : primitiveVectors.card = 72 := by
  decide

/-- Integers reduce mod `9` as expected. -/
theorem redMod9_intCast (n : ℤ) (h : ((n : ℤ) : K₃) ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨(n : K₃), h⟩ = (n : ZMod 9) := by
  rw [show (⟨(n : K₃), h⟩ : v₃.adicCompletionIntegers ℚ)
      = (n : v₃.adicCompletionIntegers ℚ) from Subtype.ext (by norm_cast), map_intCast]

/-- **Half-integers reduce by `× 5`**: `2⁻¹ = 5` in `ℤ/9`.  This is the bridge that turns
the `(A,B,C,E)/2` coordinates of a Hurwitz quaternion into the `mod 9` matrix entries. -/
theorem redMod9_half (A : ℤ) (h : algebraMap ℚ K₃ ((A : ℚ) / 2) ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨algebraMap ℚ K₃ ((A : ℚ) / 2), h⟩ = 5 * (A : ZMod 9) := by
  have h2m : (2 : K₃) ∈ v₃.adicCompletionIntegers ℚ := by
    have : ‖(2 : K₃)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (R := K₃) 2
    exact Valued.toNormedField.norm_le_one_iff.mp (by simpa using this)
  have hAm : ((A : ℤ) : K₃) ∈ v₃.adicCompletionIntegers ℚ := by
    have : ‖((A : ℤ) : K₃)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K₃) A
    exact Valued.toNormedField.norm_le_one_iff.mp this
  have hprod : (2 : K₃) * algebraMap ℚ K₃ ((A : ℚ) / 2) = ((A : ℤ) : K₃) := by
    rw [show (2 : K₃) = algebraMap ℚ K₃ 2 from (map_ofNat _ 2).symm, ← map_mul]
    rw [show (2 : ℚ) * ((A : ℚ) / 2) = ((A : ℤ) : ℚ) by ring]
    exact map_intCast _ A
  have h2e : (⟨(2 : K₃), h2m⟩ : v₃.adicCompletionIntegers ℚ) = 2 :=
    Subtype.ext (by norm_cast)
  have hAm' : (2 : K₃) * algebraMap ℚ K₃ ((A : ℚ) / 2) ∈ v₃.adicCompletionIntegers ℚ := by
    rw [hprod]; exact hAm
  have key : (2 : ZMod 9) * redMod9 ⟨algebraMap ℚ K₃ ((A : ℚ) / 2), h⟩ = (A : ZMod 9) := by
    have hm := redMod9_mul' h2m h hAm'
    rw [h2e, map_ofNat] at hm
    rw [← hm, ← redMod9_intCast A hAm]
    congr 1
    exact Subtype.ext hprod
  have h52 : (5 : ZMod 9) * 2 = 1 := by decide
  calc redMod9 ⟨algebraMap ℚ K₃ ((A : ℚ) / 2), h⟩
      = ((5 : ZMod 9) * 2) * redMod9 ⟨algebraMap ℚ K₃ ((A : ℚ) / 2), h⟩ := by
        rw [h52, one_mul]
    _ = 5 * ((2 : ZMod 9) * redMod9 ⟨algebraMap ℚ K₃ ((A : ℚ) / 2), h⟩) := by rw [mul_assoc]
    _ = 5 * (A : ZMod 9) := by rw [key]

theorem half_mem (A : ℤ) :
    algebraMap ℚ K₃ ((A : ℚ) / 2) ∈ v₃.adicCompletionIntegers ℚ :=
  Valued.toNormedField.norm_le_one_iff.mp (norm_algebraMap_half_le_one A)

theorem ν₃_mem : ν₃ ∈ v₃.adicCompletionIntegers ℚ :=
  Valued.toNormedField.norm_le_one_iff.mp (le_of_eq norm_ν₃)

theorem redMod9_congr {x y : K₃} (hx : x ∈ v₃.adicCompletionIntegers ℚ)
    (hy : y ∈ v₃.adicCompletionIntegers ℚ) (h : x = y) :
    redMod9 ⟨x, hx⟩ = redMod9 ⟨y, hy⟩ := by
  congr 1
  exact Subtype.ext h

/-- The entries of `unitsMod9 u` are the `mod 9` reductions of the entries of
`θ₃(u ⊗ 1)`. -/
theorem unitsMod9_entry (u : (hurwitzOrder)ˣ) (i j : Fin 2)
    (h : theta3 ((((u : hurwitzOrder) : D)) ⊗ₜ[ℚ] (1 : K₃)) i j
      ∈ v₃.adicCompletionIntegers ℚ) :
    (unitsMod9 u).1 i j
      = redMod9 ⟨theta3 ((((u : hurwitzOrder) : D)) ⊗ₜ[ℚ] (1 : K₃)) i j, h⟩ := rfl

/-- The `mod 9` value of an entry of `θ₃` on a Hurwitz quaternion: a `ℤ`-combination of
`1` and `ν₃` with halved coefficients reduces by `A/2 ↦ 5A` and `ν₃ ↦ 4`. -/
theorem redMod9_entry (A B : ℤ) (h : algebraMap ℚ K₃ ((A : ℚ) / 2)
      + algebraMap ℚ K₃ ((B : ℚ) / 2) * ν₃ ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨algebraMap ℚ K₃ ((A : ℚ) / 2) + algebraMap ℚ K₃ ((B : ℚ) / 2) * ν₃, h⟩
      = 5 * (A : ZMod 9) + 5 * (B : ZMod 9) * 4 := by
  rw [redMod9_add' (half_mem A) (mul_mem (half_mem B) ν₃_mem) h,
    redMod9_mul' (half_mem B) ν₃_mem (mul_mem (half_mem B) ν₃_mem),
    redMod9_half A (half_mem A), redMod9_half B (half_mem B), redMod9_ν₃ ν₃_mem]

/-- **The `mod 9` matrix of a Hurwitz unit**, in terms of its halved coordinates
`(A,B,C,E)`: each entry is a `ℤ`-combination of `1` and `ν₃` over `2`, so it reduces by
`A/2 ↦ 5A` and `ν₃ ↦ 4`.  This is the table [Jacobs, p. 23] recomputes for the orbit
count — derived here rather than transcribed. -/
theorem unitsMod9_apply (u : (hurwitzOrder)ˣ) {A B C E : ℤ}
    (ht : ofTuple (A, B, C, E) = ((u : hurwitzOrder) : ℍ[ℚ])) :
    (unitsMod9 u).1 = Matrix.of
      ![![5 * ((A + E : ℤ) : ZMod 9) + 5 * ((B : ℤ) : ZMod 9) * 4,
          5 * ((B - C : ℤ) : ZMod 9) + 5 * ((-E : ℤ) : ZMod 9) * 4],
        ![5 * ((B + C : ℤ) : ZMod 9) + 5 * ((-E : ℤ) : ZMod 9) * 4,
          5 * ((A - E : ℤ) : ZMod 9) + 5 * ((-B : ℤ) : ZMod 9) * 4]] := by
  have hloc : (((u : hurwitzOrder) : D)) ⊗ₜ[ℚ] (1 : K₃) ∈ localOrder v₃ := by
    simpa using tmul_mem_localOrder (w := v₃) (u : hurwitzOrder).2 1
  have hint := mem_integralMatrices_iff.mp (theta_localOrder_subset _ hloc)
  have hre : ((u : hurwitzOrder) : ℍ[ℚ]).re = (A : ℚ) / 2 := by rw [← ht]; rfl
  have himI : ((u : hurwitzOrder) : ℍ[ℚ]).imI = (B : ℚ) / 2 := by rw [← ht]; rfl
  have himJ : ((u : hurwitzOrder) : ℍ[ℚ]).imJ = (C : ℚ) / 2 := by rw [← ht]; rfl
  have himK : ((u : hurwitzOrder) : ℍ[ℚ]).imK = (E : ℚ) / 2 := by rw [← ht]; rfl
  have hθ : theta3 ((((u : hurwitzOrder) : D)) ⊗ₜ[ℚ] (1 : K₃)) = Matrix.of
      ![![algebraMap ℚ K₃ (((A + E : ℤ) : ℚ) / 2) + algebraMap ℚ K₃ ((B : ℚ) / 2) * ν₃,
          algebraMap ℚ K₃ (((B - C : ℤ) : ℚ) / 2)
            + algebraMap ℚ K₃ (((-E : ℤ) : ℚ) / 2) * ν₃],
        ![algebraMap ℚ K₃ (((B + C : ℤ) : ℚ) / 2)
            + algebraMap ℚ K₃ (((-E : ℤ) : ℚ) / 2) * ν₃,
          algebraMap ℚ K₃ (((A - E : ℤ) : ℚ) / 2)
            + algebraMap ℚ K₃ (((-B : ℤ) : ℚ) / 2) * ν₃]] := by
    rw [show theta3 ((((u : hurwitzOrder) : D)) ⊗ₜ[ℚ] (1 : K₃))
        = theta ν₃ sq_ν₃ ((((u : hurwitzOrder) : D)) ⊗ₜ[ℚ] (1 : K₃)) from rfl,
      theta_tmul_one]
    refine Matrix.ext fun i j => ?_
    have e1 : (((A + E : ℤ) : ℚ) / 2) = (A : ℚ) / 2 + (E : ℚ) / 2 := by push_cast; ring
    have e2 : (((B - C : ℤ) : ℚ) / 2) = (B : ℚ) / 2 - (C : ℚ) / 2 := by push_cast; ring
    have e3 : (((B + C : ℤ) : ℚ) / 2) = (B : ℚ) / 2 + (C : ℚ) / 2 := by push_cast; ring
    have e4 : (((A - E : ℤ) : ℚ) / 2) = (A : ℚ) / 2 - (E : ℚ) / 2 := by push_cast; ring
    have e5 : (((-E : ℤ) : ℚ) / 2) = -((E : ℚ) / 2) := by push_cast; ring
    have e6 : (((-B : ℤ) : ℚ) / 2) = -((B : ℚ) / 2) := by push_cast; ring
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one, hre, himI, himJ, himK,
        e1, e2, e3, e4, e5, e6, map_add, map_sub, map_neg] <;>
      ring_nf
  refine Matrix.ext fun i j => ?_
  rw [unitsMod9_entry u i j (hint i j)]
  fin_cases i <;> fin_cases j
  · rw [redMod9_congr _ (add_mem (half_mem (A + E)) (mul_mem (half_mem B) ν₃_mem))
      (by rw [hθ]; simp), redMod9_entry]
    simp
  · rw [redMod9_congr _ (add_mem (half_mem (B - C)) (mul_mem (half_mem (-E)) ν₃_mem))
      (by rw [hθ]; simp), redMod9_entry]
    simp
  · rw [redMod9_congr _ (add_mem (half_mem (B + C)) (mul_mem (half_mem (-E)) ν₃_mem))
      (by rw [hθ]; simp), redMod9_entry]
    simp
  · rw [redMod9_congr _ (add_mem (half_mem (A - E)) (mul_mem (half_mem (-B)) ν₃_mem))
      (by rw [hθ]; simp), redMod9_entry]
    simp

/-- The explicit `mod 9` matrix attached to a unit tuple (the right-hand side of
`unitsMod9_apply`). -/
def tupleMat (t : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (ZMod 9) :=
  Matrix.of
    ![![5 * ((t.1 + t.2.2.2 : ℤ) : ZMod 9) + 5 * ((t.2.1 : ℤ) : ZMod 9) * 4,
        5 * ((t.2.1 - t.2.2.1 : ℤ) : ZMod 9) + 5 * ((-t.2.2.2 : ℤ) : ZMod 9) * 4],
      ![5 * ((t.2.1 + t.2.2.1 : ℤ) : ZMod 9) + 5 * ((-t.2.2.2 : ℤ) : ZMod 9) * 4,
        5 * ((t.1 - t.2.2.2 : ℤ) : ZMod 9) + 5 * ((-t.2.1 : ℤ) : ZMod 9) * 4]]

/-- **The `mod 9` image of the unit group is exactly `tupleMat '' unitTuples`.**  This is
what turns the orbit computation into a finite check. -/
theorem exists_unit_iff_exists_tuple (P : Matrix (Fin 2) (Fin 2) (ZMod 9) → Prop) :
    (∃ u : (hurwitzOrder)ˣ, P (unitsMod9 u).1) ↔ ∃ t ∈ unitTuples, P (tupleMat t) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨t, ht, hx⟩ := exists_tuple_of_unit u
    obtain ⟨A, B, C, E⟩ := t
    refine ⟨(A, B, C, E), ht, ?_⟩
    simp only [tupleMat]
    rwa [← unitsMod9_apply u hx]
  · rintro ⟨t, ht, hP⟩
    obtain ⟨u, hu⟩ := exists_unit_of_tuple ht
    obtain ⟨A, B, C, E⟩ := t
    refine ⟨u, ?_⟩
    simp only [tupleMat] at hP
    rw [unitsMod9_apply u hu.symm]
    exact hP

set_option maxRecDepth 200000 in
/-- The converse scalar criterion: a primitive column completes to a unimodular matrix. -/
theorem exists_completion :
    ∀ x y : ZMod 9, (IsUnit x ∨ IsUnit y) → ∃ b d : ZMod 9, IsUnit (x * d - b * y) := by
  decide

/-- **[Jacobs, Prop 1.25]**, second half: every primitive vector is `M · e₁` for some
invertible `M`.  With the first half this says `GL₂(ℤ/9)` acts transitively on the
primitive vectors — the input to the orbit count. -/
theorem exists_matrix_mulVec_e1 {v : (ZMod 9) × (ZMod 9)} (hv : v ∈ primitiveVectors) :
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod 9), IsUnit M.det ∧
      ((M.mulVec ![1, 0]) 0, (M.mulVec ![1, 0]) 1) = v := by
  simp only [primitiveVectors, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨b, d, hbd⟩ := exists_completion v.1 v.2 hv
  refine ⟨Matrix.of ![![v.1, b], ![v.2, d]], ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simpa using hbd
  · refine Prod.ext ?_ ?_ <;>
      simp [Matrix.mulVec, Matrix.vecHead]

set_option maxRecDepth 100000 in
/-- The scalar form of [Jacobs, Prop 1.25]: in `ℤ/9` (a local ring with maximal ideal
`(3)`), if the first column of a `2×2` matrix consists of non-units then so does the
determinant. -/
theorem not_isUnit_det_of_not_isUnit_col :
    ∀ a b c d : ZMod 9, ¬IsUnit a → ¬IsUnit c → ¬IsUnit (a * d - b * c) := by
  decide

/-- **[Jacobs, Prop 1.25]**, first half: an invertible matrix carries `e₁` to a primitive
vector.  (Otherwise both entries of the first column would be non-units, forcing the
determinant to be one too.) -/
theorem mulVec_e1_mem_primitiveVectors {M : Matrix (Fin 2) (Fin 2) (ZMod 9)}
    (hM : IsUnit M.det) :
    ((M.mulVec ![1, 0]) 0, (M.mulVec ![1, 0]) 1) ∈ primitiveVectors := by
  have h0 : (M.mulVec ![1, 0]) 0 = M 0 0 := by
    simp [Matrix.mulVec, Matrix.vecHead]
  have h1 : (M.mulVec ![1, 0]) 1 = M 1 0 := by
    simp [Matrix.mulVec, Matrix.vecHead]
  simp only [primitiveVectors, Finset.mem_filter, Finset.mem_univ, true_and, h0, h1]
  by_contra hc
  push Not at hc
  rw [Matrix.det_fin_two] at hM
  exact not_isUnit_det_of_not_isUnit_col _ _ _ _ hc.1 hc.2 hM

set_option maxRecDepth 100000 in
/-- **The orbit computation, finite form** [Jacobs, Thm 2.1 proof, p. 24: "an
unilluminating calculation shows that the orbit space consists of three elements"].
Kernel `decide` over the `24 × 72 × 3` table — no `native_decide`.  `ExistsUnique` is
spelled out because its `Decidable` instance is not found through the `∃!` binder. -/
theorem orbits_tupleMat :
    ∀ x ∈ primitiveVectors, ∃ i : Fin 3,
      (∃ t ∈ unitTuples,
        (tupleMat t).mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0] = ![x.1, x.2]) ∧
      ∀ j : Fin 3, (∃ t ∈ unitTuples,
        (tupleMat t).mulVec ![((![1, 5, 7] : Fin 3 → ℤ) j : ZMod 9), 0] = ![x.1, x.2]) →
        j = i := by
  decide

/-- **The orbit computation** [Jacobs, Thm 2.1 proof, p. 24]: the `𝓞_D^×`-orbits of the
primitive vectors are exactly three, with representatives `(1,0), (5,0), (7,0)`.
Stated as a partition into three explicit orbits. -/
theorem orbits_unitsMod9 :
    ∀ x ∈ primitiveVectors, ∃! i : Fin 3,
      ∃ u : (hurwitzOrder)ˣ,
        (unitsMod9 u).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0] = ![x.1, x.2] := by
  intro x hx
  obtain ⟨i, hi, huniq⟩ := orbits_tupleMat x hx
  refine ⟨i, (exists_unit_iff_exists_tuple
    (fun M => M.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0] = ![x.1, x.2])).mpr hi,
    fun j hj => huniq j ?_⟩
  exact (exists_unit_iff_exists_tuple
    (fun M => M.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) j : ZMod 9), 0] = ![x.1, x.2])).mp hj

/-- The `Σ₁(9)` conditions, read mod `9`: the `(0,0)` entry reduces to `1` and the `(1,0)`
entry to `0`.  (Both are `valuation ≤ γ₉ = v(9)` statements, and `redMod9_eq_zero_of_le`
turns those into vanishing reductions.) -/
theorem redMod9_of_mem_sigma1 {M : Matrix (Fin 2) (Fin 2) K₃} (hM : M ∈ Sigma1)
    (h00 : M 0 0 ∈ v₃.adicCompletionIntegers ℚ) (h10 : M 1 0 ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨M 0 0, h00⟩ = 1 ∧ redMod9 ⟨M 1 0, h10⟩ = 0 := by
  obtain ⟨⟨-, hc, -, -⟩, ha1⟩ := hM
  have h1m : (1 : K₃) ∈ v₃.adicCompletionIntegers ℚ := one_mem _
  refine ⟨?_, redMod9_eq_zero_of_le h10 (hc.trans (le_of_eq valued_nine_eq.symm))⟩
  have hsub : M 0 0 - 1 ∈ v₃.adicCompletionIntegers ℚ := sub_mem h00 h1m
  have hz := redMod9_eq_zero_of_le hsub (ha1.trans (le_of_eq valued_nine_eq.symm))
  rw [show (⟨M 0 0 - 1, hsub⟩ : v₃.adicCompletionIntegers ℚ) = ⟨M 0 0, h00⟩ - ⟨1, h1m⟩ from
      Subtype.ext (by simp), map_sub, sub_eq_zero] at hz
  rw [hz, show (⟨(1 : K₃), h1m⟩ : v₃.adicCompletionIntegers ℚ) = 1 from Subtype.ext (by simp),
    map_one]

/-- **`U₁(9)` lands in the stabiliser of `e₁` mod `9`**: the `Σ₁(9)` conditions say
exactly that the first column reduces to `(1, 0)`, i.e. that the reduced matrix fixes `e₁`.
This is the step of the [Jacobs, (1.4.5)–(1.4.10)] chain that identifies `U₁(9)` inside
`U₀(1)` as a point stabiliser, and hence the `U₀/U₁(9)` cosets with primitive vectors. -/
theorem redMat_mulVec_e1_of_mem_sigma1 {M : Matrix (Fin 2) (Fin 2) K₃} (hM : M ∈ Sigma1)
    (hint : M ∈ integralMatrices) :
    (((redMat ⟨M, hint⟩).mulVec ![1, 0]) 0, ((redMat ⟨M, hint⟩).mulVec ![1, 0]) 1)
      = ((1 : ZMod 9), (0 : ZMod 9)) := by
  obtain ⟨h00, h10⟩ := redMod9_of_mem_sigma1 hM (mem_integralMatrices_iff.mp hint 0 0)
    (mem_integralMatrices_iff.mp hint 1 0)
  have e0 : (redMat ⟨M, hint⟩) 0 0 = redMod9 ⟨M 0 0, mem_integralMatrices_iff.mp hint 0 0⟩ :=
    rfl
  have e1 : (redMat ⟨M, hint⟩) 1 0 = redMod9 ⟨M 1 0, mem_integralMatrices_iff.mp hint 1 0⟩ :=
    rfl
  have hv : ∀ (N : Matrix (Fin 2) (Fin 2) (ZMod 9)) (a : Fin 2),
      (N.mulVec ![1, 0]) a = N a 0 := by
    intro N a
    simp [Matrix.mulVec, Matrix.vecHead]
  rw [hv, hv]
  exact Prod.ext (e0 ▸ h00) (e1 ▸ h10)

/-- **The class representatives hit the three orbit representatives.**  The `3`-component
of `cᵢ` is `diag(dᵢ, eᵢ)`, so mod `9` it carries `e₁` to `(dᵢ, 0)` — and `(d₀,d₁,d₂) =
(1,5,7)` are exactly the orbit representatives of `orbits_unitsMod9`.  This is the link
between `classRep` and the orbit count. -/
theorem redMat_classRep_mulVec_e1 (i : Fin 3) :
    ((((redMat ⟨toMatrix ℚ D v₃ (classRep i),
        (classRep_mem_integralMatrices i).1⟩).mulVec ![1, 0]) 0),
      (((redMat ⟨toMatrix ℚ D v₃ (classRep i),
        (classRep_mem_integralMatrices i).1⟩).mulVec ![1, 0]) 1))
      = (((((![1, 5, 7] : Fin 3 → ℤ) i : ℤ)) : ZMod 9), (0 : ZMod 9)) := by
  have hv : ∀ (N : Matrix (Fin 2) (Fin 2) (ZMod 9)) (a : Fin 2),
      (N.mulVec ![1, 0]) a = N a 0 := by
    intro N a
    simp [Matrix.mulVec, Matrix.vecHead]
  have hM := toMatrix_classRep i
  rw [hv, hv]
  have hmem : ((((![1, 5, 7] : Fin 3 → ℤ) i : ℤ)) : K₃) ∈ v₃.adicCompletionIntegers ℚ := by
    have hn : ‖((((![1, 5, 7] : Fin 3 → ℤ) i : ℤ)) : K₃)‖ = 1 :=
      (classDiag_fst_eq i) ▸ (norm_classDiag_eq_one i).1
    exact Valued.toNormedField.norm_le_one_iff.mp (le_of_eq hn)
  have hval0 : toMatrix ℚ D v₃ (classRep i) 0 0
      = ((((![1, 5, 7] : Fin 3 → ℤ) i : ℤ)) : K₃) := by rw [hM]; rfl
  have hval1 : toMatrix ℚ D v₃ (classRep i) 1 0 = (0 : K₃) := by rw [hM]; rfl
  refine Prod.ext ?_ ?_
  · show redMod9 ⟨toMatrix ℚ D v₃ (classRep i) 0 0, _⟩ = _
    rw [redMod9_congr _ hmem hval0]
    exact redMod9_intCast _ hmem
  · show redMod9 ⟨toMatrix ℚ D v₃ (classRep i) 1 0, _⟩ = _
    rw [redMod9_congr _ (zero_mem _) hval1]
    exact redMod9_zero' _

/-- **Converse of `redMat_mulVec_e1_of_mem_sigma1`**: if an integral matrix fixes `e₁`
mod `9`, its `(0,0)` and `(1,0)` entries satisfy the `Σ₁(9)` valuation conditions.  This is
the direction that turns the orbit bookkeeping back into `U₁(9)` membership. -/
theorem valued_sigma1_of_redMod9 {M : Matrix (Fin 2) (Fin 2) K₃} (hint : M ∈ integralMatrices)
    (h00 : redMod9 ⟨M 0 0, mem_integralMatrices_iff.mp hint 0 0⟩ = 1)
    (h10 : redMod9 ⟨M 1 0, mem_integralMatrices_iff.mp hint 1 0⟩ = 0) :
    Valued.v (M 0 0 - 1) ≤ γ₉ ∧ Valued.v (M 1 0) ≤ γ₉ := by
  have h1m : (1 : K₃) ∈ v₃.adicCompletionIntegers ℚ := one_mem _
  refine ⟨?_, ?_⟩
  · have hsub : M 0 0 - 1 ∈ v₃.adicCompletionIntegers ℚ :=
      sub_mem (mem_integralMatrices_iff.mp hint 0 0) h1m
    have hz : redMod9 ⟨M 0 0 - 1, hsub⟩ = 0 := by
      rw [show (⟨M 0 0 - 1, hsub⟩ : v₃.adicCompletionIntegers ℚ)
          = ⟨M 0 0, mem_integralMatrices_iff.mp hint 0 0⟩ - ⟨1, h1m⟩ from
            Subtype.ext (by simp),
        map_sub, h00,
        show (⟨(1 : K₃), h1m⟩ : v₃.adicCompletionIntegers ℚ) = 1 from Subtype.ext (by simp),
        map_one, sub_self]
    exact (valued_le_of_redMod9_eq_zero hsub hz).trans (le_of_eq valued_nine_eq)
  · exact (valued_le_of_redMod9_eq_zero _ h10).trans (le_of_eq valued_nine_eq)

/-- A `U₀(1)` element has integral `3`-component matrix, and so does its inverse.  (B07a
again: `θ₃` carries the local order into the integral matrices.) -/
theorem U0_toMatrix_mem_integralMatrices {u : Dfx ℚ D} (hu : u ∈ U0) :
    toMatrix ℚ D v₃ u ∈ integralMatrices ∧
      toMatrix ℚ D v₃ u⁻¹ ∈ integralMatrices := by
  have key : ∀ g : Dfx ℚ D,
      toLocal ℚ D v₃ (g : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder v₃ →
      toMatrix ℚ D v₃ g ∈ integralMatrices := by
    intro g hg
    have h2 := theta_localOrder_subset _ hg
    have h3 : toMatrix ℚ D v₃ g
        = theta3 ((toLocal ℚ D v₃) (g : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)) := rfl
    rw [h3]
    exact h2
  exact ⟨key u (hu v₃).1, key u⁻¹ (hu v₃).2⟩

/-- The mod-`9` image of a `U₀(1)` element is invertible: it has an integral inverse, so
its determinant is a unit.  This is what puts it in `GL₂(ℤ/9)`, where the orbit count
applies. -/
theorem isUnit_det_redMat_of_mem_U0 {u : Dfx ℚ D} (hu : u ∈ U0) :
    IsUnit (redMat ⟨toMatrix ℚ D v₃ u, (U0_toMatrix_mem_integralMatrices hu).1⟩).det := by
  have hmul : (redMat ⟨toMatrix ℚ D v₃ u, (U0_toMatrix_mem_integralMatrices hu).1⟩)
      * (redMat ⟨toMatrix ℚ D v₃ u⁻¹, (U0_toMatrix_mem_integralMatrices hu).2⟩) = 1 := by
    rw [← map_mul]
    have h1 : (⟨toMatrix ℚ D v₃ u, (U0_toMatrix_mem_integralMatrices hu).1⟩ :
          integralMatrices)
        * ⟨toMatrix ℚ D v₃ u⁻¹, (U0_toMatrix_mem_integralMatrices hu).2⟩ = 1 :=
      Subtype.ext (by rw [Subring.coe_mul, ← map_mul, mul_inv_cancel, map_one]; rfl)
    rw [h1, map_one]
  have hmul' : (redMat ⟨toMatrix ℚ D v₃ u⁻¹, (U0_toMatrix_mem_integralMatrices hu).2⟩)
      * (redMat ⟨toMatrix ℚ D v₃ u, (U0_toMatrix_mem_integralMatrices hu).1⟩) = 1 := by
    rw [← map_mul]
    have h2 : (⟨toMatrix ℚ D v₃ u⁻¹, (U0_toMatrix_mem_integralMatrices hu).2⟩ :
          integralMatrices)
        * ⟨toMatrix ℚ D v₃ u, (U0_toMatrix_mem_integralMatrices hu).1⟩ = 1 :=
      Subtype.ext (by rw [Subring.coe_mul, ← map_mul, inv_mul_cancel, map_one]; rfl)
    rw [h2, map_one]
  have hU : IsUnit (redMat ⟨toMatrix ℚ D v₃ u,
      (U0_toMatrix_mem_integralMatrices hu).1⟩) := ⟨⟨_, _, hmul, hmul'⟩, rfl⟩
  exact (Matrix.isUnit_iff_isUnit_det _).mp hU

/-- Hence a `U₀(1)` element carries `e₁` to a primitive vector mod `9` — the point at
which [Jacobs, Prop 1.25] and the orbit count take over. -/
theorem U0_mulVec_e1_mem_primitiveVectors {u : Dfx ℚ D} (hu : u ∈ U0) :
    ((((redMat ⟨toMatrix ℚ D v₃ u,
        (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0]) 0),
      (((redMat ⟨toMatrix ℚ D v₃ u,
        (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0]) 1))
      ∈ primitiveVectors :=
  mulVec_e1_mem_primitiveVectors (isUnit_det_redMat_of_mem_U0 hu)

/-- The orbit equation of `orbits_unitsMod9`, repackaged as an identity of vectors (its
statement lists the two coordinates separately). -/
theorem orbit_eq_mulVec {u : Dfx ℚ D} (hu : u ∈ U0) (i : Fin 3) (γ : (hurwitzOrder)ˣ)
    (horb : (unitsMod9 γ).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0]
      = ![(((redMat ⟨toMatrix ℚ D v₃ u,
              (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0]) 0),
          (((redMat ⟨toMatrix ℚ D v₃ u,
              (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0]) 1)]) :
    (unitsMod9 γ).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0]
      = (redMat ⟨toMatrix ℚ D v₃ u,
          (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0] := by
  rw [horb]
  refine funext fun k => ?_
  fin_cases k <;> simp

/-- If `N` and `M` agree on `e₁` and `N` is invertible, then `N⁻¹M` fixes `e₁`.  This is
the algebraic step that turns the orbit equation into the `Σ₁(9)` hypothesis. -/
theorem mulVec_e1_of_mul_eq {N M Ninv : Matrix (Fin 2) (Fin 2) (ZMod 9)}
    (hiN : Ninv * N = 1) (h : N.mulVec ![1, 0] = M.mulVec ![1, 0]) :
    (Ninv * M).mulVec ![1, 0] = ![1, 0] := by
  rw [← Matrix.mulVec_mulVec, ← h, Matrix.mulVec_mulVec, hiN, Matrix.one_mulVec]

/-- A `1`-unit is a unit: `v(a − 1) ≤ γ₉ < 1` forces `v(a) = 1`. -/
theorem valued_eq_one_of_sub_one_le {a : K₃} (h : Valued.v (a - 1) ≤ γ₉) :
    Valued.v a = 1 := by
  have hlt : Valued.v (a - 1) < Valued.v (1 : K₃) := by
    rw [map_one]
    exact lt_of_le_of_lt h γ₉_lt_one
  have := Valuation.map_add_eq_of_lt_left Valued.v hlt
  rw [map_one] at this
  simpa using this

/-- **`U₁(9)` membership from the mod-`9` conditions**: for `g ∈ U₀(1)` whose reduced
matrix and reduced inverse both fix `e₁`, all the `Σ₁(9)` conditions follow.  This is the
form in which the orbit argument concludes. -/
theorem mem_U1_9_of_redMod9 {g : Dfx ℚ D} (hg : g ∈ U0)
    (h00 : redMod9 ⟨toMatrix ℚ D v₃ g 0 0,
      mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hg).1 0 0⟩ = 1)
    (h10 : redMod9 ⟨toMatrix ℚ D v₃ g 1 0,
      mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hg).1 1 0⟩ = 0)
    (h00' : redMod9 ⟨toMatrix ℚ D v₃ g⁻¹ 0 0,
      mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hg).2 0 0⟩ = 1)
    (h10' : redMod9 ⟨toMatrix ℚ D v₃ g⁻¹ 1 0,
      mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hg).2 1 0⟩ = 0) :
    g ∈ U1_9 := by
  obtain ⟨ha1, hc⟩ :=
    valued_sigma1_of_redMod9 (U0_toMatrix_mem_integralMatrices hg).1 h00 h10
  obtain ⟨ha1', hc'⟩ :=
    valued_sigma1_of_redMod9 (U0_toMatrix_mem_integralMatrices hg).2 h00' h10'
  have hdet : ∀ M N : Matrix (Fin 2) (Fin 2) K₃, M * N = 1 → M.det ≠ 0 := by
    intro M N h hd
    have hc2 := congrArg Matrix.det h
    rw [Matrix.det_mul, hd, zero_mul, Matrix.det_one] at hc2
    exact zero_ne_one hc2
  refine ⟨hg, ⟨⟨fun i j => ?_, hc, valued_eq_one_of_sub_one_le ha1, ?_⟩, ha1⟩,
    ⟨⟨fun i j => ?_, hc', valued_eq_one_of_sub_one_le ha1', ?_⟩, ha1'⟩⟩
  · exact mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hg).1 i j
  · exact hdet _ _ (by rw [← map_mul, mul_inv_cancel, map_one])
  · exact mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hg).2 i j
  · exact hdet _ _ (by rw [← map_mul, inv_mul_cancel, map_one])

/-- The mod-`9` matrix of a global unit's adelic image is its `unitsMod9` image.  This is
the bridge between the adelic bookkeeping and the finite orbit table. -/
theorem redMat_unitsIncl_eq_unitsMod9 (γ : (hurwitzOrder)ˣ) (x : Dˣ)
    (hx : ((x : D)) = ((γ : hurwitzOrder) : ℍ[ℚ])) (hU : unitsIncl ℚ D x ∈ U0) :
    redMat ⟨toMatrix ℚ D v₃ (unitsIncl ℚ D x),
      (U0_toMatrix_mem_integralMatrices hU).1⟩ = (unitsMod9 γ).1 := by
  refine Matrix.ext fun i j => ?_
  show redMod9 ⟨toMatrix ℚ D v₃ (unitsIncl ℚ D x) i j, _⟩ = _
  rw [unitsMod9_entry γ i j (by
    have h := (U0_toMatrix_mem_integralMatrices hU).1
    rw [mem_integralMatrices_iff] at h
    have he : toMatrix ℚ D v₃ (unitsIncl ℚ D x)
        = theta3 (((x : D)) ⊗ₜ[ℚ] (1 : K₃)) := by
      rw [toMatrix_apply, toLocal_unitsIncl]
      rfl
    rw [← hx, ← he]
    exact h i j)]
  exact redMod9_congr _ _ (by
    rw [toMatrix_apply, toLocal_unitsIncl, hx]
    rfl)

/-- The mod-`9` matrix is multiplicative on `U₀(1)`. -/
theorem redMat_mul_of_mem_U0 {a b : Dfx ℚ D} (ha : a ∈ U0) (hb : b ∈ U0)
    (hab : a * b ∈ U0) :
    redMat ⟨toMatrix ℚ D v₃ (a * b), (U0_toMatrix_mem_integralMatrices hab).1⟩
      = redMat ⟨toMatrix ℚ D v₃ a, (U0_toMatrix_mem_integralMatrices ha).1⟩
        * redMat ⟨toMatrix ℚ D v₃ b, (U0_toMatrix_mem_integralMatrices hb).1⟩ := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext (by rw [Subring.coe_mul]; exact map_mul _ _ _)

/-- **The class representatives lie in `U₀(1)`**: `cᵢ` is trivial away from `3`, and at `3`
both its matrix and the inverse are integral (the diagonal entries `1,5,7,2,4` are
`3`-units). -/
theorem classRep_mem_U0 (i : Fin 3) : classRep i ∈ U0 := by
  refine mem_U0_of_toMatrix (fun w hw => ⟨?_, ?_⟩) (classRep_mem_integralMatrices i).1
    (classRep_mem_integralMatrices i).2
  · rw [classRep, toLocal_unitAt_ne _ _ _ _ hw]
    exact (localOrder w).one_mem
  · rw [classRep, unitAt_inv, toLocal_unitAt_ne _ _ _ _ hw]
    exact (localOrder w).one_mem

/-- A Hurwitz unit gives a global unit whose adelic image lies in `U₀(1)` — the `γ` of the
orbit argument, viewed adelically. -/
theorem exists_globalUnit_of_hurwitzUnit (γ : (hurwitzOrder)ˣ) :
    ∃ x : Dˣ, unitsIncl ℚ D x ∈ U0 ∧ ((x : D)) = ((γ : hurwitzOrder) : ℍ[ℚ]) := by
  refine ⟨Units.map (Subring.subtype hurwitzOrder).toMonoidHom γ, ?_, rfl⟩
  exact (unitsIncl_mem_U0_iff _).mpr ⟨γ, rfl⟩

/-- The mod-`9` matrices of `g` and `g⁻¹` are two-sided inverses, for `g ∈ U₀(1)`. -/
theorem redMat_inv_mul_of_mem_U0 {g : Dfx ℚ D} (hg : g ∈ U0) :
    redMat ⟨toMatrix ℚ D v₃ g⁻¹, (U0_toMatrix_mem_integralMatrices hg).2⟩
      * redMat ⟨toMatrix ℚ D v₃ g, (U0_toMatrix_mem_integralMatrices hg).1⟩ = 1 := by
  rw [← map_mul]
  have h : (⟨toMatrix ℚ D v₃ g⁻¹, (U0_toMatrix_mem_integralMatrices hg).2⟩ :
        integralMatrices)
      * ⟨toMatrix ℚ D v₃ g, (U0_toMatrix_mem_integralMatrices hg).1⟩ = 1 :=
    Subtype.ext (by rw [Subring.coe_mul, ← map_mul, inv_mul_cancel, map_one]; rfl)
  rw [h, map_one]

theorem redMat_mul_inv_of_mem_U0 {g : Dfx ℚ D} (hg : g ∈ U0) :
    redMat ⟨toMatrix ℚ D v₃ g, (U0_toMatrix_mem_integralMatrices hg).1⟩
      * redMat ⟨toMatrix ℚ D v₃ g⁻¹, (U0_toMatrix_mem_integralMatrices hg).2⟩ = 1 := by
  rw [← map_mul]
  have h : (⟨toMatrix ℚ D v₃ g, (U0_toMatrix_mem_integralMatrices hg).1⟩ :
        integralMatrices)
      * ⟨toMatrix ℚ D v₃ g⁻¹, (U0_toMatrix_mem_integralMatrices hg).2⟩ = 1 :=
    Subtype.ext (by rw [Subring.coe_mul, ← map_mul, mul_inv_cancel, map_one]; rfl)
  rw [h, map_one]

/-- The mod-`9` action of `γ·cᵢ` on `e₁` is `unitsMod9 γ` applied to the `i`-th orbit
representative.  (Multiplicativity, plus the two computations
`redMat_unitsIncl_eq_unitsMod9` and `redMat_classRep_mulVec_e1`.) -/
theorem redMat_globalUnit_mul_classRep_mulVec_e1 (γ : (hurwitzOrder)ˣ) (x : Dˣ)
    (hx : ((x : D)) = ((γ : hurwitzOrder) : ℍ[ℚ])) (hxU : unitsIncl ℚ D x ∈ U0) (i : Fin 3)
    (hprod : unitsIncl ℚ D x * classRep i ∈ U0) :
    (redMat ⟨toMatrix ℚ D v₃ (unitsIncl ℚ D x * classRep i),
        (U0_toMatrix_mem_integralMatrices hprod).1⟩).mulVec ![1, 0]
      = (unitsMod9 γ).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0] := by
  rw [redMat_mul_of_mem_U0 hxU (classRep_mem_U0 i) hprod,
    redMat_unitsIncl_eq_unitsMod9 γ x hx hxU, ← Matrix.mulVec_mulVec]
  congr 1
  refine funext fun k => ?_
  have h := redMat_classRep_mulVec_e1 i
  fin_cases k
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- If a `U₀(1)` element fixes `e₁` mod `9`, so does its inverse. -/
theorem inv_mulVec_e1_of_mulVec_e1 {g : Dfx ℚ D} (hg : g ∈ U0)
    (h : (redMat ⟨toMatrix ℚ D v₃ g,
      (U0_toMatrix_mem_integralMatrices hg).1⟩).mulVec ![1, 0] = ![1, 0]) :
    (redMat ⟨toMatrix ℚ D v₃ g⁻¹,
      (U0_toMatrix_mem_integralMatrices hg).2⟩).mulVec ![1, 0] = ![1, 0] := by
  have hc := congrArg (fun w => (redMat ⟨toMatrix ℚ D v₃ g⁻¹,
    (U0_toMatrix_mem_integralMatrices hg).2⟩).mulVec w) h
  rw [Matrix.mulVec_mulVec, redMat_inv_mul_of_mem_U0 hg, Matrix.one_mulVec] at hc
  exact hc.symm

/-- Reading the `e₁`-fixing statement entrywise: the two `redMod9` conditions. -/
theorem redMod9_entries_of_mulVec_e1 {g : Dfx ℚ D} (hg : g ∈ U0)
    (h : (redMat ⟨toMatrix ℚ D v₃ g,
      (U0_toMatrix_mem_integralMatrices hg).1⟩).mulVec ![1, 0] = ![1, 0]) :
    redMod9 ⟨toMatrix ℚ D v₃ g 0 0,
        mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hg).1 0 0⟩ = 1 ∧
      redMod9 ⟨toMatrix ℚ D v₃ g 1 0,
        mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hg).1 1 0⟩ = 0 := by
  have hv : ∀ (N : Matrix (Fin 2) (Fin 2) (ZMod 9)) (a : Fin 2),
      (N.mulVec ![1, 0]) a = N a 0 := by
    intro N a
    simp [Matrix.mulVec, Matrix.vecHead]
  constructor
  · have hc := congrFun h 0
    rw [hv] at hc
    exact hc
  · have hc := congrFun h 1
    rw [hv] at hc
    exact hc

/-- **The corrected element fixes `e₁` mod `9`.**  If `γcᵢ` and `u` have the same mod-`9`
action on `e₁`, then `(γcᵢ)⁻¹u` fixes it — which is the `Σ₁(9)` hypothesis. -/
theorem corrected_mulVec_e1 {u : Dfx ℚ D} (hu : u ∈ U0) (x : Dˣ) (i : Fin 3)
    (hprod : unitsIncl ℚ D x * classRep i ∈ U0)
    (hcorr : (unitsIncl ℚ D x * classRep i)⁻¹ * u ∈ U0)
    (hagree : (redMat ⟨toMatrix ℚ D v₃ (unitsIncl ℚ D x * classRep i),
        (U0_toMatrix_mem_integralMatrices hprod).1⟩).mulVec ![1, 0]
      = (redMat ⟨toMatrix ℚ D v₃ u,
          (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0]) :
    (redMat ⟨toMatrix ℚ D v₃ ((unitsIncl ℚ D x * classRep i)⁻¹ * u),
      (U0_toMatrix_mem_integralMatrices hcorr).1⟩).mulVec ![1, 0] = ![1, 0] := by
  rw [redMat_mul_of_mem_U0 (U0.inv_mem hprod) hu hcorr]
  exact mulVec_e1_of_mul_eq (redMat_inv_mul_of_mem_U0 hprod) hagree

/-- **The orbit index of a `U₀(1)` element.**  Composing `U0_mulVec_e1_mem_primitiveVectors`
with the orbit count: the mod-`9` image of `u` sends `e₁` into exactly one of the three
Hurwitz-unit orbits, and the witnessing unit `γ` is what will absorb into the global factor
of `classRep_complete`. -/
theorem exists_unique_orbit_index_of_mem_U0 {u : Dfx ℚ D} (hu : u ∈ U0) :
    ∃! i : Fin 3, ∃ γ : (hurwitzOrder)ˣ,
      (unitsMod9 γ).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0]
        = ![(((redMat ⟨toMatrix ℚ D v₃ u,
                (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0]) 0),
            (((redMat ⟨toMatrix ℚ D v₃ u,
                (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0]) 1)] :=
  orbits_unitsMod9 _ (U0_mulVec_e1_mem_primitiveVectors hu)

set_option maxRecDepth 100000 in
/-- **The finite heart of [Jacobs, Lemma 2.2]**: among the `24` Hurwitz units, only the
identity reduces mod `9` to a matrix of the shape `(∗ ∗; 0 1)` — i.e. only `t = (2,0,0,0)`
(the tuple of `1`) satisfies the `Σ₁(9)` conditions on the `(0,0)` and `(1,0)` entries.

Conjugation by `classRep i` may be ignored here: its `3`-component is the diagonal
`diag(dᵢ, eᵢ)` with `(dᵢ, eᵢ) ∈ {(1,1), (5,2), (7,4)}`, all units mod `9`, and for diagonal
`C = diag(a,b)` one has `(C⁻¹MC)₀₀ = M₀₀` and `(C⁻¹MC)₁₀ = M₁₀·(a/b)`.  So the `(0,0)`
entry is unchanged and the `(1,0)` entry is scaled by a unit — the two conditions are
therefore independent of `i`. -/
theorem only_one_tuple_sigma1 :
    ∀ t ∈ unitTuples, (tupleMat t) 0 0 = 1 → (tupleMat t) 1 0 = 0 → t = (2, 0, 0, 0) := by
  decide

/-- **[Jacobs, Lemma 2.2]**: the stabilisers are trivial — `Γᵢ = cᵢ⁻¹ D^× cᵢ ∩ U₁(9) = 1`.
(In the framework's terms: `stabilizerAt (globalUnits) U1_9 (classRep i) = ⊥`; the proof
is the finite check that no nontrivial Hurwitz unit is `≡ (∗ ∗; 0 1) mod 9` after
conjugation by `cᵢ`.) -/
theorem stabilizerAt_classRep (i : Fin 3) :
    AutomorphicFunction.stabilizerAt (globalUnits ℚ D) U1_9 (classRep i) = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨huU, hconj⟩ := hu
  obtain ⟨x, hx⟩ := hconj
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx
  have hMu : toMatrix ℚ D v₃ u ∈ integralMatrices :=
    mem_integralMatrices_iff.mpr fun a b => huU.2.1.1.1 a b
  have hMu' : toMatrix ℚ D v₃ u⁻¹ ∈ integralMatrices :=
    mem_integralMatrices_iff.mpr fun a b => huU.2.2.1.1 a b
  have hcint := classRep_mem_integralMatrices i
  have hinvexp : (classRep i * u * (classRep i)⁻¹)⁻¹ = classRep i * u⁻¹ * (classRep i)⁻¹ := by
    group
  have hconjU0 : classRep i * u * (classRep i)⁻¹ ∈ U0 := by
    refine mem_U0_of_toMatrix (fun w hw => ⟨?_, ?_⟩) ?_ ?_
    · rw [Units.val_mul, Units.val_mul, map_mul, map_mul, classRep,
        toLocal_unitAt_ne _ _ _ _ hw, unitAt_inv, toLocal_unitAt_ne _ _ _ _ hw,
        one_mul, mul_one]
      exact (huU.1 w).1
    · rw [hinvexp, Units.val_mul, Units.val_mul, map_mul, map_mul, classRep,
        toLocal_unitAt_ne _ _ _ _ hw, unitAt_inv, toLocal_unitAt_ne _ _ _ _ hw,
        one_mul, mul_one]
      exact (huU.1 w).2
    · rw [map_mul, map_mul]
      exact integralMatrices.mul_mem (integralMatrices.mul_mem hcint.1 hMu) hcint.2
    · rw [hinvexp, map_mul, map_mul]
      exact integralMatrices.mul_mem (integralMatrices.mul_mem hcint.1 hMu') hcint.2
  have hxU0 : unitsIncl ℚ D x ∈ U0 := by rw [hx]; exact hconjU0
  obtain ⟨x', hx'⟩ := (unitsIncl_mem_U0_iff x).mp hxU0
  obtain ⟨t, ht, htx⟩ := exists_tuple_of_unit x'
  -- the `3`-component of `unitsIncl x`, and its two `Σ₁(9)` entries
  have hN : toMatrix ℚ D v₃ (unitsIncl ℚ D x)
      = toMatrix ℚ D v₃ (classRep i) * toMatrix ℚ D v₃ u
        * toMatrix ℚ D v₃ (classRep i)⁻¹ := by
    rw [hx, map_mul, map_mul]
  have hd1 : (((classDiag i).1 : ℤ) : K₃) ≠ 0 := classDiag_fst_ne_zero i
  have hd2 : (((classDiag i).2 : ℤ) : K₃) ≠ 0 := classDiag_snd_ne_zero i
  have hCeq : toMatrix ℚ D v₃ (classRep i)
      = Matrix.of ![![(((classDiag i).1 : ℤ) : K₃), 0],
                    ![0, (((classDiag i).2 : ℤ) : K₃)]] := by
    rw [toMatrix_classRep, classDiag_fst_eq, classDiag_snd_eq]
  have hconjE := diag_conj_entries hd1 hd2 (toMatrix ℚ D v₃ u)
  rw [← hCeq, ← toMatrix_classRep_inv i] at hconjE
  have h00 : toMatrix ℚ D v₃ (unitsIncl ℚ D x) 0 0 = toMatrix ℚ D v₃ u 0 0 := by
    rw [hN]; exact hconjE.1
  have h10v : Valued.v (toMatrix ℚ D v₃ (unitsIncl ℚ D x) 1 0) ≤ γ₉ := by
    rw [hN, hconjE.2, map_mul, map_mul, map_inv₀,
      (valued_classDiag_eq_one i).1, (valued_classDiag_eq_one i).2, inv_one, mul_one,
      one_mul]
    simpa using huU.2.1.1.2.1
  have hNint : toMatrix ℚ D v₃ (unitsIncl ℚ D x) ∈ integralMatrices := by
    rw [hN]
    exact integralMatrices.mul_mem (integralMatrices.mul_mem hcint.1 hMu) hcint.2
  have hNint' := mem_integralMatrices_iff.mp hNint
  -- the two `mod 9` conditions on the `3`-component of `unitsIncl x`
  have hr00 : redMod9 ⟨toMatrix ℚ D v₃ (unitsIncl ℚ D x) 0 0, hNint' 0 0⟩ = 1 := by
    rw [redMod9_congr (hNint' 0 0) (mem_integralMatrices_iff.mp hMu 0 0) h00]
    exact (redMod9_of_mem_sigma1 huU.2.1 (mem_integralMatrices_iff.mp hMu 0 0)
      (mem_integralMatrices_iff.mp hMu 1 0)).1
  have hr10 : redMod9 ⟨toMatrix ℚ D v₃ (unitsIncl ℚ D x) 1 0, hNint' 1 0⟩ = 0 :=
    redMod9_eq_zero_of_le _ (h10v.trans (le_of_eq valued_nine_eq.symm))
  -- identify that `3`-component with `unitsMod9 x'`
  have hNθ : toMatrix ℚ D v₃ (unitsIncl ℚ D x) = theta3 (((x : D)) ⊗ₜ[ℚ] (1 : K₃)) := by
    rw [toMatrix_apply, toLocal_unitsIncl]
    rfl
  obtain ⟨A, B, C, E⟩ := t
  have hmat : (unitsMod9 x').1 = tupleMat (A, B, C, E) := by
    simp only [tupleMat]
    exact unitsMod9_apply x' htx
  have hentry : ∀ a b : Fin 2, (tupleMat (A, B, C, E)) a b
      = redMod9 ⟨toMatrix ℚ D v₃ (unitsIncl ℚ D x) a b, hNint' a b⟩ := by
    intro a b
    rw [← hmat, unitsMod9_entry x' a b
      (by rw [hx', ← hNθ]; exact hNint' a b)]
    exact redMod9_congr _ _ (by rw [hNθ, hx'])
  have ht0 : (A, B, C, E) = ((2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) :=
    only_one_tuple_sigma1 _ ht (by rw [hentry 0 0]; exact hr00)
      (by rw [hentry 1 0]; exact hr10)
  -- hence `x = 1`, hence `u = 1`
  rw [ht0] at htx
  have hx1 : (x : D) = 1 := by
    rw [← hx', ← htx]
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [ofTuple]
  have hx1' : unitsIncl ℚ D x = 1 := by
    refine Units.ext ?_
    show Algebra.TensorProduct.includeLeftRingHom ((x : D)) = 1
    rw [hx1, map_one]
  rw [hx1'] at hx
  have hcu : classRep i * u = classRep i := mul_inv_eq_one.mp hx.symm
  exact mul_left_cancel (a := classRep i) (by simpa using hcu)

/-- **Existence half of [Jacobs, Theorem 2.1], at the `U₀(1)` level**: every `u ∈ U₀(1)`
factors as `d · cᵢ · w` with `d` a global unit and `w ∈ U₁(9)`.  The index `i` is the orbit
index of `u`'s mod-`9` action on `e₁`, and `d` is the Hurwitz unit witnessing that orbit. -/
theorem exists_classRep_factorisation_of_mem_U0 {u : Dfx ℚ D} (hu : u ∈ U0) :
    ∃ i : Fin 3, ∃ d ∈ globalUnits ℚ D, ∃ w ∈ U1_9, u = d * classRep i * w := by
  obtain ⟨i, ⟨γ, horb⟩, -⟩ := exists_unique_orbit_index_of_mem_U0 hu
  obtain ⟨x, hxU, hx⟩ := exists_globalUnit_of_hurwitzUnit γ
  have hprod : unitsIncl ℚ D x * classRep i ∈ U0 := U0.mul_mem hxU (classRep_mem_U0 i)
  have hcorr : (unitsIncl ℚ D x * classRep i)⁻¹ * u ∈ U0 :=
    U0.mul_mem (U0.inv_mem hprod) hu
  have hagree : (redMat ⟨toMatrix ℚ D v₃ (unitsIncl ℚ D x * classRep i),
        (U0_toMatrix_mem_integralMatrices hprod).1⟩).mulVec ![1, 0]
      = (redMat ⟨toMatrix ℚ D v₃ u,
          (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0] := by
    rw [redMat_globalUnit_mul_classRep_mulVec_e1 γ x hx hxU i hprod]
    exact orbit_eq_mulVec hu i γ horb
  have hfix := corrected_mulVec_e1 hu x i hprod hcorr hagree
  have hfix' := inv_mulVec_e1_of_mulVec_e1 hcorr hfix
  refine ⟨i, unitsIncl ℚ D x, ⟨x, rfl⟩, (unitsIncl ℚ D x * classRep i)⁻¹ * u, ?_, ?_⟩
  · obtain ⟨e0, e1⟩ := redMod9_entries_of_mulVec_e1 hcorr hfix
    obtain ⟨e0', e1'⟩ := redMod9_entries_of_mulVec_e1 (U0.inv_mem hcorr) (by simpa using hfix')
    exact mem_U1_9_of_redMod9 hcorr e0 e1 (by simpa using e0') (by simpa using e1')
  · group

/-- **Existence half of [Jacobs, Theorem 2.1]** for a general `g ∈ D_f^×`, under
class-number-one: `hcn` splits `g = d₀·u₀` with `u₀ ∈ U₀(1)`, and the `U₀(1)` factorisation
then applies, `d₀` being absorbed into the global factor. -/
theorem exists_classRep_factorisation (hcn : HClassNumberOne) (g : Dfx ℚ D) :
    ∃ i : Fin 3, ∃ d ∈ globalUnits ℚ D, ∃ w ∈ U1_9, g = d * classRep i * w := by
  obtain ⟨d₀, hd₀, u₀, hu₀, rfl⟩ := hcn g
  obtain ⟨i, d, hd, w, hw, hfac⟩ := exists_classRep_factorisation_of_mem_U0 hu₀
  refine ⟨i, d₀ * d, (globalUnits ℚ D).mul_mem hd₀ hd, w, hw, ?_⟩
  rw [hfac]
  group

/-- `cᵢ` realises orbit index `i` (with the trivial Hurwitz unit).  Combined with the
uniqueness clause of `exists_unique_orbit_index_of_mem_U0`, this pins the index of `cᵢ`. -/
theorem classRep_orbit_index (i : Fin 3) :
    ∃ γ : (hurwitzOrder)ˣ,
      (unitsMod9 γ).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0]
        = (redMat ⟨toMatrix ℚ D v₃ (classRep i),
            (U0_toMatrix_mem_integralMatrices (classRep_mem_U0 i)).1⟩).mulVec ![1, 0] := by
  refine ⟨1, ?_⟩
  have h := redMat_classRep_mulVec_e1 i
  rw [map_one, Units.val_one, Matrix.one_mulVec]
  refine funext fun k => ?_
  fin_cases k
  · simpa using (congrArg Prod.fst h).symm
  · simpa using (congrArg Prod.snd h).symm

/-- A `U₁(9)` element fixes `e₁` mod `9` — the `(∗ ∗; 0 1)` shape read as an action on the
first basis vector. -/
theorem redMat_mulVec_e1_of_mem_U1_9 {w : Dfx ℚ D} (hw : w ∈ U1_9) :
    (redMat ⟨toMatrix ℚ D v₃ w,
      (U0_toMatrix_mem_integralMatrices hw.1).1⟩).mulVec ![1, 0] = ![1, 0] := by
  obtain ⟨h00, h10⟩ := redMod9_of_mem_sigma1 hw.2.1
    (mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hw.1).1 0 0)
    (mem_integralMatrices_iff.mp (U0_toMatrix_mem_integralMatrices hw.1).1 1 0)
  have hv : ∀ (N : Matrix (Fin 2) (Fin 2) (ZMod 9)) (a : Fin 2),
      (N.mulVec ![1, 0]) a = N a 0 := by
    intro N a
    simp [Matrix.mulVec, Matrix.vecHead]
  refine funext fun k => ?_
  fin_cases k
  · rw [hv]; exact h00
  · rw [hv]; exact h10

/-- **The orbit index reads off a factorisation**: if `u = d·c_j·w` with `d` a global unit
lying in `U₀(1)` and `w ∈ U₁(9)`, then `u` realises orbit index `j`.  The global factor
supplies the Hurwitz unit, and the `U₁(9)` factor acts trivially on `e₁`. -/
theorem orbit_index_of_factorisation {u : Dfx ℚ D} (hu : u ∈ U0) (x : Dˣ) (j : Fin 3)
    (hxU : unitsIncl ℚ D x ∈ U0) {w : Dfx ℚ D} (hw : w ∈ U1_9)
    (heq : u = unitsIncl ℚ D x * classRep j * w) :
    ∃ γ : (hurwitzOrder)ˣ,
      (unitsMod9 γ).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) j : ZMod 9), 0]
        = (redMat ⟨toMatrix ℚ D v₃ u,
            (U0_toMatrix_mem_integralMatrices hu).1⟩).mulVec ![1, 0] := by
  subst heq
  obtain ⟨γ, hγ⟩ := (unitsIncl_mem_U0_iff x).mp hxU
  have hp : unitsIncl ℚ D x * classRep j ∈ U0 := U0.mul_mem hxU (classRep_mem_U0 j)
  refine ⟨γ, ?_⟩
  rw [redMat_mul_of_mem_U0 hp hw.1 hu, ← Matrix.mulVec_mulVec,
    redMat_mulVec_e1_of_mem_U1_9 hw,
    redMat_globalUnit_mul_classRep_mulVec_e1 γ x hγ.symm hxU j hp]

/-- **Uniqueness of the class index**: `cᵢ` and `c_j` lie in the same `D^×`–`U₁(9)` double
coset only when `i = j`.  Both indices are orbit indices of the single element `cᵢ`, and
`exists_unique_orbit_index_of_mem_U0` says there is only one. -/
theorem classRep_index_unique {i j : Fin 3} {d : Dfx ℚ D} (hd : d ∈ globalUnits ℚ D)
    {w : Dfx ℚ D} (hw : w ∈ U1_9) (h : classRep i = d * classRep j * w) : i = j := by
  obtain ⟨x, rfl⟩ := hd
  have hdU : unitsIncl ℚ D x ∈ U0 := by
    have hx : unitsIncl ℚ D x = classRep i * w⁻¹ * (classRep j)⁻¹ := by rw [h]; group
    rw [hx]
    exact U0.mul_mem (U0.mul_mem (classRep_mem_U0 i) (U0.inv_mem (U1_9_le_U0 hw)))
      (U0.inv_mem (classRep_mem_U0 j))
  obtain ⟨i₀, -, huniq⟩ := exists_unique_orbit_index_of_mem_U0 (classRep_mem_U0 i)
  obtain ⟨γ, hγ⟩ := orbit_index_of_factorisation (classRep_mem_U0 i) x j hdU hw h
  have hvec : ∀ m : Fin 3, (∃ δ : (hurwitzOrder)ˣ,
      (unitsMod9 δ).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) m : ZMod 9), 0]
        = (redMat ⟨toMatrix ℚ D v₃ (classRep i),
            (U0_toMatrix_mem_integralMatrices (classRep_mem_U0 i)).1⟩).mulVec ![1, 0]) →
      m = i₀ := by
    rintro m ⟨δ, hδ⟩
    refine huniq m ⟨δ, ?_⟩
    rw [hδ]
    refine funext fun k => ?_
    fin_cases k <;> simp
  rw [hvec i (classRep_orbit_index i), hvec j ⟨γ, hγ⟩]

/-- **[Jacobs, Theorem 2.1]**: under `HClassNumberOne`, the `classRep` family is a
complete system of representatives: every `g ∈ D_f^×` lies in `D^× · cᵢ · U₁(9)` for a
unique `i`. -/
theorem classRep_complete (hcn : HClassNumberOne) (g : Dfx ℚ D) :
    ∃! i : Fin 3, ∃ d ∈ globalUnits ℚ D, ∃ u ∈ U1_9, g = d * classRep i * u := by
  obtain ⟨i, d, hd, u, hu, hfac⟩ := exists_classRep_factorisation hcn g
  refine ⟨i, ⟨d, hd, u, hu, hfac⟩, ?_⟩
  rintro j ⟨d', hd', u', hu', hfac'⟩
  have heq : d * classRep i * u = d' * classRep j * u' := by rw [← hfac, ← hfac']
  have h : classRep i = d⁻¹ * d' * classRep j * (u' * u⁻¹) := by
    rw [show d⁻¹ * d' * classRep j * (u' * u⁻¹) = d⁻¹ * (d' * classRep j * u') * u⁻¹ by group,
      ← heq]
    group
  exact (classRep_index_unique
    ((globalUnits ℚ D).mul_mem ((globalUnits ℚ D).inv_mem hd) hd')
    (U1_9.mul_mem hu' (U1_9.inv_mem hu)) h).symm

/-- The double-coset section form used by `AutomorphicFunction.bijective_evalAtReps`:
each double-coset class contains exactly one `classRep`. -/
theorem exists_classRep_section (hcn : HClassNumberOne) :
    ∃ σ : DoubleCoset.Quotient ((globalUnits ℚ D : Subgroup (Dfx ℚ D)) : Set (Dfx ℚ D))
        (U1_9 : Set (Dfx ℚ D)) → Dfx ℚ D,
      (∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient _ _) = q) ∧
        ∀ q, ∃ i : Fin 3, σ q = classRep i := by
  classical
  have key : ∀ q : DoubleCoset.Quotient
      ((globalUnits ℚ D : Subgroup (Dfx ℚ D)) : Set (Dfx ℚ D)) (U1_9 : Set (Dfx ℚ D)),
      ∃ i : Fin 3, (Quotient.mk'' (classRep i) : DoubleCoset.Quotient _ _) = q := by
    intro q
    obtain ⟨i, ⟨d, hd, u, hu, hfac⟩, -⟩ := classRep_complete hcn q.out
    refine ⟨i, ?_⟩
    rw [← Quotient.out_eq' q]
    exact Quotient.sound' (DoubleCoset.rel_iff.mpr ⟨d, hd, u, hu, hfac⟩)
  exact ⟨fun q => classRep (key q).choose, fun q => (key q).choose_spec, fun q => ⟨_, rfl⟩⟩

end Jacobs.U3
