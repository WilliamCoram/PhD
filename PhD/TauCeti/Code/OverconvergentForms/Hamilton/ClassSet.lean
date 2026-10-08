/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Hamilton.ClassNumberOne

/-!
# The class set of `U₁(9)`: three classes with trivial stabilisers

Given class number one, `D^× \ D_f^× / U₁(9) = 𝒪^× \ U₀(1) / U₁(9)`, and `U₀(1) / U₁(9)` is the set
of `72` primitive vectors of `(ℤ/9)²` through the bottom row of `θ₃` modulo `9`. The `24` Hurwitz
units act with three orbits, represented by `c₀ = 1`, `c₁ = ι₃(diag(5, 2))`, `c₂ = ι₃(diag(7, 4))`,
and the three stabilisers are trivial.

[Jac03, Theorem 2.1]: the class set of `U₁(9)` has three elements. [Jac03, Lemma 2.2]: the groups
`Γ_i` are trivial.

## Main definitions

* `Hamilton.classDiag`, `Hamilton.diagGL`, `Hamilton.classRep`: the three representatives.
* `Hamilton.redMod9`, `Hamilton.redMat`, `Hamilton.unitsMod9`: reduction modulo `9`.
* `Hamilton.primitiveVectors`: the `72` primitive vectors of `(ℤ/9)²`.

## Main results

* `Hamilton.redMod9_eq_zero_iff`, `Hamilton.redMod9_surjective`: the reduction modulo `9`.
* `Hamilton.mem_U1_9_iff_bottomRow`: `U₁(9)` inside `U₀(1)` through the bottom row modulo `9`.
* `Hamilton.existsUnique_orbit`, `Hamilton.eq_one_of_vecMul_unitsMod9`: the three orbits of the
  Hurwitz units on the primitive vectors, acting freely.
* `Hamilton.isCompleteFamily_classRep`, `Hamilton.isSection_classRep`,
  `Hamilton.card_classSet_U1_9`: the class set of `U₁(9)` has the three elements `c₀, c₁, c₂`.
* `Hamilton.stabilizer_classRep`: the stabilisers are trivial.

Roadmap: §0.5.2, §0.5.3. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Hamilton/ClassSet.lean`.
-/

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField AdelicAlgebra Quaternion

noncomputable section

namespace Hamilton

open scoped AdelicAlgebra.RightAlgebra

/-- The diagonals of the class representatives: `(1, 1)`, `(5, 2)`, `(7, 4)`. -/
def classDiag : Fin 3 → ℤ × ℤ := ![(1, 1), (5, 2), (7, 4)]

/-- An integer prime to `3` is a nonzero element of `K₃`. -/
theorem ratCast_ne_zero_of_not_dvd {x : ℤ} (hx : ¬ (3 : ℤ) ∣ x) : ((x : ℚ) : K₃) ≠ 0 :=
  fun h => by
    have h1 := valued_intCast_eq_one (q := 3) (n := x) hx
    rw [h, map_zero] at h1
    exact zero_ne_one h1

/-- The diagonal matrix `diag(x, y)` of integers prime to `3`, in `GL₂(K₃)`. -/
def diagGL (x y : ℤ) (hx : ¬ (3 : ℤ) ∣ x) (hy : ¬ (3 : ℤ) ∣ y) : GL (Fin 2) K₃ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![((x : ℚ) : K₃), ((y : ℚ) : K₃)]) (by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      exact mul_ne_zero (ratCast_ne_zero_of_not_dvd hx) (ratCast_ne_zero_of_not_dvd hy))

/-- The first diagonal entries are prime to `3`. -/
theorem classDiag_fst_not_dvd (i : Fin 3) : ¬ (3 : ℤ) ∣ (classDiag i).1 := by
  fin_cases i
  · show ¬ (3 : ℤ) ∣ 1; omega
  · show ¬ (3 : ℤ) ∣ 5; omega
  · show ¬ (3 : ℤ) ∣ 7; omega

/-- The second diagonal entries are prime to `3`. -/
theorem classDiag_snd_not_dvd (i : Fin 3) : ¬ (3 : ℤ) ∣ (classDiag i).2 := by
  fin_cases i
  · show ¬ (3 : ℤ) ∣ 1; omega
  · show ¬ (3 : ℤ) ∣ 2; omega
  · show ¬ (3 : ℤ) ∣ 4; omega

/-- **The class representatives** `c₀ = 1`, `c₁ = ι₃(diag(5, 2))`, `c₂ = ι₃(diag(7, 4))`. -/
def classRep (i : Fin 3) : Dfx ℚ ℍ[ℚ] :=
  unitAt ℚ ℍ[ℚ] v₃ (diagGL (classDiag i).1 (classDiag i).2 (classDiag_fst_not_dvd i)
    (classDiag_snd_not_dvd i))

/-- `c₀ = 1`. -/
theorem classRep_zero : classRep 0 = 1 := by
  have h : diagGL (classDiag 0).1 (classDiag 0).2 (classDiag_fst_not_dvd 0)
      (classDiag_snd_not_dvd 0) = 1 := by
    refine Units.ext ?_
    show Matrix.diagonal ![(((1 : ℤ) : ℚ) : K₃), (((1 : ℤ) : ℚ) : K₃)] = 1
    rw [Int.cast_one, Rat.cast_one, ← Matrix.diagonal_one]
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [classRep, h, map_one]

/-- The `3`-component of `cᵢ` is `diag(xᵢ, yᵢ)`. -/
theorem toMatrix_classRep (i : Fin 3) :
    toMatrix ℚ ℍ[ℚ] v₃ (classRep i) =
      Matrix.diagonal ![(((classDiag i).1 : ℚ) : K₃), (((classDiag i).2 : ℚ) : K₃)] := by
  rw [classRep, ← coe_toGL, toGL_unitAt]
  rfl

private theorem diagGL_mem_integralGL (x y : ℤ) (hx : ¬ (3 : ℤ) ∣ x) (hy : ¬ (3 : ℤ) ∣ y) :
    diagGL x y hx hy ∈ integralGL v₃ := by
  have hx1 := valued_intCast_eq_one (q := 3) (n := x) hx
  have hy1 := valued_intCast_eq_one (q := 3) (n := y) hy
  refine (mem_integralGL_iff v₃).mpr ⟨fun a b => ?_, ?_⟩
  · show Matrix.diagonal ![((x : ℚ) : K₃), ((y : ℚ) : K₃)] a b ∈ v₃.adicCompletionIntegers ℚ
    rw [Matrix.diagonal_apply]
    split_ifs
    · fin_cases a
      · exact hx1.le
      · exact hy1.le
    · exact zero_mem _
  · show Valued.v (Matrix.diagonal ![((x : ℚ) : K₃), ((y : ℚ) : K₃)]).det = 1
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    show Valued.v (((x : ℚ) : K₃) * ((y : ℚ) : K₃)) = 1
    rw [map_mul, hx1, hy1, one_mul]

/-- The representatives lie in `U₀(1)`. -/
theorem classRep_mem_U0 (i : Fin 3) : classRep i ∈ U0 :=
  (unitAt_mem_U0_iff v₃ theta3_isIntegral).mpr (diagGL_mem_integralGL _ _ _ _)

-- the identification `𝒪₃ ≅ ℤ_3`, with its codomain written at `v₃`
private def intEquiv3 : ℤ_[3] ≃A[ℤ] v₃.adicCompletionIntegers ℚ :=
  PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨3, Nat.prime_three⟩

/-- **Reduction modulo `9`** on the `3`-adic integers. -/
def redMod9 : v₃.adicCompletionIntegers ℚ →+* ZMod 9 :=
  (PadicInt.toZModPow 2).comp (intEquiv3.symm : _ ≃A[ℤ] _).toRingEquiv.toRingHom

/-- Integers reduce as expected. -/
theorem redMod9_intCast (n : ℤ) (h : ((n : ℚ) : K₃) ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨((n : ℚ) : K₃), h⟩ = (n : ZMod 9) := by
  rw [show (⟨((n : ℚ) : K₃), h⟩ : v₃.adicCompletionIntegers ℚ) =
      (n : v₃.adicCompletionIntegers ℚ) from Subtype.ext (by simp), map_intCast]

-- the kernel of the reduction is `9 𝒪₃`
private theorem redMod9_eq_zero_iff_dvd (x : v₃.adicCompletionIntegers ℚ) :
    redMod9 x = 0 ↔ (9 : v₃.adicCompletionIntegers ℚ) ∣ x := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp
      (by rw [← PadicInt.ker_toZModPow (p := 3) 2]; exact h :
        intEquiv3.symm x ∈ Ideal.span {((3 : ℕ) : ℤ_[3]) ^ 2})
    refine ⟨intEquiv3 z, ?_⟩
    have hc := congrArg intEquiv3 hz
    rw [map_mul, show ((3 : ℕ) : ℤ_[3]) ^ 2 = (9 : ℤ_[3]) by norm_num, map_ofNat,
      ContinuousAlgEquiv.apply_symm_apply] at hc
    rw [← hc]
    exact mul_comm _ _
  · rintro ⟨z, rfl⟩
    rw [map_mul, map_ofNat, show (9 : ZMod 9) = 0 from rfl, zero_mul]

/-- The kernel of the reduction is `9 𝒪₃`, in valuative form. -/
theorem redMod9_eq_zero_iff (x : v₃.adicCompletionIntegers ℚ) :
    redMod9 x = 0 ↔ Valued.v (x : K₃) ≤ Valued.v ((9 : ℚ) : K₃) := by
  rw [Rat.cast_ofNat, redMod9_eq_zero_iff_dvd]
  have h9 : (9 : K₃) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (by
      have h := valued_nine
      rw [Rat.cast_ofNat] at h
      rw [h]
      exact levelThreshold_ne_zero 2)
  constructor
  · rintro ⟨z, rfl⟩
    rw [MulMemClass.coe_mul, map_mul]
    rw [show ((9 : v₃.adicCompletionIntegers ℚ) : K₃) = 9 by norm_cast]
    exact (mul_le_mul' le_rfl z.2).trans_eq (mul_one _)
  · intro h
    have hq : (x : K₃) / 9 ∈ v₃.adicCompletionIntegers ℚ := by
      show Valued.v ((x : K₃) / 9) ≤ 1
      rw [Valuation.map_div]
      exact div_le_one_of_le₀ h zero_le
    refine ⟨⟨(x : K₃) / 9, hq⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul, show ((9 : v₃.adicCompletionIntegers ℚ) : K₃) = 9 by norm_cast]
    exact (mul_div_cancel₀ _ h9).symm

/-- The reduction is surjective. -/
theorem redMod9_surjective : Function.Surjective redMod9 := by
  have hA : Function.Surjective (PadicInt.toZModPow 2 : ℤ_[3] →+* ZMod (3 ^ 2)) := fun z =>
    ⟨(z.val : ℤ_[3]), by simp [PadicInt.toZModPow]⟩
  exact hA.comp intEquiv3.symm.surjective

private theorem redMod9_one' (h : (1 : K₃) ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨1, h⟩ = 1 := by
  rw [← map_one redMod9]
  congr 1

private theorem redMod9_zero' (h : (0 : K₃) ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨0, h⟩ = 0 := by
  rw [← map_zero redMod9]
  congr 1

private theorem redMod9_add' {x y : K₃} (hx : x ∈ v₃.adicCompletionIntegers ℚ)
    (hy : y ∈ v₃.adicCompletionIntegers ℚ) (hxy : x + y ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨x + y, hxy⟩ = redMod9 ⟨x, hx⟩ + redMod9 ⟨y, hy⟩ := by
  rw [← map_add redMod9]
  congr 1

private theorem redMod9_mul' {x y : K₃} (hx : x ∈ v₃.adicCompletionIntegers ℚ)
    (hy : y ∈ v₃.adicCompletionIntegers ℚ) (hxy : x * y ∈ v₃.adicCompletionIntegers ℚ) :
    redMod9 ⟨x * y, hxy⟩ = redMod9 ⟨x, hx⟩ * redMod9 ⟨y, hy⟩ := by
  rw [← map_mul redMod9]
  congr 1

private theorem entry_mem {M : Matrix (Fin 2) (Fin 2) K₃} (hM : M ∈ integralMatrices v₃)
    (i j : Fin 2) : M i j ∈ v₃.adicCompletionIntegers ℚ :=
  hM i j

private theorem redMod9_congr {x y : K₃} (hx : x ∈ v₃.adicCompletionIntegers ℚ)
    (hy : y ∈ v₃.adicCompletionIntegers ℚ) (h : x = y) : redMod9 ⟨x, hx⟩ = redMod9 ⟨y, hy⟩ := by
  subst h
  rfl

/-- Reduction modulo `9` of the integral matrices. -/
def redMat : integralMatrices v₃ →+* Matrix (Fin 2) (Fin 2) (ZMod 9) where
  toFun M := Matrix.of fun i j => redMod9 ⟨M.1 i j, entry_mem M.2 i j⟩
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
    have hM0 := entry_mem M.2 i 0
    have hM1 := entry_mem M.2 i 1
    have hN0 := entry_mem N.2 0 j
    have hN1 := entry_mem N.2 1 j
    simp only [Matrix.of_apply, Subring.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [redMod9_add' (mul_mem hM0 hN0) (mul_mem hM1 hN1)
        (add_mem (mul_mem hM0 hN0) (mul_mem hM1 hN1)),
      redMod9_mul' hM0 hN0 (mul_mem hM0 hN0), redMod9_mul' hM1 hN1 (mul_mem hM1 hN1)]

-- `θ₃` on the Hurwitz order, landing in the integral matrices
private def hurwitzToMat : hurwitzOrder →+* integralMatrices v₃ where
  toFun x := ⟨RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃) ((x : ℍ[ℚ]) ⊗ₜ[ℚ] 1),
    (Set.ext_iff.mp theta3_isIntegral _).mp
      (Set.mem_image_of_mem _ (tmul_mem_localOrder x.2 (one_mem _)))⟩
  map_one' := Subtype.ext (by
    show RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃)
      (((1 : hurwitzOrder) : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : K₃)) = 1
    rw [OneMemClass.coe_one, ← Algebra.TensorProduct.one_def, map_one])
  map_mul' x y := Subtype.ext (by
    show RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃)
      (((x * y : hurwitzOrder) : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : K₃)) =
        RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃) ((x : ℍ[ℚ]) ⊗ₜ[ℚ] 1) *
          RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃) ((y : ℍ[ℚ]) ⊗ₜ[ℚ] 1)
    rw [MulMemClass.coe_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one])
  map_zero' := Subtype.ext (by
    show RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃)
      (((0 : hurwitzOrder) : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : K₃)) = 0
    rw [ZeroMemClass.coe_zero, TensorProduct.zero_tmul, map_zero])
  map_add' x y := Subtype.ext (by
    show RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃)
      (((x + y : hurwitzOrder) : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : K₃)) =
        RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃) ((x : ℍ[ℚ]) ⊗ₜ[ℚ] 1) +
          RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃) ((y : ℍ[ℚ]) ⊗ₜ[ℚ] 1)
    rw [AddMemClass.coe_add, TensorProduct.add_tmul, map_add])

/-- **The Hurwitz units modulo `9`**, through `θ₃`. -/
def unitsMod9 : (hurwitzOrder)ˣ →* GL (Fin 2) (ZMod 9) :=
  Units.map (redMat.comp hurwitzToMat).toMonoidHom

/-- The primitive vectors of `(ℤ/9)²`. -/
def primitiveVectors : Finset (ZMod 9 × ZMod 9) :=
  Finset.univ.filter fun v ↦ IsUnit v.1 ∨ IsUnit v.2

/-- There are `72` primitive vectors. -/
theorem card_primitiveVectors : primitiveVectors.card = 72 := by
  decide

private theorem redMat_apply {M : Matrix (Fin 2) (Fin 2) K₃} (hM : M ∈ integralMatrices v₃)
    (i j : Fin 2) : redMat ⟨M, hM⟩ i j = redMod9 ⟨M i j, entry_mem hM i j⟩ :=
  rfl

-- the bottom row of a `2 × 2` matrix
private theorem vecMul_zero_one (N : Matrix (Fin 2) (Fin 2) (ZMod 9)) :
    Matrix.vecMul ![0, 1] N = ![N 1 0, N 1 1] := by
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

-- congruence modulo `9`, in valuative form
private theorem redMod9_eq_iff (x y : v₃.adicCompletionIntegers ℚ) :
    redMod9 x = redMod9 y ↔ Valued.v ((x : K₃) - y) ≤ Valued.v ((9 : ℚ) : K₃) := by
  rw [← sub_eq_zero, ← map_sub, redMod9_eq_zero_iff, AddSubgroupClass.coe_sub]

private theorem redMod9_eq_one_iff (x : v₃.adicCompletionIntegers ℚ) :
    redMod9 x = 1 ↔ Valued.v ((x : K₃) - 1) ≤ Valued.v ((9 : ℚ) : K₃) := by
  rw [← map_one redMod9, redMod9_eq_iff, OneMemClass.coe_one]

/-- **`U₁(9)` inside `U₀(1)` through the bottom row**: `g ∈ U₀(1)` lies in `U₁(9)` exactly when the
bottom row of `θ₃(g)` is `(0, 1)` modulo `9`. -/
theorem mem_U1_9_iff_bottomRow {g : Dfx ℚ ℍ[ℚ]} (hg : g ∈ U0)
    (hint : toMatrix ℚ ℍ[ℚ] v₃ g ∈ integralMatrices v₃) :
    g ∈ U1_9 ↔ Matrix.vecMul ![0, 1] (redMat ⟨toMatrix ℚ ℍ[ℚ] v₃ g, hint⟩) = ![0, 1] := by
  rw [mem_U1_9_iff, vecMul_zero_one, redMat_apply, redMat_apply]
  constructor
  · rintro ⟨-, h10, h11⟩
    rw [(redMod9_eq_zero_iff ⟨_, entry_mem hint 1 0⟩).mpr h10,
      (redMod9_eq_one_iff ⟨_, entry_mem hint 1 1⟩).mpr h11]
  · intro h
    exact ⟨hg, (redMod9_eq_zero_iff ⟨_, entry_mem hint 1 0⟩).mp (congrFun h 0),
      (redMod9_eq_one_iff ⟨_, entry_mem hint 1 1⟩).mp (congrFun h 1)⟩

private theorem inv_two_mem : (2 : K₃)⁻¹ ∈ v₃.adicCompletionIntegers ℚ := by
  show Valued.v (2 : K₃)⁻¹ ≤ 1
  rw [map_inv₀, valued_ofNat_eq_one 2 (by norm_num), inv_one]

-- `1/2 ≡ 5 mod 9`
private theorem redMod9_inv_two : redMod9 ⟨(2 : K₃)⁻¹, inv_two_mem⟩ = 5 := by
  have h : ((2 : ℤ) : v₃.adicCompletionIntegers ℚ) * ⟨(2 : K₃)⁻¹, inv_two_mem⟩ = 1 :=
    Subtype.ext (by
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, Int.cast_ofNat]
      exact mul_inv_cancel₀ (isUnit_two v₃).ne_zero)
  have h' := congrArg redMod9 h
  rw [map_mul, map_intCast, map_one, Int.cast_ofNat] at h'
  calc redMod9 ⟨(2 : K₃)⁻¹, inv_two_mem⟩
      = (5 * 2) * redMod9 ⟨(2 : K₃)⁻¹, inv_two_mem⟩ := by
        rw [show (5 : ZMod 9) * 2 = 1 by decide, one_mul]
    _ = 5 := by rw [mul_assoc, h', mul_one]

-- `ν₃ ≡ 22 ≡ 4 mod 9`
private theorem redMod9_ν₃ : redMod9 ⟨ν₃, valued_ν₃.le⟩ = 4 := by
  have h22 : (((22 : ℤ) : v₃.adicCompletionIntegers ℚ) : K₃) = 22 := by
    rw [SubringClass.coe_intCast, Int.cast_ofNat]
  have hsub : redMod9 (⟨ν₃, valued_ν₃.le⟩ - ((22 : ℤ) : v₃.adicCompletionIntegers ℚ)) = 0 := by
    rw [redMod9_eq_zero_iff, AddSubgroupClass.coe_sub, h22]
    refine valued_ν₃_sub_twentyTwo.trans ?_
    rw [Rat.cast_ofNat, Rat.cast_ofNat, show (27 : K₃) = 3 * 9 by norm_num, map_mul]
    refine mul_le_of_le_one_left' ?_
    rw [valued_three, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  rw [map_sub, sub_eq_zero, map_intCast] at hsub
  rw [hsub]
  decide

-- an entry `a/2 + (b/2) ν₃` of `θ₃` on a Hurwitz quaternion reduces to `5 (a + 4b)`
private theorem redMod9_half {x : K₃} (hx : x ∈ v₃.adicCompletionIntegers ℚ) (a b : ℤ)
    (h : x = (a : K₃) / 2 + (b : K₃) / 2 * ν₃) :
    redMod9 ⟨x, hx⟩ = 5 * ((a : ZMod 9) + 4 * b) := by
  have e : (⟨x, hx⟩ : v₃.adicCompletionIntegers ℚ) =
      (a : v₃.adicCompletionIntegers ℚ) * ⟨(2 : K₃)⁻¹, inv_two_mem⟩ +
        (b : v₃.adicCompletionIntegers ℚ) * ⟨(2 : K₃)⁻¹, inv_two_mem⟩ * ⟨ν₃, valued_ν₃.le⟩ :=
    Subtype.ext (by
      simp only [AddMemClass.coe_add, MulMemClass.coe_mul, SubringClass.coe_intCast]
      rw [h]
      ring)
  rw [e, map_add, map_mul, map_mul, map_mul, map_intCast, map_intCast, redMod9_inv_two,
    redMod9_ν₃]
  ring

-- `θ₃` on the Hurwitz order is the splitting
private theorem coe_hurwitzToMat (x : hurwitzOrder) :
    ((hurwitzToMat x : integralMatrices v₃) : Matrix (Fin 2) (Fin 2) K₃) =
      Quaternion.splitHom (R := ℚ) ν₃ (1 : K₃) sq_ν₃_add_one_sq (x : ℍ[ℚ]) := by
  show RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃) ((x : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : K₃)) = _
  exact (Quaternion.splitEquiv_tmul ν₃ 1 _ _ (x : ℍ[ℚ]) 1).trans (one_smul _ _)

-- `θ₃` modulo `9` of the Hurwitz quaternion with coordinates `(A, B, C, E) / 2`
private def tupleMat (t : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (ZMod 9) :=
  !![5 * (((t.1 + t.2.2.2 : ℤ) : ZMod 9) + 4 * (t.2.1 : ℤ)),
      5 * (((t.2.1 - t.2.2.1 : ℤ) : ZMod 9) + 4 * (-t.2.2.2 : ℤ));
    5 * (((t.2.1 + t.2.2.1 : ℤ) : ZMod 9) + 4 * (-t.2.2.2 : ℤ)),
      5 * (((t.1 - t.2.2.2 : ℤ) : ZMod 9) + 4 * (-t.2.1 : ℤ))]

private theorem coe_unitsMod9 {γ : (hurwitzOrder)ˣ} {t : ℤ × ℤ × ℤ × ℤ}
    (ht : ofTuple t = ((γ : hurwitzOrder) : ℍ[ℚ])) :
    (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) = tupleMat t := by
  obtain ⟨A, B, C, E⟩ := t
  have hθ := coe_hurwitzToMat (γ : hurwitzOrder)
  rw [← ht, Quaternion.splitHom_apply] at hθ
  have hmem := (hurwitzToMat (γ : hurwitzOrder)).2
  have hentry : ∀ i j, (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) i j =
      redMod9 ⟨(hurwitzToMat (γ : hurwitzOrder) : Matrix (Fin 2) (Fin 2) K₃) i j,
        entry_mem hmem i j⟩ := fun _ _ => rfl
  have h00 : (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) 0 0 = tupleMat (A, B, C, E) 0 0 := by
    rw [hentry, redMod9_half (entry_mem hmem 0 0) (A + E) B (by
      rw [hθ]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
        Matrix.cons_val_fin_one, ofTuple_re, ofTuple_imI, ofTuple_imK, map_div₀, map_intCast,
        map_ofNat, Int.cast_add]
      ring)]
    rfl
  have h01 : (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) 0 1 = tupleMat (A, B, C, E) 0 1 := by
    rw [hentry, redMod9_half (entry_mem hmem 0 1) (B - C) (-E) (by
      rw [hθ]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, ofTuple_imI, ofTuple_imJ, ofTuple_imK,
        map_div₀, map_intCast, map_ofNat, Int.cast_sub, Int.cast_neg]
      ring)]
    rfl
  have h10 : (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) 1 0 = tupleMat (A, B, C, E) 1 0 := by
    rw [hentry, redMod9_half (entry_mem hmem 1 0) (B + C) (-E) (by
      rw [hθ]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, ofTuple_imI, ofTuple_imJ, ofTuple_imK,
        map_div₀, map_intCast, map_ofNat, Int.cast_add, Int.cast_neg]
      ring)]
    rfl
  have h11 : (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) 1 1 = tupleMat (A, B, C, E) 1 1 := by
    rw [hentry, redMod9_half (entry_mem hmem 1 1) (A - E) (-B) (by
      rw [hθ]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, ofTuple_re, ofTuple_imI, ofTuple_imK, map_div₀, map_intCast,
        map_ofNat, Int.cast_sub, Int.cast_neg]
      ring)]
    rfl
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

-- the Hurwitz units modulo `9` are the matrices of the `24` unit tuples
private theorem exists_unitsMod9_iff (P : Matrix (Fin 2) (Fin 2) (ZMod 9) → Prop) :
    (∃ γ : (hurwitzOrder)ˣ, P (unitsMod9 γ)) ↔ ∃ t ∈ unitTuples, P (tupleMat t) := by
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨t, ht, hx⟩ := exists_tuple_of_unit γ
    refine ⟨t, ht, ?_⟩
    rw [← coe_unitsMod9 hx]
    exact hγ
  · rintro ⟨t, ht, hP⟩
    refine ⟨(isUnit_ofTuple ht).unit, ?_⟩
    rw [coe_unitsMod9 (γ := (isUnit_ofTuple ht).unit) (t := t) rfl]
    exact hP

private theorem classDiag_snd_inv (i : Fin 3) :
    (((classDiag i).2 : ℤ) : ZMod 9)⁻¹ = ![1, 5, 7] i :=
  ZMod.inv_eq_of_mul_eq_one 9 _ _ (by fin_cases i <;> decide)

set_option maxRecDepth 100000 in
-- the orbit computation, as a finite check over the `24 × 72` table
private theorem orbits_tupleMat : ∀ x ∈ primitiveVectors, ∃ i : Fin 3,
    (∃ t ∈ unitTuples, Matrix.vecMul ![x.1, x.2] (tupleMat t) = ![0, ![1, 5, 7] i]) ∧
      ∀ j : Fin 3, (∃ t ∈ unitTuples,
        Matrix.vecMul ![x.1, x.2] (tupleMat t) = ![0, ![1, 5, 7] j]) → j = i := by
  decide

set_option maxRecDepth 100000 in
private theorem only_one_tupleMat : ∀ i : Fin 3, ∀ t ∈ unitTuples,
    Matrix.vecMul ![0, ![1, 5, 7] i] (tupleMat t) = ![0, ![1, 5, 7] i] → t = (2, 0, 0, 0) := by
  decide

/-- **The three orbits**: every primitive vector is, up to a Hurwitz unit, exactly one of the three
bottom rows `(0, d_i⁻¹)` of the `c_i⁻¹`. -/
theorem existsUnique_orbit {x : ZMod 9 × ZMod 9} (hx : x ∈ primitiveVectors) :
    ∃! i : Fin 3, ∃ γ : (hurwitzOrder)ˣ,
      Matrix.vecMul ![x.1, x.2] (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) =
        ![0, (((classDiag i).2 : ℤ) : ZMod 9)⁻¹] := by
  simp only [classDiag_snd_inv]
  obtain ⟨i, hi, huniq⟩ := orbits_tupleMat x hx
  exact ⟨i, (exists_unitsMod9_iff fun M => Matrix.vecMul ![x.1, x.2] M = ![0, ![1, 5, 7] i]).mpr hi,
    fun j hj => huniq j
      ((exists_unitsMod9_iff fun M => Matrix.vecMul ![x.1, x.2] M = ![0, ![1, 5, 7] j]).mp hj)⟩

/-- Only the identity Hurwitz unit fixes one of the three bottom rows. -/
theorem eq_one_of_vecMul_unitsMod9 {i : Fin 3} {γ : (hurwitzOrder)ˣ}
    (h : Matrix.vecMul ![0, (((classDiag i).2 : ℤ) : ZMod 9)⁻¹]
      (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) =
        ![0, (((classDiag i).2 : ℤ) : ZMod 9)⁻¹]) : γ = 1 := by
  obtain ⟨t, ht, hx⟩ := exists_tuple_of_unit γ
  rw [classDiag_snd_inv, coe_unitsMod9 hx] at h
  obtain rfl := only_one_tupleMat i t ht h
  refine Units.ext (Subtype.ext ?_)
  rw [← hx]
  ext <;> norm_num [ofTuple]

private theorem toMatrix_mem_integralMatrices {u : Dfx ℚ ℍ[ℚ]} (hu : u ∈ U0) :
    toMatrix ℚ ℍ[ℚ] v₃ u ∈ integralMatrices v₃ :=
  (toGL_mem_integralGL v₃ theta3_isIntegral hu).1

-- `θ₃` modulo `9` on `U₀(1)`
private def redU0 : U0 →* Matrix (Fin 2) (Fin 2) (ZMod 9) where
  toFun u := redMat ⟨toMatrix ℚ ℍ[ℚ] v₃ u, toMatrix_mem_integralMatrices u.2⟩
  map_one' := by
    rw [← map_one redMat]
    exact congrArg redMat (Subtype.ext (map_one (toMatrix ℚ ℍ[ℚ] v₃)))
  map_mul' u u' := by
    rw [← map_mul redMat]
    exact congrArg redMat
      (Subtype.ext (map_mul (toMatrix ℚ ℍ[ℚ] v₃) (u : Dfx ℚ ℍ[ℚ]) (u' : Dfx ℚ ℍ[ℚ])))

private theorem isUnit_redU0 (u : U0) : IsUnit (redU0 u) :=
  (redU0.toHomUnits u).isUnit

-- over `ℤ/9` the units are the residues prime to `3`
private theorem isUnit_iff_ne_zero_mod_three :
    ∀ x : ZMod 9, IsUnit x ↔ ZMod.castHom (show 3 ∣ 9 by norm_num) (ZMod 3) x ≠ 0 := by
  decide

-- the bottom row of an invertible matrix over `ℤ/9` is primitive
private theorem mem_primitiveVectors_of_isUnit {N : Matrix (Fin 2) (Fin 2) (ZMod 9)}
    (hN : IsUnit N) : (N 1 0, N 1 1) ∈ primitiveVectors := by
  have hdet := (Matrix.isUnit_iff_isUnit_det N).mp hN
  rw [isUnit_iff_ne_zero_mod_three, Matrix.det_fin_two, map_sub, map_mul, map_mul] at hdet
  simp only [primitiveVectors, Finset.mem_filter, Finset.mem_univ, true_and,
    isUnit_iff_ne_zero_mod_three]
  by_contra h
  simp only [not_or, ne_eq, not_not] at h
  rw [h.1, h.2, mul_zero, mul_zero, sub_zero] at hdet
  exact hdet rfl

-- the Hurwitz units inside `D_f^×`
private def hurwitzIncl : (hurwitzOrder)ˣ →* Dfx ℚ ℍ[ℚ] :=
  (unitsIncl ℚ ℍ[ℚ]).comp (Units.map hurwitzOrder.subtype.toMonoidHom)

private theorem hurwitzIncl_mem_U0 (γ : (hurwitzOrder)ˣ) : hurwitzIncl γ ∈ U0 := by
  show unitsIncl ℚ ℍ[ℚ] (Units.map hurwitzOrder.subtype.toMonoidHom γ) ∈ U0
  exact unitsIncl_mem_U0_iff.mpr ⟨(γ : hurwitzOrder).2, ((γ⁻¹ : (hurwitzOrder)ˣ) : hurwitzOrder).2⟩

private theorem hurwitzIncl_mem_globalUnits (γ : (hurwitzOrder)ˣ) :
    hurwitzIncl γ ∈ globalUnits ℚ ℍ[ℚ] :=
  ⟨Units.map hurwitzOrder.subtype.toMonoidHom γ, rfl⟩

-- `D^× ∩ U₀(1)` consists of the Hurwitz units
private theorem exists_hurwitzIncl_eq {d : Dfx ℚ ℍ[ℚ]} (hd : d ∈ globalUnits ℚ ℍ[ℚ])
    (hd0 : d ∈ U0) : ∃ γ : (hurwitzOrder)ˣ, hurwitzIncl γ = d := by
  obtain ⟨δ, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := unitsIncl_mem_U0_iff.mp hd0
  refine ⟨⟨⟨δ, h1⟩, ⟨↑δ⁻¹, h2⟩, Subtype.ext δ.mul_inv, Subtype.ext δ.inv_mul⟩, ?_⟩
  show unitsIncl ℚ ℍ[ℚ] _ = unitsIncl ℚ ℍ[ℚ] δ
  exact congrArg (unitsIncl ℚ ℍ[ℚ]) (Units.ext rfl)

private theorem redU0_hurwitzIncl (γ : (hurwitzOrder)ˣ) :
    redU0 ⟨hurwitzIncl γ, hurwitzIncl_mem_U0 γ⟩ =
      (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) := by
  show redMat _ = redMat (hurwitzToMat (γ : hurwitzOrder))
  refine congrArg redMat (Subtype.ext ?_)
  show toMatrix ℚ ℍ[ℚ] v₃ (unitsIncl ℚ ℍ[ℚ] (Units.map hurwitzOrder.subtype.toMonoidHom γ)) = _
  rw [toMatrix_unitsIncl, coe_hurwitzToMat]
  rfl

-- `redMat` on a diagonal matrix of integers
private theorem redMat_diagonal {M : Matrix (Fin 2) (Fin 2) K₃} (hM : M ∈ integralMatrices v₃)
    (x y : ℤ) (h : M = Matrix.diagonal ![((x : ℚ) : K₃), ((y : ℚ) : K₃)]) :
    redMat ⟨M, hM⟩ = Matrix.diagonal ![(x : ZMod 9), (y : ZMod 9)] := by
  subst h
  refine Matrix.ext fun a b => ?_
  rw [redMat_apply]
  fin_cases a <;> fin_cases b
  · exact redMod9_intCast x _
  · exact redMod9_zero' _
  · exact redMod9_zero' _
  · exact redMod9_intCast y _

private theorem redU0_classRep (i : Fin 3) :
    redU0 ⟨classRep i, classRep_mem_U0 i⟩ =
      Matrix.diagonal ![((classDiag i).1 : ZMod 9), ((classDiag i).2 : ZMod 9)] := by
  show redMat _ = _
  exact redMat_diagonal _ _ _ (toMatrix_classRep i)

-- `r · diag(xᵢ, yᵢ) = (0, 1)` exactly when `r = (0, yᵢ⁻¹)`
private theorem vecMul_diag_eq_iff : ∀ (i : Fin 3) (r₀ r₁ : ZMod 9),
    Matrix.vecMul ![r₀, r₁]
        (Matrix.diagonal ![((classDiag i).1 : ZMod 9), ((classDiag i).2 : ZMod 9)]) = ![0, 1] ↔
      ![r₀, r₁] = ![0, ![1, 5, 7] i] := by
  decide

-- `u cᵢ ∈ U₁(9)` exactly when the bottom row of `θ₃(u)` modulo `9` is `(0, yᵢ⁻¹)`
private theorem mul_classRep_mem_U1_9_iff {u : Dfx ℚ ℍ[ℚ]} (hu : u ∈ U0) (i : Fin 3) :
    u * classRep i ∈ U1_9 ↔ Matrix.vecMul ![0, 1] (redU0 ⟨u, hu⟩) = ![0, ![1, 5, 7] i] := by
  have hmem := mul_mem hu (classRep_mem_U0 i)
  have e : redMat ⟨toMatrix ℚ ℍ[ℚ] v₃ (u * classRep i), toMatrix_mem_integralMatrices hmem⟩ =
      redU0 ⟨u, hu⟩ *
        Matrix.diagonal ![((classDiag i).1 : ZMod 9), ((classDiag i).2 : ZMod 9)] := by
    rw [← redU0_classRep i, ← map_mul]
    rfl
  rw [mem_U1_9_iff_bottomRow hmem (toMatrix_mem_integralMatrices hmem), e,
    ← Matrix.vecMul_vecMul, vecMul_zero_one (redU0 ⟨u, hu⟩)]
  exact vecMul_diag_eq_iff i _ _

-- `c_j⁻¹ γ cᵢ ∈ U₁(9)` makes `γ` carry `(0, y_j⁻¹)` to `(0, yᵢ⁻¹)` modulo `9`
private theorem vecMul_unitsMod9_of_mem {i j : Fin 3} {γ : (hurwitzOrder)ˣ}
    (h : (classRep j)⁻¹ * hurwitzIncl γ * classRep i ∈ U1_9) :
    Matrix.vecMul ![0, ![1, 5, 7] j] (unitsMod9 γ : Matrix (Fin 2) (Fin 2) (ZMod 9)) =
      ![0, ![1, 5, 7] i] := by
  have hj := inv_mem (classRep_mem_U0 j)
  have hmem := mul_mem hj (hurwitzIncl_mem_U0 γ)
  have h1 := (mul_classRep_mem_U1_9_iff hmem i).mp h
  have h2 := (mul_classRep_mem_U1_9_iff hj j).mp (by rw [inv_mul_cancel]; exact one_mem _)
  rwa [show (⟨(classRep j)⁻¹ * hurwitzIncl γ, hmem⟩ : U0) =
      ⟨(classRep j)⁻¹, hj⟩ * ⟨hurwitzIncl γ, hurwitzIncl_mem_U0 γ⟩ from rfl, map_mul,
    redU0_hurwitzIncl, ← Matrix.vecMul_vecMul, h2] at h1

/-- The three representatives meet every double coset. -/
theorem isCompleteFamily_classRep : IsCompleteFamily classRep U1_9 := by
  intro g
  obtain ⟨d, hd, u, hu, rfl⟩ := exists_factor g
  -- the bottom row of `θ₃(u⁻¹)` modulo `9` is primitive, hence in one of the three orbits
  obtain ⟨i, ⟨γ, hγ⟩, -⟩ := existsUnique_orbit (mem_primitiveVectors_of_isUnit
    (isUnit_redU0 (⟨u, hu⟩⁻¹ : U0)))
  refine ⟨i, d * hurwitzIncl γ, mul_mem hd (hurwitzIncl_mem_globalUnits γ),
    (classRep i)⁻¹ * (hurwitzIncl γ)⁻¹ * u, ?_, by group⟩
  have hmem : u⁻¹ * hurwitzIncl γ ∈ U0 := mul_mem (inv_mem hu) (hurwitzIncl_mem_U0 γ)
  rw [← inv_mem_iff, show ((classRep i)⁻¹ * (hurwitzIncl γ)⁻¹ * u)⁻¹ =
      u⁻¹ * hurwitzIncl γ * classRep i by group, mul_classRep_mem_U1_9_iff hmem,
    show (⟨u⁻¹ * hurwitzIncl γ, hmem⟩ : U0) =
      (⟨u, hu⟩ : U0)⁻¹ * ⟨hurwitzIncl γ, hurwitzIncl_mem_U0 γ⟩ from rfl, map_mul,
    redU0_hurwitzIncl, ← Matrix.vecMul_vecMul, vecMul_zero_one, ← classDiag_snd_inv]
  exact hγ

/-- **The class set of `U₁(9)` has exactly the three elements `c₀, c₁, c₂`.** -/
theorem isSection_classRep : IsSection classRep U1_9 := by
  refine isSection_iff.mpr ⟨isCompleteFamily_classRep, fun i j hij => ?_⟩
  obtain ⟨d, hd, w, hw, h⟩ := hij
  -- `d = c_j w⁻¹ cᵢ⁻¹` is a Hurwitz unit carrying `(0, y_j⁻¹)` to `(0, yᵢ⁻¹)`
  have hd0 : d ∈ U0 := by
    rw [show d = classRep j * w⁻¹ * (classRep i)⁻¹ by rw [h]; group]
    exact mul_mem (mul_mem (classRep_mem_U0 j) (inv_mem (U1_9_le_U0 hw)))
      (inv_mem (classRep_mem_U0 i))
  obtain ⟨γ, rfl⟩ := exists_hurwitzIncl_eq hd hd0
  have hγ := vecMul_unitsMod9_of_mem (i := i) (j := j) (γ := γ) (by
    rw [show (classRep j)⁻¹ * hurwitzIncl γ * classRep i = w⁻¹ by rw [h]; group]
    exact inv_mem hw)
  -- so `(0, y_j⁻¹)` lies in the orbits of both `i` and `j`
  have hx : ∀ k : Fin 3, ((0 : ZMod 9), ![1, 5, 7] k) ∈ primitiveVectors := by decide
  obtain ⟨k, -, hk⟩ := existsUnique_orbit (hx j)
  refine (hk i ⟨γ, ?_⟩).trans (hk j ⟨1, ?_⟩).symm
  · rw [classDiag_snd_inv]
    exact hγ
  · simp only [classDiag_snd_inv, map_one, Units.val_one, Matrix.vecMul_one]

/-- The class set of `U₁(9)` has three elements. -/
theorem card_classSet_U1_9 : Nat.card (classSet ℚ ℍ[ℚ] U1_9) = 3 := by
  rw [← Nat.card_eq_of_bijective _ isSection_classRep, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **The three stabilisers are trivial.** -/
theorem stabilizer_classRep (i : Fin 3) : stabilizer (classRep i) U1_9 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun u hu' => ?_
  obtain ⟨hu, hd⟩ := hu'
  -- `cᵢ u cᵢ⁻¹` is a Hurwitz unit fixing `(0, yᵢ⁻¹)` modulo `9`, so it is `1`
  obtain ⟨γ, hγ⟩ := exists_hurwitzIncl_eq hd (mul_mem (mul_mem (classRep_mem_U0 i)
    (U1_9_le_U0 hu)) (inv_mem (classRep_mem_U0 i)))
  have h1 := vecMul_unitsMod9_of_mem (i := i) (j := i) (γ := γ) (by
    rw [hγ, show (classRep i)⁻¹ * (classRep i * u * (classRep i)⁻¹) * classRep i = u by group]
    exact hu)
  have hγ1 : γ = 1 := eq_one_of_vecMul_unitsMod9 (i := i) (by rw [classDiag_snd_inv]; exact h1)
  calc u = (classRep i)⁻¹ * (classRep i * u * (classRep i)⁻¹) * classRep i := by group
    _ = 1 := by rw [← hγ, hγ1, map_one]; group

end Hamilton
