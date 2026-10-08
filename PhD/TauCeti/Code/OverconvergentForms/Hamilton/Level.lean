/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Hamilton.Setting
import PhD.TauCeti.Code.OverconvergentForms.Quaternion.Hurwitz
import PhD.TauCeti.Code.OverconvergentForms.Level.HeckePair

/-!
# The levels `U₀(1)` and `U₁(9)` of Hamilton's quaternions

The Hurwitz order is presented by the basis `1, i, j, ω`; `U₀(1)` is the unit group of its adelic
completion, the rigidification `θ₃` is integral for it, and `U₁(9)` is the standard level at `3`
with exponent `2`. Both are compact open, and `D^× ∩ U₀(1)` is the group of the `24` Hurwitz units.

[Jac03, Definition 1.20]: "`U₁(p^n) = ∏_q W_q` where
`W_p = {((a b), (c d)) ∈ GL₂(ℤ_p) : ((a b), (c d)) ≡ ((∗ ∗), (0 1)) mod p^n}`." [Jac03,
Proposition 1.21]: "For all `n ∈ ℕ`, `U₀(p^n)` and `U₁(p^n)` are open compact subgroups of `D_f^×`."

## Main definitions

* `Hamilton.hurwitzBasis`, `Hamilton.U0`, `Hamilton.U1_9`.

## Main results

* `Hamilton.hurwitzBasis_apply`, `Hamilton.isOrderBasis_hurwitzBasis`,
  `Hamilton.orderOf_hurwitzBasis`: the order presented by the basis is the Hurwitz order;
  `Hamilton.unitsIncl_mem_U0_iff`.
* `Hamilton.imI_mem_hurwitzOrder`, `Hamilton.imJ_mem_hurwitzOrder`, `Hamilton.imK_mem_hurwitzOrder`,
  `Hamilton.hurwitzOmega_mem_hurwitzOrder`, `Hamilton.exists_int_of_mem_range`,
  `Hamilton.tmul_mem_localOrder`.
* `Hamilton.theta3_isIntegral`: `θ₃(𝒪 ⊗ ℤ_3) = M₂(ℤ_3)`.
* `Hamilton.valued_nine`, `Hamilton.mem_U1_9_iff`, `Hamilton.U1_9_le_U0`, `Hamilton.isCompact_U1_9`,
  `Hamilton.isOpen_U1_9`, `Hamilton.mem_U1_9_of_toGL`.

Roadmap: §0.5. Tau Ceti home: `TauCeti/NumberTheory/AutomorphicForm/Hamilton/Level.lean`.
-/

open scoped Quaternion TensorProduct WithZero
open IsDedekindDomain NumberField AdelicAlgebra Quaternion

noncomputable section

namespace Hamilton

open scoped AdelicAlgebra.RightAlgebra

-- the coordinates `(re − k, i − k, j − k, 2k)` in the basis `1, i, j, ω = (1 + i + j + k)/2`
private def hurwitzCoords : ℍ[ℚ] ≃ₗ[ℚ] (Fin 4 → ℚ) where
  toFun x := ![x.re - x.imK, x.imI - x.imK, x.imJ - x.imK, 2 * x.imK]
  invFun c := ⟨c 0 + c 3 / 2, c 1 + c 3 / 2, c 2 + c 3 / 2, c 3 / 2⟩
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' r x := by
    funext i
    fin_cases i <;> simp <;> ring
  left_inv x := by
    ext <;> simp
  right_inv c := by
    funext i
    fin_cases i <;> simp
    ring

private theorem hurwitzCoords_symm_apply (c : Fin 4 → ℚ) :
    hurwitzCoords.symm c = ⟨c 0 + c 3 / 2, c 1 + c 3 / 2, c 2 + c 3 / 2, c 3 / 2⟩ :=
  rfl

/-- **The basis `1, i, j, ω` of `ℍ[ℚ]`**, a `ℤ`-basis of the Hurwitz order. -/
def hurwitzBasis : Module.Basis (Fin 4) ℚ ℍ[ℚ] :=
  Module.Basis.ofEquivFun hurwitzCoords

/-- The Hurwitz basis is `1, i, j, ω`. -/
theorem hurwitzBasis_apply (i : Fin 4) :
    hurwitzBasis i = ![(1 : ℍ[ℚ]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, hurwitzOmega] i := by
  simp only [hurwitzBasis, Module.Basis.coe_ofEquivFun, hurwitzCoords_symm_apply]
  fin_cases i <;> ext <;> simp [hurwitzOmega]

private theorem hurwitzBasis_repr (x : ℍ[ℚ]) (k : Fin 4) :
    hurwitzBasis.repr x k = ![x.re - x.imK, x.imI - x.imK, x.imJ - x.imK, 2 * x.imK] k := by
  rw [hurwitzBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

private theorem intCast_mem_range (n : ℤ) : (n : ℚ) ∈ (algebraMap (𝓞 ℚ) ℚ).range :=
  ⟨n, map_intCast _ n⟩

/-- An element of `𝓞 ℚ`, read in `ℚ`, is an integer. -/
theorem exists_int_of_mem_range {c : ℚ} (hc : c ∈ (algebraMap (𝓞 ℚ) ℚ).range) :
    ∃ n : ℤ, c = n := by
  obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hc
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (NumberField.RingOfIntegers.isIntegral_coe r)
  exact ⟨n, by rw [← hn, eq_intCast]⟩

-- a Hurwitz quaternion has integral Hurwitz coordinates: all four coordinates of `2x` have the
-- parity of `2x.imK`
private theorem repr_mem_of_mem_hurwitzOrder {x : ℍ[ℚ]} (hx : x ∈ hurwitzOrder) (k : Fin 4) :
    hurwitzBasis.repr x k ∈ (algebraMap (𝓞 ℚ) ℚ).range := by
  obtain ⟨A, B, C, D, hr, hi, hj, hk, hAB, hBC, hCD⟩ := mem_hurwitzOrder_iff.mp hx
  obtain ⟨a, ha⟩ : ∃ a : ℤ, A = D + 2 * a := ⟨(A - D) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, B = D + 2 * b := ⟨(B - D) / 2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c : ℤ, C = D + 2 * c := ⟨(C - D) / 2, by omega⟩
  rw [hurwitzBasis_repr]
  fin_cases k
  · convert intCast_mem_range a using 1
    simp [hr, hk, ha]
    ring
  · convert intCast_mem_range b using 1
    simp [hi, hk, hb]
    ring
  · convert intCast_mem_range c using 1
    simp [hj, hk, hc]
    ring
  · convert intCast_mem_range D using 1
    simp [hk]
    ring

/-- `i` is a Hurwitz quaternion. -/
theorem imI_mem_hurwitzOrder : (⟨0, 1, 0, 0⟩ : ℍ[ℚ]) ∈ hurwitzOrder :=
  mem_hurwitzOrder_iff.mpr ⟨0, 2, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- `j` is a Hurwitz quaternion. -/
theorem imJ_mem_hurwitzOrder : (⟨0, 0, 1, 0⟩ : ℍ[ℚ]) ∈ hurwitzOrder :=
  mem_hurwitzOrder_iff.mpr ⟨0, 0, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- `k` is a Hurwitz quaternion. -/
theorem imK_mem_hurwitzOrder : (⟨0, 0, 0, 1⟩ : ℍ[ℚ]) ∈ hurwitzOrder :=
  mem_hurwitzOrder_iff.mpr ⟨0, 0, 0, 2, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- `ω = (1 + i + j + k)/2` is a Hurwitz quaternion. -/
theorem hurwitzOmega_mem_hurwitzOrder : hurwitzOmega ∈ hurwitzOrder :=
  mem_hurwitzOrder_iff.mpr ⟨1, 1, 1, 1, by norm_num [hurwitzOmega], by norm_num [hurwitzOmega],
    by norm_num [hurwitzOmega], by norm_num [hurwitzOmega], by norm_num, by norm_num, by norm_num⟩

private theorem hurwitzBasis_mem (i : Fin 4) : hurwitzBasis i ∈ hurwitzOrder := by
  rw [hurwitzBasis_apply]
  fin_cases i
  exacts [one_mem _, imI_mem_hurwitzOrder, imJ_mem_hurwitzOrder, hurwitzOmega_mem_hurwitzOrder]

/-- **The Hurwitz basis presents an order.** -/
theorem isOrderBasis_hurwitzBasis : IsOrderBasis hurwitzBasis :=
  ⟨repr_mem_of_mem_hurwitzOrder (one_mem _), fun i j =>
    repr_mem_of_mem_hurwitzOrder (mul_mem (hurwitzBasis_mem i) (hurwitzBasis_mem j))⟩

/-- **The order presented by the Hurwitz basis is the Hurwitz order.** -/
theorem orderOf_hurwitzBasis : orderOf hurwitzBasis isOrderBasis_hurwitzBasis = hurwitzOrder := by
  refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => repr_mem_of_mem_hurwitzOrder hx⟩
  choose n hn using fun k => exists_int_of_mem_range (mem_orderOf_iff.mp hx k)
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  simp only [hurwitzBasis_repr] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  refine mem_hurwitzOrder_iff.mpr ⟨2 * n 0 + n 3, 2 * n 1 + n 3, 2 * n 2 + n 3, n 3, ?_, ?_, ?_,
    ?_, by omega, by omega, by omega⟩ <;> push_cast <;> linarith

/-- **`U₀(1)`**, the units of the adelic Hurwitz order. -/
abbrev U0 : Subgroup (Dfx ℚ ℍ[ℚ]) := AdelicAlgebra.U0 hurwitzBasis isOrderBasis_hurwitzBasis

/-- **`D^× ∩ U₀(1)` is the group of Hurwitz units.** -/
theorem unitsIncl_mem_U0_iff {x : (ℍ[ℚ])ˣ} :
    unitsIncl ℚ ℍ[ℚ] x ∈ U0 ↔
      (x : ℍ[ℚ]) ∈ hurwitzOrder ∧ ((x⁻¹ : (ℍ[ℚ])ˣ) : ℍ[ℚ]) ∈ hurwitzOrder := by
  rw [AdelicAlgebra.unitsIncl_mem_U0_iff, orderOf_hurwitzBasis]

/-- A Hurwitz quaternion tensored with a local integer lies in the local order. -/
theorem tmul_mem_localOrder {w : HeightOneSpectrum (𝓞 ℚ)} {d : ℍ[ℚ]} (hd : d ∈ hurwitzOrder)
    {z : w.adicCompletion ℚ} (hz : z ∈ w.adicCompletionIntegers ℚ) :
    d ⊗ₜ[ℚ] z ∈ localOrder hurwitzBasis isOrderBasis_hurwitzBasis w := by
  rw [← orderOf_hurwitzBasis] at hd
  refine mem_localOrder_iff.mpr fun i => ?_
  obtain ⟨n, hn⟩ := exists_int_of_mem_range (mem_orderOf_iff.mp hd i)
  rw [rightBasis_repr_tmul, hn, map_intCast]
  exact mul_mem hz (intCast_mem _ n)

/-- **`θ₃` is integral for the Hurwitz order**: `θ₃(𝒪 ⊗ ℤ_3) = M₂(ℤ_3)`. -/
theorem theta3_isIntegral :
    RigidificationAt.IsIntegral hurwitzBasis isOrderBasis_hurwitzBasis v₃ := by
  have hν := sq_ν₃_add_one_sq
  have hθ : ∀ (x : ℍ[ℚ]) (s : K₃), RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃)
      (x ⊗ₜ[ℚ] s) = s • Quaternion.splitHom (R := ℚ) ν₃ (1 : K₃) hν x :=
    fun x s => Quaternion.splitEquiv_tmul ν₃ 1 hν _ x s
  have hν𝒪 : ν₃ ∈ v₃.adicCompletionIntegers ℚ := valued_ν₃.le
  have h2 : Valued.v (2 : K₃) = 1 := valued_ofNat_eq_one 2 (by norm_num)
  have h2𝒪 : (2 : K₃) ∈ v₃.adicCompletionIntegers ℚ := h2.le
  have hinv2 : (2 : K₃)⁻¹ ∈ v₃.adicCompletionIntegers ℚ := by
    show Valued.v (2 : K₃)⁻¹ ≤ 1
    rw [map_inv₀, h2, inv_one]
  have h2ne : (2 : K₃) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
  -- the images `1, I, J, Ω` of the Hurwitz basis are integral (`ν₃` and `1/2` are)
  have hbasis : ∀ i a b, Quaternion.splitHom (R := ℚ) ν₃ (1 : K₃) hν (hurwitzBasis i) a b ∈
      v₃.adicCompletionIntegers ℚ := by
    intro i a b
    rw [hurwitzBasis_apply, Quaternion.splitHom_apply]
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [hurwitzOmega] <;>
      apply_rules [add_mem, sub_mem, mul_mem, neg_mem, one_mem, zero_mem, hν𝒪, hinv2]
  rw [RigidificationAt.IsIntegral]
  refine Set.ext fun M => ⟨?_, fun hM => ?_⟩
  · rintro ⟨x, hx, rfl⟩
    intro a b
    rw [← (rightBasis (R := K₃) hurwitzBasis).sum_repr x, map_sum, Matrix.sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_smul, rightBasis_apply, hθ, one_smul, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (mem_localOrder_iff.mp hx i) (hbasis i a b)
  · -- the explicit inverse has integral Hurwitz coordinates
    refine ⟨(RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃)).symm M, ?_,
      AlgEquiv.apply_symm_apply _ M⟩
    have hM' : ∀ a b, M a b ∈ v₃.adicCompletionIntegers ℚ := hM
    rw [show RigidificationAt.equiv (F := ℚ) (D := ℍ[ℚ]) (v := v₃) =
        Quaternion.splitEquiv ν₃ 1 hν (IsUnit.mk0 _ h2ne) from rfl,
      Quaternion.splitEquiv_symm_apply ν₃ 1 hν _ (mul_inv_cancel₀ h2ne) M]
    refine sum_mem fun n _ => tmul_mem_localOrder ?_ ?_
    · fin_cases n
      exacts [one_mem _, imI_mem_hurwitzOrder, imJ_mem_hurwitzOrder, imK_mem_hurwitzOrder]
    · fin_cases n
      · show (2 : K₃)⁻¹ * (M 0 0 + M 1 1) ∈ _
        exact mul_mem hinv2 (add_mem (hM' 0 0) (hM' 1 1))
      · show -((2 : K₃)⁻¹ * (M 0 0 - M 1 1) * ν₃ + (2 : K₃)⁻¹ * (M 0 1 + M 1 0) * 1) ∈ _
        exact neg_mem (add_mem (mul_mem (mul_mem hinv2 (sub_mem (hM' 0 0) (hM' 1 1))) hν𝒪)
          (mul_mem (mul_mem hinv2 (add_mem (hM' 0 1) (hM' 1 0))) (one_mem _)))
      · show (2 : K₃)⁻¹ * (M 1 0 - M 0 1) ∈ _
        exact mul_mem hinv2 (sub_mem (hM' 1 0) (hM' 0 1))
      · show (2 : K₃)⁻¹ * (M 0 1 + M 1 0) * ν₃ - (2 : K₃)⁻¹ * (M 0 0 - M 1 1) * 1 ∈ _
        exact sub_mem (mul_mem (mul_mem hinv2 (add_mem (hM' 0 1) (hM' 1 0))) hν𝒪)
          (mul_mem (mul_mem hinv2 (sub_mem (hM' 0 0) (hM' 1 1))) (one_mem _))

/-- `θ₃` at the constant family of places `fun _ : Unit ↦ v₃`. -/
instance (k : Unit) : RigidificationAt ℚ ℍ[ℚ] ((fun _ : Unit ↦ v₃) k) := theta3

/-- **`U₁(9)`**: the standard level at `3` with exponent `2`. -/
@[nolint defsWithUnderscore]
def U1_9 : Subgroup (Dfx ℚ ℍ[ℚ]) :=
  U1Level hurwitzBasis isOrderBasis_hurwitzBasis (fun _ : Unit ↦ v₃) fun _ ↦ 2

/-- `v(9) = v(3)^2` is the threshold of exponent `2`. -/
theorem valued_nine : Valued.v ((9 : ℚ) : K₃) = levelThreshold 2 := by
  rw [Rat.cast_ofNat, show (9 : K₃) = 3 ^ 2 by norm_num, map_pow, valued_three, levelThreshold,
    ← WithZero.exp_nsmul]
  norm_num

/-- **`U₁(9)` in coordinates**: `9 ∣ c` and `d ≡ 1 mod 9`. -/
theorem mem_U1_9_iff {g : Dfx ℚ ℍ[ℚ]} :
    g ∈ U1_9 ↔ g ∈ U0 ∧ Valued.v (toMatrix ℚ ℍ[ℚ] v₃ g 1 0) ≤ Valued.v ((9 : ℚ) : K₃) ∧
      Valued.v (toMatrix ℚ ℍ[ℚ] v₃ g 1 1 - 1) ≤ Valued.v ((9 : ℚ) : K₃) := by
  rw [valued_nine, U1_9, U1Level, standardLevel, Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨hU0, h⟩
    exact ⟨hU0, (mem_levelAt_iff.mp (h ())).1.2.2, (mem_levelAt_iff.mp (h ())).2⟩
  · rintro ⟨hU0, h10, h11⟩
    obtain ⟨hent, hdet⟩ :=
      (mem_integralGL_iff v₃).mp (toGL_mem_integralGL v₃ theta3_isIntegral hU0)
    exact ⟨hU0, fun _ => ⟨⟨hent, hdet, h10⟩, h11⟩⟩

/-- `U₁(9) ⊆ U₀(1)`. -/
theorem U1_9_le_U0 : U1_9 ≤ U0 :=
  fun _ hg => (mem_U1_9_iff.mp hg).1

/-- `U₀(1)` is compact. -/
theorem isCompact_U0 : IsCompact (U0 : Set (Dfx ℚ ℍ[ℚ])) := AdelicAlgebra.isCompact_U0

/-- `U₀(1)` is open. -/
theorem isOpen_U0 : IsOpen (U0 : Set (Dfx ℚ ℍ[ℚ])) := AdelicAlgebra.isOpen_U0

/-- **`U₁(9)` is compact.** -/
theorem isCompact_U1_9 : IsCompact (U1_9 : Set (Dfx ℚ ℍ[ℚ])) :=
  isCompact_U1Level _

/-- **`U₁(9)` is open.** -/
theorem isOpen_U1_9 : IsOpen (U1_9 : Set (Dfx ℚ ℍ[ℚ])) :=
  isOpen_U1Level _

/-- An element of `D_f^×` is in `U₁(9)` as soon as it is integral away from `3` and `θ₃` of it is
in `Iw₁(9)`. -/
theorem mem_U1_9_of_toGL {g : Dfx ℚ ℍ[ℚ]}
    (h3 : toGL ℚ ℍ[ℚ] v₃ g ∈ LocalLevel.iwahoriOne K₃ (levelThreshold 2))
    (haway : ∀ w, w ≠ v₃ →
      toLocalUnits ℚ ℍ[ℚ] w g ∈ localUnits hurwitzBasis isOrderBasis_hurwitzBasis w) :
    g ∈ U1_9 := by
  have hU0 : g ∈ U0 := mem_U0_of_toGL v₃ theta3_isIntegral
    ((mem_integralGL_iff v₃).mpr ⟨h3.1.1, h3.1.2.1⟩) haway
  rw [U1_9, U1Level, standardLevel, Subgroup.mem_inf, Subgroup.mem_iInf]
  exact ⟨hU0, fun _ => h3⟩

end Hamilton
