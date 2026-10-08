/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Hamilton.EtaDecomposition

/-!
# The nine factorisations `c_i x_t⁻¹ = d(i,t) c_{σ(i,t)} u(i,t)`

The certificate of the Hecke operator `U_3` at level `U₁(9)`: for each class `i` and coset `t`, the
element `c_i x_t⁻¹` factors as `d(i,t) · c_{σ(i,t)} · u(i,t)` with `d(i,t) ∈ D^×` of reduced norm
`1/3` and `u(i,t) ∈ U₁(9)`.

[Jac03, Lemmas 2.4–2.5 and §B.1]: the factorisations, with `d(i,t) = ± h/3` for
`h ∈ {1 + i − j, (−1 + i + 3j + k)/2, −(1 + 3i + j + k)/2}` and
`σ = ((2, 1, 1), (0, 2, 2), (1, 0, 0))`.

## Main definitions

* `Hamilton.hA`, `Hamilton.hB`, `Hamilton.hC`, `Hamilton.third`: the quaternions `h` and the units
  `h/3`.
* `Hamilton.sigmaTable`, `Hamilton.dTable`, `Hamilton.uCand`.

## Main results

* `Hamilton.nrd_hA`, `Hamilton.nrd_hB`, `Hamilton.nrd_hC`, `Hamilton.nrd_dTable`: the reduced norms.
* `Hamilton.uCand_away`, `Hamilton.toGL_uCand_mem`: `u(i,t)` away from `3` and at `3`; the nine
  matrix computations at `3` are one certificate (`ν₃ ≡ 22 mod 27`) and three divisibilities each.
* `Hamilton.uCand_mem`: `u(i,t) ∈ U₁(9)`.
* `Hamilton.factorisation`: `c_i x_t⁻¹ = d(i,t) · c_{σ(i,t)} · u(i,t)`.

Roadmap: §0.5.5. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Hamilton/Factorisations.lean`.
-/

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField AdelicAlgebra Quaternion QuaternionAlgebra

noncomputable section

namespace Hamilton

open scoped AdelicAlgebra.RightAlgebra

/-- `h_A = 1 + i − j`. -/
def hA : ℍ[ℚ] := ⟨1, 1, -1, 0⟩

/-- `h_B = (−1 + i + 3j + k)/2`. -/
def hB : ℍ[ℚ] := ⟨-(1 / 2), 1 / 2, 3 / 2, 1 / 2⟩

/-- `h_C = −(1 + 3i + j + k)/2`. -/
def hC : ℍ[ℚ] := ⟨-(1 / 2), -(3 / 2), -(1 / 2), -(1 / 2)⟩

/-- `h_A` is a Hurwitz quaternion. -/
theorem hA_mem : hA ∈ hurwitzOrder :=
  mem_hurwitzOrder_iff.mpr ⟨2, 2, -2, 0, by norm_num [hA], by norm_num [hA], by norm_num [hA],
    by norm_num [hA], by norm_num, by norm_num, by norm_num⟩

/-- `h_B` is a Hurwitz quaternion. -/
theorem hB_mem : hB ∈ hurwitzOrder :=
  mem_hurwitzOrder_iff.mpr ⟨-1, 1, 3, 1, by norm_num [hB], by norm_num [hB], by norm_num [hB],
    by norm_num [hB], by norm_num, by norm_num, by norm_num⟩

/-- `h_C` is a Hurwitz quaternion. -/
theorem hC_mem : hC ∈ hurwitzOrder :=
  mem_hurwitzOrder_iff.mpr ⟨-1, -3, -1, -1, by norm_num [hC], by norm_num [hC], by norm_num [hC],
    by norm_num [hC], by norm_num, by norm_num, by norm_num⟩

/-- `nrd h_A = 3`. -/
theorem nrd_hA : nrd hA = 3 :=
  (nrd_apply hA).trans (by norm_num [hA])

/-- `nrd h_B = 3`. -/
theorem nrd_hB : nrd hB = 3 :=
  (nrd_apply hB).trans (by norm_num [hB])

/-- `nrd h_C = 3`. -/
theorem nrd_hC : nrd hC = 3 :=
  (nrd_apply hC).trans (by norm_num [hC])

/-- The unit `h/3` of `ℍ[ℚ]`, for `h` of reduced norm `3`; its inverse is `h̄`. -/
def third (h : ℍ[ℚ]) (hh : nrd h = 3) : (ℍ[ℚ])ˣ :=
  ⟨(3⁻¹ : ℚ) • h, star h, by
    rw [smul_mul_assoc, Quaternion.self_mul_star, ← nrd_eq_normSq, hh]
    ext <;> norm_num, by
    rw [mul_smul_comm, Quaternion.star_mul_self, ← nrd_eq_normSq, hh]
    ext <;> norm_num⟩

/-- **The class-index table `σ(i, t)`.** -/
def sigmaTable : Fin 3 → Fin 3 → Fin 3 := ![![2, 1, 1], ![0, 2, 2], ![1, 0, 0]]

/-- The diagonal never occurs. -/
theorem sigmaTable_ne (i t : Fin 3) : sigmaTable i t ≠ i := by
  fin_cases i <;> fin_cases t <;> decide

/-- **The global factors `d(i, t) = ± h/3`.** -/
def dTable : Fin 3 → Fin 3 → (ℍ[ℚ])ˣ :=
  ![![-third hA nrd_hA, third hC nrd_hC, third hB nrd_hB],
    ![third hA nrd_hA, third hC nrd_hC, third hB nrd_hB],
    ![third hA nrd_hA, -third hC nrd_hC, -third hB nrd_hB]]

private theorem nrd_third (h : ℍ[ℚ]) (hh : nrd h = 3) :
    nrd ((third h hh : (ℍ[ℚ])ˣ) : ℍ[ℚ]) = 1 / 3 := by
  have hh' := (nrd_apply h).symm.trans hh
  refine (nrd_apply _).trans ?_
  simp only [third, Units.val_mk, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
    Quaternion.imK_smul, smul_eq_mul]
  linear_combination (1 / 9 : ℚ) * hh'

private theorem nrd_neg_third (h : ℍ[ℚ]) (hh : nrd h = 3) :
    nrd ((-third h hh : (ℍ[ℚ])ˣ) : ℍ[ℚ]) = 1 / 3 := by
  have e : ((-third h hh : (ℍ[ℚ])ˣ) : ℍ[ℚ]) = (-1 : ℚ) • ((third h hh : (ℍ[ℚ])ˣ) : ℍ[ℚ]) := by
    rw [Units.val_neg, neg_one_smul]
  rw [e]
  refine (nrd_smul _ _).trans ?_
  rw [nrd_third h hh]
  norm_num

/-- **`nrd d(i, t) = 1/3`.** -/
theorem nrd_dTable (i t : Fin 3) : nrd ((dTable i t : (ℍ[ℚ])ˣ) : ℍ[ℚ]) = 1 / 3 := by
  fin_cases i <;> fin_cases t
  exacts [nrd_neg_third hA nrd_hA, nrd_third hC nrd_hC, nrd_third hB nrd_hB,
    nrd_third hA nrd_hA, nrd_third hC nrd_hC, nrd_third hB nrd_hB, nrd_third hA nrd_hA,
    nrd_neg_third hC nrd_hC, nrd_neg_third hB nrd_hB]

/-- The level factor, defined by the factorisation equation. -/
def uCand (i t : Fin 3) : Dfx ℚ ℍ[ℚ] :=
  (unitsIncl ℚ ℍ[ℚ] (dTable i t) * classRep (sigmaTable i t))⁻¹ * (classRep i * (etaRep3 t)⁻¹)

-- `3` is a unit away from `3`
private theorem valued_three_eq_one_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₃) :
    Valued.v ((3 : ℚ) : w.adicCompletion ℚ) = 1 := by
  set p := Rat.HeightOneSpectrum.primesEquiv w
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hwp : w = padicPlace (p : ℕ) := (Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply w).symm
  have hp3 : (p : ℕ) ≠ 3 := fun h => hw (by
    rw [← Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply w]
    exact congrArg Rat.HeightOneSpectrum.primesEquiv.symm (Subtype.ext h))
  have hdvd : ¬ ((p : ℕ) : ℤ) ∣ 3 := fun hd => hp3 (by
    have hd' : (p : ℕ) ∣ 3 := by exact_mod_cast hd
    exact (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_three).mp hd')
  rw [hwp]
  have h := valued_intCast_eq_one (q := (p : ℕ)) hdvd
  rwa [Int.cast_ofNat] at h

private theorem inv_three_mem {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₃) :
    algebraMap ℚ (w.adicCompletion ℚ) 3⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  show Valued.v (algebraMap ℚ (w.adicCompletion ℚ) 3⁻¹) ≤ 1
  rw [map_inv₀, map_inv₀, eq_ratCast, valued_three_eq_one_of_ne hw, inv_one]

-- the classes and the coset representatives are trivial away from `3`
private theorem toLocalUnits_unitAt_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₃)
    (m : GL (Fin 2) K₃) : toLocalUnits ℚ ℍ[ℚ] w (unitAt ℚ ℍ[ℚ] v₃ m) = 1 :=
  toLocalUnits_localIncl_of_ne v₃ hw _

-- a unit `d = h'/3` with `h'` and `d⁻¹` Hurwitz is integral away from `3`
private theorem mem_localUnits_of_eq {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₃)
    {d : (ℍ[ℚ])ˣ} {h : ℍ[ℚ]} (hmem : h ∈ hurwitzOrder) (hd : (d : ℍ[ℚ]) = (3⁻¹ : ℚ) • h)
    (hdinv : ((d⁻¹ : (ℍ[ℚ])ˣ) : ℍ[ℚ]) ∈ hurwitzOrder) :
    toLocalUnits ℚ ℍ[ℚ] w (unitsIncl ℚ ℍ[ℚ] d) ∈
      localUnits hurwitzBasis isOrderBasis_hurwitzBasis w := by
  refine ⟨?_, ?_⟩
  · show (d : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈
      localOrder hurwitzBasis isOrderBasis_hurwitzBasis w
    rw [hd, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    exact tmul_mem_localOrder hmem (inv_three_mem hw)
  · show ((d⁻¹ : (ℍ[ℚ])ˣ) : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈
      localOrder hurwitzBasis isOrderBasis_hurwitzBasis w
    exact tmul_mem_localOrder hdinv (one_mem _)

private theorem mem_localUnits_third {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₃) {h : ℍ[ℚ]}
    (hmem : h ∈ hurwitzOrder) (hh : nrd h = 3) :
    toLocalUnits ℚ ℍ[ℚ] w (unitsIncl ℚ ℍ[ℚ] (third h hh)) ∈
      localUnits hurwitzBasis isOrderBasis_hurwitzBasis w :=
  mem_localUnits_of_eq hw hmem rfl (star_mem_hurwitzOrder hmem)

private theorem mem_localUnits_neg_third {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₃)
    {h : ℍ[ℚ]} (hmem : h ∈ hurwitzOrder) (hh : nrd h = 3) :
    toLocalUnits ℚ ℍ[ℚ] w (unitsIncl ℚ ℍ[ℚ] (-third h hh)) ∈
      localUnits hurwitzBasis isOrderBasis_hurwitzBasis w :=
  mem_localUnits_of_eq hw (neg_mem hmem) (by rw [Units.val_neg, smul_neg]; rfl)
    (by rw [inv_neg, Units.val_neg]; exact neg_mem (star_mem_hurwitzOrder hmem))

/-- Away from `3` the level factor and its inverse are integral: `d⁻¹ = ± h̄` is a Hurwitz
quaternion and `d = ± h/3` is integral where `3` is a unit. -/
theorem uCand_away (i t : Fin 3) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₃) :
    toLocalUnits ℚ ℍ[ℚ] w (uCand i t) ∈
      localUnits hurwitzBasis isOrderBasis_hurwitzBasis w := by
  have hc : ∀ j, toLocalUnits ℚ ℍ[ℚ] w (classRep j) = 1 := fun _ =>
    toLocalUnits_unitAt_of_ne hw _
  have he : toLocalUnits ℚ ℍ[ℚ] w (etaRep3 t) = 1 := toLocalUnits_unitAt_of_ne hw _
  simp only [uCand, map_mul, map_inv, hc, he, mul_one, inv_one]
  refine inv_mem ?_
  fin_cases i <;> fin_cases t
  exacts [mem_localUnits_neg_third hw hA_mem nrd_hA, mem_localUnits_third hw hC_mem nrd_hC,
    mem_localUnits_third hw hB_mem nrd_hB, mem_localUnits_third hw hA_mem nrd_hA,
    mem_localUnits_third hw hC_mem nrd_hC, mem_localUnits_third hw hB_mem nrd_hB,
    mem_localUnits_third hw hA_mem nrd_hA, mem_localUnits_neg_third hw hC_mem nrd_hC,
    mem_localUnits_neg_third hw hB_mem nrd_hB]

private theorem levelThreshold_zero : levelThreshold 0 = 1 := by
  rw [levelThreshold]
  simp

-- `v(X + Y ν₃) ≤ v(3)^j` as soon as `3^j ∣ X + 22 Y`, for `j ≤ 3`
private theorem valued_lin_le {X Y : ℤ} {j : ℕ} (hj : j ≤ 3) (h : (3 : ℤ) ^ j ∣ X + 22 * Y) :
    Valued.v ((X : K₃) + (Y : K₃) * ν₃) ≤ levelThreshold j := by
  obtain ⟨m, hm⟩ := h
  have e : (X : K₃) + (Y : K₃) * ν₃ = (3 : K₃) ^ j * (m : K₃) + (Y : K₃) * (ν₃ - 22) := by
    have := congrArg (fun z : ℤ => (z : K₃)) hm
    push_cast at this
    linear_combination this
  rw [e]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul, map_pow, valued_pow_eq_levelThreshold v₃ valued_three]
    exact mul_le_of_le_one_right' (intCast_mem (v₃.adicCompletionIntegers ℚ) m)
  · rw [map_mul]
    refine (mul_le_of_le_one_left' (intCast_mem (v₃.adicCompletionIntegers ℚ) Y)).trans ?_
    refine valued_ν₃_sub_twentyTwo.trans ?_
    rw [Rat.cast_ofNat, show (27 : K₃) = 3 ^ 3 by norm_num, map_pow,
      valued_pow_eq_levelThreshold v₃ valued_three, levelThreshold, levelThreshold,
      WithZero.exp_le_exp]
    omega

-- the entry `(X + Y ν₃) / (3^k m')` with `3 ∤ m'` and `3^(k+e) ∣ X + 22 Y` has `v ≤ v(3)^e`
private theorem valued_frac_le {X Y m' : ℤ} {k e : ℕ} (hke : k + e ≤ 3) (hm' : ¬ (3 : ℤ) ∣ m')
    (h : (3 : ℤ) ^ (k + e) ∣ X + 22 * Y) :
    Valued.v (((X : K₃) + (Y : K₃) * ν₃) / ((3 ^ k * m' : ℤ) : K₃)) ≤ levelThreshold e := by
  have hM : Valued.v (((3 ^ k * m' : ℤ) : K₃)) = levelThreshold k := by
    rw [Int.cast_mul, Int.cast_pow, map_mul, map_pow, Int.cast_ofNat,
      valued_pow_eq_levelThreshold v₃ valued_three, ← Rat.cast_intCast,
      valued_intCast_eq_one (q := 3) hm', mul_one]
  rw [Valuation.map_div, hM,
    div_le_iff₀ (lt_of_le_of_ne zero_le (Ne.symm (levelThreshold_ne_zero k)))]
  refine (valued_lin_le hke h).trans_eq ?_
  rw [levelThreshold, levelThreshold, levelThreshold, ← WithZero.exp_add]
  congr 1
  push_cast
  ring

private theorem toMatrix_inv (g : Dfx ℚ ℍ[ℚ]) :
    toMatrix ℚ ℍ[ℚ] v₃ g⁻¹ = (toMatrix ℚ ℍ[ℚ] v₃ g)⁻¹ := by
  rw [← coe_toGL, ← coe_toGL, map_inv, Matrix.coe_units_inv]

private theorem inv_diagonal_two {a b : K₃} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Matrix.diagonal ![a, b])⁻¹ = Matrix.diagonal ![a⁻¹, b⁻¹] := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  fin_cases j
  · exact inv_mul_cancel₀ ha
  · exact inv_mul_cancel₀ hb

private theorem inv_etaMat (t : K₃) :
    (!![((3 : ℚ) : K₃), 0; 9 * t, 1])⁻¹ = !![((3 : ℚ) : K₃)⁻¹, 0; -(3 * t), 1] := by
  refine Matrix.inv_eq_left_inv ?_
  have e1 : ((3 : ℚ) : K₃)⁻¹ * ((3 : ℚ) : K₃) + 0 * (9 * t) = 1 := by
    rw [inv_mul_cancel₀ three_ne_zero']
    ring
  have e2 : ((3 : ℚ) : K₃)⁻¹ * 0 + 0 * 1 = 0 := by ring
  have e3 : -(3 * t) * ((3 : ℚ) : K₃) + 1 * (9 * t) = 0 := by
    rw [Rat.cast_ofNat]
    ring
  have e4 : -(3 * t) * 0 + 1 * 1 = (1 : K₃) := by ring
  rw [Matrix.mul_fin_two, e1, e2, e3, e4, Matrix.one_fin_two]

-- `θ₃(u(i,t)) = c_σ⁻¹ θ₃(d⁻¹) c_i x_t⁻¹`, as a product of explicit matrices
private theorem toMatrix_uCand (i t : Fin 3) :
    toMatrix ℚ ℍ[ℚ] v₃ (uCand i t) =
      Matrix.diagonal ![(((classDiag (sigmaTable i t)).1 : ℚ) : K₃)⁻¹,
          (((classDiag (sigmaTable i t)).2 : ℚ) : K₃)⁻¹] *
        Quaternion.splitHom (R := ℚ) ν₃ (1 : K₃) sq_ν₃_add_one_sq
          (((dTable i t)⁻¹ : (ℍ[ℚ])ˣ) : ℍ[ℚ]) *
        Matrix.diagonal ![(((classDiag i).1 : ℚ) : K₃), (((classDiag i).2 : ℚ) : K₃)] *
        !![((3 : ℚ) : K₃)⁻¹, 0; -(3 * (((t : ℕ) : ℚ) : K₃)), 1] := by
  rw [uCand, mul_inv_rev, ← map_inv (unitsIncl ℚ ℍ[ℚ]), map_mul, map_mul, map_mul, toMatrix_inv,
    toMatrix_inv, toMatrix_classRep, toMatrix_classRep, toMatrix_etaRep3, toMatrix_unitsIncl,
    inv_diagonal_two (ratCast_ne_zero_of_not_dvd (classDiag_fst_not_dvd _))
      (ratCast_ne_zero_of_not_dvd (classDiag_snd_not_dvd _)), inv_etaMat]
  simp only [mul_assoc]

-- `2 d(i,t)⁻¹` in coordinates
private def invTuple : Fin 3 → Fin 3 → ℤ × ℤ × ℤ × ℤ :=
  ![![(-2, 2, -2, 0), (-1, 3, 1, 1), (-1, -1, -3, -1)],
    ![(2, -2, 2, 0), (-1, 3, 1, 1), (-1, -1, -3, -1)],
    ![(2, -2, 2, 0), (1, -3, -1, -1), (1, 1, 3, 1)]]

private theorem star_eq_ofTuple {h : ℍ[ℚ]} {s : ℤ × ℤ × ℤ × ℤ} (hs : h = ofTuple s) :
    star h = ofTuple (s.1, -s.2.1, -s.2.2.1, -s.2.2.2) := by
  subst hs
  ext <;> simp only [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star, ofTuple_re, ofTuple_imI, ofTuple_imJ, ofTuple_imK] <;> push_cast <;> ring

private theorem hA_eq : hA = ofTuple (2, 2, -2, 0) := by
  ext <;> norm_num [hA, ofTuple]

private theorem hB_eq : hB = ofTuple (-1, 1, 3, 1) := by
  ext <;> norm_num [hB, ofTuple]

private theorem hC_eq : hC = ofTuple (-1, -3, -1, -1) := by
  ext <;> norm_num [hC, ofTuple]

private theorem coe_third_inv {h : ℍ[ℚ]} (hh : nrd h = 3) {s : ℤ × ℤ × ℤ × ℤ}
    (hs : h = ofTuple s) :
    (((third h hh)⁻¹ : (ℍ[ℚ])ˣ) : ℍ[ℚ]) = ofTuple (s.1, -s.2.1, -s.2.2.1, -s.2.2.2) :=
  star_eq_ofTuple hs

private theorem coe_neg_third_inv {h : ℍ[ℚ]} (hh : nrd h = 3) {s : ℤ × ℤ × ℤ × ℤ}
    (hs : h = ofTuple s) :
    (((-third h hh)⁻¹ : (ℍ[ℚ])ˣ) : ℍ[ℚ]) = ofTuple (-s.1, s.2.1, s.2.2.1, s.2.2.2) := by
  rw [inv_neg, Units.val_neg, coe_third_inv hh hs]
  ext <;> simp only [Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
    Quaternion.imK_neg, ofTuple_re, ofTuple_imI, ofTuple_imJ, ofTuple_imK] <;> push_cast <;> ring

private theorem coe_dTable_inv (i t : Fin 3) :
    (((dTable i t)⁻¹ : (ℍ[ℚ])ˣ) : ℍ[ℚ]) = ofTuple (invTuple i t) := by
  fin_cases i <;> fin_cases t
  exacts [coe_neg_third_inv nrd_hA hA_eq, coe_third_inv nrd_hC hC_eq, coe_third_inv nrd_hB hB_eq,
    coe_third_inv nrd_hA hA_eq, coe_third_inv nrd_hC hC_eq, coe_third_inv nrd_hB hB_eq,
    coe_third_inv nrd_hA hA_eq, coe_neg_third_inv nrd_hC hC_eq, coe_neg_third_inv nrd_hB hB_eq]

-- the four entries of `D(x_s, y_s)⁻¹ S D(x_i, y_i) E` for `E = ((e 0), (f 1))`
private theorem diag_mul_mul_diag_mul (a b c d e f : K₃) (S : Matrix (Fin 2) (Fin 2) K₃) :
    Matrix.diagonal ![a, b] * S * Matrix.diagonal ![c, d] * !![e, 0; f, 1] =
      !![a * (S 0 0 * c * e + S 0 1 * d * f), a * S 0 1 * d;
        b * (S 1 0 * c * e + S 1 1 * d * f), b * S 1 1 * d] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

-- **the certificate**: a matrix of this shape lies in `Iw₁(9)` as soon as three explicit
-- integers are divisible by `3`, `27` and `9`
private theorem mem_iwahoriOne_of_eq {g : GL (Fin 2) K₃} {xs ys xi yi : ℤ} {n : ℕ}
    {q : ℤ × ℤ × ℤ × ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) K₃) =
      Matrix.diagonal ![((xs : ℚ) : K₃)⁻¹, ((ys : ℚ) : K₃)⁻¹] *
        Quaternion.splitHom (R := ℚ) ν₃ (1 : K₃) sq_ν₃_add_one_sq (ofTuple q) *
        Matrix.diagonal ![((xi : ℚ) : K₃), ((yi : ℚ) : K₃)] *
        !![((3 : ℚ) : K₃)⁻¹, 0; -(3 * ((n : ℚ) : K₃)), 1])
    (hdet : Valued.v (g : Matrix (Fin 2) (Fin 2) K₃).det = 1)
    (hxs : ¬ (3 : ℤ) ∣ xs) (hys : ¬ (3 : ℤ) ∣ ys)
    (h00 : (3 : ℤ) ^ (1 + 0) ∣ (q.1 + q.2.2.2) * xi - 9 * n * yi * (q.2.1 - q.2.2.1) +
      22 * (q.2.1 * xi + 9 * n * yi * q.2.2.2))
    (h10 : (3 : ℤ) ^ (1 + 2) ∣ (q.2.1 + q.2.2.1) * xi - 9 * n * yi * (q.1 - q.2.2.2) +
      22 * (-q.2.2.2 * xi + 9 * n * yi * q.2.1))
    (h11 : (3 : ℤ) ^ (0 + 2) ∣ (q.1 - q.2.2.2) * yi - 3 ^ 0 * (2 * ys) + 22 * (-q.2.1 * yi)) :
    g ∈ LocalLevel.iwahoriOne K₃ (levelThreshold 2) := by
  have hxs0 : ((xs : ℚ) : K₃) ≠ 0 := ratCast_ne_zero_of_not_dvd hxs
  have hys0 : ((ys : ℚ) : K₃) ≠ 0 := ratCast_ne_zero_of_not_dvd hys
  rw [Rat.cast_intCast] at hxs0 hys0
  rw [diag_mul_mul_diag_mul, Quaternion.splitHom_apply] at hg
  have e00 : (g : Matrix (Fin 2) (Fin 2) K₃) 0 0 =
      ((((q.1 + q.2.2.2) * xi - 9 * n * yi * (q.2.1 - q.2.2.1) : ℤ) : K₃) +
        ((q.2.1 * xi + 9 * n * yi * q.2.2.2 : ℤ) : K₃) * ν₃) / ((3 ^ 1 * (2 * xs) : ℤ) : K₃) := by
    rw [hg]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, ofTuple_re, ofTuple_imI, ofTuple_imJ,
      ofTuple_imK, map_div₀, map_intCast, map_ofNat, Rat.cast_intCast, Rat.cast_natCast,
      Rat.cast_ofNat]
    push_cast
    haveI := charZero_K₃
    field_simp
    ring
  have e01 : (g : Matrix (Fin 2) (Fin 2) K₃) 0 1 =
      ((((q.2.1 - q.2.2.1) * yi : ℤ) : K₃) + ((-q.2.2.2 * yi : ℤ) : K₃) * ν₃) /
        ((3 ^ 0 * (2 * xs) : ℤ) : K₃) := by
    rw [hg]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, ofTuple_re, ofTuple_imI, ofTuple_imJ,
      ofTuple_imK, map_div₀, map_intCast, map_ofNat, Rat.cast_intCast, Rat.cast_natCast,
      Rat.cast_ofNat]
    push_cast
    haveI := charZero_K₃
    field_simp
    ring
  have e10 : (g : Matrix (Fin 2) (Fin 2) K₃) 1 0 =
      ((((q.2.1 + q.2.2.1) * xi - 9 * n * yi * (q.1 - q.2.2.2) : ℤ) : K₃) +
        ((-q.2.2.2 * xi + 9 * n * yi * q.2.1 : ℤ) : K₃) * ν₃) / ((3 ^ 1 * (2 * ys) : ℤ) : K₃) := by
    rw [hg]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, ofTuple_re, ofTuple_imI, ofTuple_imJ,
      ofTuple_imK, map_div₀, map_intCast, map_ofNat, Rat.cast_intCast, Rat.cast_natCast,
      Rat.cast_ofNat]
    push_cast
    haveI := charZero_K₃
    field_simp
    ring
  have e11 : (g : Matrix (Fin 2) (Fin 2) K₃) 1 1 =
      ((((q.1 - q.2.2.2) * yi : ℤ) : K₃) + ((-q.2.1 * yi : ℤ) : K₃) * ν₃) /
        ((3 ^ 0 * (2 * ys) : ℤ) : K₃) := by
    rw [hg]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, ofTuple_re, ofTuple_imI, ofTuple_imJ,
      ofTuple_imK, map_div₀, map_intCast, map_ofNat, Rat.cast_intCast, Rat.cast_natCast,
      Rat.cast_ofNat]
    push_cast
    haveI := charZero_K₃
    field_simp
    ring
  have e11' : (g : Matrix (Fin 2) (Fin 2) K₃) 1 1 - 1 =
      ((((q.1 - q.2.2.2) * yi - 3 ^ 0 * (2 * ys) : ℤ) : K₃) + ((-q.2.1 * yi : ℤ) : K₃) * ν₃) /
        ((3 ^ 0 * (2 * ys) : ℤ) : K₃) := by
    rw [e11]
    push_cast
    haveI := charZero_K₃
    field_simp
    ring
  have hm'x : ¬ (3 : ℤ) ∣ 2 * xs := by omega
  have hm'y : ¬ (3 : ℤ) ∣ 2 * ys := by omega
  have h01 : (3 : ℤ) ^ (0 + 0) ∣ (q.2.1 - q.2.2.1) * yi + 22 * (-q.2.2.2 * yi) := by
    simp
  have h11a : (3 : ℤ) ^ (0 + 0) ∣ (q.1 - q.2.2.2) * yi + 22 * (-q.2.1 * yi) := by
    simp
  refine ⟨⟨?_, hdet, ?_⟩, ?_⟩
  · simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [e00]
      exact (valued_frac_le (by norm_num) hm'x h00).trans_eq levelThreshold_zero
    · rw [e01]
      exact (valued_frac_le (by norm_num) hm'x h01).trans_eq levelThreshold_zero
    · rw [e10]
      exact (valued_frac_le (by norm_num) hm'y h10).trans (levelThreshold_lt_one (by norm_num)).le
    · rw [e11]
      exact (valued_frac_le (by norm_num) hm'y h11a).trans_eq levelThreshold_zero
  · rw [e10]
    exact valued_frac_le (by norm_num) hm'y h10
  · rw [e11']
    exact valued_frac_le (by norm_num) hm'y h11

-- `v(det θ₃(u(i,t))) = 1`: the determinant is multiplicative and `nrd d = 1/3`, `det x_t = 3`
private theorem valued_det_uCand (i t : Fin 3) :
    Valued.v (toMatrix ℚ ℍ[ℚ] v₃ (uCand i t)).det = 1 := by
  let φ : Dfx ℚ ℍ[ℚ] →* WithZero (Multiplicative ℤ) :=
    ((Valued.v : Valuation K₃ (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom.comp
      Matrix.detMonoidHom).comp (toMatrix ℚ ℍ[ℚ] v₃)
  have hφ : ∀ g, φ g = Valued.v (toMatrix ℚ ℍ[ℚ] v₃ g).det := fun _ => rfl
  have hc : ∀ j, φ (classRep j) = 1 := fun j => by
    rw [hφ, toMatrix_classRep, Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [map_mul, valued_intCast_eq_one (q := 3) (classDiag_fst_not_dvd j),
      valued_intCast_eq_one (q := 3) (classDiag_snd_not_dvd j), one_mul]
  have he : φ (etaRep3 t) = WithZero.exp (-1) := by
    rw [hφ, etaRep3, det_toMatrix_etaAdelicRep, Rat.cast_ofNat, valued_three]
  have h2 := isUnit_two v₃
  have hm1 : IsUnit (algebraMap ℚ K₃ (-1)) := by rw [map_neg, map_one]; exact isUnit_one.neg
  have hd : φ (unitsIncl ℚ ℍ[ℚ] (dTable i t)) = WithZero.exp 1 := by
    rw [hφ, toMatrix_unitsIncl]
    refine (congrArg Valued.v (QuaternionAlgebra.det_map_eq_nrd
      (Quaternion.splitHom (R := ℚ) ν₃ (1 : K₃) sq_ν₃_add_one_sq) h2 hm1 hm1 _)).trans ?_
    rw [nrd_dTable i t,
      map_div₀, map_one, map_ofNat, Valuation.map_div, map_one, valued_three, one_div,
      ← WithZero.exp_neg, neg_neg]
  rw [← hφ, uCand, map_mul, map_inv, map_mul, map_mul, map_inv, hc, hc, hd, he, mul_one, one_mul,
    ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add]
  norm_num

/-- At `3` the level factor lies in `Iw₁(9)`: the nine matrix computations. -/
theorem toGL_uCand_mem (i t : Fin 3) :
    toGL ℚ ℍ[ℚ] v₃ (uCand i t) ∈ LocalLevel.iwahoriOne K₃ (levelThreshold 2) := by
  have hg := toMatrix_uCand i t
  rw [coe_dTable_inv] at hg
  refine mem_iwahoriOne_of_eq hg (valued_det_uCand i t) (classDiag_fst_not_dvd _)
    (classDiag_snd_not_dvd _) ?_ ?_ ?_ <;>
  · fin_cases i <;> fin_cases t <;> decide

/-- **`u(i, t) ∈ U₁(9)`.** -/
theorem uCand_mem (i t : Fin 3) : uCand i t ∈ U1_9 :=
  mem_U1_9_of_toGL (toGL_uCand_mem i t) fun _ hw => uCand_away i t hw

/-- **The nine factorisations** `c_i x_t⁻¹ = d(i,t) · c_{σ(i,t)} · u(i,t)`. -/
theorem factorisation (i t : Fin 3) :
    classRep i * (etaRep3 t)⁻¹ =
      unitsIncl ℚ ℍ[ℚ] (dTable i t) * classRep (sigmaTable i t) * uCand i t := by
  rw [uCand, mul_inv_cancel_left]

end Hamilton
