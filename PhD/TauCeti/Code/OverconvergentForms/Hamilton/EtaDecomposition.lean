/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Hamilton.ClassSet

/-!
# `U₁(9) η₃ U₁(9)` is three right cosets

The instance of the coset decomposition of `U η_𝔭 U` at `p = 3`, `t = 2`, with the residue system
`{0, 1, 2}`: `U₁(9) η₃ U₁(9) = ∐_{t ∈ {0,1,2}} U₁(9) · ι₃(((3 0), (9t 1)))`.

[Jac03, Lemma 2.3]: the double coset `U₁(9) η₃ U₁(9)` is the union of the three cosets of
`((3 0), (9t 1))`, `t ∈ {0, 1, 2}`.

## Main definitions

* `Hamilton.eta3`, `Hamilton.etaRep3`.

## Main results

* `Hamilton.valued_le_valued_three`: `3` is a uniformiser of `K₃`.
* `Hamilton.existsUnique_fin_three`: `{0, 1, 2}` is a residue system of `ℤ_3`.
* `Hamilton.toMatrix_etaRep3`: `θ₃(x_t) = ((3 0), (9t 1))`.
* `Hamilton.bijOn_etaRep3`, `Hamilton.etaRep3_injective`: the three right cosets.

Roadmap: §0.5.4. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Hamilton/EtaDecomposition.lean`.
-/

open scoped Quaternion TensorProduct Pointwise
open IsDedekindDomain NumberField AdelicAlgebra Quaternion

noncomputable section

namespace Hamilton

open scoped AdelicAlgebra.RightAlgebra

/-- `3 ≠ 0` in `K₃`. -/
theorem three_ne_zero' : ((3 : ℚ) : K₃) ≠ 0 := by
  rw [Rat.cast_ofNat]
  intro h
  have h3 := valued_three
  rw [h, map_zero] at h3
  exact WithZero.exp_ne_zero h3.symm

/-- `v(3) < 1`. -/
theorem valued_three_lt_one : Valued.v ((3 : ℚ) : K₃) < 1 := by
  rw [Rat.cast_ofNat, valued_three, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/-- `3` is a uniformiser of `K₃`. -/
theorem valued_le_valued_three {x : K₃} (hx : Valued.v x < 1) :
    Valued.v x ≤ Valued.v ((3 : ℚ) : K₃) := by
  rw [Rat.cast_ofNat, valued_three]
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]
    exact zero_le
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

-- distinct residues differ by a unit
private theorem valued_natCast_sub_eq_one {s t : Fin 3} (hst : s ≠ t) :
    Valued.v ((((s : ℕ) : ℚ) : K₃) - (((t : ℕ) : ℚ) : K₃)) = 1 := by
  have hs := s.isLt
  have ht := t.isLt
  have hne : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
  haveI := charZero_K₃
  rw [show (((s : ℕ) : ℚ) : K₃) - (((t : ℕ) : ℚ) : K₃) =
      ((((s : ℕ) - (t : ℕ) : ℤ) : ℚ) : K₃) by
    simp only [Int.cast_sub, Rat.cast_sub, Int.cast_natCast]]
  exact valued_intCast_eq_one (q := 3) (by omega)

-- an integer `z ≡ n mod 3` that is `3`-adically close to `x` puts `x` in the class of `n`
private theorem valued_sub_lt_one_of_dvd {x : K₃} {z : ℤ} {n : ℕ}
    (hz : Valued.v (x - (z : K₃)) ≤ Valued.v ((3 : ℚ) : K₃)) (hn : (3 : ℤ) ∣ z - n) :
    Valued.v (x - ((n : ℚ) : K₃)) < 1 := by
  obtain ⟨k, hk⟩ := hn
  have e : x - ((n : ℚ) : K₃) = (x - (z : K₃)) + ((3 : ℚ) : K₃) * (k : K₃) := by
    have hk' : (z : K₃) = (n : K₃) + 3 * (k : K₃) := by
      have := congrArg (fun m : ℤ => (m : K₃)) hk
      push_cast at this
      linear_combination this
    rw [Rat.cast_natCast, Rat.cast_ofNat, hk']
    ring
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_add_le _ hz ?_) valued_three_lt_one
  rw [map_mul]
  exact mul_le_of_le_one_right' (intCast_mem (v₃.adicCompletionIntegers ℚ) k)

/-- **`{0, 1, 2}` is a residue system of `ℤ_3`.** -/
theorem existsUnique_fin_three {x : K₃} (hx : Valued.v x ≤ 1) :
    ∃! t : Fin 3, Valued.v (x - (((t : ℕ) : ℚ) : K₃)) < 1 := by
  -- an integer approximation of `x` modulo `3`, reduced into `{0, 1, 2}`
  obtain ⟨z, hz, -⟩ := exists_intCast_approx (w := v₃) ∅ (Finset.notMem_empty v₃) ⟨x, hx⟩
    (M := 3) (by norm_num)
  have hz' : Valued.v (x - (z : K₃)) ≤ Valued.v ((3 : ℚ) : K₃) := by
    simpa using hz
  obtain ⟨t, ht⟩ : ∃ t : Fin 3, (3 : ℤ) ∣ z - ((t : ℕ) : ℤ) := by
    rcases (by omega : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2) with h | h | h
    · exact ⟨⟨0, by norm_num⟩, show (3 : ℤ) ∣ z - ((0 : ℕ) : ℤ) by omega⟩
    · exact ⟨⟨1, by norm_num⟩, show (3 : ℤ) ∣ z - ((1 : ℕ) : ℤ) by omega⟩
    · exact ⟨⟨2, by norm_num⟩, show (3 : ℤ) ∣ z - ((2 : ℕ) : ℤ) by omega⟩
  refine ⟨t, valued_sub_lt_one_of_dvd hz' ht, fun s hs => ?_⟩
  -- two residues in the class of `x` differ by a non-unit, so they agree
  by_contra hst
  have h := valued_natCast_sub_eq_one hst
  rw [show (((s : ℕ) : ℚ) : K₃) - (((t : ℕ) : ℚ) : K₃) =
      (x - (((t : ℕ) : ℚ) : K₃)) - (x - (((s : ℕ) : ℚ) : K₃)) by ring] at h
  exact (lt_of_le_of_lt (Valuation.map_sub _ _ _)
    (max_lt (valued_sub_lt_one_of_dvd hz' ht) hs)).ne h

/-- **`η₃ = ι₃(diag(3, 1))`.** -/
def eta3 : Dfx ℚ ℍ[ℚ] := etaAdelic ℚ ℍ[ℚ] v₃ ((3 : ℚ) : K₃) three_ne_zero'

/-- **The representatives `x_t = ι₃(((3 0), (9t 1)))`.** -/
def etaRep3 (t : Fin 3) : Dfx ℚ ℍ[ℚ] :=
  etaAdelicRep ℚ ℍ[ℚ] v₃ ((3 : ℚ) : K₃) three_ne_zero' 2 (((t : ℕ) : ℚ) : K₃)

/-- `θ₃(x_t) = ((3 0), (9t 1))`. -/
theorem toMatrix_etaRep3 (t : Fin 3) :
    toMatrix ℚ ℍ[ℚ] v₃ (etaRep3 t) = !![((3 : ℚ) : K₃), 0; 9 * (((t : ℕ) : ℚ) : K₃), 1] := by
  rw [etaRep3, toMatrix_etaAdelicRep, show (((t : ℕ) : ℚ) : K₃) * ((3 : ℚ) : K₃) ^ 2 =
    9 * (((t : ℕ) : ℚ) : K₃) by rw [Rat.cast_ofNat]; ring]

-- `v(3)²` is the threshold of `U₁(9)`
private theorem valued_three_sq : Valued.v ((3 : ℚ) : K₃) ^ 2 = levelThreshold 2 :=
  valued_pow_eq_levelThreshold v₃ (by rw [Rat.cast_ofNat, valued_three]) 2

/-- **`U₁(9) η₃ U₁(9) = ∐_{t ∈ {0,1,2}} U₁(9) x_t`.** -/
theorem bijOn_etaRep3 :
    Set.BijOn (Quotient.mk'' : Dfx ℚ ℍ[ℚ] → Quotient (QuotientGroup.rightRel U1_9))
      (Set.range etaRep3)
      ((Quotient.mk'' : Dfx ℚ ℍ[ℚ] → Quotient (QuotientGroup.rightRel U1_9)) ''
        (({eta3} : Set (Dfx ℚ ℍ[ℚ])) * (U1_9 : Set (Dfx ℚ ℍ[ℚ])))) := by
  have hup : U1_9 ≤ levelAt ℚ ℍ[ℚ] v₃
      (LocalLevel.iwahori K₃ (Valued.v ((3 : ℚ) : K₃) ^ 2)) := by
    rw [valued_three_sq]
    intro g hg
    rw [U1_9, U1Level, standardLevel, Subgroup.mem_inf, Subgroup.mem_iInf] at hg
    exact mem_levelAt_iff.mpr (LocalLevel.iwahoriOne_le_iwahori _ (mem_levelAt_iff.mp (hg.2 ())))
  have hlow : (LocalLevel.iwahoriPrincipal K₃ (Valued.v ((3 : ℚ) : K₃) ^ 2)).map
      (unitAt ℚ ℍ[ℚ] v₃) ≤ U1_9 := by
    rw [valued_three_sq]
    exact unitAt_iwahoriPrincipal_le_U1Level (w := fun _ : Unit ↦ v₃) (fun _ _ _ => rfl)
      (fun _ => theta3_isIntegral) (fun _ => 2) ()
  exact bijOn_etaAdelicRep v₃ three_ne_zero' valued_three_lt_one
    (fun _ hx => valued_le_valued_three hx) (by norm_num) hup hlow
    (fun t : Fin 3 => (((t : ℕ) : ℚ) : K₃))
    (fun t => by rw [Rat.cast_natCast]; exact natCast_mem (v₃.adicCompletionIntegers ℚ) _)
    (fun _ hx => existsUnique_fin_three hx)

/-- The three representatives are distinct. -/
theorem etaRep3_injective : Function.Injective etaRep3 := by
  intro s t h
  by_contra hst
  have h' := congrFun (congrFun (congrArg (toMatrix ℚ ℍ[ℚ] v₃) h) 1) 0
  rw [toMatrix_etaRep3, toMatrix_etaRep3] at h'
  have h9 : (9 : K₃) ≠ 0 := by
    have h3 := three_ne_zero'
    rw [Rat.cast_ofNat] at h3
    rw [show (9 : K₃) = 3 * 3 by norm_num]
    exact mul_ne_zero h3 h3
  have h'' : (9 : K₃) * (((s : ℕ) : ℚ) : K₃) = 9 * (((t : ℕ) : ℚ) : K₃) := h'
  have e : (((s : ℕ) : ℚ) : K₃) - (((t : ℕ) : ℚ) : K₃) = 0 :=
    sub_eq_zero.mpr (mul_left_cancel₀ h9 h'')
  have h1 := valued_natCast_sub_eq_one hst
  rw [e, map_zero] at h1
  exact zero_ne_one h1

end Hamilton
