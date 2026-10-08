/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Hamilton.Level

/-!
# Class number one: `D_f^× = D^× · U₀(1)` for Hamilton's quaternions

Every right ideal of the Hurwitz order is principal, and the idelic dictionary turns this into the
triviality of `D^× \ D_f^× / U₀(1)`: to `g ∈ D_f^×` one attaches the right ideal
`I_g = {y ∈ 𝒪 | g⁻¹ y is everywhere integral}`, a generator `x` of `I_g` satisfies
`g ∈ x · (𝒪 ⊗ ℤ̂)` with `x⁻¹ g` a unit, and clearing denominators reduces to integral `g`. No
Jacquet–Langlands correspondence is used. As a consequence every open subgroup has a finite class
set.

[Voi21, Lemma 27.6.8]: "The set of locally principal, right fractional `O`-ideals is in bijection
with `B̂^× / Ô^×` via the map `I ↦ α̂ Ô^×`, where `I_p = α_p O_p` and `α̂ = (α_p)_p`; this map
induces a bijection `Cls_R O ↔ B^× \ B̂^× / Ô^×`." [Jac03, Lemma 1.22]: "`D_f^× = D^× U₀(1)`."

## Main definitions

* `Hamilton.denominatorIdeal`: the right ideal `I_g` of the Hurwitz order.

## Main results

* `Hamilton.exists_intCast_mul_mem_integralAdeles`, `Hamilton.exists_intCast_smul_toLocal_mem`:
  clearing denominators; `Hamilton.exists_intCast_approx`: integer approximation.
* `Hamilton.denominatorIdeal_ne_bot`, `Hamilton.exists_mem_denominatorIdeal_sub_smul`,
  `Hamilton.exists_eq_generator_mul`: the idelic dictionary.
* `Hamilton.exists_factor_of_forall_mem`, `Hamilton.exists_factor`: class number one.
* `Hamilton.subsingleton_classSet_U0`, `Hamilton.hasFiniteClassSets`.

Roadmap: §0.3.5, §0.5.1. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Hamilton/ClassNumberOne.lean`.
-/

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField AdelicAlgebra Quaternion

noncomputable section

namespace Hamilton

open scoped AdelicAlgebra.RightAlgebra

local notation "𝒪loc" => localOrder hurwitzBasis isOrderBasis_hurwitzBasis

section Integers

private theorem valued_intCast (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    Valued.v ((n : v.adicCompletion ℚ)) = v.valuation ℚ (n : ℚ) := by
  rw [← Rat.cast_intCast, valued_ratCast]

private theorem valued_intCast_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    Valued.v ((n : v.adicCompletion ℚ)) ≤ 1 :=
  intCast_mem (v.adicCompletionIntegers ℚ) n

private theorem valued_intCast_ne_zero {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℤ} (hn : n ≠ 0) :
    Valued.v ((n : v.adicCompletion ℚ)) ≠ 0 := by
  rw [valued_intCast]
  exact (Valuation.ne_zero_iff _).mpr (Int.cast_ne_zero.mpr hn)

private theorem intCast_ne_zero_adic {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℤ} (hn : n ≠ 0) :
    (n : v.adicCompletion ℚ) ≠ 0 :=
  fun h => valued_intCast_ne_zero hn (by rw [h, map_zero])

private theorem valued_intCast_eq_intValuation (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    Valued.v ((n : v.adicCompletion ℚ)) = v.intValuation (Rat.ringOfIntegersEquiv.symm n) := by
  rw [valued_intCast, ← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) v
    (Rat.ringOfIntegersEquiv.symm n)]
  exact congrArg _ (Rat.ringOfIntegersEquiv_symm_apply_coe n).symm

-- a quotient by `n` is integral as soon as its numerator is as divisible as `n²`
private theorem valued_div_intCast_le_one {v : HeightOneSpectrum (𝓞 ℚ)}
    {a : v.adicCompletion ℚ} {n : ℤ} (hn : n ≠ 0)
    (ha : Valued.v a ≤ Valued.v (((n ^ 2 : ℤ) : v.adicCompletion ℚ))) :
    Valued.v (a / (n : v.adicCompletion ℚ)) ≤ 1 := by
  have hsq : Valued.v (((n ^ 2 : ℤ) : v.adicCompletion ℚ)) ≤
      Valued.v ((n : v.adicCompletion ℚ)) := by
    rw [Int.cast_pow, map_pow, sq]
    exact mul_le_of_le_one_left' (valued_intCast_le_one v n)
  rw [Valuation.map_div]
  exact (div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm (valued_intCast_ne_zero hn)))).mpr
    (ha.trans hsq)

-- per-place denominator clearing
private theorem exists_intCast_mul_mem {v : HeightOneSpectrum (𝓞 ℚ)} (x : v.adicCompletion ℚ) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨r, hr, hrx⟩ :=
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hr' : ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) = r :=
    (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* _) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply r)
  refine ⟨Rat.ringOfIntegersEquiv r, by simpa using nonZeroDivisors.ne_zero hr, ?_⟩
  rwa [← map_intCast (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)), hr', mul_comm]

/-- Every adele of `ℚ` has a nonzero integer multiple that is integral everywhere. -/
theorem exists_intCast_mul_mem_integralAdeles (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ((N : ℚ) : v.adicCompletion ℚ) * a v ∈ v.adicCompletionIntegers ℚ := by
  classical
  choose n hn0 hn using fun v : HeightOneSpectrum (𝓞 ℚ) => exists_intCast_mul_mem (a v)
  have hS : {v : HeightOneSpectrum (𝓞 ℚ) | a v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp a.2
  refine ⟨∏ v ∈ hS.toFinset, n v, Finset.prod_ne_zero_iff.mpr fun v _ => hn0 v, fun v => ?_⟩
  rw [Rat.cast_intCast]
  by_cases hv : v ∈ hS.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, Int.cast_mul, mul_comm (n v : v.adicCompletion ℚ),
      mul_assoc]
    exact mul_mem (intCast_mem _ _) (hn v)
  · exact mul_mem (intCast_mem _ _) (not_not.mp fun h => hv (hS.mem_toFinset.mpr h))

end Integers

section LocalOrder

-- every element of `D_f` is integral at all but finitely many places
private theorem eventually_toLocal_mem_localOrder (x : Df ℚ ℍ[ℚ]) :
    ∀ᶠ w in Filter.cofinite, toLocal ℚ ℍ[ℚ] w x ∈ 𝒪loc w := by
  filter_upwards [Filter.eventually_all.mpr fun i =>
    ((rightBasis (R := FiniteAdeleRing (𝓞 ℚ) ℚ) hurwitzBasis).repr x i).2] with w hw
  exact mem_localOrder_iff.mpr fun i => by rw [rightBasis_repr_toLocal]; exact hw i

/-- **Clearing denominators in `D_f`**: a nonzero integer multiple of `x` is everywhere integral. -/
theorem exists_intCast_smul_toLocal_mem (x : Df ℚ ℍ[ℚ]) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ w, toLocal ℚ ℍ[ℚ] w ((N : ℚ) • x) ∈ 𝒪loc w := by
  classical
  choose n hn0 hn using fun i : Fin 4 => exists_intCast_mul_mem_integralAdeles
    ((rightBasis (R := FiniteAdeleRing (𝓞 ℚ) ℚ) hurwitzBasis).repr x i)
  refine ⟨∏ i, n i, Finset.prod_ne_zero_iff.mpr fun i _ => hn0 i, fun w => ?_⟩
  refine mem_localOrder_iff.mpr fun i => ?_
  rw [map_smul, Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul (w.adicCompletion ℚ), map_smul,
    Finsupp.smul_apply, smul_eq_mul, rightBasis_repr_toLocal,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Int.cast_mul,
    mul_comm (n i : w.adicCompletion ℚ), mul_assoc]
  have h := hn i w
  rw [Rat.cast_intCast] at h
  exact mul_mem (intCast_mem _ _) h

end LocalOrder

section Approximation

-- density of `ℤ` in `𝒪_w`: a rational close to `c` is `w`-integral, and is close to an integer
private theorem exists_intCast_valued_sub_le {w : HeightOneSpectrum (𝓞 ℚ)}
    (c : w.adicCompletionIntegers ℚ) {M : ℤ} (hM : M ≠ 0) :
    ∃ z : ℤ, Valued.v ((c : w.adicCompletion ℚ) - (z : w.adicCompletion ℚ)) ≤
      Valued.v ((M : w.adicCompletion ℚ)) := by
  have hMv : Valued.v ((M : w.adicCompletion ℚ)) ≠ 0 := valued_intCast_ne_zero hM
  have hball : {y : w.adicCompletion ℚ |
      Valued.v (y - (c : w.adicCompletion ℚ)) < Valued.v ((M : w.adicCompletion ℚ))} ∈
      nhds (c : w.adicCompletion ℚ) := by
    rw [Valued.mem_nhds]
    exact ⟨Units.mk0 (Valued.v.restrict ((M : w.adicCompletion ℚ))) (by simpa using hMv),
      fun y hy => by simpa using hy⟩
  obtain ⟨y, hyball, q, rfl⟩ :=
    mem_closure_iff_nhds.mp
      (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) (v := w) (c : w.adicCompletion ℚ)) _ hball
  have hq1 : w.valuation ℚ q ≤ 1 := by
    have hc : Valued.v ((c : w.adicCompletion ℚ)) ≤ 1 := c.2
    have h := Valuation.map_add_le Valued.v (hyball.le.trans (valued_intCast_le_one w M)) hc
    rwa [sub_add_cancel, eq_ratCast, valued_ratCast] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer w hq1
    (Units.mk0 (Valued.v ((M : w.adicCompletion ℚ))) hMv)
  refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
  have hz : ((Rat.ringOfIntegersEquiv a : ℤ) : w.adicCompletion ℚ) =
      algebraMap ℚ (w.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a) := by
    rw [← Rat.ringOfIntegersEquiv_apply_coe a, map_intCast]
  rw [← sub_add_sub_cancel _ (algebraMap ℚ (w.adicCompletion ℚ) q) _]
  refine Valuation.map_add_le Valued.v ?_ ?_
  · rw [Valuation.map_sub_swap]
    exact hyball.le
  · rw [hz, ← map_sub, eq_ratCast, valued_ratCast, Valuation.map_sub_swap]
    exact ha.le

-- at a place `v ≠ w`: a `w`-unit integer at least as `v`-divisible as `M`
private theorem exists_intCast_eq_one_of_le_aux {w v : HeightOneSpectrum (𝓞 ℚ)} (hvw : v ≠ w)
    {M : ℤ} (hM : M ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ Valued.v ((n : w.adicCompletion ℚ)) = 1 ∧
      Valued.v ((n : v.adicCompletion ℚ)) ≤ Valued.v ((M : v.adicCompletion ℚ)) := by
  have hnotle : ¬ (v.asIdeal ≤ w.asIdeal) := fun h =>
    hvw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isMaximal.ne_top h))
  obtain ⟨r, hrv, hrw⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hr0 : r ≠ 0 := fun h => hrw (h ▸ Submodule.zero_mem _)
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt (valued_intCast_ne_zero (v := v) hM)
  have hsymm : Rat.ringOfIntegersEquiv.symm ((Rat.ringOfIntegersEquiv r) ^ k) = r ^ k := by
    rw [map_pow, RingEquiv.symm_apply_apply]
  refine ⟨(Rat.ringOfIntegersEquiv r) ^ k, ?_, ?_, ?_⟩
  · exact pow_ne_zero _ (by simpa using hr0)
  · rw [valued_intCast_eq_intValuation, hsymm, map_pow,
      (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w r).mpr hrw, one_pow]
  · rw [valued_intCast_eq_intValuation, hsymm]
    exact ((HeightOneSpectrum.intValuation_le_pow_iff_mem v (r ^ k) k).mpr
      (Ideal.pow_mem_pow hrv k)).trans hk.le

-- a `w`-unit integer at least as divisible as `M` at every place of `T ∌ w`
private theorem exists_intCast_valued_eq_one_of_le {w : HeightOneSpectrum (𝓞 ℚ)}
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hw : w ∉ T) {M : ℤ} (hM : M ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ Valued.v ((m : w.adicCompletion ℚ)) = 1 ∧
      ∀ v ∈ T, Valued.v ((m : v.adicCompletion ℚ)) ≤ Valued.v ((M : v.adicCompletion ℚ)) := by
  classical
  revert hw
  induction T using Finset.induction_on with
  | empty => exact fun _ => ⟨1, one_ne_zero, by simp, by simp⟩
  | insert a s ha ih =>
    intro hw
    obtain ⟨m', hm'0, hm'w, hm'T⟩ := ih fun h => hw (Finset.mem_insert_of_mem h)
    obtain ⟨n, hn0, hnw, hnv⟩ := exists_intCast_eq_one_of_le_aux (w := w) (v := a)
      (fun h => hw (h ▸ Finset.mem_insert_self a s)) hM
    refine ⟨m' * n, mul_ne_zero hm'0 hn0, ?_, ?_⟩
    · rw [Int.cast_mul, Valuation.map_mul, hm'w, hnw, one_mul]
    · intro v hv
      rw [Int.cast_mul, Valuation.map_mul]
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (mul_le_mul' (valued_intCast_le_one v m') hnv).trans_eq (one_mul _)
      · exact (mul_le_mul' (hm'T v hv) (valued_intCast_le_one v n)).trans_eq (mul_one _)

/-- **Integer approximation**: a local integer at `w` is congruent modulo `M` to an integer that is
divisible by `M` at the finitely many places of `T`. -/
theorem exists_intCast_approx {w : HeightOneSpectrum (𝓞 ℚ)}
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hw : w ∉ T) (c : w.adicCompletionIntegers ℚ) {M : ℤ}
    (hM : M ≠ 0) :
    ∃ z : ℤ, Valued.v ((c : w.adicCompletion ℚ) - ((z : ℚ) : w.adicCompletion ℚ)) ≤
        Valued.v (((M : ℚ)) : w.adicCompletion ℚ) ∧
      ∀ v ∈ T, Valued.v (((z : ℚ)) : v.adicCompletion ℚ) ≤
        Valued.v (((M : ℚ)) : v.adicCompletion ℚ) := by
  simp only [Rat.cast_intCast]
  obtain ⟨m, -, hmw, hmT⟩ := exists_intCast_valued_eq_one_of_le T hw hM
  have hmne : (m : w.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mp (hmw ▸ one_ne_zero)
  have hc' : (c : w.adicCompletion ℚ) / (m : w.adicCompletion ℚ) ∈
      w.adicCompletionIntegers ℚ := by
    show Valued.v ((c : w.adicCompletion ℚ) / (m : w.adicCompletion ℚ)) ≤ 1
    rw [Valuation.map_div, hmw, div_one]
    exact c.2
  obtain ⟨t, ht⟩ := exists_intCast_valued_sub_le ⟨_, hc'⟩ hM
  refine ⟨m * t, ?_, ?_⟩
  · have key : (c : w.adicCompletion ℚ) - ((m * t : ℤ) : w.adicCompletion ℚ) =
        (m : w.adicCompletion ℚ) *
          ((c : w.adicCompletion ℚ) / (m : w.adicCompletion ℚ) - (t : w.adicCompletion ℚ)) := by
      rw [mul_sub, mul_div_cancel₀ _ hmne, Int.cast_mul]
    rw [key, Valuation.map_mul, hmw, one_mul]
    exact ht
  · intro v hv
    rw [Int.cast_mul, Valuation.map_mul]
    exact (mul_le_mul' (hmT v hv) (valued_intCast_le_one v t)).trans_eq (mul_one _)

end Approximation

section Dictionary

-- a rational integer of `𝒪` enters `D ⊗ A` as the scalar `n • 1`
private theorem intCast_tmul_one {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℤ) :
    (((n : hurwitzOrder) : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : A)) = (n : ℚ) • (1 : ℍ[ℚ] ⊗[ℚ] A) := by
  rw [Subring.coe_intCast, ← map_intCast (algebraMap ℚ ℍ[ℚ]) n, Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul', ← Algebra.TensorProduct.one_def]

private theorem mul_intCast_tmul_one {v : HeightOneSpectrum (𝓞 ℚ)} (x : Dv ℚ ℍ[ℚ] v) (n : ℤ) :
    x * (((n : hurwitzOrder) : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = (n : ℚ) • x := by
  rw [intCast_tmul_one, mul_smul_comm, mul_one]

-- an integer multiple, read as a local scalar
private theorem intCast_smul_eq {v : HeightOneSpectrum (𝓞 ℚ)} (x : Dv ℚ ℍ[ℚ] v) (n : ℤ) :
    (n : ℚ) • x = (n : v.adicCompletion ℚ) • x := by
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

/-- **The denominator ideal** `I_g = {y ∈ 𝒪 | g⁻¹ y ∈ 𝒪 ⊗ ℤ̂}` of `g ∈ D_f^×`, a right ideal of the
Hurwitz order. -/
def denominatorIdeal (g : Dfx ℚ ℍ[ℚ]) : Submodule (hurwitzOrder)ᵐᵒᵖ hurwitzOrder where
  carrier := {y | ∀ w : HeightOneSpectrum (𝓞 ℚ),
    toLocal ℚ ℍ[ℚ] w ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) * ((y : ℍ[ℚ]) ⊗ₜ[ℚ] 1) ∈ 𝒪loc w}
  add_mem' := by
    intro a b ha hb w
    rw [Subring.coe_add, TensorProduct.add_tmul, mul_add]
    exact add_mem (ha w) (hb w)
  zero_mem' := by
    intro w
    rw [Subring.coe_zero, TensorProduct.zero_tmul, mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro c y hy w
    rw [MulOpposite.smul_eq_mul_unop, Subring.coe_mul, ← mul_one (1 : w.adicCompletion ℚ),
      ← Algebra.TensorProduct.tmul_mul_tmul, ← mul_assoc]
    exact mul_mem (hy w) (tmul_mem_localOrder (c.unop).2 (one_mem _))

-- a common denominator of `g⁻¹` lies in `I_g`
private theorem intCast_mem_denominatorIdeal {g : Dfx ℚ ℍ[ℚ]} {N : ℤ}
    (hN : ∀ w, toLocal ℚ ℍ[ℚ] w ((N : ℚ) • ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ])) ∈ 𝒪loc w) :
    ((N : ℤ) : hurwitzOrder) ∈ denominatorIdeal g := fun w => by
  rw [mul_intCast_tmul_one, ← map_smul]
  exact hN w

private theorem coe_intCast_ne_zero {n : ℤ} (hn : n ≠ 0) : ((n : hurwitzOrder) : ℍ[ℚ]) ≠ 0 := by
  rw [Subring.coe_intCast]
  exact fun h => hn (by exact_mod_cast congrArg QuaternionAlgebra.re h)

/-- `I_g` is nonzero: it contains a common denominator of `g⁻¹`. -/
theorem denominatorIdeal_ne_bot (g : Dfx ℚ ℍ[ℚ]) : denominatorIdeal g ≠ ⊥ := by
  obtain ⟨N, hN0, hN⟩ := exists_intCast_smul_toLocal_mem ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ])
  exact (denominatorIdeal g).ne_bot_iff.mpr ⟨_, intCast_mem_denominatorIdeal hN,
    fun h => coe_intCast_ne_zero hN0 (by rw [h, Subring.coe_zero])⟩

/-- The local lattice of `g` at `w` is generated, modulo `N`, by global elements of the
denominator ideal. -/
theorem exists_mem_denominatorIdeal_sub_smul {g : Dfx ℚ ℍ[ℚ]} {N : ℤ} (hN : N ≠ 0)
    (hNmem : ((N : ℤ) : hurwitzOrder) ∈ denominatorIdeal g) {w : HeightOneSpectrum (𝓞 ℚ)}
    {ξ : Dv ℚ ℍ[ℚ] w} (hξ : ξ ∈ 𝒪loc w)
    (hξg : toLocal ℚ ℍ[ℚ] w ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) * ξ ∈ 𝒪loc w) :
    ∃ y ∈ denominatorIdeal g, ∃ δ ∈ 𝒪loc w, ξ - (y : ℍ[ℚ]) ⊗ₜ[ℚ] 1 = (N : ℚ) • δ := by
  classical
  -- the finitely many bad places of `g⁻¹`, away from `w`
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) |
      toLocal ℚ ℍ[ℚ] v ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) ∉ 𝒪loc v}.Finite :=
    Filter.eventually_cofinite.mp (eventually_toLocal_mem_localOrder _)
  have hwT : w ∉ hfin.toFinset.erase w := Finset.notMem_erase w _
  -- integer approximations of the coordinates of `ξ` modulo `N²`
  choose z hzw hzT using fun i : Fin 4 => exists_intCast_approx (hfin.toFinset.erase w) hwT
    ⟨_, mem_localOrder_iff.mp hξ i⟩ (M := N ^ 2) (pow_ne_zero 2 hN)
  simp only [Rat.cast_intCast] at hzw hzT
  -- the global element `y = ∑ zᵢ bᵢ` of the Hurwitz order
  set y₀ : ℍ[ℚ] := ∑ i, (z i : ℚ) • hurwitzBasis i with hy₀
  have hrepr : ∀ i, hurwitzBasis.repr y₀ i = z i := fun i => by
    simp [hy₀, Finsupp.single_apply]
  have hy₀mem : y₀ ∈ hurwitzOrder := by
    rw [← orderOf_hurwitzBasis]
    exact mem_orderOf_iff.mpr fun i => by rw [hrepr i]; exact ⟨z i, map_intCast _ _⟩
  let y : hurwitzOrder := ⟨y₀, hy₀mem⟩
  have hyrepr : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (i : Fin 4),
      (rightBasis (R := v.adicCompletion ℚ) hurwitzBasis).repr ((y : ℍ[ℚ]) ⊗ₜ[ℚ] 1) i =
        (z i : v.adicCompletion ℚ) := fun v i => by
    rw [rightBasis_repr_tmul, one_mul]
    show algebraMap ℚ _ (hurwitzBasis.repr y₀ i) = _
    rw [hrepr, map_intCast]
  -- `N • g⁻¹` is integral everywhere
  have hNg : ∀ v, (N : v.adicCompletion ℚ) • toLocal ℚ ℍ[ℚ] v ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) ∈
      𝒪loc v := fun v => by
    have h := hNmem v
    rwa [mul_intCast_tmul_one, intCast_smul_eq] at h
  -- the error term, divided by `N`
  set δ : Dv ℚ ℍ[ℚ] w := (N : w.adicCompletion ℚ)⁻¹ • (ξ - (y : ℍ[ℚ]) ⊗ₜ[ℚ] 1) with hδ_def
  have hδmem : δ ∈ 𝒪loc w := mem_localOrder_iff.mpr fun i => by
    rw [hδ_def, map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, hyrepr w i,
      ← div_eq_inv_mul]
    exact valued_div_intCast_le_one hN (hzw i)
  have hNδ : (N : w.adicCompletion ℚ) • δ = ξ - (y : ℍ[ℚ]) ⊗ₜ[ℚ] 1 := by
    rw [hδ_def, smul_smul, mul_inv_cancel₀ (intCast_ne_zero_adic hN), one_smul]
  refine ⟨y, fun v => ?_, δ, hδmem, by rw [intCast_smul_eq, hNδ]⟩
  rcases eq_or_ne v w with rfl | hvw
  · -- at `w`: `y ⊗ 1 = ξ − N δ`, and both terms are integral against `g⁻¹`
    rw [show (y : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) = ξ - (N : v.adicCompletion ℚ) • δ by
      rw [hNδ, sub_sub_cancel], mul_sub, mul_smul_comm, ← smul_mul_assoc]
    exact sub_mem hξg (mul_mem (hNg v) hδmem)
  · by_cases hvT : v ∈ hfin.toFinset.erase w
    · -- a bad place of `g⁻¹`: the `zᵢ` are `v`-divisible by `N²`, so `y ⊗ 1 = N • Y` with `Y`
      -- integral
      set Y : Dv ℚ ℍ[ℚ] v := (N : v.adicCompletion ℚ)⁻¹ • ((y : ℍ[ℚ]) ⊗ₜ[ℚ] 1) with hY_def
      have hY : Y ∈ 𝒪loc v := mem_localOrder_iff.mpr fun i => by
        rw [hY_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hyrepr v i, ← div_eq_inv_mul]
        exact valued_div_intCast_le_one hN (hzT i v hvT)
      rw [show (y : ℍ[ℚ]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) = (N : v.adicCompletion ℚ) • Y by
        rw [hY_def, smul_smul, mul_inv_cancel₀ (intCast_ne_zero_adic hN), one_smul],
        mul_smul_comm, ← smul_mul_assoc]
      exact mul_mem (hNg v) hY
    · -- a good place of `g⁻¹`: both factors are integral
      exact mul_mem (not_not.mp fun hbad =>
          hvT (Finset.mem_erase.mpr ⟨hvw, hfin.mem_toFinset.mpr hbad⟩))
        (tmul_mem_localOrder y.2 (one_mem _))

private theorem toLocal_unitsIncl (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ])ˣ) :
    toLocal ℚ ℍ[ℚ] w ((unitsIncl ℚ ℍ[ℚ] x : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) = (x : ℍ[ℚ]) ⊗ₜ[ℚ] 1 := by
  rw [coe_unitsIncl, ← incl_apply, toLocal_incl]

/-- A generator of the denominator ideal divides `g` on the left, locally everywhere. -/
theorem exists_eq_generator_mul {g : Dfx ℚ ℍ[ℚ]}
    (hg : ∀ w, toLocal ℚ ℍ[ℚ] w (g : Df ℚ ℍ[ℚ]) ∈ 𝒪loc w) {x : hurwitzOrder}
    (hx : denominatorIdeal g = Submodule.span (hurwitzOrder)ᵐᵒᵖ {x})
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ ζ ∈ 𝒪loc w, toLocal ℚ ℍ[ℚ] w (g : Df ℚ ℍ[ℚ]) = ((x : ℍ[ℚ]) ⊗ₜ[ℚ] 1) * ζ := by
  obtain ⟨N, hN, hNint⟩ := exists_intCast_smul_toLocal_mem ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ])
  have hNmem := intCast_mem_denominatorIdeal hNint
  -- `g` is its own integrality certificate: `g⁻¹ g = 1`
  have hinv : toLocal ℚ ℍ[ℚ] w ((g⁻¹ : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) *
      toLocal ℚ ℍ[ℚ] w (g : Df ℚ ℍ[ℚ]) ∈ 𝒪loc w := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    exact one_mem _
  obtain ⟨y, hy, δ, hδ, heq⟩ := exists_mem_denominatorIdeal_sub_smul hN hNmem (hg w) hinv
  -- both the approximation `y` and the denominator `N` are right multiples of `x`
  rw [hx] at hy hNmem
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨s₀, hs₀⟩ := Submodule.mem_span_singleton.mp hNmem
  refine ⟨((s.unop : hurwitzOrder) : ℍ[ℚ]) ⊗ₜ[ℚ] 1 +
      ((((s₀.unop : hurwitzOrder) : ℍ[ℚ]) ⊗ₜ[ℚ] 1) * δ),
    add_mem (tmul_mem_localOrder (s.unop).2 (one_mem _))
      (mul_mem (tmul_mem_localOrder (s₀.unop).2 (one_mem _)) hδ), ?_⟩
  rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul,
    ← MulOpposite.smul_eq_mul_unop, hs, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, ← Subring.coe_mul, ← MulOpposite.smul_eq_mul_unop, hs₀, intCast_tmul_one,
    smul_mul_assoc, one_mul]
  exact sub_eq_iff_eq_add'.mp heq

/-- Class number one for everywhere-integral `g`. -/
theorem exists_factor_of_forall_mem {g : Dfx ℚ ℍ[ℚ]}
    (hg : ∀ w, toLocal ℚ ℍ[ℚ] w (g : Df ℚ ℍ[ℚ]) ∈ 𝒪loc w) :
    ∃ d ∈ globalUnits ℚ ℍ[ℚ], ∃ u ∈ U0, g = d * u := by
  obtain ⟨x, hx⟩ := right_ideal_principal (denominatorIdeal g)
  have hx0 : (x : ℍ[ℚ]) ≠ 0 := fun h => denominatorIdeal_ne_bot g (by
    rw [hx, show x = 0 from Subtype.ext h, Submodule.span_zero_singleton])
  have hxmem : x ∈ denominatorIdeal g := hx ▸ Submodule.mem_span_singleton_self x
  obtain ⟨d, hd⟩ : ∃ d : Dfx ℚ ℍ[ℚ], d = unitsIncl ℚ ℍ[ℚ] (Units.mk0 (x : ℍ[ℚ]) hx0) :=
    ⟨_, rfl⟩
  refine ⟨d, ⟨Units.mk0 (x : ℍ[ℚ]) hx0, hd.symm⟩, d⁻¹ * g, ?_, (mul_inv_cancel_left d g).symm⟩
  refine mem_U0_iff.mpr ⟨mem_adelicOrder_iff_forall.mpr fun w => ?_,
    mem_adelicOrder_iff_forall.mpr fun w => ?_⟩
  · -- `d⁻¹ g` is integral: the generator cancels against `exists_eq_generator_mul`
    obtain ⟨ζ, hζ, hgζ⟩ := exists_eq_generator_mul hg hx w
    rw [Units.val_mul, map_mul, hd, ← map_inv, toLocal_unitsIncl, Units.val_inv_eq_inv_val,
      Units.val_mk0, hgζ, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      inv_mul_cancel₀ hx0, ← Algebra.TensorProduct.one_def, one_mul]
    exact hζ
  · -- its inverse `g⁻¹ d` is integral: this is `x ∈ I_g`
    rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul, hd, toLocal_unitsIncl, Units.val_mk0]
    exact hxmem w

/-- **Class number one**: `D_f^× = D^× · U₀(1)`. -/
theorem exists_factor (g : Dfx ℚ ℍ[ℚ]) : ∃ d ∈ globalUnits ℚ ℍ[ℚ], ∃ u ∈ U0, g = d * u := by
  obtain ⟨N, hN0, hNint⟩ := exists_intCast_smul_toLocal_mem (g : Df ℚ ℍ[ℚ])
  obtain ⟨dN, hdN⟩ : ∃ d : Dfx ℚ ℍ[ℚ], d = unitsIncl ℚ ℍ[ℚ]
      (Units.mk0 (((N : ℤ) : hurwitzOrder) : ℍ[ℚ]) (coe_intCast_ne_zero hN0)) := ⟨_, rfl⟩
  -- clearing denominators: `dN g = N g` is everywhere integral
  have hg' : ∀ w, toLocal ℚ ℍ[ℚ] w ((dN * g : Dfx ℚ ℍ[ℚ]) : Df ℚ ℍ[ℚ]) ∈ 𝒪loc w := fun w => by
    rw [Units.val_mul, map_mul, hdN, toLocal_unitsIncl, Units.val_mk0, intCast_tmul_one,
      smul_mul_assoc, one_mul, ← map_smul]
    exact hNint w
  obtain ⟨d, hd, u, hu, heq⟩ := exists_factor_of_forall_mem hg'
  exact ⟨dN⁻¹ * d, mul_mem (inv_mem ⟨_, hdN.symm⟩) hd, u, hu,
    by rw [mul_assoc, ← heq, inv_mul_cancel_left]⟩

end Dictionary

/-- **The class set of `U₀(1)` is a point.** -/
theorem subsingleton_classSet_U0 : Subsingleton (classSet ℚ ℍ[ℚ] U0) := by
  have h : ∀ g : Dfx ℚ ℍ[ℚ],
      (DoubleCoset.mk _ _ g : classSet ℚ ℍ[ℚ] U0) = DoubleCoset.mk _ _ 1 := fun g => by
    obtain ⟨d, hd, u, hu, rfl⟩ := exists_factor g
    exact classSet_mk_eq_iff.mpr ⟨d⁻¹, inv_mem hd, u⁻¹, inv_mem hu, by group⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, rfl⟩ := Quotient.exists_rep p
  obtain ⟨g', rfl⟩ := Quotient.exists_rep q
  exact (h g).trans (h g').symm

/-- **Every open subgroup of `D_f^×` has a finite class set**, for Hamilton's quaternions. -/
instance hasFiniteClassSets : HasFiniteClassSets ℚ ℍ[ℚ] :=
  haveI : Module.Finite ℚ ℍ[ℚ] := Module.Finite.of_basis hurwitzBasis
  haveI : Subsingleton (classSet ℚ ℍ[ℚ] U0) := subsingleton_classSet_U0
  hasFiniteClassSets_of_finite isCompact_U0 isOpen_U0

end Hamilton
