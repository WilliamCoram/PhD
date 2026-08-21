/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.U3.«2_Level»

/-!
# Local coordinates of the Hurwitz order and integer approximation

Part 2 of the class-number-one chain (board `.mathlib-quality/hurwitz-cn1/`).

The idelic dictionary recovers a global lattice from its completions through the
elementary content of [Voight, Lemma 9.5.3] (p. 145): on each coordinate of a free
`ℤ`-basis, `ℤ/N ≃ 𝓞_w/N𝓞_w` — that is, an element of the local integers can be
approximated to any modulus `N` by a rational integer, with prescribed divisibility at
finitely many other places.  This file provides exactly that, for the coordinates of
`localOrder w` against the Hurwitz `ℤ`-basis `1, i, j, ω`.

* `JacobsSlash.hurwitzGen`: the basis tuple `![1, qi, qj, qomega]`.
* `JacobsSlash.mem_localOrder_iff_exists_coords`: `localOrder w` is the set of
  `𝓞_w`-combinations of the basis (the public form of `Level.lean`'s
  `localOrder ≤ localSpan` bridge).
* `JacobsSlash.exists_intCast_valued_sub_le`: density of `ℤ` in `𝓞_w`
  (via mathlib's `denseRange_algebraMap` for the adic completion).
* `JacobsSlash.exists_intCast_valued_eq_one_of_le`: a nonzero rational integer that is a
  `w`-unit and as `v`-divisible as a prescribed modulus at each place `v` of a finite set
  `T ∌ w`.
* `JacobsSlash.exists_intCast_approx`: the multi-place version — close to a given
  local integer at `w`, valuation-small at each place of a finite set `T ∌ w`.
-/

open Quaternion IsDedekindDomain NumberField QMF
open scoped TensorProduct

/- See `Setting.lean`: pin the adic `Algebra ℚ K_w` instance path used by the `QMF`
framework, keeping statements syntactically aligned with `Level.lean`'s. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/-- The `ℤ`-basis `1, i, j, ω` of the Hurwitz order, as a `Fin 4`-tuple
[Jacobs p. 22; Voight (11.1.3)]. -/
noncomputable def hurwitzGen : Fin 4 → D := ![1, qi, qj, qomega]

/-- Each `hurwitzGen i` is a Hurwitz quaternion. -/
theorem hurwitzGen_mem (i : Fin 4) : hurwitzGen i ∈ hurwitzOrder := by
  fin_cases i
  exacts [Subring.one_mem _, qi_mem, qj_mem, qomega_mem]

/-- **Reconstruction from coordinates**: a Hurwitz quaternion is the integer combination of
`1, i, j, ω` read off by `mem_hurwitzOrder_iff_isInt` (`d.re − d.imK`, `d.imI − d.imK`,
`d.imJ − d.imK`, `2 d.imK`).  The converse direction of `mem_hurwitzOrder_iff_coords`,
in the explicit form the tensor computation consumes. -/
private theorem exists_intCast_smul_eq {d : D} (hd : d ∈ hurwitzOrder) :
    ∃ n : Fin 4 → ℤ, d = ∑ i, (n i : ℚ) • hurwitzGen i := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨e, he⟩⟩ := mem_hurwitzOrder_iff_isInt.mp hd
  refine ⟨![a, b, c, e], ?_⟩
  rw [Fin.sum_univ_four]
  simp only [hurwitzGen, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [re_add, imI_add, imJ_add, imK_add, re_smul, imI_smul, imJ_smul, imK_smul,
      smul_eq_mul, re_one, imI_one, imJ_one, imK_one, qi_re, qi_imI, qi_imJ, qi_imK,
      qj_re, qj_imI, qj_imJ, qj_imK, qomega_re, qomega_imI, qomega_imJ, qomega_imK] <;>
    linarith

/-- The set of `𝓞_w`-combinations of `1 ⊗ 1, i ⊗ 1, j ⊗ 1, ω ⊗ 1`, as an additive
submonoid.  (Presented additively for the same reason as `Level.lean`'s `localSpan`: the
only closure property needing real work is multiplicativity.) -/
private noncomputable def coordSpan (w : HeightOneSpectrum (RingOfIntegers ℚ)) :
    AddSubmonoid (D ⊗[ℚ] w.adicCompletion ℚ) where
  carrier := {x | ∃ c : Fin 4 → w.adicCompletionIntegers ℚ,
    x = ∑ i, hurwitzGen i ⊗ₜ[ℚ] (c i : w.adicCompletion ℚ)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

/-- A pure tensor `d ⊗ z` with `d` Hurwitz and `z` a local integer has integer coordinates:
expand `d` by `exists_intCast_smul_eq` and move the scalars across the tensor. -/
private theorem tmul_mem_coordSpan {w : HeightOneSpectrum (RingOfIntegers ℚ)} {d : D}
    (hd : d ∈ hurwitzOrder) (z : w.adicCompletionIntegers ℚ) :
    d ⊗ₜ[ℚ] (z : w.adicCompletion ℚ) ∈ coordSpan w := by
  obtain ⟨n, hn⟩ := exists_intCast_smul_eq hd
  refine ⟨fun i => ⟨(n i : w.adicCompletion ℚ), intCast_mem _ _⟩ * z, ?_⟩
  rw [hn, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.smul_tmul, Algebra.smul_def, map_intCast]
  rfl

/-- `coordSpan` is in fact a subring: by bilinearity a product of two basis combinations is a
sum of pure tensors `(hurwitzGen i * hurwitzGen j) ⊗ (a i * b j)`, and both factors are again
integral. -/
private noncomputable def coordSubring (w : HeightOneSpectrum (RingOfIntegers ℚ)) :
    Subring (D ⊗[ℚ] w.adicCompletion ℚ) where
  carrier := coordSpan w
  zero_mem' := zero_mem _
  one_mem' := by
    have h := tmul_mem_coordSpan (w := w) (Subring.one_mem hurwitzOrder) 1
    rwa [OneMemClass.coe_one, ← Algebra.TensorProduct.one_def] at h
  add_mem' := add_mem
  neg_mem' := by
    rintro x ⟨a, rfl⟩
    exact ⟨-a, by simp [TensorProduct.tmul_neg]⟩
  mul_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    rw [Finset.sum_mul_sum]
    refine AddSubmonoid.sum_mem _ fun i _ => AddSubmonoid.sum_mem _ fun j _ => ?_
    have h := tmul_mem_coordSpan (w := w)
      (hurwitzOrder.mul_mem (hurwitzGen_mem i) (hurwitzGen_mem j)) (a i * b j)
    rwa [MulMemClass.coe_mul, ← Algebra.TensorProduct.tmul_mul_tmul] at h

/-- **`localOrder w` in coordinates**: the local order is exactly the set of
`𝓞_w`-linear combinations of the images of `1, i, j, ω`.  (Forward direction:
`Subring.closure_le` against `coordSubring`, whose multiplicativity multiplies out
products of basis combinations via `mem_hurwitzOrder_iff_isInt`; backward:
`tmul_mem_localOrder` and closure under sums.) -/
theorem mem_localOrder_iff_exists_coords {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    {x : D ⊗[ℚ] w.adicCompletion ℚ} :
    x ∈ localOrder w ↔ ∃ c : Fin 4 → w.adicCompletionIntegers ℚ,
      x = ∑ i, hurwitzGen i ⊗ₜ[ℚ] (c i : w.adicCompletion ℚ) := by
  constructor
  · intro hx
    have h : localOrder w ≤ coordSubring w := by
      rw [localOrder, Subring.closure_le]
      rintro y (⟨d, hd, rfl⟩ | ⟨z, rfl⟩)
      · have h := tmul_mem_coordSpan (w := w) hd 1
        rwa [OneMemClass.coe_one] at h
      · exact tmul_mem_coordSpan (Subring.one_mem hurwitzOrder) z
    exact h hx
  · rintro ⟨c, rfl⟩
    exact Subring.sum_mem _ fun i _ => tmul_mem_localOrder (hurwitzGen_mem i) (c i)

/-- The completed valuation of a rational, read on `ℚ`. -/
private theorem valued_algebraMap (v : HeightOneSpectrum (RingOfIntegers ℚ)) (q : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q

/-- The completed valuation of a rational integer, read on `ℚ`. -/
private theorem valued_intCast (v : HeightOneSpectrum (RingOfIntegers ℚ)) (n : ℤ) :
    Valued.v ((n : v.adicCompletion ℚ)) = v.valuation ℚ (n : ℚ) := by
  rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) n, valued_algebraMap]

/-- The completed valuation of a rational integer as an `intValuation` on `𝓞_ℚ ≃ ℤ`; this is
the form the ideal-theoretic API (`intValuation_le_pow_iff_mem`, `intValuation_eq_one_iff_…`)
consumes. -/
private theorem valued_intCast_eq_intValuation (v : HeightOneSpectrum (RingOfIntegers ℚ))
    (n : ℤ) :
    Valued.v ((n : v.adicCompletion ℚ)) = v.intValuation (Rat.ringOfIntegersEquiv.symm n) := by
  rw [valued_intCast, ← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) v
    (Rat.ringOfIntegersEquiv.symm n)]
  exact congrArg _ (Rat.ringOfIntegersEquiv_symm_apply_coe n).symm

/-- A rational integer is a local integer at every place. -/
private theorem valued_intCast_le_one (v : HeightOneSpectrum (RingOfIntegers ℚ)) (n : ℤ) :
    Valued.v ((n : v.adicCompletion ℚ)) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (intCast_mem _ n)

/-- A nonzero rational integer has nonzero valuation at every place. -/
private theorem valued_intCast_ne_zero {v : HeightOneSpectrum (RingOfIntegers ℚ)} {n : ℤ}
    (hn : n ≠ 0) : Valued.v ((n : v.adicCompletion ℚ)) ≠ 0 := by
  rw [valued_intCast]
  exact (Valuation.ne_zero_iff _).mpr (Int.cast_ne_zero.mpr hn)

/-- **Density of `ℤ` in the local integers** (the coordinatewise content of
[Voight (9.5.2)]): a `w`-adic integer is approximable by a rational integer to any
integer modulus.  A rational within `v(M)` of `c` comes from
`HeightOneSpectrum.denseRange_algebraMap`; it is `w`-integral by the ultrametric
inequality, so `HeightOneSpectrum.exists_valuation_sub_lt_of_integer` (which clears the
`w`-unit denominator) replaces it by an element of `𝓞_ℚ ≃ ℤ`. -/
theorem exists_intCast_valued_sub_le {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (c : w.adicCompletionIntegers ℚ) {M : ℤ} (hM : M ≠ 0) :
    ∃ z : ℤ, Valued.v ((c : w.adicCompletion ℚ) - (z : w.adicCompletion ℚ))
      ≤ Valued.v ((M : w.adicCompletion ℚ)) := by
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
  have hq1 : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) q) ≤ 1 := by
    have hc : Valued.v ((c : w.adicCompletion ℚ)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2
    have h := Valuation.map_add_le Valued.v (hyball.le.trans (valued_intCast_le_one w M)) hc
    rwa [sub_add_cancel] at h
  rw [valued_algebraMap] at hq1
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer w hq1
    (Units.mk0 (Valued.v ((M : w.adicCompletion ℚ))) hMv)
  refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
  have hz : ((Rat.ringOfIntegersEquiv a : ℤ) : w.adicCompletion ℚ)
      = algebraMap ℚ (w.adicCompletion ℚ) (algebraMap (RingOfIntegers ℚ) ℚ a) := by
    rw [← Rat.ringOfIntegersEquiv_apply_coe a, map_intCast]
  rw [← sub_add_sub_cancel _ (algebraMap ℚ (w.adicCompletion ℚ) q) _]
  refine Valuation.map_add_le Valued.v ?_ ?_
  · rw [Valuation.map_sub_swap]
    exact hyball.le
  · rw [hz, ← map_sub, valued_algebraMap, Valuation.map_sub_swap]
    exact ha.le

/-- The per-place kernel of `exists_intCast_valued_eq_one_of_le`: at a place `v ≠ w` there is
a nonzero rational integer that is a `w`-unit and `v`-adically at least as divisible as `M`.
Distinct height-one primes of a Dedekind domain are distinct maximal ideals, so
`v.asIdeal ⊄ w.asIdeal`; a witness `r` of that, raised to a power large enough to beat
`v(M)` (`WithZero.exists_exp_neg_natCast_lt`), does the job. -/
private theorem exists_intCast_eq_one_of_le_aux {w v : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hvw : v ≠ w) {M : ℤ} (hM : M ≠ 0) :
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

/-- A rational integer that is a `w`-unit but valuation-`≤ v(M)` at every place of a
finite set `T ∌ w`: induct on `T`, multiplying in the per-place witnesses of
`exists_intCast_eq_one_of_le_aux` (each of which is a `w`-unit, and integral — hence of
valuation `≤ 1` — at every other place). -/
theorem exists_intCast_valued_eq_one_of_le {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (T : Finset (HeightOneSpectrum (RingOfIntegers ℚ))) (hw : w ∉ T) {M : ℤ} (hM : M ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ Valued.v ((m : w.adicCompletion ℚ)) = 1 ∧
      ∀ v ∈ T, Valued.v ((m : v.adicCompletion ℚ))
        ≤ Valued.v ((M : v.adicCompletion ℚ)) := by
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

/-- **Integer approximation with divisibility side conditions** (the elementary core of
the local-global dictionary, [Voight, Lemma 9.5.3]): a `w`-adic integer is approximable
mod `M` at `w` by a rational integer that is simultaneously valuation-small at each
place of a finite set `T ∌ w`.  (Write `z = m * t` with `m` the `w`-unit of
`exists_intCast_valued_eq_one_of_le` and `t` an integer approximation of `c / m`.) -/
theorem exists_intCast_approx {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (T : Finset (HeightOneSpectrum (RingOfIntegers ℚ))) (hw : w ∉ T)
    (c : w.adicCompletionIntegers ℚ) {M : ℤ} (hM : M ≠ 0) :
    ∃ z : ℤ, Valued.v ((c : w.adicCompletion ℚ) - (z : w.adicCompletion ℚ))
        ≤ Valued.v ((M : w.adicCompletion ℚ)) ∧
      ∀ v ∈ T, Valued.v ((z : v.adicCompletion ℚ))
        ≤ Valued.v ((M : v.adicCompletion ℚ)) := by
  obtain ⟨m, -, hmw, hmT⟩ := exists_intCast_valued_eq_one_of_le T hw hM
  have hmne : (m : w.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mp (hmw ▸ one_ne_zero)
  have hc' : (c : w.adicCompletion ℚ) / (m : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_div, hmw, div_one]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2
  obtain ⟨t, ht⟩ := exists_intCast_valued_sub_le ⟨_, hc'⟩ hM
  refine ⟨m * t, ?_, ?_⟩
  · have key : (c : w.adicCompletion ℚ) - ((m * t : ℤ) : w.adicCompletion ℚ)
        = (m : w.adicCompletion ℚ) *
          ((c : w.adicCompletion ℚ) / (m : w.adicCompletion ℚ) - (t : w.adicCompletion ℚ)) := by
      rw [mul_sub, mul_div_cancel₀ _ hmne, Int.cast_mul]
    rw [key, Valuation.map_mul, hmw, one_mul]
    exact ht
  · intro v hv
    rw [Int.cast_mul, Valuation.map_mul]
    exact (mul_le_mul' (hmT v hv) (valued_intCast_le_one v t)).trans_eq (mul_one _)

end JacobsSlash
