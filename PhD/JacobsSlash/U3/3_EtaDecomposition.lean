/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.Padics.RingHoms
import PhD.JacobsSlash.U3.«2_Level»
import PhD.QMF.«04_UpiElement»

/-!
# The right-coset decomposition of `U₁(9)·η₃·U₁(9)` [Jacobs, Lemma 2.3]

The thesis display, in its own right-handed form [Jacobs, p. 20]:

> "`U (3 0; 0 1) U = ⊔_t U (3 0; 9t 1)`"

`η₃` is the adelic element with `3`-component `(3 0; 0 1)` and trivial components
elsewhere; the three right-coset representatives are `v_t = η₃ · u_t` with
`u_t = (1 0; 9t 1)` at `3`, so `v_t` has `3`-component `(3 0; 9t 1)` — the thesis's
matrices verbatim.  Right cosets are classes of `QuotientGroup.rightRel U₁(9)`
(`AbstractHeckeOperatorSlash.RightCosets`), and the covering statement is a
`Set.BijOn` onto the image of `{η₃}·U₁(9)` — exactly the index set of
`heckeOperatorSlash`.

## Main definitions

* `JacobsSlash.eta3`: the adelic `η₃`, trivial away from `3` and `(3 0; 0 1)` at `3`.
* `JacobsSlash.etaRep`: the three coset representatives `v_t = η₃ · u_t`, `t : Fin 3`.

## Main results

* `JacobsSlash.etaRep_mul_inv_notMem`: the three right cosets are pairwise disjoint.
* `JacobsSlash.exists_etaRep_mem`: they cover `{η₃}·U₁(9)`.
* `JacobsSlash.bijOn_etaRep`: [Jacobs, Lemma 2.3] — `etaRep` is a bijection onto the
  image of `{η₃}·U₁(9)` in the right-coset space of `U₁(9)`.
* `JacobsSlash.finite_image_eta3`: the finiteness the slash Hecke sum needs.
-/

open Quaternion IsDedekindDomain NumberField QMF AbstractHeckeOperatorSlash
open scoped Pointwise TensorProduct

/- See `1_Setting.lean`: pin the adic `Algebra ℚ K₃` path, the one the `QMF` framework
uses. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/-- The uniformiser `3` of `K₃`, as the `Sigma0'.eta` datum. -/
noncomputable def pi3 : K₃ := (3 : K₃)

theorem valued_pi3_le_one : Valued.v pi3 ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mp norm_three_lt_one.le

theorem pi3_ne_zero : pi3 ≠ 0 := three_ne_zero

/-- The adelic Hecke element `η₃` [Jacobs, p. 24: "`η₃,q = 1` if `q ≠ 3`,
`(3 0; 0 1)` if `q = 3`"], in the thesis's own normalisation
(`v`-component `(3 0; 0 1)` via `etaAdelic'`). -/
noncomputable def eta3 : Dfx ℚ D := etaAdelic' ℚ D v₃ pi3 pi3_ne_zero

theorem eta3_mem_levelMonoid' : eta3 ∈ levelMonoid' ℚ D v₃ γ₉ γ₉_lt_one :=
  etaAdelic'_mem_levelMonoid' ℚ D v₃ γ₉ γ₉_lt_one pi3 valued_pi3_le_one pi3_ne_zero

/-- The lower unipotent `(1 0; c 1)` as a unit of `M₂(K₃)`. -/
noncomputable def lowerUnip (c : K₃) : (Matrix (Fin 2) (Fin 2) K₃)ˣ where
  val := Matrix.of ![![1, 0], ![c, 1]]
  inv := Matrix.of ![![1, 0], ![-c, 1]]
  val_inv := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem lowerUnip_val (c : K₃) :
    ((lowerUnip c : (Matrix (Fin 2) (Fin 2) K₃)ˣ) : Matrix (Fin 2) (Fin 2) K₃)
      = Matrix.of ![![1, 0], ![c, 1]] := rfl

@[simp] theorem lowerUnip_inv (c : K₃) :
    (((lowerUnip c)⁻¹ : (Matrix (Fin 2) (Fin 2) K₃)ˣ) : Matrix (Fin 2) (Fin 2) K₃)
      = Matrix.of ![![1, 0], ![-c, 1]] := rfl

theorem valued_le_one_of_le_γ₉ {c : K₃} (hc : Valued.v c ≤ γ₉) : Valued.v c ≤ 1 :=
  hc.trans γ₉_lt_one.le

theorem lowerUnip_mem_integralMatrices {c : K₃} (hc : Valued.v c ≤ 1) :
    ((lowerUnip c : (Matrix (Fin 2) (Fin 2) K₃)ˣ) : Matrix (Fin 2) (Fin 2) K₃)
      ∈ integralMatrices := by
  intro i j
  have hcn : ‖c‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hc
  fin_cases i <;> fin_cases j
  · simp
  · simp
  · simpa using hcn
  · simp

theorem lowerUnip_mem_sigma1 {c : K₃} (hc : Valued.v c ≤ γ₉) :
    ((lowerUnip c : (Matrix (Fin 2) (Fin 2) K₃)ˣ) : Matrix (Fin 2) (Fin 2) K₃) ∈ Sigma1 := by
  refine ⟨⟨fun i j => ?_, ?_, ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j
    · simp
    · simp
    · simpa using valued_le_one_of_le_γ₉ hc
    · simp
  · simpa using hc
  · simp
  · rw [Matrix.det_fin_two]; simp
  · simp

/-- The level element `u_t = (1 0; 9t 1)` at `3`, trivial elsewhere. -/
noncomputable def levelUnip (t : Fin 3) : Dfx ℚ D :=
  unitAt ℚ D v₃ (lowerUnip (9 * ((t : ℕ) : K₃)))

theorem valued_nine_mul_le (t : Fin 3) : Valued.v (9 * ((t : ℕ) : K₃)) ≤ γ₉ := by
  rw [map_mul]
  refine le_trans (mul_le_mul' valued_nine_le_γ₉ ?_) (by rw [mul_one])
  exact Valued.toNormedField.norm_le_one_iff.mp
    (IsUltrametricDist.norm_natCast_le_one (R := K₃) _)

theorem levelUnip_mem_U1_9 (t : Fin 3) : levelUnip t ∈ U1_9 := by
  have hc : Valued.v (9 * ((t : ℕ) : K₃)) ≤ γ₉ := valued_nine_mul_le t
  have hcn : Valued.v (-(9 * ((t : ℕ) : K₃))) ≤ γ₉ := by rwa [Valuation.map_neg]
  refine unitAt_mem_U1_9 (lowerUnip_mem_integralMatrices (valued_le_one_of_le_γ₉ hc))
    ?_ (lowerUnip_mem_sigma1 hc) ?_
  · rw [lowerUnip_inv]
    exact lowerUnip_mem_integralMatrices (valued_le_one_of_le_γ₉ hcn)
  · rw [lowerUnip_inv]
    exact lowerUnip_mem_sigma1 hcn

@[simp] theorem toMatrix_levelUnip (t : Fin 3) :
    toMatrix ℚ D v₃ (levelUnip t)
      = Matrix.of ![![1, 0], ![9 * ((t : ℕ) : K₃), 1]] := by
  rw [levelUnip, toMatrix_unitAt, lowerUnip_val]

@[simp] theorem toMatrix_levelUnip_inv (t : Fin 3) :
    toMatrix ℚ D v₃ (levelUnip t)⁻¹
      = Matrix.of ![![1, 0], ![-(9 * ((t : ℕ) : K₃)), 1]] := by
  rw [levelUnip, unitAt_inv, toMatrix_unitAt, lowerUnip_inv]

/-- The right-coset representatives `v_t = η₃ · u_t` of `U₁(9)·η₃·U₁(9)`: `3`-component
`(3 0; 9t 1)` — the thesis's matrices `U(3 0; 9t 1)` [Jacobs, Lemma 2.3, p. 20]
verbatim.  By construction each lies in `{η₃} · U₁(9)`, which is what `bijOn_etaRep`
needs. -/
noncomputable def etaRep : Fin 3 → Dfx ℚ D := fun t => eta3 * levelUnip t

theorem etaRep_mem_levelMonoid' (t : Fin 3) :
    etaRep t ∈ levelMonoid' ℚ D v₃ γ₉ γ₉_lt_one :=
  Submonoid.mul_mem _ eta3_mem_levelMonoid'
    (U1_9_subset_levelMonoid (levelUnip_mem_U1_9 t))

theorem toMatrix_eta3 :
    toMatrix ℚ D v₃ eta3 = Matrix.of ![![(3 : K₃), 0], ![0, 1]] := by
  rw [eta3, toMatrix_etaAdelic' ℚ D v₃ γ₉ γ₉_lt_one pi3 valued_pi3_le_one pi3_ne_zero]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Sigma0'.eta, pi3]

/-- The `3`-component of `v_t` is `(3 0; 9t 1)`. -/
theorem toMatrix_etaRep (t : Fin 3) :
    toMatrix ℚ D v₃ (etaRep t) = Matrix.of ![![(3 : K₃), 0], ![9 * ((t : ℕ) : K₃), 1]] := by
  rw [etaRep, map_mul, toMatrix_eta3, toMatrix_levelUnip]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The `3`-components of the representatives lie in `Σ₁(9)`.  (In the thesis
orientation the congruence is exact: the `(1,1)`-entry is literally `1`.) -/
theorem toMatrix_etaRep_mem_sigma1 (t : Fin 3) :
    toMatrix ℚ D v₃ (etaRep t) ∈ Sigma1 := by
  have hc : Valued.v (9 * ((t : ℕ) : K₃)) ≤ γ₉ := valued_nine_mul_le t
  rw [toMatrix_etaRep]
  refine ⟨⟨fun i j => ?_, ?_, ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j
    · simpa [pi3] using valued_pi3_le_one
    · simp
    · simpa using valued_le_one_of_le_γ₉ hc
    · simp
  · simpa using hc
  · simp
  · rw [Matrix.det_fin_two]
    simp
  · simp

/-- The `3`-component of `v_s⁻¹` is `(1/3 0; −3s 1)`, the matrix inverse of
`toMatrix_etaRep` (inverses in a monoid are unique). -/
theorem toMatrix_etaRep_inv (s : Fin 3) :
    toMatrix ℚ D v₃ ((etaRep s)⁻¹)
      = Matrix.of ![![(3 : K₃)⁻¹, 0], ![-(3 * ((s : ℕ) : K₃)), 1]] := by
  have h3 : (3 : K₃) ≠ 0 := three_ne_zero
  have h1 : toMatrix ℚ D v₃ ((etaRep s)⁻¹) * toMatrix ℚ D v₃ (etaRep s) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : toMatrix ℚ D v₃ (etaRep s)
      * (Matrix.of ![![(3 : K₃)⁻¹, 0], ![-(3 * ((s : ℕ) : K₃)), 1]]) = 1 := by
    rw [toMatrix_etaRep]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.one_apply]
    · simp [h3]
    · simp
    · simp; ring
    · simp
  calc toMatrix ℚ D v₃ ((etaRep s)⁻¹)
      = toMatrix ℚ D v₃ ((etaRep s)⁻¹)
          * (toMatrix ℚ D v₃ (etaRep s)
            * Matrix.of ![![(3 : K₃)⁻¹, 0], ![-(3 * ((s : ℕ) : K₃)), 1]]) := by
        rw [h2, mul_one]
    _ = Matrix.of ![![(3 : K₃)⁻¹, 0], ![-(3 * ((s : ℕ) : K₃)), 1]] := by
        rw [← mul_assoc, h1, one_mul]

/-- The `3`-component of `v_t v_s⁻¹` is the lower unipotent `(1 0; 3(t−s) 1)`. -/
theorem toMatrix_etaRep_mul_inv (t s : Fin 3) :
    toMatrix ℚ D v₃ (etaRep t * (etaRep s)⁻¹)
      = Matrix.of ![![1, 0], ![3 * (((t : ℕ) : K₃) - ((s : ℕ) : K₃)), 1]] := by
  have h3 : (3 : K₃) ≠ 0 := three_ne_zero
  rw [map_mul, toMatrix_etaRep, toMatrix_etaRep_inv]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · field_simp
    ring
  · ring
  · field_simp
    ring
  · ring

/-- For distinct `s, t : Fin 3` the difference `t − s` is a unit at `3` (it is `±1` or
`±2`). -/
theorem valued_sub_eq_one {s t : Fin 3} (hst : s ≠ t) :
    Valued.v (((t : ℕ) : K₃) - ((s : ℕ) : K₃)) = 1 := by
  have h2 : ‖(2 : K₃)‖ = 1 := norm_two_eq_one
  refine valued_eq_one_of_norm_eq_one ?_
  fin_cases s <;> fin_cases t <;> simp_all <;> norm_num [h2]

/-- **Disjointness** [Jacobs, Lemma 2.3]: distinct representatives give distinct right
cosets, because `v_t v_s⁻¹ = (1 0; 3(t−s) 1)` has lower-left valuation `v(3) = exp(−1)`,
one step *above* the threshold `γ₉ = exp(−2)` — this is exactly where "`3` is a
uniformizer" (`valued_three_eq`) is needed, `v(3) < 1` being too weak. -/
theorem etaRep_mul_inv_notMem {s t : Fin 3} (hst : s ≠ t) :
    etaRep t * (etaRep s)⁻¹ ∉ U1_9 := by
  intro hmem
  have hs1 := hmem.2.1
  rw [toMatrix_etaRep_mul_inv] at hs1
  have hle : Valued.v (3 * (((t : ℕ) : K₃) - ((s : ℕ) : K₃))) ≤ γ₉ := by
    simpa using hs1.1.2.1
  rw [map_mul, valued_three_eq, valued_sub_eq_one hst, mul_one, γ₉,
    ← WithZero.exp_eq_coe_ofAdd, WithZero.exp_le_exp] at hle
  omega

theorem etaRep_injective : Function.Injective etaRep := by
  intro s t h
  by_contra hst
  exact etaRep_mul_inv_notMem (Ne.symm hst)
    (by rw [h, mul_inv_cancel]; exact U1_9.one_mem)

/-- **The residue field of `𝓞₃` is `𝔽₃`**, in the form the covering argument needs: every
local integer is congruent to one of `0, 1, 2` modulo `3`.  Proved by transporting to
`ℤ_[3]` along mathlib's `PadicInt.adicCompletionIntegersEquiv` (which is available on the
nose because `v₃` is *defined* as `primesEquiv.symm ⟨3, _⟩`) and using
`PadicInt.zmodRepr`. -/
theorem exists_fin3_approx {x : K₃} (hx : x ∈ v₃.adicCompletionIntegers ℚ) :
    ∃ t : Fin 3, Valued.v (x - ((t : ℕ) : K₃)) ≤ Valued.v (3 : K₃) := by
  have key : ∃ (n : ℕ) (c : v₃.adicCompletionIntegers ℚ),
      n < 3 ∧ x - (n : K₃) = (c : K₃) * 3 := by
    set e := PadicInt.adicCompletionIntegersEquiv (RingOfIntegers ℚ) ⟨3, Nat.prime_three⟩
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    obtain ⟨n, hn3, hnmem⟩ := PadicInt.exists_mem_range y
    obtain ⟨b, hb⟩ : ∃ b : ℤ_[3], b * 3 = y - (n : ℤ_[3]) := by
      rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hnmem
    refine ⟨n, e b, hn3, ?_⟩
    have h1 := congrArg (fun w : v₃.adicCompletionIntegers ℚ => (w : K₃)) (congrArg e hb)
    simp only [map_mul, map_sub, map_natCast, map_ofNat, hy] at h1
    push_cast at h1
    exact h1.symm
  obtain ⟨n, c, hn3, hnc⟩ := key
  refine ⟨⟨n, hn3⟩, ?_⟩
  rw [show ((⟨n, hn3⟩ : Fin 3) : ℕ) = n from rfl, hnc, map_mul]
  exact le_trans (mul_le_mul' c.2 le_rfl) (by rw [one_mul])

@[simp] theorem toLocal_eta3_ne {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w ((eta3 : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) = 1 :=
  toLocal_etaAdelic'_ne ℚ D v₃ pi3 pi3_ne_zero hw

@[simp] theorem toLocal_eta3_inv_ne {w : HeightOneSpectrum (RingOfIntegers ℚ)}
    (hw : w ≠ v₃) :
    toLocal ℚ D w ((eta3⁻¹ : Dfx ℚ D) :
      D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) = 1 :=
  toLocal_etaAdelic'_inv_ne ℚ D v₃ pi3 pi3_ne_zero hw

/-- `(η₃ u) · v_t⁻¹ = η₃ · (u · u_t⁻¹) · η₃⁻¹`. -/
theorem mul_etaRep_inv_conj (t : Fin 3) (u : Dfx ℚ D) :
    (eta3 * u) * (etaRep t)⁻¹ = eta3 * (u * (levelUnip t)⁻¹) * eta3⁻¹ := by
  rw [etaRep, mul_inv_rev]
  group

/-- Away from `3`, the components of `(η₃ u) v_t⁻¹` and of its inverse are integral: the
`η₃` factors are trivial there, so only `u u_t⁻¹` is seen — and both `u` and `u_t` lie in
`U₀(1)`. -/
theorem toLocal_ne_mem_localOrder {u : Dfx ℚ D} (hu : u ∈ U1_9) (t : Fin 3)
    {w : HeightOneSpectrum (RingOfIntegers ℚ)} (hw : w ≠ v₃) :
    toLocal ℚ D w (((eta3 * u) * (etaRep t)⁻¹ : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w ∧
      toLocal ℚ D w ((((eta3 * u) * (etaRep t)⁻¹)⁻¹ : Dfx ℚ D) :
        D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈ localOrder w := by
  have hX : u * (levelUnip t)⁻¹ ∈ U0 :=
    U0.mul_mem hu.1 (U0.inv_mem (levelUnip_mem_U1_9 t).1)
  constructor
  · rw [mul_etaRep_inv_conj, Units.val_mul, Units.val_mul, map_mul, map_mul,
      toLocal_eta3_ne hw, toLocal_eta3_inv_ne hw, one_mul, mul_one]
    exact (hX w).1
  · rw [mul_etaRep_inv_conj, mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul,
      Units.val_mul, map_mul, map_mul, toLocal_eta3_ne hw, toLocal_eta3_inv_ne hw,
      one_mul, mul_one]
    exact (hX w).2

theorem toMatrix_eta3_inv :
    toMatrix ℚ D v₃ eta3⁻¹ = Matrix.of ![![(3 : K₃)⁻¹, 0], ![0, 1]] := by
  have h3 : (3 : K₃) ≠ 0 := three_ne_zero
  have h1 : toMatrix ℚ D v₃ eta3⁻¹ * toMatrix ℚ D v₃ eta3 = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : toMatrix ℚ D v₃ eta3 * Matrix.of ![![(3 : K₃)⁻¹, 0], ![0, 1]] = 1 := by
    rw [toMatrix_eta3]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h3]
  calc toMatrix ℚ D v₃ eta3⁻¹
      = toMatrix ℚ D v₃ eta3⁻¹
          * (toMatrix ℚ D v₃ eta3 * Matrix.of ![![(3 : K₃)⁻¹, 0], ![0, 1]]) := by
        rw [h2, mul_one]
    _ = Matrix.of ![![(3 : K₃)⁻¹, 0], ![0, 1]] := by rw [← mul_assoc, h1, one_mul]

/-- Conjugation by `η₃` at `3`: `(α β; γ δ) ↦ (α 3β; γ/3 δ)`.  (The same formula as the
left library's `η₃⁻¹·X·η₃` — the two conjugations are literally equal maps.) -/
theorem toMatrix_eta3_conj (X : Dfx ℚ D) :
    toMatrix ℚ D v₃ (eta3 * X * eta3⁻¹)
      = Matrix.of ![![toMatrix ℚ D v₃ X 0 0, 3 * toMatrix ℚ D v₃ X 0 1],
                    ![toMatrix ℚ D v₃ X 1 0 / 3, toMatrix ℚ D v₃ X 1 1]] := by
  have h3 : (3 : K₃) ≠ 0 := three_ne_zero
  rw [map_mul, map_mul, toMatrix_eta3, toMatrix_eta3_inv]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  all_goals (try field_simp)
  all_goals (try ring)

/-- The `3`-component of `(η₃ u) · v_t⁻¹`, in terms of that of `u`. -/
theorem toMatrix_mul_etaRep_inv (t : Fin 3) (u : Dfx ℚ D) :
    toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹)
      = Matrix.of ![![toMatrix ℚ D v₃ u 0 0 - 9 * ((t : ℕ) : K₃) * toMatrix ℚ D v₃ u 0 1,
            3 * toMatrix ℚ D v₃ u 0 1],
          ![(toMatrix ℚ D v₃ u 1 0 - 9 * ((t : ℕ) : K₃) * toMatrix ℚ D v₃ u 1 1) / 3,
            toMatrix ℚ D v₃ u 1 1]] := by
  rw [mul_etaRep_inv_conj, toMatrix_eta3_conj, map_mul, toMatrix_levelUnip_inv]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  all_goals ring

/-- `v(x) ≤ v(9)` implies `v(x/3) ≤ v(3)`. -/
theorem valued_div_three {x : K₃} (hx : Valued.v x ≤ Valued.v (9 : K₃)) :
    Valued.v (x / 3) ≤ Valued.v (3 : K₃) := by
  have h30 : Valued.v (3 : K₃) ≠ 0 := by
    rw [valued_three_eq]; exact WithZero.exp_ne_zero
  rw [map_div₀, div_le_iff₀ (lt_of_le_of_ne zero_le (Ne.symm h30)), ← map_mul,
    show (3 : K₃) * 3 = 9 by norm_num]
  exact hx

/-- The `3`-component of `((η₃ u) · v_t⁻¹)⁻¹ = η₃ · (u_t u⁻¹) · η₃⁻¹`, in terms of that
of `u⁻¹`. -/
theorem toMatrix_mul_etaRep_inv_inv (t : Fin 3) (u : Dfx ℚ D) :
    toMatrix ℚ D v₃ (((eta3 * u) * (etaRep t)⁻¹))⁻¹
      = Matrix.of ![![toMatrix ℚ D v₃ u⁻¹ 0 0, 3 * toMatrix ℚ D v₃ u⁻¹ 0 1],
          ![(9 * ((t : ℕ) : K₃) * toMatrix ℚ D v₃ u⁻¹ 0 0
              + toMatrix ℚ D v₃ u⁻¹ 1 0) / 3,
            9 * ((t : ℕ) : K₃) * toMatrix ℚ D v₃ u⁻¹ 0 1
              + toMatrix ℚ D v₃ u⁻¹ 1 1]] := by
  rw [show ((eta3 * u) * (etaRep t)⁻¹)⁻¹ = eta3 * (levelUnip t * u⁻¹) * eta3⁻¹ by
        rw [etaRep, mul_inv_rev, mul_inv_rev, mul_inv_rev]; group,
    toMatrix_eta3_conj, map_mul, toMatrix_levelUnip]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  all_goals ring

/-- **Covering** [Jacobs, Lemma 2.3]: every `η₃ · u` with `u ∈ U₁(9)` lies in one of the
three right cosets `U₁(9) · v_t`.  The index is forced: writing the `3`-component of `u`
as `(a b; c d)`, the lower-left entry of `(η₃u)v_t⁻¹` is `3d·(c/(9d) − t)`, so
`exists_fin3_approx` applied to `c/(9d)` supplies the (unique mod `3`) `t` — the mirror
of the left library's argument with the `d`-unit in place of the `a`-unit. -/
theorem exists_etaRep_mem {u : Dfx ℚ D} (hu : u ∈ U1_9) :
    ∃ t : Fin 3, (eta3 * u) * (etaRep t)⁻¹ ∈ U1_9 := by
  have h3 : (3 : K₃) ≠ 0 := three_ne_zero
  have hv3 : Valued.v (3 : K₃) ≤ 1 := valued_pi3_le_one
  obtain ⟨⟨hAint, hAc, hAd, -⟩, hAd1⟩ := hu.2.1
  obtain ⟨⟨hBint, hBc, hBd, -⟩, -⟩ := hu.2.2
  have hA11 : toMatrix ℚ D v₃ u 1 1 ≠ 0 := by
    intro h
    rw [h, map_zero] at hAd
    exact zero_ne_one hAd
  have hx : Valued.v (toMatrix ℚ D v₃ u 1 0 / (9 * toMatrix ℚ D v₃ u 1 1)) ≤ 1 := by
    rw [map_div₀, map_mul, valued_nine_eq, hAd, mul_one]
    exact div_le_one_of_le₀ hAc zero_le
  obtain ⟨t, ht⟩ := exists_fin3_approx hx
  refine ⟨t, ?_⟩
  -- the lower-left entry of the conjugate, rewritten through the approximation
  have hll : (toMatrix ℚ D v₃ u 1 0 - 9 * ((t : ℕ) : K₃) * toMatrix ℚ D v₃ u 1 1) / 3
      = 3 * toMatrix ℚ D v₃ u 1 1
        * (toMatrix ℚ D v₃ u 1 0 / (9 * toMatrix ℚ D v₃ u 1 1) - ((t : ℕ) : K₃)) := by
    field_simp
    ring
  have hllv : Valued.v ((toMatrix ℚ D v₃ u 1 0
      - 9 * ((t : ℕ) : K₃) * toMatrix ℚ D v₃ u 1 1) / 3) ≤ γ₉ := by
    rw [hll, map_mul, map_mul, hAd, mul_one]
    calc Valued.v (3 : K₃) * Valued.v (_ - ((t : ℕ) : K₃))
        ≤ Valued.v (3 : K₃) * Valued.v (3 : K₃) := mul_le_mul' le_rfl ht
      _ = Valued.v (9 : K₃) := by rw [← map_mul]; norm_num
      _ = γ₉ := valued_nine_eq
  have hnat : Valued.v (9 * ((t : ℕ) : K₃)) ≤ γ₉ := valued_nine_mul_le t
  -- the `3`-component of the conjugate is in `Σ₁(9)`
  have hM : toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹) ∈ Sigma1 := by
    rw [toMatrix_mul_etaRep_inv]
    refine ⟨⟨fun i j => ?_, ?_, ?_, ?_⟩, ?_⟩
    · fin_cases i <;> fin_cases j
      · refine le_trans (Valued.v.map_sub _ _) (max_le (hAint 0 0) ?_)
        rw [map_mul]
        exact le_trans (mul_le_mul' (le_trans hnat γ₉_lt_one.le) (hAint 0 1))
          (by rw [one_mul])
      · simpa using le_trans (mul_le_mul' hv3 (hAint 0 1)) (by rw [one_mul])
      · simpa using le_trans hllv γ₉_lt_one.le
      · simpa using le_of_eq hAd
    · simpa using hllv
    · simpa using hAd
    · rw [← toMatrix_mul_etaRep_inv]
      intro hdet
      have h1 : toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹)
          * toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      have h2 := congrArg Matrix.det h1
      rw [Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at h2
      exact zero_ne_one h2
    · simpa using hAd1
  -- integrality of the inverse's `3`-component
  have hint' : ∀ i j,
      Valued.v (toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹)⁻¹ i j) ≤ 1 := by
    intro i j
    rw [toMatrix_mul_etaRep_inv_inv]
    fin_cases i <;> fin_cases j
    · simpa using hBint 0 0
    · simpa using le_trans (mul_le_mul' hv3 (hBint 0 1)) (by rw [one_mul])
    · refine le_trans (valued_div_three ?_) hv3
      refine le_trans (Valued.v.map_add _ _) (max_le ?_ ?_)
      · rw [map_mul]
        exact le_trans (mul_le_mul' (le_trans hnat (le_of_eq valued_nine_eq.symm))
          (hBint 0 0)) (by rw [mul_one])
      · rw [← valued_nine_eq] at hBc; exact hBc
    · refine le_trans (Valued.v.map_add _ _) (max_le ?_ (hBint 1 1))
      rw [map_mul]
      exact le_trans (mul_le_mul' (le_trans hnat γ₉_lt_one.le) (hBint 0 1))
        (by rw [one_mul])
  have hmul1 : toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹)
      * toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hmul2 : toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹)⁻¹
      * toMatrix ℚ D v₃ ((eta3 * u) * (etaRep t)⁻¹) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  refine mem_U1_9_of_toMatrix (fun w hw => ?_) ?_
    (mem_integralMatrices_iff.mpr fun i j => hint' i j) hM
    (sigma1_of_mul_eq_one hM hint' hmul1 hmul2)
  · exact toLocal_ne_mem_localOrder hu t hw
  · exact mem_integralMatrices_iff.mpr fun i j => hM.1.1 i j

/-- **[Jacobs, Lemma 2.3]**, adelic right-coset form: the image of `{η₃}·U₁(9)` in the
right-coset space of `U₁(9)` is exactly the three classes of the `etaRep t`, and these
are pairwise distinct.  (Bijectivity form consumed by `heckeOperatorSlash_eq_finsetSum`
/ `heckeOperatorSlash_apply_rep`.) -/
theorem bijOn_etaRep :
    Set.BijOn (Quotient.mk'' : Dfx ℚ D → RightCosets U1_9) (Set.range etaRep)
      ((Quotient.mk'' : Dfx ℚ D → RightCosets U1_9) ''
        (({eta3} : Set (Dfx ℚ D)) * (U1_9 : Set (Dfx ℚ D)))) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨etaRep t, ⟨eta3, rfl, levelUnip t, levelUnip_mem_U1_9 t, rfl⟩, rfl⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
    rcases eq_or_ne s t with rfl | hst
    · rfl
    · refine absurd ?_ (etaRep_mul_inv_notMem hst)
      rw [← QuotientGroup.rightRel_apply (s := U1_9)]
      exact Quotient.eq''.mp h
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨e, he, u, hu, rfl⟩ := hg
    rw [Set.mem_singleton_iff] at he
    subst he
    obtain ⟨t, ht⟩ := exists_etaRep_mem hu
    refine ⟨etaRep t, ⟨t, rfl⟩, ?_⟩
    refine Quotient.eq''.mpr ?_
    rw [QuotientGroup.rightRel_apply]
    exact ht

/-- The finiteness input for `heckeOperatorSlash` at `η₃`, discharged by the explicit
decomposition (no adelic topology needed). -/
theorem finite_image_eta3 :
    (((Quotient.mk'' : Dfx ℚ D → RightCosets U1_9) ''
      (({eta3} : Set (Dfx ℚ D)) * (U1_9 : Set (Dfx ℚ D)))) :
      Set (RightCosets U1_9)).Finite := by
  rw [← bijOn_etaRep.image_eq]
  exact (Set.finite_range etaRep).image _

end JacobsSlash
