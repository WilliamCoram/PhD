/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.MvPowerSeries.Restricted

/-!
# Restricted multivariate power series

This file develops basic API for restricted multivariate power series, building on
`MvPowerSeries.IsRestricted`.

## Main definitions

* `MvPowerSeries.Restricted R c`: the type of power series restricted for `c`, as a ring.
* `MvPowerSeries.Restricted.monomial`, `MvPowerSeries.Restricted.X`, `MvPowerSeries.Restricted.C`:
  monomials, variables and constants as restricted power series.
* `MvPowerSeries.Restricted.map`: functoriality along a norm-nonincreasing ring homomorphism of
  the coefficients.
* `MvPolynomial.toRestricted`: the canonical ring homomorphism from multivariate polynomials to
  restricted power series.

## Main results

* `MvPowerSeries.isRestricted_of_finite_support`: a power series with finitely many nonzero
  coefficients is restricted; in particular every multivariate polynomial is restricted
  (`MvPolynomial.isRestricted_toMvPowerSeries`).
* `MvPowerSeries.isRestricted_X` and closure of restrictedness under subtraction, finite sums,
  scalar multiplication and powers.
* `MvPolynomial.toRestricted` is injective (`MvPolynomial.toRestricted_injective`).
-/

namespace MvPowerSeries

open Filter

variable {R : Type*} [NormedRing R] {σ : Type*}

/-! ### Restrictedness of basic series and closure properties -/

/-- A power series with finitely many nonzero coefficients is restricted for every `c`. -/
lemma isRestricted_of_finite_support (c : σ → ℝ) {f : MvPowerSeries σ R}
    (hf : (Function.support fun t ↦ coeff t f).Finite) : IsRestricted c f :=
  tendsto_nhds_of_eventually_eq <| eventually_cofinite.mpr <| hf.subset fun t ht ↦
    Function.mem_support.mpr fun h0 ↦ ht (by simp [h0])

lemma isRestricted_X (c : σ → ℝ) (s : σ) : IsRestricted c (X s : MvPowerSeries σ R) := by
  rw [X_def]
  exact isRestricted_monomial c (Finsupp.single s 1) 1

lemma isRestricted.sub (c : σ → ℝ) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hg : IsRestricted c g) : IsRestricted c (f - g) :=
  show f - g ∈ IsRestricted.addSubgroup c from sub_mem hf hg

lemma isRestricted.sum (c : σ → ℝ) {ι : Type*} {s : Finset ι} {f : ι → MvPowerSeries σ R}
    (hf : ∀ i ∈ s, IsRestricted c (f i)) : IsRestricted c (∑ i ∈ s, f i) :=
  show ∑ i ∈ s, f i ∈ IsRestricted.addSubgroup c from sum_mem hf

lemma isRestricted.smul (c : σ → ℝ) (r : R) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (r • f) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  refine tendsto_const_nhds.squeeze (mul_zero ‖r‖ ▸ hf.const_mul ‖r‖) (fun t ↦ ?_) fun t ↦ ?_
  · dsimp [Finsupp.prod]; positivity
  · rw [coeff_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_mul_le r _) (by dsimp [Finsupp.prod]; positivity)

lemma isRestricted.pow [IsUltrametricDist R] (c : σ → ℝ) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (n : ℕ) : IsRestricted c (f ^ n) :=
  show f ^ n ∈ IsRestricted.subring c from pow_mem hf n

/-- A norm-nonincreasing ring homomorphism maps restricted power series to restricted power
series: the weighted coefficient norms only shrink. -/
lemma isRestricted_map {S : Type*} [NormedRing S] (c : σ → ℝ) {φ : R →+* S}
    (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (map φ f) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  refine tendsto_const_nhds.squeeze hf (fun t ↦ ?_) fun t ↦ ?_
  · dsimp [Finsupp.prod]; positivity
  · rw [coeff_map]
    exact mul_le_mul_of_nonneg_right (hφ _) (by dsimp [Finsupp.prod]; positivity)

/-- Applying a norm-bounded map `π : R → S` (`‖π x‖ ≤ Cπ * ‖x‖`, not assumed a homomorphism)
coefficientwise sends restricted power series to restricted power series. -/
lemma isRestricted_mk {S : Type*} [NormedRing S] {c : σ → ℝ} (hc : ∀ i, 0 ≤ c i) (π : R → S)
    {Cπ : ℝ} (hCπ : ∀ x, ‖π x‖ ≤ Cπ * ‖x‖) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (fun t ↦ π (coeff t f) : MvPowerSeries σ S) := by
  rw [IsRestricted] at hf
  refine tendsto_const_nhds.squeeze (mul_zero Cπ ▸ hf.const_mul Cπ) (fun t ↦ ?_) fun t ↦ ?_
  · exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) _)
  · rw [coeff_apply, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hCπ _) (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) _)

/-! ### The ring of restricted power series -/

variable [IsUltrametricDist R]

variable (R) in
/-- The type of restricted `MvPowerSeries σ R`. -/
def Restricted (c : σ → ℝ) : Type _ := MvPowerSeries.IsRestricted.subring (R := R) c

/-- Ring structure on `Restricted R c`. -/
noncomputable
instance (c : σ → ℝ) : Ring (Restricted R c) :=
  Subring.toRing (MvPowerSeries.IsRestricted.subring c)

/-- Commutative ring structure on `Restricted R c` when `R` is commutative.  The underlying
`Ring` structure is definitionally the `Ring (Restricted R c)` instance. -/
noncomputable instance {S : Type*} [NormedCommRing S] [IsUltrametricDist S] (c : σ → ℝ) :
    CommRing (Restricted S c) :=
  { (inferInstance : Ring (Restricted S c)) with
    mul_comm := fun f g ↦ Subtype.ext (mul_comm f.1 g.1) }

namespace Restricted

@[ext]
lemma ext {c : σ → ℝ} {f g : Restricted R c} (h : f.1 = g.1) : f = g := Subtype.ext h

variable (c : σ → ℝ)

@[simp] lemma val_zero : (0 : Restricted R c).1 = 0 := rfl

@[simp] lemma val_one : (1 : Restricted R c).1 = 1 := rfl

@[simp] lemma val_add (f g : Restricted R c) : (f + g).1 = f.1 + g.1 := rfl

@[simp] lemma val_neg (f : Restricted R c) : (-f).1 = -f.1 := rfl

@[simp] lemma val_sub (f g : Restricted R c) : (f - g).1 = f.1 - g.1 := rfl

@[simp] lemma val_mul (f g : Restricted R c) : (f * g).1 = f.1 * g.1 := rfl

@[simp] lemma val_pow (f : Restricted R c) (n : ℕ) : (f ^ n).1 = f.1 ^ n := rfl

@[simp] lemma val_sum {ι : Type*} (s : Finset ι) (g : ι → Restricted R c) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, val_add, ih]

/-- `MvPowerSeries.monomial n a` as an element of `Restricted R c`. -/
noncomputable def monomial (n : σ →₀ ℕ) (a : R) : Restricted R c :=
  ⟨MvPowerSeries.monomial n a, isRestricted_monomial c n a⟩

@[simp] lemma val_monomial (n : σ →₀ ℕ) (a : R) :
    (monomial c n a).1 = MvPowerSeries.monomial n a := rfl

variable (R) in
/-- `MvPowerSeries.X s` as an element of `Restricted R c`. -/
noncomputable def X (s : σ) : Restricted R c := ⟨MvPowerSeries.X s, isRestricted_X c s⟩

@[simp] lemma val_X (s : σ) : (X R c s).1 = MvPowerSeries.X s := rfl

/-- The constant `MvPowerSeries.C a` as an element of `Restricted R c`, bundled as a ring
homomorphism. -/
noncomputable def C : R →+* Restricted R c :=
  RingHom.codRestrict MvPowerSeries.C (IsRestricted.subring c) (isRestricted_C c)

@[simp] lemma val_C (a : R) : (C c a).1 = MvPowerSeries.C a := rfl

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

/-- Functoriality of restricted power series along a norm-nonincreasing ring homomorphism
`φ : R →+* S`, as a ring homomorphism `Restricted R c →+* Restricted S c`. -/
noncomputable def map {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    Restricted R c →+* Restricted S c :=
  RingHom.codRestrict ((MvPowerSeries.map φ).comp (IsRestricted.subring c).subtype)
    (IsRestricted.subring c) fun f ↦ isRestricted_map c hφ f.2

@[simp] lemma val_map {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (f : Restricted R c) :
    (map c hφ f).1 = MvPowerSeries.map φ f.1 := rfl

lemma map_injective {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (hφinj : Function.Injective φ) :
    Function.Injective (map c hφ) := fun a b h ↦
  Restricted.ext <| MvPowerSeries.ext fun t ↦ hφinj <| by
    simpa only [val_map, MvPowerSeries.coeff_map] using
      congrArg (fun r : Restricted S c ↦ MvPowerSeries.coeff t r.1) h

end Restricted

end MvPowerSeries

/-! ### Multivariate polynomials are restricted

`MvPolynomial σ R` requires `CommSemiring R`, so these results are stated for a normed
commutative ring. -/

namespace MvPolynomial

variable {R : Type*} [NormedCommRing R] {σ : Type*}

/-- Multivariate polynomials are restricted for every `c`. -/
lemma isRestricted_toMvPowerSeries (c : σ → ℝ) (p : MvPolynomial σ R) :
    MvPowerSeries.IsRestricted c (p : MvPowerSeries σ R) :=
  MvPowerSeries.isRestricted_of_finite_support c <| p.support.finite_toSet.subset fun t ht ↦ by
    simpa [mem_support_iff, coeff_coe] using Function.mem_support.mp ht

variable [IsUltrametricDist R] (c : σ → ℝ)

/-- The canonical map from multivariate polynomials to restricted power series, as a ring
homomorphism. -/
noncomputable def toRestricted : MvPolynomial σ R →+* MvPowerSeries.Restricted R c :=
  RingHom.codRestrict coeToMvPowerSeries.ringHom (MvPowerSeries.IsRestricted.subring c)
    fun p ↦ isRestricted_toMvPowerSeries c p

@[simp] lemma val_toRestricted (p : MvPolynomial σ R) :
    (toRestricted c p).1 = (p : MvPowerSeries σ R) := rfl

@[simp] lemma toRestricted_monomial (n : σ →₀ ℕ) (a : R) :
    toRestricted c (monomial n a) = MvPowerSeries.Restricted.monomial c n a :=
  MvPowerSeries.Restricted.ext (by simp [coe_monomial])

@[simp] lemma toRestricted_X (s : σ) :
    toRestricted c (X s) = MvPowerSeries.Restricted.X R c s :=
  MvPowerSeries.Restricted.ext (by simp [coe_X])

@[simp] lemma toRestricted_C (a : R) :
    toRestricted c (C a) = MvPowerSeries.Restricted.C c a :=
  MvPowerSeries.Restricted.ext (by simp [coe_C])

lemma toRestricted_injective : Function.Injective (toRestricted (R := R) c) :=
  fun _ _ h ↦ coe_injective σ R (congrArg Subtype.val h)

@[simp] lemma toRestricted_inj {p q : MvPolynomial σ R} :
    toRestricted c p = toRestricted c q ↔ p = q :=
  (toRestricted_injective c).eq_iff

@[simp] lemma toRestricted_eq_zero_iff {p : MvPolynomial σ R} :
    toRestricted c p = 0 ↔ p = 0 :=
  (toRestricted_injective c).eq_iff' (map_zero _)

@[simp] lemma toRestricted_eq_one_iff {p : MvPolynomial σ R} :
    toRestricted c p = 1 ↔ p = 1 :=
  (toRestricted_injective c).eq_iff' (map_one _)

end MvPolynomial
