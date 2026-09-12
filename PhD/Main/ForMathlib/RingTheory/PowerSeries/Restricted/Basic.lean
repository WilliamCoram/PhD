/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Order.Filter.Cofinite

-- note part of this file is my PR #39583 and replaces the existing Mathlib file... e.g. only ever
-- import this!

/-!
# Univariate restricted power series

`IsRestricted` : We say a univariate power series over a normed ring `R` is restricted for a
real number `c` if `‖coeff t f‖ * c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section
namespace PowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] (c : ℝ) (f : PowerSeries R)

/-- Predicate for when `f` is a restricted power series. -/
abbrev IsRestricted :=
  MvPowerSeries.IsRestricted (σ := Unit) (fun _ ↦ c) f

private lemma isRestricted_comp_uniqueEquiv :
    (fun (t : Unit →₀ ℕ) ↦ ‖MvPowerSeries.coeff t f‖ * t.prod (fun _ x ↦ c ^ x)) =
    (fun (n : ℕ) ↦ ‖coeff n f‖ * c ^ n) ∘ Finsupp.uniqueEquiv () := by
  funext t
  simp only [Function.comp_apply, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit,
    Finsupp.prod_pow, Finset.univ_unique, Finset.prod_singleton, coeff,
    show (Finsupp.single () (t ())) = t by grind]

lemma isRestricted_iff : IsRestricted c f ↔
    Tendsto (fun (t : ℕ) ↦ ‖coeff t f‖ * c ^ t) cofinite (𝓝 0) := by
  rw [IsRestricted, MvPowerSeries.IsRestricted, isRestricted_comp_uniqueEquiv]
  exact ⟨fun H ↦ (H.comp (Finsupp.uniqueEquiv ()).symm.injective.tendsto_cofinite).congr fun n ↦
    by simp, fun H ↦ H.comp (Finsupp.uniqueEquiv ()).injective.tendsto_cofinite⟩

lemma isRestricted_iff' : IsRestricted c f ↔
    Tendsto (fun (t : ℕ) ↦ ‖coeff t f‖ * c ^ t) atTop (𝓝 0) := by
  simp_rw [isRestricted_iff, Nat.cofinite_eq_atTop]

@[simp]
lemma isRestricted_abs_iff : IsRestricted |c| f ↔ IsRestricted c f :=
  MvPowerSeries.isRestricted_abs_iff (fun _ ↦ c) f

lemma isRestricted_zero : IsRestricted c (0 : PowerSeries R) :=
 MvPowerSeries.isRestricted_zero (fun _ ↦ c)

lemma isRestricted_monomial (n : ℕ) (a : R) : IsRestricted c (monomial n a) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) ((Finsupp.single () n)) a

lemma isRestricted_one : IsRestricted c (1 : PowerSeries R) :=
  MvPowerSeries.isRestricted_monomial (fun _ ↦ c) 0 1

lemma isRestricted_C (a : R) : IsRestricted c (C a) :=
  MvPowerSeries.isRestricted_C (fun _ ↦ c) a

variable {f} in
lemma isRestricted.add {g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) :=
  MvPowerSeries.isRestricted.add (fun _ ↦ c) hf hg

variable {f} in
lemma isRestricted.neg (hf : IsRestricted c f) : IsRestricted c (-f) :=
  MvPowerSeries.isRestricted.neg (fun _ ↦ c) hf

lemma isRestricted.mul [IsUltrametricDist R] (c : ℝ) {f g : PowerSeries R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) :=
  MvPowerSeries.isRestricted.mul (fun _ ↦ c) hf hg

variable {f} in
/-- A power series with finitely many nonzero coefficients is restricted for every `c`. -/
lemma isRestricted_of_finite_support (hf : (Function.support fun n ↦ coeff n f).Finite) :
    IsRestricted c f :=
  (isRestricted_iff c f).mpr <| tendsto_nhds_of_eventually_eq <| eventually_cofinite.mpr <|
    hf.subset fun n hn ↦ Function.mem_support.mpr fun h0 ↦ hn (by simp [h0])

lemma isRestricted_X : IsRestricted c (X : PowerSeries R) := by
  rw [X_eq]
  exact isRestricted_monomial c 1 1

variable {f} in
lemma isRestricted.sub {g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f - g) :=
  MvPowerSeries.isRestricted.sub (fun _ ↦ c) hf hg

lemma isRestricted.sum {ι : Type*} {s : Finset ι} {g : ι → PowerSeries R}
    (hg : ∀ i ∈ s, IsRestricted c (g i)) : IsRestricted c (∑ i ∈ s, g i) :=
  MvPowerSeries.isRestricted.sum (fun _ ↦ c) hg

variable {f} in
lemma isRestricted.smul (r : R) (hf : IsRestricted c f) : IsRestricted c (r • f) :=
  MvPowerSeries.isRestricted.smul (fun _ ↦ c) r hf

variable {f} in
lemma isRestricted.pow [IsUltrametricDist R] (hf : IsRestricted c f) (n : ℕ) :
    IsRestricted c (f ^ n) :=
  MvPowerSeries.isRestricted.pow (fun _ ↦ c) hf n

variable {f} in
/-- A norm-nonincreasing ring homomorphism maps restricted power series to restricted power
series: the weighted coefficient norms only shrink. -/
lemma isRestricted_map {S : Type*} [NormedRing S] {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (hf : IsRestricted c f) : IsRestricted c (map φ f) :=
  MvPowerSeries.isRestricted_map (fun _ ↦ c) hφ hf

variable {f} in
/-- Applying a norm-bounded map `π : R → S` (`‖π x‖ ≤ Cπ * ‖x‖`, not assumed a homomorphism)
coefficientwise sends restricted power series to restricted power series. -/
lemma isRestricted_mk {S : Type*} [NormedRing S] (hc : 0 ≤ c) (π : R → S) {Cπ : ℝ}
    (hCπ : ∀ x, ‖π x‖ ≤ Cπ * ‖x‖) (hf : IsRestricted c f) :
    IsRestricted c (PowerSeries.mk fun n ↦ π (coeff n f)) := by
  rw [isRestricted_iff]
  refine squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc n))
    (fun n ↦ ?_) (by simpa using ((isRestricted_iff c f).mp hf).const_mul Cπ)
  simpa [coeff_mk, ← mul_assoc] using mul_le_mul_of_nonneg_right (hCπ _) (pow_nonneg hc n)

namespace IsRestricted

/-- Restricted power series as an additive subgroup of `PowerSeries R`. -/
def addSubgroup (c : ℝ) : AddSubgroup (PowerSeries R) :=
  MvPowerSeries.IsRestricted.addSubgroup (fun _ ↦ c)

variable [IsUltrametricDist R]

/-- Restricted power series as an subring of `PowerSeries R`. -/
def subring (c : ℝ) : Subring (PowerSeries R) :=
  MvPowerSeries.IsRestricted.subring (fun _ ↦ c)

end IsRestricted

variable [IsUltrametricDist R]

variable (R) in
/-- The type of restricted `PowerSeries R`. -/
abbrev Restricted (c : ℝ) : Type _ := MvPowerSeries.Restricted R (σ := Unit) (fun _ ↦ c)

/-- When `R` is commutative, so is `Restricted R c`; the instance is inherited from the
multivariate case. -/
noncomputable example {S : Type*} [NormedCommRing S] [IsUltrametricDist S] (d : ℝ) :
    CommRing (Restricted S d) := inferInstance

namespace Restricted

/-- `PowerSeries.monomial n a` as an element of `Restricted R c`. -/
noncomputable def monomial (n : ℕ) (a : R) : Restricted R c :=
  ⟨PowerSeries.monomial n a, isRestricted_monomial c n a⟩

@[simp] lemma val_monomial (n : ℕ) (a : R) :
    (monomial c n a).1 = PowerSeries.monomial n a := rfl

variable (R) in
/-- `PowerSeries.X` as an element of `Restricted R c`. -/
noncomputable def X : Restricted R c := ⟨PowerSeries.X, isRestricted_X c⟩

@[simp] lemma val_X : (X R c).1 = PowerSeries.X := rfl

/-- The constant `PowerSeries.C a` as an element of `Restricted R c`, bundled as a ring
homomorphism. -/
noncomputable def C : R →+* Restricted R c :=
  RingHom.codRestrict PowerSeries.C (IsRestricted.subring c) (isRestricted_C c)

@[simp] lemma val_C (a : R) : (C c a).1 = PowerSeries.C a := rfl

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

/-- Functoriality of restricted power series along a norm-nonincreasing ring homomorphism
`φ : R →+* S`, as a ring homomorphism `Restricted R c →+* Restricted S c`; inherited from the
multivariate case. -/
noncomputable def map {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    Restricted R c →+* Restricted S c :=
  MvPowerSeries.Restricted.map (fun _ ↦ c) hφ

@[simp] lemma val_map {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (g : Restricted R c) :
    (map c hφ g).1 = PowerSeries.map φ g.1 := rfl

lemma map_injective {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (hφinj : Function.Injective φ) :
    Function.Injective (map c hφ) :=
  MvPowerSeries.Restricted.map_injective (fun _ ↦ c) hφ hφinj

end Restricted

end PowerSeries

/-! ### Polynomials are restricted -/

namespace Polynomial

variable {R : Type*} [NormedRing R] (c : ℝ)

/-- Polynomials are restricted for every `c`. -/
lemma isRestricted_toPowerSeries (p : Polynomial R) :
    PowerSeries.IsRestricted c (p : PowerSeries R) :=
  PowerSeries.isRestricted_of_finite_support c <| p.support.finite_toSet.subset fun n hn ↦ by
    simpa [mem_support_iff, coeff_coe] using Function.mem_support.mp hn

variable [IsUltrametricDist R]

/-- The canonical map from polynomials to restricted power series, as a ring homomorphism. -/
noncomputable def toRestricted : Polynomial R →+* PowerSeries.Restricted R c :=
  RingHom.codRestrict coeToPowerSeries.ringHom (PowerSeries.IsRestricted.subring c)
    fun p ↦ isRestricted_toPowerSeries c p

@[simp] lemma val_toRestricted (p : Polynomial R) :
    (toRestricted c p).1 = (p : PowerSeries R) := rfl

@[simp] lemma toRestricted_monomial (n : ℕ) (a : R) :
    toRestricted c (monomial n a) = PowerSeries.Restricted.monomial c n a :=
  Subtype.ext (by simp [coe_monomial])

@[simp] lemma toRestricted_X : toRestricted c X = PowerSeries.Restricted.X R c :=
  Subtype.ext (by simp [coe_X])

@[simp] lemma toRestricted_C (a : R) : toRestricted c (C a) = PowerSeries.Restricted.C c a :=
  Subtype.ext (by simp [coe_C])

lemma toRestricted_injective : Function.Injective (toRestricted (R := R) c) :=
  fun _ _ h ↦ coe_injective R (congrArg Subtype.val h)

@[simp] lemma toRestricted_inj {p q : Polynomial R} :
    toRestricted c p = toRestricted c q ↔ p = q :=
  (toRestricted_injective c).eq_iff

@[simp] lemma toRestricted_eq_zero_iff {p : Polynomial R} :
    toRestricted c p = 0 ↔ p = 0 :=
  (toRestricted_injective c).eq_iff' (map_zero _)

@[simp] lemma toRestricted_eq_one_iff {p : Polynomial R} :
    toRestricted c p = 1 ↔ p = 1 :=
  (toRestricted_injective c).eq_iff' (map_one _)

end Polynomial
