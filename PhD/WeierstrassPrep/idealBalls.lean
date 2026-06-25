import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted

import PhD.WeierstrassPrep.Restricted_powerbounded_topnil
import PhD.WeierstrassPrep.EpsilonDense
import PhD.WeierstrassPrep.ResPoly
import PhD.WeierstrassPrep.ResC

open Filter Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  [Filter.NeBot (𝓝[≠] (0 : R))]

-- these instances should be made global at some points

local instance instNonarch {S : Type*} [NormedCommRing S] [IsUltrametricDist S] :
    NonarchimedeanRing S where
  is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup).is_nonarchimedean

local instance instLinTopZ (S : Type*) [Ring S] [TopologicalSpace S] [NonarchimedeanRing S] :
    IsLinearTopology ℤ S := by
  apply IsLinearTopology.mk_of_hasBasis' (R := ℤ)
    (p := fun U : AddSubgroup S => (U : Set S) ∈ nhds 0)
    (s := fun U : AddSubgroup S => U)
  · refine ⟨fun U => ⟨fun hU => ?_,
      fun ⟨_, hN_mem, hN⟩ => Filter.mem_of_superset hN_mem hN⟩⟩
    obtain ⟨V, hV⟩ := NonarchimedeanRing.is_nonarchimedean U hU
    exact ⟨V.toAddSubgroup, V.mem_nhds_zero, hV⟩
  · intro _ n _ hm
    exact zsmul_mem hm n

local instance : StrongPos (fun _ : Unit ↦ (1 : ℝ)) where
  pos := by simp

namespace PowerBounded

/-- The `ε`-ball ideal `R_ε = {a ∈ R° : ‖a‖ ≤ ε}` of the power-bounded subring `R°`. -/
def closedBall_ideal (ε : ℝ) (hε : 0 ≤ ε) :
    Ideal ↥(PowerBounded.subring R (S := ℤ)) where
  carrier := {a | ‖(a : R)‖ ≤ ε}
  add_mem' {a b} ha hb := by
    simpa using (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by
    rwa [Set.mem_setOf_eq, ZeroMemClass.coe_zero, norm_zero]
  smul_mem' c {a} ha := by
    simp only [smul_eq_mul, Set.mem_setOf_eq, Subring.coe_mul, norm_mul]
    calc _ ≤ 1 * ε := mul_le_mul (IsPowerBounded.norm_le_one_of_neBot (by aesop)) ha (norm_nonneg _)
          (by linarith)
         _ = ε := one_mul _

@[simp]
lemma mem_closedBall_ideal (ε : ℝ) (hε : 0 ≤ ε) (a : ↥(PowerBounded.subring R (S := ℤ))) :
    a ∈ closedBall_ideal ε hε ↔ ‖(a : R)‖ ≤ ε := Iff.rfl

/-- The `ε`-ball ideal `R_ε = {a ∈ R° : ‖a‖ < ε}` of the power-bounded subring `R°`. -/
def openBall_ideal (ε : ℝ) (hε : 0 < ε) :
    Ideal ↥(PowerBounded.subring R (S := ℤ)) where
  carrier := {a | ‖(a : R)‖ < ε}
  add_mem' {a b} ha hb := calc
    _ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max ↑a ↑b
    _ < ε := by exact max_lt ha hb
  zero_mem' := by simpa
  smul_mem' := fun c {a} ha => by
    simp only [smul_eq_mul, Set.mem_setOf_eq, Subring.coe_mul, norm_mul]
    calc _ < 1 * ε := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
          (IsPowerBounded.norm_le_one_of_neBot (by aesop)) ha (norm_nonneg _) (by linarith)
         _ = ε := one_mul _

-- not sure if there should be a simp normal form or?
/-- The topologicalNilradical is equivalent to the open ball of radius one. -/
lemma topologicalNilradical_is_openBall_one :
    PowerBounded.topologicalNilradical ℤ (R := R) = openBall_ideal (R := R) 1 (by simp) := by
  refine Submodule.ext fun a => ?_
  simp_rw [IsTopologicallyNilpotent.mem_PowerBounded.topologicalNilradical_iff,
    IsTopologicallyNilpotent.iff_norm_lt_one]
  rfl

@[simp]
lemma mem_openBall_ideal (ε : ℝ) (hε : 0 < ε) (a : ↥(PowerBounded.subring R (S := ℤ))) :
    a ∈ openBall_ideal ε hε ↔ ‖(a : R)‖ < ε := Iff.rfl

end PowerBounded

section Restricted

namespace Restricted

open PowerBounded

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => subring R (S := ℤ)
/-- `T°`, the power-bounded subring of `T = PowerSeries.Restricted R 1`. -/
local notation "T°" => subring (PowerSeries.Restricted R 1) (S := ℤ)

/-- The `v`-th coefficient of a power-bounded series `f ∈ T°`, packaged as an element of `R°`. -/
noncomputable def pbCoeff (f : ↥T°) (v : ℕ) : ↥R° :=
  ⟨PowerSeries.coeff v (f : PowerSeries.Restricted R 1).1,
    powerBounded_coeffs_of_powerBounded (f : PowerSeries.Restricted R 1) f.2 v⟩

@[simp]
lemma pbCoeff_coe (f : ↥T°) (v : ℕ) :
  ((pbCoeff f v : ↥R°) : R) = PowerSeries.coeff v (f : PowerSeries.Restricted R 1).1 := rfl

lemma pbCoeff_add (f g : ↥T°) (v : ℕ) : pbCoeff (f + g) v = pbCoeff f v + pbCoeff g v := by
  apply Subtype.ext
  rfl

lemma pbCoeff_mul (f g : ↥T°) (v : ℕ) :
    pbCoeff (f * g) v = ∑ p ∈ Finset.antidiagonal v, pbCoeff f p.1 * pbCoeff g p.2 := by
  apply Subtype.ext
  push_cast [pbCoeff_coe]
  -- missing API that needs to be added
  have : ((f : PowerSeries.Restricted R 1) * (g : PowerSeries.Restricted R 1)).1 =
    ((f : PowerSeries.Restricted R 1).1 * (g : PowerSeries.Restricted R 1).1) := by rfl
  simp [this, PowerSeries.coeff_mul]

@[simp]
lemma pbCoeff_zero (v : ℕ) : pbCoeff (0 : ↥T°) v = 0 := by rfl

@[simp]
lemma pbCoeff_one_zero : pbCoeff (1 : ↥T°) 0 = 1 := by
  apply Subtype.ext
  aesop

@[simp]
lemma pbCoeff_one_pos {v : ℕ} (hv : 0 < v) : pbCoeff (1 : ↥T°) v = 0 := by
  apply Subtype.ext
  -- missing API
  have : (1 : PowerSeries.Restricted R 1).1 = 1 := by rfl
  simp [this]
  grind

-- maybe there is a way to deduplicate the work?

/-- For `ε > 0`, the support of `v ↦ mk_{R_ε} (pbCoeff f v)` is finite. -/
lemma closedBall_residueCoeff_support_finite (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
    (Function.support fun v : ℕ =>
      Ideal.Quotient.mk (closedBall_ideal ε hε.le) (pbCoeff f v)).Finite := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ v ≥ N, ‖PowerSeries.coeff v f.1.1‖ ≤ ε := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (by simpa using (PowerSeries.isRestricted_iff' 1 f.1.1).mp f.1.2) ε hε
    refine ⟨N, fun v hv => ?_⟩
    simp only [ge_iff_le, dist_zero_right, norm_norm] at hN
    grind
  refine Set.Finite.subset (Set.finite_Iio N) (fun v hv ↦ ?_)
  by_contra hvN
  apply hv
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal]
  exact hN v (Nat.le_of_not_lt hvN)

/-- For `ε > 0`, the support of `v ↦ mk_{R_ε} (pbCoeff f v)` is finite. -/
lemma openBall_residueCoeff_support_finite (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
    (Function.support fun v : ℕ =>
      Ideal.Quotient.mk (openBall_ideal ε hε) (pbCoeff f v)).Finite := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ v ≥ N, ‖PowerSeries.coeff v f.1.1‖ < ε := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (by simpa using (PowerSeries.isRestricted_iff' 1 f.1.1).mp f.1.2) ε hε
    refine ⟨N, fun v hv => ?_⟩
    simp only [ge_iff_le, dist_zero_right, norm_norm] at hN
    grind
  refine Set.Finite.subset (Set.finite_Iio N) (fun v hv ↦ ?_)
  by_contra hvN
  apply hv
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_openBall_ideal]
  exact hN v (Nat.le_of_not_lt hvN)

/-- The residue of `f ∈ T°` modulo `R_ε`, as a polynomial in `(R° ⧸ R_ε)[X]`. -/
noncomputable def closedBall_residuePolynomial (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
    Polynomial (↥R° ⧸ closedBall_ideal ε hε.le) :=
  ⟨Finsupp.ofSupportFinite (fun v => Ideal.Quotient.mk (closedBall_ideal ε hε.le) (pbCoeff f v))
    (closedBall_residueCoeff_support_finite ε hε f)⟩

/-- The residue of `f ∈ T°` modulo `R_ε`, as a polynomial in `(R° ⧸ R_ε)[X]`. -/
noncomputable def openBall_residuePolynomial (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
    Polynomial (↥R° ⧸ openBall_ideal ε hε) :=
  ⟨Finsupp.ofSupportFinite (fun v => Ideal.Quotient.mk (openBall_ideal ε hε) (pbCoeff f v))
    (openBall_residueCoeff_support_finite ε hε f)⟩

@[simp]
lemma closedBall_residuePolynomial_coeff (ε : ℝ) (hε : 0 < ε) (f : ↥T°) (v : ℕ) :
  (closedBall_residuePolynomial ε hε f).coeff v = Ideal.Quotient.mk (closedBall_ideal ε hε.le)
  (pbCoeff f v) := rfl

@[simp] lemma openBall_residuePolynomial_coeff (ε : ℝ) (hε : 0 < ε) (f : ↥T°) (v : ℕ) :
  (openBall_residuePolynomial ε hε f).coeff v = Ideal.Quotient.mk (openBall_ideal ε hε)
  (pbCoeff f v) := rfl

lemma closedBall_residuePolynomial_zero (ε : ℝ) (hε : 0 < ε) :
    closedBall_residuePolynomial ε hε (0 : ↥T°) = 0 := by
  apply Polynomial.ext
  simp


lemma openBall_residuePolynomial_zero (ε : ℝ) (hε : 0 < ε) :
    openBall_residuePolynomial ε hε (0 : ↥T°) = 0 := by
  apply Polynomial.ext
  simp

lemma closedBall_residuePolynomial_one (ε : ℝ) (hε : 0 < ε) :
    closedBall_residuePolynomial ε hε (1 : ↥T°) = 1 := by
  apply Polynomial.ext
  intro v
  rw [closedBall_residuePolynomial_coeff]
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [pbCoeff_one_zero, map_one, Polynomial.coeff_one_zero]
  · rw [pbCoeff_one_pos hv, map_zero, Polynomial.coeff_one, if_neg hv.ne']

lemma openBall_residuePolynomial_one (ε : ℝ) (hε : 0 < ε) :
    openBall_residuePolynomial ε hε (1 : ↥T°) = 1 := by
  apply Polynomial.ext
  intro v
  rw [openBall_residuePolynomial_coeff]
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [pbCoeff_one_zero, map_one, Polynomial.coeff_one_zero]
  · rw [pbCoeff_one_pos hv, map_zero, Polynomial.coeff_one, if_neg hv.ne']

lemma closedBall_residuePolynomial_add (ε : ℝ) (hε : 0 < ε) (f g : ↥T°) :
    closedBall_residuePolynomial ε hε (f + g) = closedBall_residuePolynomial ε hε f +
    closedBall_residuePolynomial ε hε g := by
  apply Polynomial.ext
  aesop

lemma openBall_residuePolynomial_add (ε : ℝ) (hε : 0 < ε) (f g : ↥T°) :
    openBall_residuePolynomial ε hε (f + g) = openBall_residuePolynomial ε hε f +
    openBall_residuePolynomial ε hε g := by
  apply Polynomial.ext
  aesop

lemma closedBall_residuePolynomial_mul (ε : ℝ) (hε : 0 < ε) (f g : ↥T°) :
    closedBall_residuePolynomial ε hε (f * g) = closedBall_residuePolynomial ε hε f *
    closedBall_residuePolynomial ε hε g := by
  apply Polynomial.ext
  intro v
  rw [closedBall_residuePolynomial_coeff, Polynomial.coeff_mul, pbCoeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, closedBall_residuePolynomial_coeff, closedBall_residuePolynomial_coeff]

lemma openBall_residuePolynomial_mul (ε : ℝ) (hε : 0 < ε) (f g : ↥T°) :
    openBall_residuePolynomial ε hε (f * g)
      = openBall_residuePolynomial ε hε f * openBall_residuePolynomial ε hε g := by
  apply Polynomial.ext
  intro v
  rw [openBall_residuePolynomial_coeff, Polynomial.coeff_mul, pbCoeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, openBall_residuePolynomial_coeff, openBall_residuePolynomial_coeff]

/-- The reduction-mod-`ε` ring hom `τ_ε : T° →+* (R° ⧸ R_ε)[X]`. -/
noncomputable
def closedBall_residueRingHom (ε : ℝ) (hε : 0 < ε) :
    ↥T° →+* Polynomial (↥R° ⧸ closedBall_ideal ε hε.le) where
  toFun := closedBall_residuePolynomial ε hε
  map_zero' := closedBall_residuePolynomial_zero ε hε
  map_one' := closedBall_residuePolynomial_one ε hε
  map_add' := closedBall_residuePolynomial_add ε hε
  map_mul' := closedBall_residuePolynomial_mul ε hε

@[simp]
lemma closedBall_residueRingHom_apply (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
  closedBall_residueRingHom ε hε f = closedBall_residuePolynomial ε hε f := rfl

/-- The reduction-mod-`ε` ring hom `τ_ε : T° →+* (R° ⧸ R_ε)[X]`. -/
noncomputable def openBall_residueRingHom (ε : ℝ) (hε : 0 < ε) :
    ↥T° →+* Polynomial (↥R° ⧸ openBall_ideal ε hε) where
  toFun := openBall_residuePolynomial ε hε
  map_zero' := openBall_residuePolynomial_zero ε hε
  map_one' := openBall_residuePolynomial_one ε hε
  map_add' := openBall_residuePolynomial_add ε hε
  map_mul' := openBall_residuePolynomial_mul ε hε

@[simp]
lemma openBall_residueRingHom_apply (ε : ℝ) (hε : 0 < ε) (f : ↥T°) :
  openBall_residueRingHom ε hε f = openBall_residuePolynomial ε hε f := rfl

local instance : NormMulClass (PowerSeries.Restricted R 1) :=
  MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ 1)

-- note this should not be proven like this
-- instead it should be a general statement for MvPowerSeries and this as a corollary
-- do when I clean up Restricted and MvRestricted
local instance : NormOneClass (PowerSeries.Restricted R 1) where
  norm_one := by
    rw [← PowerSeries.Restricted.C_one (S := R) 1, PowerSeries.Restricted.norm_C, norm_one]

omit [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] in
lemma pbPoly_map_coe (p : Polynomial ↥R°) :
    (Polynomial.toRestricted 1 (Polynomial.map (subring R).subtype p)).1  =
    ((p.map (PowerBounded.subring R (S := ℤ)).subtype : Polynomial R) : PowerSeries R) := by
  rfl

/-- Embed a polynomial over `R°` as an element of `T°`. -/
noncomputable
def pbPoly_to_pbRestricted (p : Polynomial ↥R°) : ↥T° :=
  ⟨Polynomial.toRestricted 1 (p.map (PowerBounded.subring R (S := ℤ)).subtype), by
    refine IsPowerBounded.isPowerBounded_of_norm_le_one ?_
    rw [norm_eq, PowerSeries.gaussNorm_eq]
    refine ciSup_le fun v => ?_
    simpa [one_pow, mul_one, pbPoly_map_coe, Polynomial.coeff_coe, Polynomial.coeff_map] using
      IsPowerBounded.norm_le_one_of_neBot (p.coeff v).2⟩

@[simp]
lemma pbPoly_to_pbRestricted_coe (p : Polynomial ↥R°) :
    (pbPoly_to_pbRestricted p : PowerSeries.Restricted R 1)
    = Polynomial.toRestricted 1 (p.map (PowerBounded.subring R (S := ℤ)).subtype) := rfl

lemma closedBall_residueRingHom_pbPoly_to_pbRestricted {ε : ℝ} (hε0 : 0 < ε) (p : Polynomial ↥R°) :
    Restricted.closedBall_residueRingHom ε hε0 (pbPoly_to_pbRestricted p)
    = p.map (Ideal.Quotient.mk (PowerBounded.closedBall_ideal ε hε0.le)) := by
  apply Polynomial.ext
  intro v
  rw [closedBall_residueRingHom_apply, closedBall_residuePolynomial_coeff, Polynomial.coeff_map]
  congr
  apply Subtype.ext
  rw [pbCoeff_coe, pbPoly_to_pbRestricted_coe, pbPoly_map_coe, Polynomial.coeff_coe,
    Polynomial.coeff_map, Subring.subtype_apply]

lemma openBall_residueRingHom_pbPoly_to_pbRestricted {ε : ℝ} (hε0 : 0 < ε) (p : Polynomial ↥R°) :
    Restricted.openBall_residueRingHom ε hε0 (pbPoly_to_pbRestricted p)
    = p.map (Ideal.Quotient.mk (PowerBounded.openBall_ideal ε hε0)) := by
  apply Polynomial.ext
  intro v
  rw [openBall_residueRingHom_apply, openBall_residuePolynomial_coeff, Polynomial.coeff_map]
  congr
  apply Subtype.ext
  rw [pbCoeff_coe, pbPoly_to_pbRestricted_coe, pbPoly_map_coe, Polynomial.coeff_coe,
    Polynomial.coeff_map, Subring.subtype_apply]

/-- If `τ_ε(h) = 0` then every coefficient of `h` lies in `R_ε`, so `‖h‖ ≤ ε`. -/
lemma closedBall_norm_le_of_residueRingHom_eq_zero {ε : ℝ} (hε0 : 0 < ε) (h : ↥T°)
    (hh : closedBall_residueRingHom ε hε0 h = 0) :
    ‖(h : PowerSeries.Restricted R 1)‖ ≤ ε := by
  have (v : ℕ): ‖PowerSeries.coeff v (h : PowerSeries.Restricted R 1).1‖ ≤ ε := by
    apply Polynomial.ext_iff.mp at hh
    specialize hh v
    rwa [closedBall_residueRingHom_apply, closedBall_residuePolynomial_coeff,
      Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal,
      pbCoeff_coe] at hh
  rw [norm_eq, PowerSeries.gaussNorm_eq]
  exact ciSup_le fun v => by simpa [one_pow, mul_one] using this v

/-- If `τ_ε(h) = 0` then every coefficient of `h` lies in `R_ε`, so `‖h‖ ≤ ε`. -/
lemma openBall_norm_lt_of_residueRingHom_eq_zero {ε : ℝ} (hε0 : 0 < ε) (h : ↥T°)
    (hh : Restricted.openBall_residueRingHom ε hε0 h = 0) :
    ‖(h : PowerSeries.Restricted R 1)‖ < ε := by
  have (v : ℕ): ‖PowerSeries.coeff v (h : PowerSeries.Restricted R 1).1‖ < ε := by
    apply Polynomial.ext_iff.mp at hh
    specialize hh v
    rwa [openBall_residueRingHom_apply, openBall_residuePolynomial_coeff, Polynomial.coeff_zero,
      Ideal.Quotient.eq_zero_iff_mem, mem_openBall_ideal, pbCoeff_coe] at hh
  obtain ⟨a, ha⟩ := gaussNorm_achieved' 1 (by simp) h.1
  simp only [one_pow, mul_one] at ha
  simp_rw [norm_eq, ← ha]
  exact this a

/-- Converse direction: if `‖h‖ ≤ ε` then every coefficient lies in `R_ε`, so `τ_ε(h) = 0`. -/
lemma closedBall_residueRingHom_eq_zero_of_norm_le {ε : ℝ} (hε0 : 0 < ε) (h : ↥T°)
    (hh : ‖(h : PowerSeries.Restricted R 1)‖ ≤ ε) :
    closedBall_residueRingHom ε hε0 h = 0 := by
  apply Polynomial.ext
  intro v
  rw [closedBall_residueRingHom_apply, closedBall_residuePolynomial_coeff, Polynomial.coeff_zero,
    Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal, pbCoeff_coe]
  refine le_trans ?_ hh
  have := PowerSeries.le_gaussNorm norm 1 (h : PowerSeries.Restricted R 1).1
    (Restricted.hasGaussNorm 1 (h : PowerSeries.Restricted R 1)) v
  rwa [one_pow, mul_one, ← Restricted.norm_eq] at this

/-- Converse direction: if `‖h‖ < ε` then every coefficient lies in `R_ε`, so `τ_ε(h) = 0`. -/
lemma openBall_residueRingHom_eq_zero_of_norm_lt {ε : ℝ} (hε0 : 0 < ε) (h : ↥T°)
    (hh : ‖(h : PowerSeries.Restricted R 1)‖ < ε) :
    openBall_residueRingHom ε hε0 h = 0 := by
  apply Polynomial.ext
  intro v
  rw [openBall_residueRingHom_apply, openBall_residuePolynomial_coeff, Polynomial.coeff_zero,
    Ideal.Quotient.eq_zero_iff_mem, mem_openBall_ideal, pbCoeff_coe]
  refine LE.le.trans_lt ?_ hh
  have := PowerSeries.le_gaussNorm norm 1 (h : PowerSeries.Restricted R 1).1
    (Restricted.hasGaussNorm 1 (h : PowerSeries.Restricted R 1)) v
  rwa [one_pow, mul_one, ← Restricted.norm_eq] at this

end Restricted

end Restricted
