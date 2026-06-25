import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted

import PhD.WeierstrassPrep.Restricted_powerbounded_topnil
import PhD.WeierstrassPrep.EpsilonDense
import PhD.WeierstrassPrep.ResPoly
import PhD.WeierstrassPrep.ResC
import PhD.WeierstrassPrep.idealBalls
import PhD.WeierstrassPrep.Polylift
import PhD.WeierstrassPrep.ResUnits
import PhD.WeierstrassPrep.WeierstrassDivision

open Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormMulClass R]
  [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))] [Nontrivial R]

-- still need to get around this
local instance : StrongPos (fun _ : Unit ↦ (1 : ℝ)) where
  pos := by simp

local instance : NormMulClass (PowerSeries.Restricted R 1) :=
  MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ 1)

-- note this should not be proven like this
-- instead it should be a general statement for MvPowerSeries and this as a corollary
-- do when I clean up Restricted and MvRestricted
local instance : NormOneClass (PowerSeries.Restricted R 1) where
  norm_one := by
    rw [← PowerSeries.Restricted.C_one (S := R) 1, PowerSeries.Restricted.norm_C, norm_one]

local instance {S : Type*} [NormedCommRing S] [IsUltrametricDist S] :
    NonarchimedeanRing S where
  is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup).is_nonarchimedean

local instance (S : Type*) [Ring S] [TopologicalSpace S] [NonarchimedeanRing S] :
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

-- needed so that `openBall_ideal`/`topologicalNilradical` of `T = Restricted R 1` are available.
local instance : Filter.NeBot (𝓝[≠] (0 : (PowerSeries.Restricted R 1))) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr_ne, hr⟩ : ∃ r : R, r ≠ 0 ∧ ‖r‖ < ε := by
    have hR : (0 : R) ∈ closure ({0}ᶜ : Set R) :=
      mem_closure_iff_nhdsWithin_neBot.mpr inferInstance
    obtain ⟨r, hr_mem, hr_dist⟩ := Metric.mem_closure_iff.mp hR ε hε
    rw [dist_comm, dist_zero_right] at hr_dist
    exact ⟨r, hr_mem, hr_dist⟩
  have hcoe : (Restricted.monomial 1 0 r).1 = PowerSeries.monomial 0 r := rfl
  have hub : ‖Restricted.monomial 1 0 r‖ ≤ ‖r‖ := by
    rw [Restricted.norm_eq, hcoe, PowerSeries.gaussNorm_eq]
    refine ciSup_le (fun i => ?_)
    rw [PowerSeries.coeff_monomial, one_pow, mul_one]
    split_ifs with h
    · exact le_refl _
    · simp
  have hlb : ‖r‖ ≤ ‖Restricted.monomial 1 0 r‖ := by
    rw [Restricted.norm_eq, hcoe]
    have h := PowerSeries.le_gaussNorm (norm : R → ℝ) 1 (Restricted.monomial 1 0 r).1
      (Restricted.hasGaussNorm 1 (Restricted.monomial 1 0 r)) 0
    rw [hcoe] at h
    simpa [PowerSeries.coeff_monomial] using h
  have hne : Restricted.monomial 1 0 r ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hr_ne) hlb)
  exact ⟨Restricted.monomial 1 0 r, hne,
    by rw [dist_comm, dist_zero_right]; exact lt_of_le_of_lt hub hr⟩

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of `T = PowerSeries.Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)

-- an assortment of lemmas that I have been able to extract
-- these could be generalised and placed into mathlib files
-- TODO: create a 'mathlib' file that contains all of these small lemmas

-- note in all the below I can suppress s and r!
lemma test1 (s : ℕ) (r : Polynomial R) (rd : r.degree < s) :
    ∀ v, s < v → ((Polynomial.monomial s 1) - r).coeff v = 0 := fun v hv => by
  rw [Polynomial.coeff_sub, Polynomial.monomial_one_right_eq_X_pow, Polynomial.coeff_X_pow,
    if_neg (by omega), Polynomial.coeff_eq_zero_of_degree_lt (rd.trans_le (mod_cast hv.le)),
    sub_zero]

lemma test2 (s : ℕ) (r : Polynomial R) (rd : r.degree < s) :
    ((Polynomial.monomial s 1) - r).coeff s = 1 := by
  rw [Polynomial.coeff_sub, Polynomial.monomial_one_right_eq_X_pow, Polynomial.coeff_X_pow,
    if_pos rfl, Polynomial.coeff_eq_zero_of_degree_lt rd, sub_zero]

lemma test3 (s : ℕ) (r : Polynomial R) (rd : r.degree < s) :
    ((Polynomial.monomial s 1) - r).degree = ↑s :=
  le_antisymm ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun _ hm => test1 _ _ rd _
    (mod_cast hm)) (Polynomial.le_degree_of_ne_zero (by simp [test2 _ _ rd]))

lemma test4 (s : ℕ) (r : Polynomial R) (rd : r.degree < s) :
    ((Polynomial.monomial s 1) - r).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some
    (test3 _ _ rd),  test2 _ _ rd]

-- think I said I wanted a powerseries coeff coe as well...?
-- maybe I do not need both?
lemma Restricted.polynomial_coeff_coe (r : Polynomial R) (v : ℕ) :
  PowerSeries.coeff v (Polynomial.toRestricted 1 r).1 = r.coeff v := Polynomial.coeff_coe r v

lemma Restricted.coe_monomial (c : ℝ) (n : ℕ) (r : R) :
    Restricted.monomial c n r = Polynomial.toRestricted c (Polynomial.monomial n r) := by
  simp [monomial, Polynomial.toRestricted]

lemma Restricted.coe_monomial' (c : ℝ) (n : ℕ) :
    Restricted.monomial c n 1 = Polynomial.toRestricted c (Polynomial.X (R := R) ^ n) := by
  simp [monomial, Polynomial.toRestricted, ← Polynomial.monomial_one_right_eq_X_pow]

-- maybe I want a Restricted.X definition??
-- honestly no idea
-- this "could" make it easier
-- as if the gaussNorm is multiplicative
-- we have ‖x‖ = 1 ... and so ‖x^s‖=‖x‖^s=1
-- then a monomial is just ‖a x^s‖ = ‖a‖

-- this has become a mess... I am leaving this decision for now (will decide when I refactor my
-- MvRestricted and Restricted files)

-- note this should be generalised to c not just one... I just havent got the typing correct right now
lemma Restricted.monomial_norm (n : ℕ) (r : R) :
    ‖Restricted.monomial 1 n r‖ = ‖r‖ := by
  simp_rw [Restricted.norm_eq]

  -- I am leaving this sorried for now... see the Restricted.monomial section
  -- I have sorried something saying that the only non-zero term comes from n
  -- and this is exactly what I will need here

  sorry

lemma Restricted.monomial_one_norm (n : ℕ) : ‖Restricted.monomial (R := R) 1 n 1‖ = 1 := by
  simp [Restricted.monomial_norm]

lemma test5 (s : ℕ) (r : Polynomial R) (rd : r.degree < s) (h : ‖Polynomial.toRestricted 1 r‖ ≤ 1) :
    ‖Polynomial.toRestricted 1 ((Polynomial.monomial s 1) - r)‖ = 1 := by
  rw [Polynomial.toRestricted_sub, ← Restricted.coe_monomial]
  refine le_antisymm ?_ ?_
  · have := IsUltrametricDist.norm_add_le_max
      (Restricted.monomial 1 s 1) (- Polynomial.toRestricted 1 r)
    rw [← sub_eq_add_neg, norm_neg] at this
    exact this.trans (max_le (Restricted.monomial_one_norm s).le h)
  · have := PowerSeries.le_gaussNorm norm 1 
      (Polynomial.toRestricted 1 (Polynomial.monomial s 1 - r)).1 (Restricted.hasGaussNorm 1 _) s
    rwa [one_pow, mul_one, ← Restricted.norm_eq, Restricted.polynomial_coeff_coe _ s,
      test2 s r rd, norm_one, Polynomial.toRestricted_sub, ← Restricted.coe_monomial] at this


-- this should be generalised and places elsewhere
local instance : Nontrivial (↥R° ⧸ PowerBounded.openBall_ideal (R := R) 1 zero_lt_one) := by
    refine Ideal.Quotient.nontrivial_iff.mpr (fun hh => ?_)
    have h1 : (1 : ↥R°) ∈ PowerBounded.openBall_ideal (R := R) 1 zero_lt_one := by
      rw [hh]; exact Submodule.mem_top
    rw [PowerBounded.mem_openBall_ideal, OneMemClass.coe_one, norm_one] at h1
    exact lt_irrefl 1 h1


/-- **Weierstrass preparation, existence, normalised case `‖g‖ = 1` (PDF Theorem 4.13).**
For `g` distinguished of degree `s` with `‖g‖ = 1`, there is a monic polynomial `ω` of degree `s`
with `‖ω‖ = 1` and a unit `e` such that `g = e · ω`. -/
lemma weierstrassPreparation_exists_norm_one (g : PowerSeries.Restricted R 1) (hg : ‖g‖ = 1)
    (s : ℕ) (gd : distinguished norm 1 g.1 s)
    (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (ω : Polynomial R) (e : PowerSeries.Restricted R 1), ω.Monic ∧ ω.degree = s ∧
    ‖Polynomial.toRestricted 1 ω‖ = 1 ∧ IsUnit e ∧ g = e * (Polynomial.toRestricted 1 ω) := by
  obtain ⟨e', r, rd, h⟩ := weierstrassDivision_existance' g hg s gd
    (Restricted.monomial 1 s 1) hunit
  set ω : Polynomial R := Polynomial.monomial s 1 - r
  have rn : ‖Polynomial.toRestricted 1 r‖ ≤ 1 := by
    simpa [Restricted.monomial_norm] using weierstrassDivision_bounds_r _ s gd _ e' _ rd h
  have h : g * e' = Polynomial.toRestricted 1 ω := by
    rw [Polynomial.toRestricted_sub, ← Restricted.coe_monomial, h]
    abel
  have e'n : ‖e'‖ = 1 := by
    simp_rw [← test5 _ _ rd rn] -- Ideally I want these both on one line... but alas
    rw [← h, norm_mul, hg, one_mul]
  
  -- maybe I need to toPowerBounded definitions but this also works
  set G : ↥T° := ⟨g, IsPowerBounded.isPowerBounded_of_norm_le_one hg.le⟩
  set E : ↥T° := ⟨e', IsPowerBounded.isPowerBounded_of_norm_le_one e'n.le⟩
  set W : ↥T° := ⟨Polynomial.toRestricted 1 ω, IsPowerBounded.isPowerBounded_of_norm_le_one 
    (test5 s _ rd rn).le⟩

  have h_res : Restricted.openBall_residueRingHom 1 zero_lt_one G *
      Restricted.openBall_residueRingHom 1 zero_lt_one E =
      Restricted.openBall_residueRingHom 1 zero_lt_one W := by
    simp_rw [← map_mul, show G * E = W by exact Subtype.ext h]

  -- I think these statements can be pulled out in a general sense;
  -- i.e. these are just res reductions of out test statements
  -- and only requires all the generated results for them
  have hσW_s : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one W).coeff s = 1 := by
    rw [Restricted.openBall_residueRingHom_apply, Restricted.openBall_residuePolynomial_coeff]
    have : Restricted.pbCoeff W s = 1 := by
      apply Subtype.ext
      rw [Restricted.pbCoeff_coe, OneMemClass.coe_one]
      show PowerSeries.coeff s (Polynomial.toRestricted 1 ω).1 = 1
      rw [Restricted.polynomial_coeff_coe _ s, test2 s r rd]
    rw [this, map_one]
  have hσW_gt : ∀ v, s < v →
      (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one W).coeff v = 0 := fun v hv => by
    rw [Restricted.openBall_residueRingHom_apply, Restricted.openBall_residuePolynomial_coeff,
      Ideal.Quotient.eq_zero_iff_mem, PowerBounded.mem_openBall_ideal, Restricted.pbCoeff_coe]
    show ‖PowerSeries.coeff v (Polynomial.toRestricted 1 ω).1‖ < 1
    rw [Restricted.polynomial_coeff_coe _ v, test1 s r rd v hv, norm_zero]; exact zero_lt_one
  have hσW_deg : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one W).degree = s :=
    le_antisymm
      ((Polynomial.degree_le_iff_coeff_zero _ s).mpr fun m hm => hσW_gt m (by exact_mod_cast hm))
      (Polynomial.le_degree_of_ne_zero (by rw [hσW_s]; exact one_ne_zero))
  have hσW_monic : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one W).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff,
      Polynomial.natDegree_eq_of_degree_eq_some hσW_deg, hσW_s]
  -- this now requires gd.norm so we need to adjust as in test 5
  have hσG_s_unit :
      IsUnit ((Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one G).coeff s) := by
    rw [Restricted.openBall_residueRingHom_apply, Restricted.openBall_residuePolynomial_coeff]
    have : IsUnit (Restricted.pbCoeff G s) := by
      simpa [Restricted.isUnit_subring_iff (Restricted.pbCoeff G s)
        (by rw [Restricted.pbCoeff_coe, ← gd.norm_eq, ← Restricted.norm_eq, hg])] using gd.unit
    exact this.map _
  have hσG_gt : ∀ v, s < v →
      (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one G).coeff v = 0 := fun v hv => by
    rw [Restricted.openBall_residueRingHom_apply, Restricted.openBall_residuePolynomial_coeff,
      Ideal.Quotient.eq_zero_iff_mem, PowerBounded.mem_openBall_ideal, Restricted.pbCoeff_coe]
    show ‖PowerSeries.coeff v g.1‖ < 1
    have := gd.norm_max v hv
    rwa [← gd.norm_eq, ← Restricted.norm_eq, hg] at this
  have hσG_deg : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one G).degree = s :=
    le_antisymm
      ((Polynomial.degree_le_iff_coeff_zero _ s).mpr fun m hm => hσG_gt m (by exact_mod_cast hm))
      (Polynomial.le_degree_of_ne_zero hσG_s_unit.ne_zero)
  have hσG_lead : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one G).leadingCoeff =
      (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one G).coeff s := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hσG_deg]
  -- `σ E` is a nonzero constant with unit coefficient.
  have hσE_ne : Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h_res
    exact hσW_monic.ne_zero h_res.symm
  have hlead_ne : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one G).leadingCoeff *
      (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).leadingCoeff ≠ 0 := by
    rw [hσG_lead]
    obtain ⟨u, hu⟩ := hσG_s_unit
    rw [← hu]
    intro hzero
    apply Polynomial.leadingCoeff_ne_zero.mpr hσE_ne
    calc (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).leadingCoeff
        = ↑u⁻¹ * (↑u *
            (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).leadingCoeff) := by
          rw [← mul_assoc, u.inv_mul, one_mul]
      _ = ↑u⁻¹ * 0 := by rw [hzero]
      _ = 0 := mul_zero _
  have hnatdeg : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).natDegree = 0 := by
    have h1 := Polynomial.natDegree_mul' hlead_ne
    rw [h_res, Polynomial.natDegree_eq_of_degree_eq_some hσW_deg,
      Polynomial.natDegree_eq_of_degree_eq_some hσG_deg] at h1
    omega
  have hσE_C : Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E =
      Polynomial.C ((Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp hnatdeg)
  have hcoeff0_unit :
      IsUnit ((Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).coeff 0) := by
    have hWlead : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one W).leadingCoeff = 1 :=
      hσW_monic
    have hlead_eq := Polynomial.leadingCoeff_mul' hlead_ne
    rw [h_res, hWlead, hσG_lead] at hlead_eq
    have hElead : (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).leadingCoeff =
        (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).coeff 0 := by
      rw [Polynomial.leadingCoeff, hnatdeg]
    rw [hElead] at hlead_eq
    have hu1 : IsUnit ((Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one G).coeff s *
        (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E).coeff 0) := by
      rw [← hlead_eq]; exact isUnit_one
    exact isUnit_of_mul_isUnit_right hu1
  have hσE_unit : IsUnit (Restricted.openBall_residueRingHom (R := R) 1 zero_lt_one E) := by
    rw [hσE_C]; exact Polynomial.isUnit_C.mpr hcoeff0_unit
  -- transport unit-ness back to `e'`.
  have he'_unit : IsUnit e' := by
    have h2 : IsUnit (Ideal.Quotient.mk
        (PowerBounded.topologicalNilradical (R := PowerSeries.Restricted R 1) ℤ) E) := by
      have hu := ((Restricted.openBall_ideal_isUnit_iff E).mpr hσE_unit).map
        (Ideal.quotEquivOfEq (PowerBounded.topologicalNilradical_is_openBall_one
          (R := PowerSeries.Restricted R 1)).symm)
      rwa [Ideal.quotEquivOfEq_mk] at hu
    have hEunit : IsUnit E := (IsPowerBounded.PowerBounded_isUnit_iff_res_isUnit E).mpr h2
    exact (Restricted.isUnit_subring_iff E e'n).mp hEunit
  -- assemble: `e = (e')⁻¹`.
  obtain ⟨ue, hue⟩ := he'_unit
  refine ⟨ω, (↑ue⁻¹ : PowerSeries.Restricted R 1), test4 _ _ rd, test3 _ _ rd,
    test5 _ _ rd rn, ue⁻¹.isUnit, ?_⟩
  rw [← h, ← hue, mul_comm g (↑ue : PowerSeries.Restricted R 1), ← mul_assoc, ue.inv_mul,
    one_mul]

/-- **Weierstrass preparation, existence (PDF Theorem 4.13).**  For `g` distinguished of degree `s`
(with the `hunit` scaling hypothesis needed for Weierstrass division), there is a monic polynomial
`ω` of degree `s` with `‖ω‖ = 1` and a unit `e` such that `g = e · ω`.  Reduces to the normalised
case `weierstrassPreparation_exists_norm_one` after scaling `g` to leading-coefficient norm `1`; the
scaling unit for `g` itself is supplied by `hunit g` since a distinguished `g` is nonzero. -/
lemma weierstrassPreparation_exists (g : PowerSeries.Restricted R 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s)
    (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (ω : Polynomial R) (e : PowerSeries.Restricted R 1), ω.Monic ∧ ω.degree = s ∧
    ‖Polynomial.toRestricted 1 ω‖ = 1 ∧ IsUnit e ∧ g = e * (Polynomial.toRestricted 1 ω) := by
  obtain ⟨a, ha_norm, ha_unit⟩ := hunit g (ne_of_apply_ne Subtype.val gd.ne_zero)
  set g₁ : PowerSeries.Restricted R 1 := PowerSeries.Restricted.C 1 a * g with h
  obtain ⟨ω, e₁, hmonic, hnatdeg, hωnorm, he₁, hg₁_eq⟩ :=
    weierstrassPreparation_exists_norm_one g₁ (by simp [h, PowerSeries.Restricted.norm_C, ha_norm,
    inv_mul_cancel₀ (ne_of_gt (norm_pos_iff (a := g).mpr (ne_of_apply_ne Subtype.val gd.ne_zero)))])
    s (ext1 g s gd a ha_unit) hunit
  obtain ⟨ua, hua⟩ := PowerSeries.Restricted.C_isUnit 1 ha_unit
  refine ⟨ω, (↑ua⁻¹ : PowerSeries.Restricted R 1) * e₁, hmonic, hnatdeg, hωnorm,
    ua⁻¹.isUnit.mul he₁, ?_⟩
  rw [← one_mul g, ← ua.inv_mul, mul_assoc, hua, ← h, mul_assoc, ← hg₁_eq]

lemma weierstrassPreparation_unique (g : PowerSeries.Restricted R 1) (s : ℕ)
    (gd : distinguished norm 1 g.1 s)
    (hunit : ∀ f : PowerSeries.Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! ω : Polynomial R, ∃! e : PowerSeries.Restricted R 1, ω.Monic ∧ ω.degree = s ∧
    ‖(Polynomial.toRestricted 1 ω)‖ = 1 ∧ IsUnit e ∧
    g = e * (Polynomial.toRestricted 1 ω) := by
  obtain ⟨ω, e, ωm, ωd, ωn, ⟨ue, hue⟩, hg1⟩ := weierstrassPreparation_exists g s gd hunit
  refine ⟨ω, ⟨e, ⟨ωm, ωd, ωn, ⟨ue, hue⟩, hg1⟩, ?_⟩, ?_⟩
  · rintro e' ⟨_, _, _, _, hge'⟩
    exact sub_eq_zero.mp (norm_eq_zero.mp (by aesop))
  · rintro ω' ⟨e', ⟨ω'm, ω'd, ω'n, ⟨ue', hue'⟩, hg1'⟩, _⟩
    have rd : (ω' - ω).degree < (s : WithBot ℕ) := by
      simpa [ω'd] using Polynomial.degree_sub_lt (ω'd.trans ωd.symm) ω'm.ne_zero
        (by rw [ω'm.leadingCoeff, ωm.leadingCoeff])
    have : (0 : PowerSeries.Restricted R 1) = g * ((↑ue⁻¹ : PowerSeries.Restricted R 1) - ↑ue'⁻¹)
        + Polynomial.toRestricted 1 (ω' - ω) := by
      rw [mul_sub, Polynomial.toRestricted_sub]
      have : g * (↑ue⁻¹ : PowerSeries.Restricted R 1) = Polynomial.toRestricted 1 ω := by
        rw [hg1, ← hue, mul_comm (↑ue : PowerSeries.Restricted R 1) _, mul_assoc, ue.mul_inv,
          mul_one]
      have : g * (↑ue'⁻¹ : PowerSeries.Restricted R 1) = Polynomial.toRestricted 1 ω' := by
        rw [hg1', ← hue', mul_comm (↑ue' : PowerSeries.Restricted R 1) _, mul_assoc, ue'.mul_inv,
          mul_one]
      grind
    rw [sub_eq_zero.symm]
    exact Polynomial.coe_inj.mp (congrArg Subtype.val (norm_le_zero_iff
      (a := Polynomial.toRestricted 1 (ω' - ω)).mp (by simpa [norm_zero] using
      (weierstrassDivision_bounds_r g s gd 0 _ _ rd this))))
