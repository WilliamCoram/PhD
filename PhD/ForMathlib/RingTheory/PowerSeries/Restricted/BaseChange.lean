/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.WeierstrassDivision

/-! # Base change of restricted power series

Coefficientwise base change of restricted power series along an isometric algebra map
`K → L` (underlying map `PowerSeries.map (algebraMap K L)`): the Gauss terms are literally
preserved, so restrictedness, norms and the `IsDistinguished` structures all transport.

The endpoint is **descent by uniqueness** (`weierstrassDivision_descend`): a Weierstrass
division over a finite isometric field extension `L/K`, of data defined over `K`, descends
to `K`.  The proof needs no Galois theory and no separability — a bounded `K`-linear
retraction of the embedding retracts the division coefficientwise, and the hypothesis-free
division bounds force the difference to vanish.

## Main definitions

* `PowerSeries.Restricted.mapAlgebra`: coefficientwise base change of restricted power series
  along an isometric algebra map `K → L`, as a ring homomorphism `Restricted K c → Restricted L c`.

## Main results

* `PowerSeries.Restricted.norm_mapAlgebra`: base change is a Gauss-norm isometry.
* `PowerSeries.Restricted.weierstrassDivision_descend`: a Weierstrass division over a finite
  isometric field extension `L/K`, of data defined over `K`, descends to `K`.
-/

open Filter
open scoped Topology

namespace PowerSeries

namespace Restricted

section MapAlgebra

variable {K L : Type*} [NormedCommRing K] [IsUltrametricDist K] [NormedCommRing L]
  [IsUltrametricDist L] [Algebra K L] (c : ℝ)

/-- **Base change of restricted power series** along an isometric algebra map `K → L`
(coefficientwise `algebraMap`; underlying map `PowerSeries.map (algebraMap K L)`). -/
noncomputable def mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) :
    Restricted K c →+* Restricted L c :=
  RingHom.codRestrict ((PowerSeries.map (algebraMap K L)).comp (IsRestricted.subring c).subtype)
    (IsRestricted.subring c) fun f ↦ isRestricted_map c (fun x ↦ (hiso x).le) f.2

/-- The underlying power series of a base change is `PowerSeries.map`. -/
@[simp]
lemma val_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) (f : Restricted K c) :
    (mapAlgebra c hiso f).1 = PowerSeries.map (algebraMap K L) f.1 := rfl

/-- Base change is a Gauss-norm isometry (termwise, by `hiso`). -/
lemma norm_mapAlgebra [Fact (0 < c)] (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : Restricted K c) : ‖mapAlgebra c hiso f‖ = ‖f‖ := by
  simp [norm_def, PowerSeries.gaussNorm_eq, hiso]

/-- Base change sends polynomials to polynomials. -/
@[simp]
lemma mapAlgebra_toRestricted (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) (p : Polynomial K) :
    mapAlgebra c hiso (Polynomial.toRestricted c p) =
    Polynomial.toRestricted c (p.map (algebraMap K L)) :=
  Subtype.ext (by simp)

end MapAlgebra

section Field

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K L] {c : ℝ} [Fact (0 < c)]

omit [Fact (0 < c)] in
/-- `IsDistinguished` transfers along isometric base change of fields: unit coefficients are
nonzero coefficients, and every Gauss term is preserved. -/
lemma isDistinguished_mapAlgebra_iff (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : Restricted K c) (s : ℕ) :
    IsDistinguished norm c (mapAlgebra c hiso f).1 s ↔ IsDistinguished norm c f.1 s := by
  rw [val_mapAlgebra]
  refine ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨?_, ?_, ?_⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨?_, ?_, ?_⟩⟩
  · simpa only [PowerSeries.coeff_map, isUnit_map_iff] using h1
  · rw [← PowerSeries.gaussNorm_map norm c norm (algebraMap K L) hiso f.1]
    simpa only [PowerSeries.coeff_map, hiso] using h2
  · simpa only [PowerSeries.coeff_map, hiso] using h3
  · simpa only [PowerSeries.coeff_map, isUnit_map_iff] using h1
  · rw [PowerSeries.gaussNorm_map norm c norm (algebraMap K L) hiso f.1]
    simpa only [PowerSeries.coeff_map, hiso] using h2
  · simpa only [PowerSeries.coeff_map, hiso] using h3

omit [IsUltrametricDist K] [IsUltrametricDist L] in
private lemma lmap_mul (π : L →ₗ[K] K) (g : PowerSeries K) (h : PowerSeries L) :
    (PowerSeries.mk fun n ↦ π (coeff n (PowerSeries.map (algebraMap K L) g * h)))
      = g * PowerSeries.mk fun n ↦ π (coeff n h) := by
  ext n
  rw [coeff_mk, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [PowerSeries.coeff_map, coeff_mk, ← Algebra.smul_def, map_smul, smul_eq_mul]

omit [IsUltrametricDist K] [IsUltrametricDist L] [Fact (0 < c)] in
private lemma isRestricted_mk_apply (hc0 : 0 < c) (π : L →ₗ[K] K) {Cπ : ℝ}
    (hCπ : ∀ x : L, ‖π x‖ ≤ Cπ * ‖x‖) {h : PowerSeries L} (hh : IsRestricted c h) :
    IsRestricted c (PowerSeries.mk fun n ↦ π (coeff n h)) := by
  rw [isRestricted_iff]
  have h0 : Tendsto (fun n : ℕ ↦ Cπ * (‖coeff n h‖ * c ^ n)) cofinite (𝓝 0) := by
    simpa using ((isRestricted_iff c h).mp hh).const_mul Cπ
  refine squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc0.le n))
    (fun n ↦ ?_) h0
  rw [coeff_mk, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hCπ _) (pow_pos hc0 n).le

omit [IsUltrametricDist K] [IsUltrametricDist L] in
private lemma coeff_finsetSum_monomial_apply (π : L →ₗ[K] K) (r : Polynomial L) (k : ℕ) :
    (∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n))).coeff k = π (r.coeff k) := by
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' r.support k fun n ↦ π (r.coeff n)]
  split_ifs with hk
  · rfl
  · rw [show r.coeff k = 0 by simpa [Polynomial.mem_support_iff] using hk, map_zero]

omit [IsUltrametricDist K] [IsUltrametricDist L] in
private lemma degree_finsetSum_monomial_apply_lt (π : L →ₗ[K] K) {r : Polynomial L} {s : ℕ}
    (hr : r.degree < s) : (∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n))).degree < s := by
  rw [Polynomial.degree_lt_iff_coeff_zero] at hr ⊢
  intro m hm
  rw [coeff_finsetSum_monomial_apply, hr m hm, map_zero]

/-- **Descent by uniqueness, retraction form**: a Weierstrass division over an isometric
extension `L/K`, of data defined over `K`, descends to `K`, given any bounded `K`-linear
retraction of the embedding.  The retraction retracts the division coefficientwise, and the
hypothesis-free division bounds force the `L`-side difference to vanish.  (Finite
extensions provide a retraction — `weierstrassDivision_descend`; so does the
`t⁰`-coefficient of a Gauss extension.) -/
theorem weierstrassDivision_descend_of_retraction
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) (π : L →ₗ[K] K)
    (hπ : ∀ a : K, π (algebraMap K L a) = a) {Cπ : ℝ} (hCπ : ∀ x : L, ‖π x‖ ≤ Cπ * ‖x‖)
    {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) (f : Restricted K c) {q : Restricted L c}
    {r : Polynomial L} (hr : r.degree < s)
    (hf : mapAlgebra c hiso f = mapAlgebra c hiso g * q + Polynomial.toRestricted c r) :
    ∃ (q₀ : Restricted K c) (r₀ : Polynomial K), r₀.degree < s ∧
      f = g * q₀ + Polynomial.toRestricted c r₀ ∧ mapAlgebra c hiso q₀ = q ∧
      r₀.map (algebraMap K L) = r := by
  have hq0res : IsRestricted c (PowerSeries.mk fun n ↦ π (coeff n q.1)) :=
    isRestricted_mk_apply Fact.out π hCπ q.2
  have hr₀deg := degree_finsetSum_monomial_apply_lt π hr
  have hf1 : PowerSeries.map (algebraMap K L) f.1
      = PowerSeries.map (algebraMap K L) g.1 * q.1 + (r : PowerSeries L) := by
    have h := congrArg Subtype.val hf
    rwa [show (mapAlgebra c hiso g * q + Polynomial.toRestricted c r).1
        = (mapAlgebra c hiso g).1 * q.1 + (r : PowerSeries L) from rfl,
      val_mapAlgebra, val_mapAlgebra] at h
  have hK : f = g * ⟨PowerSeries.mk fun n ↦ π (coeff n q.1), hq0res⟩ +
      Polynomial.toRestricted c (∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n))) := by
    refine Subtype.ext ?_
    change f.1 = g.1 * PowerSeries.mk (fun n ↦ π (coeff n q.1)) +
      ((∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n)) : Polynomial K) :
        PowerSeries K)
    have h2 : PowerSeries.mk (fun n ↦ π (coeff n (PowerSeries.map (algebraMap K L) f.1)))
        = PowerSeries.mk (fun n ↦ π (coeff n
            (PowerSeries.map (algebraMap K L) g.1 * q.1 + (r : PowerSeries L)))) :=
      congrArg (fun h : PowerSeries L ↦ PowerSeries.mk fun n ↦ π (coeff n h)) hf1
    rwa [show (PowerSeries.mk fun n ↦ π (coeff n (PowerSeries.map (algebraMap K L) f.1)))
        = f.1 by ext n; rw [coeff_mk, PowerSeries.coeff_map, hπ],
      show (PowerSeries.mk fun n ↦ π (coeff n
          (PowerSeries.map (algebraMap K L) g.1 * q.1 + (r : PowerSeries L))))
        = (PowerSeries.mk fun n ↦ π (coeff n (PowerSeries.map (algebraMap K L) g.1 * q.1)))
          + PowerSeries.mk fun n ↦ π (coeff n (r : PowerSeries L)) by
        ext n; simp [map_add],
      lmap_mul,
      show (PowerSeries.mk fun n ↦ π (coeff n (r : PowerSeries L)))
        = ((∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n)) : Polynomial K) :
            PowerSeries K) by
        ext n
        rw [coeff_mk, Polynomial.coeff_coe, Polynomial.coeff_coe,
          coeff_finsetSum_monomial_apply]] at h2
  have hzero : (0 : Restricted L c) = mapAlgebra c hiso g *
      (q - mapAlgebra c hiso ⟨PowerSeries.mk fun n ↦ π (coeff n q.1), hq0res⟩) +
      Polynomial.toRestricted c (r - (∑ n ∈ r.support,
        Polynomial.monomial n (π (r.coeff n))).map (algebraMap K L)) := by
    have hmapK := congrArg (mapAlgebra c hiso) hK
    simp only [map_add, mapAlgebra_toRestricted] at hmapK
    rw [mul_sub, map_sub]
    linear_combination hf - hmapK - RingHom.map_mul (mapAlgebra c hiso) g
      ⟨PowerSeries.mk fun n ↦ π (coeff n q.1), hq0res⟩
  have hdegρ : (r - (∑ n ∈ r.support,
      Polynomial.monomial n (π (r.coeff n))).map (algebraMap K L)).degree < s :=
    (Polynomial.degree_sub_le _ _).trans_lt
      (max_lt hr (Polynomial.degree_map_le.trans_lt hr₀deg))
  have hgd' : IsDistinguished norm c (mapAlgebra c hiso g).1 s :=
    (isDistinguished_mapAlgebra_iff hiso g s).mpr hg
  have hq_eq : q - mapAlgebra c hiso ⟨PowerSeries.mk fun n ↦ π (coeff n q.1), hq0res⟩ = 0 := by
    have hb := norm_q_le_of_eq_mul_add c hgd' hdegρ hzero
    rwa [norm_zero, mul_zero, norm_le_zero_iff] at hb
  have hr_eq : r - (∑ n ∈ r.support,
      Polynomial.monomial n (π (r.coeff n))).map (algebraMap K L) = 0 := by
    have hb := norm_r_le_of_eq_mul_add c hgd' hdegρ hzero
    rw [norm_zero, norm_le_zero_iff] at hb
    exact Polynomial.toRestricted_injective c (by rw [map_zero]; exact hb)
  exact ⟨⟨PowerSeries.mk fun n ↦ π (coeff n q.1), hq0res⟩,
    ∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n)), hr₀deg, hK,
    (sub_eq_zero.mp hq_eq).symm, (sub_eq_zero.mp hr_eq).symm⟩

/-- **Descent by uniqueness**: a Weierstrass division over a finite isometric extension
`L/K`, of data defined over `K`, descends to `K`.  Finite-dimensionality over the complete
base provides the bounded retraction for
`weierstrassDivision_descend_of_retraction`. -/
theorem weierstrassDivision_descend [CompleteSpace K] [Module.Finite K L]
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) (f : Restricted K c) {q : Restricted L c}
    {r : Polynomial L} (hr : r.degree < s)
    (hf : mapAlgebra c hiso f = mapAlgebra c hiso g * q + Polynomial.toRestricted c r) :
    ∃ (q₀ : Restricted K c) (r₀ : Polynomial K), r₀.degree < s ∧
      f = g * q₀ + Polynomial.toRestricted c r₀ ∧ mapAlgebra c hiso q₀ = q ∧
      r₀.map (algebraMap K L) = r := by
  let : NormedSpace K L := ⟨fun a x ↦ le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  obtain ⟨π, hπcomp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  obtain ⟨Cπ, -, hCπ⟩ := SemilinearMapClass.bound_of_continuous π
    π.continuous_of_finiteDimensional
  exact weierstrassDivision_descend_of_retraction hiso π
    (LinearMap.congr_fun hπcomp) hCπ hg f hr hf

end Field

end Restricted

end PowerSeries
