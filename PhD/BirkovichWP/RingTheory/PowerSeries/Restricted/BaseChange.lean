/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

import PhD.ForMathlib.Algebra.Polynomial.Coeff
import PhD.ForMathlib.RingTheory.PowerSeries.Basic
import PhD.BirkovichWP.RingTheory.PowerSeries.Restricted.WeierstrassDivision

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

variable {K L : Type*} [NontriviallyNormedField K] [NontriviallyNormedField L] [Algebra K L]
  {c : ℝ}

variable [IsUltrametricDist K] [IsUltrametricDist L]

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

variable [Fact (0 < c)]

/-- **Descent by uniqueness, retraction form**: a Weierstrass division over an isometric
extension `L/K`, of data defined over `K`, descends to `K`, given any bounded `K`-linear
retraction of the embedding.  The retraction retracts the division coefficientwise, and the
hypothesis-free division bounds force the `L`-side difference to vanish.  (Finite
extensions provide a retraction — `weierstrassDivision_descend`; so does the
`t⁰`-coefficient of a Gauss extension.) -/
theorem weierstrassDivision_descend_of_retraction (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (π : L →ₗ[K] K) (hπ : ∀ a : K, π (algebraMap K L a) = a) {Cπ : ℝ}
    (hCπ : ∀ x : L, ‖π x‖ ≤ Cπ * ‖x‖) {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) (f : Restricted K c) {q : Restricted L c} {r : Polynomial L}
    (hr : r.degree < s)
    (hf : mapAlgebra c hiso f = mapAlgebra c hiso g * q + Polynomial.toRestricted c r) :
    ∃ (q₀ : Restricted K c) (r₀ : Polynomial K), r₀.degree < s ∧
      f = g * q₀ + Polynomial.toRestricted c r₀ ∧ mapAlgebra c hiso q₀ = q ∧
      r₀.map (algebraMap K L) = r := by
  set q₀ : Restricted K c := ⟨PowerSeries.mk fun n ↦ π (coeff n q.1),
    PowerSeries.isRestricted_mk c (le_of_lt Fact.out) ⇑π hCπ q.2⟩ with hq₀
  set r₀ : Polynomial K := ∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n)) with hr₀
  have : f = g * q₀ + Polynomial.toRestricted c r₀ := by
    refine Subtype.ext ?_
    change f.1 = g.1 * (PowerSeries.mk fun n ↦ π (coeff n q.1))
      + ((∑ n ∈ r.support, Polynomial.monomial n (π (r.coeff n)) : Polynomial K) : PowerSeries K)
    exact PowerSeries.eq_of_map_eq_of_retraction π hπ (fun n ↦ PowerSeries.coeff_mk n _)
      (fun n ↦ by rw [Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.coeff_finsetSum_monomial_apply]) (by simpa using congrArg Subtype.val hf)
  exact ⟨q₀, r₀, Polynomial.degree_finsetSum_monomial_apply_lt π hr, this,
    weierstrassDivision_q_unique c ((isDistinguished_mapAlgebra_iff hiso g s).mpr hg)
    (Polynomial.degree_map_le.trans_lt (Polynomial.degree_finsetSum_monomial_apply_lt π hr))
    (by rw [this, map_add, map_mul, mapAlgebra_toRestricted]) hr hf,
    weierstrassDivision_r_unique c ((isDistinguished_mapAlgebra_iff hiso g s).mpr hg)
    (Polynomial.degree_map_le.trans_lt (Polynomial.degree_finsetSum_monomial_apply_lt π hr))
    (by rw [this, map_add, map_mul, mapAlgebra_toRestricted]) hr hf⟩

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
  obtain ⟨Cπ, -, hCπ⟩ := SemilinearMapClass.bound_of_continuous π π.continuous_of_finiteDimensional
  exact weierstrassDivision_descend_of_retraction hiso π (LinearMap.congr_fun hπcomp) hCπ hg f hr hf

end Field

end Restricted

end PowerSeries
