/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

import PhD.ForMathlib.Algebra.Polynomial.Coeff
import PhD.ForMathlib.RingTheory.MvPowerSeries.Basic
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.WeierstrassDivision

/-! # Base change and descent for multivariate restricted power series

Coefficientwise base change of restricted multivariate power series along an isometric
embedding of normed fields, and descent of multivariate Weierstrass division from a finite
isometric extension back to the base, by uniqueness of the quotient.  This is the engine
behind the divisible-radii multivariate endpoints: one finite spectral-norm extension of the
bottom field realises every radius as the norm of a unit.

## Main definitions

* `MvPowerSeries.Restricted.mapAlgebra`: coefficientwise base change as a ring homomorphism,
  Gauss-norm isometric.

## Main results

* `MvPowerSeries.Restricted.coeff_finSuccEquiv_mapAlgebra`: base change intertwines the
  splitting isomorphisms.
* `MvPowerSeries.Restricted.isDistinguishedX0_mapAlgebra`: distinguishedness in `X 0` is
  preserved by base change.
* `MvPowerSeries.Restricted.weierstrassDivision_descend`: a multivariate Weierstrass
  division over a finite isometric extension, of data defined over the base, descends.
-/

namespace MvPowerSeries.Restricted

section MapAlgebra

variable {K L : Type*} [NormedCommRing K] [NormedCommRing L] [IsUltrametricDist K]
  [IsUltrametricDist L] [Algebra K L] {σ : Type*} (d : σ → ℝ)

/-- Coefficientwise base change of restricted multivariate power series along an isometric
embedding, as a ring homomorphism. -/
noncomputable def mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) :
    Restricted K d →+* Restricted L d :=
  RingHom.codRestrict
    ((MvPowerSeries.map (algebraMap K L)).comp (IsRestricted.subring d).subtype)
    (IsRestricted.subring d) fun f ↦ isRestricted_map d (fun x ↦ (hiso x).le) f.2

/-- The underlying multivariate power series of a base change is `MvPowerSeries.map`. -/
@[simp]
lemma val_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) (f : Restricted K d) :
    (mapAlgebra d hiso f).1 = MvPowerSeries.map (algebraMap K L) f.1 := rfl

/-- Base change is a Gauss-norm isometry. -/
lemma norm_mapAlgebra [Fact (∀ i, 0 < d i)] (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : Restricted K d) : ‖mapAlgebra d hiso f‖ = ‖f‖ := by
  simp [norm_def, MvPowerSeries.gaussNorm_map, hiso]

end MapAlgebra

section Split

variable {K L : Type*} [NormedCommRing K] [NormedCommRing L] [IsUltrametricDist K]
  [IsUltrametricDist L] [Algebra K L] {n : ℕ} {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

omit [IsUltrametricDist K] [IsUltrametricDist L] [Algebra K L] in
private lemma finSuccEquiv_map (φ : K →+* L) (F : MvPowerSeries (Fin (n + 1)) K) :
    MvPowerSeries.finSuccEquiv L n (MvPowerSeries.map φ F) =
      PowerSeries.map (MvPowerSeries.map φ) (MvPowerSeries.finSuccEquiv K n F) := by
  refine PowerSeries.ext fun j ↦ MvPowerSeries.ext fun i ↦ ?_
  simp [MvPowerSeries.coeff_coeff_finSuccEquiv, PowerSeries.coeff_map]

/-- Base change intertwines the splitting isomorphisms: the `X 0`-slices of the base-changed
series are the base changes of the `X 0`-slices. -/
lemma coeff_finSuccEquiv_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : Restricted K c) (j : ℕ) :
    PowerSeries.coeff j (finSuccEquiv L c (mapAlgebra c hiso f)).1 =
      mapAlgebra (Fin.tail c) hiso (PowerSeries.coeff j (finSuccEquiv K c f).1) := by
  refine Subtype.ext ?_
  calc (PowerSeries.coeff j (finSuccEquiv L c (mapAlgebra c hiso f)).1).1
      = PowerSeries.coeff j (MvPowerSeries.finSuccEquiv L n (mapAlgebra c hiso f).1) :=
        coeff_finSuccEquiv c (mapAlgebra c hiso f) j
    _ = MvPowerSeries.map (algebraMap K L)
          (PowerSeries.coeff j (MvPowerSeries.finSuccEquiv K n f.1)) := by
        rw [val_mapAlgebra, finSuccEquiv_map (algebraMap K L) f.1, PowerSeries.coeff_map]
    _ = (mapAlgebra (Fin.tail c) hiso (PowerSeries.coeff j (finSuccEquiv K c f).1)).1 :=
        congrArg (MvPowerSeries.map (algebraMap K L)) (coeff_finSuccEquiv c f j).symm

/-- Base change commutes with the `X 0`-polynomial embedding. -/
@[simp]
lemma mapAlgebra_toMvRestrictedX0 (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (ω : Polynomial (Restricted K (Fin.tail c))) :
    mapAlgebra c hiso (Polynomial.toMvRestrictedX0 c ω) =
      Polynomial.toMvRestrictedX0 c (ω.map (mapAlgebra (Fin.tail c) hiso)) :=
  Subtype.ext (MvPowerSeries.ext fun t ↦ by simp [Polynomial.coeff_toMvRestrictedX0])

private lemma gaussNorm_finSuccEquiv_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : Restricted K c) :
    PowerSeries.gaussNorm norm (c 0) (finSuccEquiv L c (mapAlgebra c hiso f)).1 =
      PowerSeries.gaussNorm norm (c 0) (finSuccEquiv K c f).1 := by
  rw [← PowerSeries.Restricted.norm_def, ← PowerSeries.Restricted.norm_def, norm_finSuccEquiv,
    norm_finSuccEquiv, norm_mapAlgebra]

private lemma norm_coeff_finSuccEquiv_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : Restricted K c) (j : ℕ) :
    ‖PowerSeries.coeff j (finSuccEquiv L c (mapAlgebra c hiso f)).1‖ =
      ‖PowerSeries.coeff j (finSuccEquiv K c f).1‖ := by
  rw [coeff_finSuccEquiv_mapAlgebra hiso f j, norm_mapAlgebra]

/-- Distinguishedness in `X 0` is preserved by base change along an isometric embedding. -/
lemma isDistinguishedX0_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {f : Restricted K c} {s : ℕ} (hf : IsDistinguishedX0 f s) :
    IsDistinguishedX0 (mapAlgebra c hiso f) s := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_finSuccEquiv_mapAlgebra hiso f s]
    exact (mapAlgebra (Fin.tail c) hiso).isUnit_map h1
  · rw [gaussNorm_finSuccEquiv_mapAlgebra hiso f, norm_coeff_finSuccEquiv_mapAlgebra hiso f s]
    exact h2
  · intro t ht
    rw [norm_coeff_finSuccEquiv_mapAlgebra hiso f t, norm_coeff_finSuccEquiv_mapAlgebra hiso f s]
    exact h3 t ht

end Split

section Descent

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K L]
  {n : ℕ} {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

omit [CompleteSpace K] in
/-- **Descent by uniqueness, retraction form**: a multivariate Weierstrass division over an
isometric extension `L`, of data defined over `K`, descends to `K`, given any bounded
`K`-linear retraction of the embedding — apply it to every multivariate coefficient; the
retraction of the `L`-division is a `K`-division, and the difference is an `L`-division of
`0`, killed by the unit-free bounds. -/
lemma weierstrassDivision_descend_of_retraction
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) (π : L →ₗ[K] K)
    (hπ : ∀ a : K, π (algebraMap K L a) = a) {Cπ : ℝ} (hCπ : ∀ x : L, ‖π x‖ ≤ Cπ * ‖x‖)
    {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) (f : Restricted K c) {q : Restricted L c}
    {r : Polynomial (Restricted L (Fin.tail c))} (hr : r.degree < s)
    (hf : mapAlgebra c hiso f = mapAlgebra c hiso g * q + Polynomial.toMvRestrictedX0 c r) :
    ∃ (q₀ : Restricted K c) (r₀ : Polynomial (Restricted K (Fin.tail c))),
      r₀.degree < s ∧ f = g * q₀ + Polynomial.toMvRestrictedX0 c r₀ ∧
      mapAlgebra c hiso q₀ = q ∧ r₀.map (mapAlgebra (Fin.tail c) hiso) = r := by
  have hc0 : ∀ i, (0 : ℝ) < c i := Fact.out
  let ρ := mapRetraction (Fin.tail c) (fun i ↦ (hc0 i.succ).le) π.toAddMonoidHom hCπ
  set q₀ : Restricted K c := mapRetraction c (fun i ↦ (hc0 i).le) π.toAddMonoidHom hCπ q
  set r₀ : Polynomial (Restricted K (Fin.tail c)) :=
    ∑ m ∈ r.support, Polynomial.monomial m (ρ (r.coeff m)) with hr₀
  have hr₀deg : r₀.degree < s := Polynomial.degree_finsetSum_monomial_apply_lt ρ hr
  have hK : f = g * q₀ + Polynomial.toMvRestrictedX0 c r₀ := by
    refine Subtype.ext ?_
    change f.1 = g.1 * q₀.1 + (Polynomial.toMvRestrictedX0 c r₀).1
    refine MvPowerSeries.eq_of_map_eq_of_retraction π hπ (fun t ↦ rfl) (fun t ↦ ?_)
      (by simpa using congrArg Subtype.val hf)
    rw [Polynomial.coeff_toMvRestrictedX0, Polynomial.coeff_toMvRestrictedX0, hr₀,
      Polynomial.coeff_finsetSum_monomial_apply]
    rfl
  have hgd' : IsDistinguishedX0 (mapAlgebra c hiso g) s := isDistinguishedX0_mapAlgebra hiso hg
  have hKmap : mapAlgebra c hiso f = mapAlgebra c hiso g * mapAlgebra c hiso q₀ +
      Polynomial.toMvRestrictedX0 c (r₀.map (mapAlgebra (Fin.tail c) hiso)) := by
    rw [hK, map_add, map_mul, mapAlgebra_toMvRestrictedX0]
  have hr₀mapdeg : (r₀.map (mapAlgebra (Fin.tail c) hiso)).degree < s :=
    Polynomial.degree_map_le.trans_lt hr₀deg
  exact ⟨q₀, r₀, hr₀deg, hK,
    weierstrassDivision_q_unique hgd' hr₀mapdeg hKmap hr hf,
    weierstrassDivision_r_unique hgd' hr₀mapdeg hKmap hr hf⟩

/-- **Descent by uniqueness** from a finite isometric extension: finite-dimensionality over
the complete base provides the bounded retraction. -/
lemma weierstrassDivision_descend [Module.Finite K L]
    (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) {g : Restricted K c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) (f : Restricted K c) {q : Restricted L c}
    {r : Polynomial (Restricted L (Fin.tail c))} (hr : r.degree < s)
    (hf : mapAlgebra c hiso f = mapAlgebra c hiso g * q + Polynomial.toMvRestrictedX0 c r) :
    ∃ (q₀ : Restricted K c) (r₀ : Polynomial (Restricted K (Fin.tail c))),
      r₀.degree < s ∧ f = g * q₀ + Polynomial.toMvRestrictedX0 c r₀ ∧
      mapAlgebra c hiso q₀ = q ∧ r₀.map (mapAlgebra (Fin.tail c) hiso) = r := by
  let : NormedSpace K L := ⟨fun a x ↦ le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  obtain ⟨π, hπcomp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  obtain ⟨Cπ, -, hCπ⟩ := SemilinearMapClass.bound_of_continuous π
    π.continuous_of_finiteDimensional
  exact weierstrassDivision_descend_of_retraction hiso π
    (LinearMap.congr_fun hπcomp) hCπ hg f hr hf

end Descent

end MvPowerSeries.Restricted
