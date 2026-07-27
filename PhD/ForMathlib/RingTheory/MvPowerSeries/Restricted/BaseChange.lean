/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
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

section Predicate

variable {K L : Type*} [NormedCommRing K] [NormedCommRing L] [Algebra K L]
  {σ : Type*} (d : σ → ℝ)

/-- Base change along an isometric embedding preserves restrictedness. -/
lemma isRestricted_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {f : MvPowerSeries σ K} (hf : IsRestricted d f) :
    IsRestricted d (MvPowerSeries.map (algebraMap K L) f) := by
  refine hf.congr fun t ↦ ?_
  rw [MvPowerSeries.coeff_map, hiso]

end Predicate

section MapAlgebra

variable {K L : Type*} [NormedCommRing K] [NormedCommRing L] [IsUltrametricDist K]
  [IsUltrametricDist L] [Algebra K L] {σ : Type*} (d : σ → ℝ)

/-- Coefficientwise base change of restricted multivariate power series along an isometric
embedding, as a ring homomorphism. -/
noncomputable def mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) :
    Restricted K d →+* Restricted L d :=
  RingHom.codRestrict
    ((MvPowerSeries.map (algebraMap K L)).comp (IsRestricted.subring d).subtype)
    (IsRestricted.subring d) fun f ↦ isRestricted_mapAlgebra d hiso f.2

@[simp]
lemma val_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖) (f : Restricted K d) :
    (mapAlgebra d hiso f).1 = MvPowerSeries.map (algebraMap K L) f.1 := rfl

/-- Base change is a Gauss-norm isometry. -/
lemma norm_mapAlgebra [Fact (∀ i, 0 < d i)] (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (f : Restricted K d) : ‖mapAlgebra d hiso f‖ = ‖f‖ := by
  rw [norm_def, norm_def, val_mapAlgebra]
  exact MvPowerSeries.gaussNorm_map norm d norm (algebraMap K L) hiso f.1

end MapAlgebra

section Split

variable {K L : Type*} [NormedCommRing K] [NormedCommRing L] [IsUltrametricDist K]
  [IsUltrametricDist L] [Algebra K L] {n : ℕ} {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

omit [IsUltrametricDist K] [IsUltrametricDist L] [Algebra K L] in
private lemma finSuccEquiv_map (φ : K →+* L) (F : MvPowerSeries (Fin (n + 1)) K) :
    MvPowerSeries.finSuccEquiv L n (MvPowerSeries.map φ F) =
      PowerSeries.map (MvPowerSeries.map φ) (MvPowerSeries.finSuccEquiv K n F) := by
  refine PowerSeries.ext fun j ↦ MvPowerSeries.ext fun i ↦ ?_
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, MvPowerSeries.coeff_map, PowerSeries.coeff_map,
    MvPowerSeries.coeff_map, MvPowerSeries.coeff_coeff_finSuccEquiv]

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
    _ = PowerSeries.coeff j (PowerSeries.map (MvPowerSeries.map (algebraMap K L))
          (MvPowerSeries.finSuccEquiv K n f.1)) := by
        rw [show (mapAlgebra c hiso f).1 = MvPowerSeries.map (algebraMap K L) f.1 from rfl,
          finSuccEquiv_map (algebraMap K L) f.1]
    _ = MvPowerSeries.map (algebraMap K L)
          (PowerSeries.coeff j (MvPowerSeries.finSuccEquiv K n f.1)) := by
        rw [PowerSeries.coeff_map]
    _ = (mapAlgebra (Fin.tail c) hiso (PowerSeries.coeff j (finSuccEquiv K c f).1)).1 :=
        congrArg (MvPowerSeries.map (algebraMap K L)) (coeff_finSuccEquiv c f j).symm

/-- Base change commutes with the `X 0`-polynomial embedding. -/
lemma mapAlgebra_toMvRestrictedX0 (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    (ω : Polynomial (Restricted K (Fin.tail c))) :
    mapAlgebra c hiso (Polynomial.toMvRestrictedX0 c ω) =
      Polynomial.toMvRestrictedX0 c (ω.map (mapAlgebra (Fin.tail c) hiso)) := by
  refine Subtype.ext (MvPowerSeries.ext fun t ↦ ?_)
  rw [val_mapAlgebra, MvPowerSeries.coeff_map, Polynomial.coeff_toMvRestrictedX0,
    Polynomial.coeff_toMvRestrictedX0, Polynomial.coeff_map, val_mapAlgebra,
    MvPowerSeries.coeff_map]

/-- Distinguishedness in `X 0` is preserved by base change along an isometric embedding. -/
lemma isDistinguishedX0_mapAlgebra (hiso : ∀ a : K, ‖algebraMap K L a‖ = ‖a‖)
    {f : Restricted K c} {s : ℕ} (hf : IsDistinguishedX0 f s) :
    IsDistinguishedX0 (mapAlgebra c hiso f) s := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_finSuccEquiv_mapAlgebra hiso f s]
    exact (mapAlgebra (Fin.tail c) hiso).isUnit_map h1
  · rw [coeff_finSuccEquiv_mapAlgebra hiso f s,
      show (norm (mapAlgebra (Fin.tail c) hiso (PowerSeries.coeff s (finSuccEquiv K c f).1))
          : ℝ) = ‖PowerSeries.coeff s (finSuccEquiv K c f).1‖ from
        norm_mapAlgebra (Fin.tail c) hiso _,
      show PowerSeries.gaussNorm norm (c 0) (finSuccEquiv L c (mapAlgebra c hiso f)).1
          = ‖finSuccEquiv L c (mapAlgebra c hiso f)‖ from
        (PowerSeries.Restricted.norm_def (c 0) _).symm,
      norm_finSuccEquiv c, norm_mapAlgebra c hiso, ← norm_finSuccEquiv (R := K) c f,
      show ‖finSuccEquiv K c f‖
          = PowerSeries.gaussNorm norm (c 0) (finSuccEquiv K c f).1 from
        PowerSeries.Restricted.norm_def (c 0) _]
    exact h2
  · intro t ht
    have h4 := h3 t ht
    rw [coeff_finSuccEquiv_mapAlgebra hiso f t, coeff_finSuccEquiv_mapAlgebra hiso f s,
      show (norm (mapAlgebra (Fin.tail c) hiso (PowerSeries.coeff t (finSuccEquiv K c f).1))
          : ℝ) = ‖PowerSeries.coeff t (finSuccEquiv K c f).1‖ from
        norm_mapAlgebra (Fin.tail c) hiso _,
      show (norm (mapAlgebra (Fin.tail c) hiso (PowerSeries.coeff s (finSuccEquiv K c f).1))
          : ℝ) = ‖PowerSeries.coeff s (finSuccEquiv K c f).1‖ from
        norm_mapAlgebra (Fin.tail c) hiso _]
    exact h4

end Split

section RetractionCore

variable {K : Type*} [NontriviallyNormedField K] {L : Type*} [NontriviallyNormedField L]
  [Algebra K L] {n : ℕ}

private lemma isRestricted_retract {σ' : Type*} {d : σ' → ℝ} (hd : ∀ i, 0 ≤ d i)
    (π : L →ₗ[K] K) {Cπ : ℝ} (hCπ : ∀ x : L, ‖π x‖ ≤ Cπ * ‖x‖) {F : MvPowerSeries σ' L}
    (hF : IsRestricted d F) :
    IsRestricted d (fun t ↦ π (MvPowerSeries.coeff t F)) := by
  have h0 : Filter.Tendsto (fun t : σ' →₀ ℕ ↦ Cπ * (‖MvPowerSeries.coeff t F‖
      * t.prod (d · ^ ·))) Filter.cofinite (nhds 0) := by
    simpa using hF.const_mul Cπ
  have hprodnn : ∀ t : σ' →₀ ℕ, (0 : ℝ) ≤ t.prod (d · ^ ·) := fun t ↦
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hd i) _
  refine squeeze_zero (fun t ↦ mul_nonneg (norm_nonneg _) (hprodnn t)) (fun t ↦ ?_) h0
  rw [MvPowerSeries.coeff_apply]
  calc ‖π (MvPowerSeries.coeff t F)‖ * t.prod (d · ^ ·)
      ≤ Cπ * ‖MvPowerSeries.coeff t F‖ * t.prod (d · ^ ·) :=
        mul_le_mul_of_nonneg_right (hCπ _) (hprodnn t)
    _ = Cπ * (‖MvPowerSeries.coeff t F‖ * t.prod (d · ^ ·)) := mul_assoc _ _ _

private lemma lmap_mul (π : L →ₗ[K] K) (g : MvPowerSeries (Fin (n + 1)) K)
    (h : MvPowerSeries (Fin (n + 1)) L) (Q : MvPowerSeries (Fin (n + 1)) K)
    (hQ : ∀ u, MvPowerSeries.coeff u Q = π (MvPowerSeries.coeff u h))
    (t : Fin (n + 1) →₀ ℕ) :
    π (MvPowerSeries.coeff t (MvPowerSeries.map (algebraMap K L) g * h))
      = MvPowerSeries.coeff t (g * Q) := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [MvPowerSeries.coeff_map, hQ p.2, ← Algebra.smul_def, map_smul, smul_eq_mul]

end RetractionCore

section Descent

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K L]
  {n : ℕ} {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

omit [CompleteSpace K] in
set_option maxHeartbeats 1000000 in
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
  have hres : ∀ A : Restricted L (Fin.tail c),
      IsRestricted (Fin.tail c) (fun t ↦ π (MvPowerSeries.coeff t A.1)) := fun A ↦
    isRestricted_retract (d := Fin.tail c) (fun i ↦ (hc0 i.succ).le) π hCπ A.2
  have hq0res : IsRestricted c (fun t ↦ π (MvPowerSeries.coeff t q.1)) :=
    isRestricted_retract (d := c) (fun i ↦ (hc0 i).le) π hCπ q.2
  have hπT0 : (⟨fun t ↦ π (MvPowerSeries.coeff t (0 : Restricted L (Fin.tail c)).1), hres 0⟩
      : Restricted K (Fin.tail c)) = 0 := by
    refine Subtype.ext (MvPowerSeries.ext fun t ↦ ?_)
    show π (MvPowerSeries.coeff t (0 : Restricted L (Fin.tail c)).1)
        = MvPowerSeries.coeff t (0 : Restricted K (Fin.tail c)).1
    rw [show (0 : Restricted L (Fin.tail c)).1 = 0 from rfl,
      show (0 : Restricted K (Fin.tail c)).1 = 0 from rfl, map_zero, map_zero, map_zero]
  have hr₀coeff : ∀ m, (∑ m ∈ r.support, Polynomial.monomial m
      (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
        : Restricted K (Fin.tail c))).coeff m
      = (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
        : Restricted K (Fin.tail c)) := by
    intro m
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' r.support m]
    split_ifs with hk
    · rfl
    · rw [show r.coeff m = 0 from by simpa [Polynomial.mem_support_iff] using hk, hπT0]
  have hr₀deg : (∑ m ∈ r.support, Polynomial.monomial m
      (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
        : Restricted K (Fin.tail c))).degree < s := by
    rw [Polynomial.degree_lt_iff_coeff_zero] at hr ⊢
    intro m hm
    rw [hr₀coeff m]
    rw [show r.coeff m = 0 from hr m hm, hπT0]
  have hf1 : MvPowerSeries.map (algebraMap K L) f.1
      = MvPowerSeries.map (algebraMap K L) g.1 * q.1
        + (Polynomial.toMvRestrictedX0 c r).1 := by
    have h := congrArg Subtype.val hf
    rwa [show (mapAlgebra c hiso g * q + Polynomial.toMvRestrictedX0 c r).1
        = (mapAlgebra c hiso g).1 * q.1 + (Polynomial.toMvRestrictedX0 c r).1 from rfl,
      val_mapAlgebra, val_mapAlgebra] at h
  have hrterm : ∀ t, π (MvPowerSeries.coeff t (Polynomial.toMvRestrictedX0 c r).1)
      = MvPowerSeries.coeff t (Polynomial.toMvRestrictedX0 c
          (∑ m ∈ r.support, Polynomial.monomial m
            (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
              : Restricted K (Fin.tail c)))).1 := by
    intro t
    rw [Polynomial.coeff_toMvRestrictedX0, Polynomial.coeff_toMvRestrictedX0]
    exact (congrArg (fun z : Restricted K (Fin.tail c) ↦
      MvPowerSeries.coeff (Finsupp.tail t) z.1) (hr₀coeff (t 0))).symm
  have hK : f = g * ⟨fun t ↦ π (MvPowerSeries.coeff t q.1), hq0res⟩
      + Polynomial.toMvRestrictedX0 c (∑ m ∈ r.support, Polynomial.monomial m
          (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
            : Restricted K (Fin.tail c))) := by
    refine Subtype.ext (MvPowerSeries.ext fun t ↦ ?_)
    calc MvPowerSeries.coeff t f.1
        = π (MvPowerSeries.coeff t (MvPowerSeries.map (algebraMap K L) f.1)) := by
          rw [MvPowerSeries.coeff_map, hπ]
      _ = π (MvPowerSeries.coeff t (MvPowerSeries.map (algebraMap K L) g.1 * q.1))
          + π (MvPowerSeries.coeff t (Polynomial.toMvRestrictedX0 c r).1) := by
          rw [hf1, map_add, map_add]
      _ = MvPowerSeries.coeff t (g.1 * (⟨fun t ↦ π (MvPowerSeries.coeff t q.1), hq0res⟩
            : Restricted K c).1)
          + MvPowerSeries.coeff t (Polynomial.toMvRestrictedX0 c
              (∑ m ∈ r.support, Polynomial.monomial m
                (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
                  : Restricted K (Fin.tail c)))).1 := by
          rw [lmap_mul π g.1 q.1 (⟨fun t ↦ π (MvPowerSeries.coeff t q.1), hq0res⟩
            : Restricted K c).1 (fun u ↦ rfl) t, hrterm t]
      _ = _ := by
          rw [show (g * ⟨fun t ↦ π (MvPowerSeries.coeff t q.1), hq0res⟩
              + Polynomial.toMvRestrictedX0 c (∑ m ∈ r.support, Polynomial.monomial m
                (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
                  : Restricted K (Fin.tail c)))).1
              = g.1 * (⟨fun t ↦ π (MvPowerSeries.coeff t q.1), hq0res⟩
                  : Restricted K c).1
                + (Polynomial.toMvRestrictedX0 c (∑ m ∈ r.support, Polynomial.monomial m
                    (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
                      : Restricted K (Fin.tail c)))).1 from rfl, map_add]
  have hzero : (0 : Restricted L c) = mapAlgebra c hiso g
      * (q - mapAlgebra c hiso ⟨fun t ↦ π (MvPowerSeries.coeff t q.1), hq0res⟩)
      + Polynomial.toMvRestrictedX0 c
        ((r - (∑ m ∈ r.support, Polynomial.monomial m
          (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
            : Restricted K (Fin.tail c))).map (mapAlgebra (Fin.tail c) hiso))) := by
    have h10 := congrArg (mapAlgebra c hiso) (sub_eq_zero_of_eq hK)
    have hmm := RingHom.map_mul (mapAlgebra c hiso) g
      (⟨fun t ↦ π (MvPowerSeries.coeff t q.1), hq0res⟩ : Restricted K c)
    rw [map_sub, map_zero, map_add, mapAlgebra_toMvRestrictedX0, hmm, hf] at h10
    rw [mul_sub, map_sub, sub_add_sub_comm]
    exact h10.symm
  have hdegρ : ((r - (∑ m ∈ r.support, Polynomial.monomial m
      (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
        : Restricted K (Fin.tail c))).map (mapAlgebra (Fin.tail c) hiso))).degree < s :=
    (Polynomial.degree_sub_le _ _).trans_lt
      (max_lt hr (Polynomial.degree_map_le.trans_lt hr₀deg))
  have hgd' : IsDistinguishedX0 (mapAlgebra c hiso g) s :=
    isDistinguishedX0_mapAlgebra hiso hg
  refine ⟨⟨fun t ↦ π (MvPowerSeries.coeff t q.1), hq0res⟩,
    ∑ m ∈ r.support, Polynomial.monomial m
      (⟨fun t ↦ π (MvPowerSeries.coeff t (r.coeff m).1), hres (r.coeff m)⟩
        : Restricted K (Fin.tail c)), hr₀deg, hK, ?_, ?_⟩
  · have hb := norm_q_le_of_eq_mul_add hgd' hdegρ hzero
    rw [norm_zero, mul_zero, norm_le_zero_iff] at hb
    exact (sub_eq_zero.mp hb).symm
  · have hb := norm_r_le_of_eq_mul_add hgd' hdegρ hzero
    rw [norm_zero, norm_le_zero_iff] at hb
    have h5 := Polynomial.toMvRestrictedX0_injective (hb.trans (map_zero _).symm)
    exact (sub_eq_zero.mp h5).symm

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
  letI : NormedSpace K L := ⟨fun a x ↦ le_of_eq (by rw [Algebra.smul_def, norm_mul, hiso])⟩
  obtain ⟨π, hπcomp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  obtain ⟨Cπ, -, hCπ⟩ := SemilinearMapClass.bound_of_continuous π
    π.continuous_of_finiteDimensional
  exact weierstrassDivision_descend_of_retraction hiso π
    (fun a ↦ LinearMap.congr_fun hπcomp a) hCπ hg f hr hf

end Descent

end MvPowerSeries.Restricted
