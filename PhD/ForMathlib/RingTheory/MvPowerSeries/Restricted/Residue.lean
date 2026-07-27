/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.Analysis.Normed.Ring.PowerBounded
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.TopologicallyNilpotentIso

/-! # Residue maps of the power-bounded subring of the multivariate Tate algebra

Let `R` be a normed commutative ring with ultrametric distance, multiplicative norm, `‖1‖ = 1`
and non-isolated origin, and write `R°` for its power-bounded subring and `T°` for the
power-bounded subring of the multivariate Tate algebra `Restricted R 1`.  For an ideal
`I ⊆ R°` that is open (equivalently, contains a ball around `0`), the coefficients of an element
of `T°` eventually lie in `I`, so reduction of coefficients modulo `I` produces a *polynomial*
over `R° ⧸ I`.

* `MvPowerSeries.Restricted.powerBoundedCoeff`: the coefficients of an element of `T°`, as
  elements of `R°`.  By `powerBoundedCoeff_eq` these are the coefficients of the image under the
  isomorphism `MvPowerSeries.Restricted.powerBoundedEquiv : ↥T° ≃+* Restricted R° 1`.

* `MvPowerSeries.Restricted.residueRingHom I hI : ↥T° →+* MvPolynomial σ (↥R° ⧸ I)`: the
  reduction ring homomorphism for an open ideal `I`.

* `MvPowerSeries.Restricted.toPowerBounded : MvPolynomial σ ↥R° →+* ↥T°`: polynomials over `R°`
  are power-bounded restricted power series, obtained by composing `MvPolynomial.toRestricted`
  with the isomorphism `powerBoundedEquiv⁻¹`.  `residueRingHom_toPowerBounded` identifies their
  residues with coefficientwise reduction.

* `MvPowerSeries.Restricted.residueRingHom_eq_zero_iff`: the kernel of `residueRingHom I hI`
  consists of the series with all coefficients in `I`.  For the ball ideals this becomes a norm
  bound: `residueRingHom_closedBall_ideal_eq_zero_iff` (`‖f‖ ≤ ε`) and
  `residueRingHom_ball_ideal_eq_zero_iff` (`‖f‖ < ε`).

* `MvPowerSeries.Restricted.residueEquiv I hI`: the residue map is surjective
  (`residueRingHom_surjective`) with kernel `(coeffIdeal 1 I).comap powerBoundedEquiv`
  (`ker_residueRingHom`), so by the first isomorphism theorem the quotient of `T°` by this
  kernel is the polynomial ring over `R° ⧸ I`.  For the ball ideals the kernel is the
  corresponding ball ideal of `T°` (`closedBallResidueEquiv`, `ballResidueEquiv`), and for the
  topological nilradical — the open unit ball — it is the topological nilradical of `T°`:
  `topologicalNilradicalResidueEquiv : ↥T° ⧸ T°° ≃+* MvPolynomial σ (↥R° ⧸ R°°)`.

The radius is fixed at `1`: the construction of the residue needs all radii at least `1` (so
that coefficients are power-bounded), while `toPowerBounded` needs all radii at most `1` (so
that monomials are power-bounded).
-/

open Filter PowerBounded
open scoped Topology

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  [NeBot (𝓝[≠] (0 : R))] {σ : Type*}

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (MvPowerSeries.Restricted R (1 : σ → ℝ)) (S := ℤ)

/-- The `t`-th coefficient of a power-bounded restricted power series, as an element of the
power-bounded subring `R°`. -/
noncomputable def powerBoundedCoeff (f : ↥T°) (t : σ →₀ ℕ) : ↥R° :=
  ⟨coeff t f.1.1, isPowerBounded_coeff 1 (fun _ ↦ le_rfl) f.2 t⟩

@[simp]
lemma powerBoundedCoeff_coe (f : ↥T°) (t : σ →₀ ℕ) :
    (powerBoundedCoeff f t : R) = coeff t f.1.1 := rfl

/-- The coefficients of `f ∈ T°` are exactly the coefficients of its image under the isomorphism
`powerBoundedEquiv : ↥T° ≃+* Restricted R° 1`. -/
lemma powerBoundedCoeff_eq (f : ↥T°) (t : σ →₀ ℕ) :
    powerBoundedCoeff f t = coeff t (powerBoundedEquiv f).1 :=
  Subtype.ext (coe_coeff_powerBoundedEquiv f t).symm

lemma powerBoundedCoeff_add (f g : ↥T°) (t : σ →₀ ℕ) :
    powerBoundedCoeff (f + g) t = powerBoundedCoeff f t + powerBoundedCoeff g t :=
  Subtype.ext rfl

@[simp]
lemma powerBoundedCoeff_zero (t : σ →₀ ℕ) : powerBoundedCoeff (0 : ↥T°) t = 0 := rfl

@[simp]
lemma powerBoundedCoeff_one_zero : powerBoundedCoeff (1 : ↥T°) 0 = 1 :=
  Subtype.ext (by simp)

variable [DecidableEq σ]

lemma powerBoundedCoeff_mul (f g : ↥T°) (t : σ →₀ ℕ) :
    powerBoundedCoeff (f * g) t
      = ∑ p ∈ Finset.antidiagonal t, powerBoundedCoeff f p.1 * powerBoundedCoeff g p.2 := by
  apply Subtype.ext
  push_cast
  simp [MvPowerSeries.coeff_mul]

@[simp]
lemma powerBoundedCoeff_one_of_ne_zero {t : σ →₀ ℕ} (ht : t ≠ 0) :
    powerBoundedCoeff (1 : ↥T°) t = 0 :=
  Subtype.ext (by simp [MvPowerSeries.coeff_one, ht])

section Residue

omit [DecidableEq σ] in
/-- For an open ideal `I ⊆ R°`, the coefficients of `f ∈ T°` eventually lie in `I`, so the
reduced coefficients have finite support. -/
private lemma support_mk_powerBoundedCoeff_finite (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°))
    (f : ↥T°) :
    (Function.support fun t ↦ Ideal.Quotient.mk I (powerBoundedCoeff f t)).Finite := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hI 0 I.zero_mem
  have hfin := Filter.eventually_cofinite.mp (Filter.Tendsto.eventually_lt_const hδ f.1.2)
  refine hfin.subset fun t ht ↦ ?_
  rw [Function.mem_support] at ht
  rw [Set.mem_ofPred_eq]
  intro hlt
  refine ht (Ideal.Quotient.eq_zero_iff_mem.mpr (hball ?_))
  rw [Metric.mem_ball, dist_zero_right, AddSubgroupClass.coe_norm, powerBoundedCoeff_coe]
  simpa only [Finsupp.prod, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one] using hlt

/-- The residue of `f ∈ T°` modulo an open ideal `I ⊆ R°`, as a polynomial over `R° ⧸ I`. -/
private noncomputable def residuePolynomial (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°))
    (f : ↥T°) : MvPolynomial σ (↥R° ⧸ I) :=
  ⟨Finsupp.ofSupportFinite _ (support_mk_powerBoundedCoeff_finite I hI f)⟩

omit [DecidableEq σ] in
private lemma coeff_residuePolynomial (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) (f : ↥T°)
    (t : σ →₀ ℕ) :
    (residuePolynomial I hI f).coeff t = Ideal.Quotient.mk I (powerBoundedCoeff f t) := rfl

/-- Reduction of coefficients modulo an open ideal `I ⊆ R°`, as a ring homomorphism from `T°`
to polynomials over the quotient. -/
noncomputable def residueRingHom (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) :
    ↥T° →+* MvPolynomial σ (↥R° ⧸ I) where
  toFun := residuePolynomial I hI
  map_zero' := by
    apply MvPolynomial.ext
    simp [coeff_residuePolynomial]
  map_one' := by
    apply MvPolynomial.ext
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · simp [coeff_residuePolynomial]
    · rw [coeff_residuePolynomial, powerBoundedCoeff_one_of_ne_zero ht, map_zero,
        MvPolynomial.coeff_one, if_neg (Ne.symm ht)]
  map_add' f g := by
    apply MvPolynomial.ext
    simp [coeff_residuePolynomial, powerBoundedCoeff_add]
  map_mul' f g := by
    apply MvPolynomial.ext
    intro t
    rw [coeff_residuePolynomial, MvPolynomial.coeff_mul, powerBoundedCoeff_mul, map_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by rw [map_mul, coeff_residuePolynomial,
      coeff_residuePolynomial]

@[simp]
lemma coeff_residueRingHom (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) (f : ↥T°) (t : σ →₀ ℕ) :
    (residueRingHom I hI f).coeff t = Ideal.Quotient.mk I (powerBoundedCoeff f t) := rfl

/-- The kernel of the residue map consists of the series with all coefficients in `I`. -/
lemma residueRingHom_eq_zero_iff (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) (f : ↥T°) :
    residueRingHom I hI f = 0 ↔ ∀ t, powerBoundedCoeff f t ∈ I := by
  simp [MvPolynomial.ext_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The residue of `f` modulo the closed ball ideal of radius `ε` vanishes if and only if
`‖f‖ ≤ ε`. -/
lemma residueRingHom_closedBall_ideal_eq_zero_iff {ε : ℝ} (hε : 0 < ε) (f : ↥T°) :
    residueRingHom (closedBall_ideal hε.le) (isOpen_closedBall_ideal hε) f = 0 ↔ ‖f.1‖ ≤ ε := by
  rw [residueRingHom_eq_zero_iff, norm_le_iff]
  simp [Finsupp.prod]

/-- The residue of `f` modulo the open ball ideal of radius `ε` vanishes if and only if
`‖f‖ < ε`. -/
lemma residueRingHom_ball_ideal_eq_zero_iff {ε : ℝ} (hε : 0 < ε) (f : ↥T°) :
    residueRingHom (ball_ideal hε) (isOpen_ball_ideal hε) f = 0 ↔ ‖f.1‖ < ε := by
  rw [residueRingHom_eq_zero_iff, norm_lt_iff]
  simp [Finsupp.prod]

end Residue

/-- A polynomial over `R°` is a power-bounded restricted power series: the ring homomorphism
`R°[Xᵢ] →+* T°` obtained by composing `MvPolynomial.toRestricted` with the isomorphism
`powerBoundedEquiv⁻¹`. -/
noncomputable def toPowerBounded : MvPolynomial σ ↥R° →+* ↥T° :=
  ofRestrictedRes.comp (MvPolynomial.toRestricted (1 : σ → ℝ))

omit [DecidableEq σ] in
@[simp]
lemma coe_toPowerBounded (p : MvPolynomial σ ↥R°) :
    (toPowerBounded p : Restricted R 1)
      = MvPolynomial.toRestricted 1
          (MvPolynomial.map (PowerBounded.subring R (S := ℤ)).subtype p) := by
  refine Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)
  show (PowerBounded.subring R (S := ℤ)).subtype (coeff t (MvPolynomial.toRestricted 1 p).1)
    = coeff t (MvPolynomial.toRestricted 1 (MvPolynomial.map R°.subtype p)).1
  simp [MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

/-- The residue of a polynomial over `R°` is its coefficientwise reduction. -/
lemma residueRingHom_toPowerBounded {I : Ideal ↥R°} (hI : IsOpen (I : Set ↥R°))
    (p : MvPolynomial σ ↥R°) :
    residueRingHom I hI (toPowerBounded p) = MvPolynomial.map (Ideal.Quotient.mk I) p := by
  apply MvPolynomial.ext
  intro t
  rw [coeff_residueRingHom, MvPolynomial.coeff_map]
  congr 1

section ResidueEquiv

/-- The residue map is surjective: every polynomial over `R° ⧸ I` lifts coefficientwise to a
polynomial over `R°`, which is a power-bounded restricted power series. -/
theorem residueRingHom_surjective (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) :
    Function.Surjective (residueRingHom (σ := σ) I hI) := fun q ↦ by
  obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective q
  exact ⟨toPowerBounded p, residueRingHom_toPowerBounded hI p⟩

/-- The kernel of the residue map is the pullback along
`powerBoundedEquiv : ↥T° ≃+* Restricted R° 1` of the ideal of series with coefficients in
`I`. -/
theorem ker_residueRingHom (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) :
    RingHom.ker (residueRingHom (σ := σ) I hI) =
      (coeffIdeal 1 I).comap (powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° (1 : σ → ℝ)) := by
  ext f
  rw [RingHom.mem_ker, residueRingHom_eq_zero_iff, Ideal.mem_comap, mem_coeffIdeal]
  exact forall_congr' fun t ↦ by rw [powerBoundedCoeff_eq]

/-- The kernel of the residue map modulo the closed ball ideal of radius `ε` is the closed ball
ideal of radius `ε` of `T°`. -/
theorem ker_residueRingHom_closedBall_ideal {ε : ℝ} (hε : 0 < ε) :
    RingHom.ker (residueRingHom (σ := σ) (closedBall_ideal hε.le) (isOpen_closedBall_ideal hε))
      = closedBall_ideal (R := Restricted R (1 : σ → ℝ)) hε.le := by
  ext f
  rw [RingHom.mem_ker, residueRingHom_closedBall_ideal_eq_zero_iff hε]
  exact (mem_closedBall_ideal hε.le).symm

/-- The kernel of the residue map modulo the open ball ideal of radius `ε` is the open ball
ideal of radius `ε` of `T°`. -/
theorem ker_residueRingHom_ball_ideal {ε : ℝ} (hε : 0 < ε) :
    RingHom.ker (residueRingHom (σ := σ) (ball_ideal hε) (isOpen_ball_ideal hε))
      = ball_ideal (R := Restricted R (1 : σ → ℝ)) hε := by
  ext f
  rw [RingHom.mem_ker, residueRingHom_ball_ideal_eq_zero_iff hε]
  exact (mem_ball_ideal hε).symm

/-- The kernel of the residue map modulo the topological nilradical of `R°` is the topological
nilradical of `T°`. -/
theorem ker_residueRingHom_topologicalNilradical :
    RingHom.ker (residueRingHom (R := R) (σ := σ) (PowerBounded.topologicalNilradical ℤ)
        isOpen_topologicalNilradical)
      = PowerBounded.topologicalNilradical ℤ := by
  rw [ker_residueRingHom, comap_powerBoundedEquiv_coeffIdeal]

/-- The first-isomorphism-theorem equivalence induced by the residue map: the quotient of `T°`
by the series with coefficients in an open ideal `I ⊆ R°` is the polynomial ring over
`R° ⧸ I`. -/
noncomputable def residueEquiv (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) :
    (↥T° ⧸ (coeffIdeal 1 I).comap (powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° (1 : σ → ℝ)))
      ≃+* MvPolynomial σ (↥R° ⧸ I) :=
  (Ideal.quotEquivOfEq (ker_residueRingHom I hI).symm).trans
    ((residueRingHom I hI).quotientKerEquivOfSurjective (residueRingHom_surjective I hI))

@[simp]
lemma residueEquiv_mk (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) (f : ↥T°) :
    residueEquiv I hI (Ideal.Quotient.mk _ f) = residueRingHom I hI f := by
  rw [residueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The quotient of `T°` by its closed ball ideal of radius `ε` is the polynomial ring over
the corresponding quotient of `R°`. -/
noncomputable def closedBallResidueEquiv {ε : ℝ} (hε : 0 < ε) :
    (↥T° ⧸ closedBall_ideal (R := Restricted R (1 : σ → ℝ)) hε.le)
      ≃+* MvPolynomial σ (↥R° ⧸ closedBall_ideal hε.le) :=
  (Ideal.quotEquivOfEq (ker_residueRingHom_closedBall_ideal hε).symm).trans
    ((residueRingHom (closedBall_ideal hε.le)
        (isOpen_closedBall_ideal hε)).quotientKerEquivOfSurjective
      (residueRingHom_surjective (closedBall_ideal hε.le) (isOpen_closedBall_ideal hε)))

@[simp]
lemma closedBallResidueEquiv_mk {ε : ℝ} (hε : 0 < ε) (f : ↥T°) :
    closedBallResidueEquiv hε (Ideal.Quotient.mk _ f)
      = residueRingHom (closedBall_ideal hε.le) (isOpen_closedBall_ideal hε) f := by
  rw [closedBallResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The quotient of `T°` by its open ball ideal of radius `ε` is the polynomial ring over the
corresponding quotient of `R°`. -/
noncomputable def ballResidueEquiv {ε : ℝ} (hε : 0 < ε) :
    (↥T° ⧸ ball_ideal (R := Restricted R (1 : σ → ℝ)) hε)
      ≃+* MvPolynomial σ (↥R° ⧸ ball_ideal hε) :=
  (Ideal.quotEquivOfEq (ker_residueRingHom_ball_ideal hε).symm).trans
    ((residueRingHom (ball_ideal hε) (isOpen_ball_ideal hε)).quotientKerEquivOfSurjective
      (residueRingHom_surjective (ball_ideal hε) (isOpen_ball_ideal hε)))

@[simp]
lemma ballResidueEquiv_mk {ε : ℝ} (hε : 0 < ε) (f : ↥T°) :
    ballResidueEquiv hε (Ideal.Quotient.mk _ f)
      = residueRingHom (ball_ideal hε) (isOpen_ball_ideal hε) f := by
  rw [ballResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- **The reduction of the Tate algebra is the polynomial ring over the reduction of the base**:
the quotient of `T°` by its topological nilradical is the polynomial ring over the quotient of
`R°` by its topological nilradical. -/
noncomputable def topologicalNilradicalResidueEquiv :
    (↥T° ⧸ PowerBounded.topologicalNilradical ℤ)
      ≃+* MvPolynomial σ (↥R° ⧸ PowerBounded.topologicalNilradical ℤ) :=
  (Ideal.quotEquivOfEq (ker_residueRingHom_topologicalNilradical (R := R) (σ := σ)).symm).trans
    ((residueRingHom (PowerBounded.topologicalNilradical ℤ)
        isOpen_topologicalNilradical).quotientKerEquivOfSurjective
      (residueRingHom_surjective (PowerBounded.topologicalNilradical ℤ)
        isOpen_topologicalNilradical))

@[simp]
lemma topologicalNilradicalResidueEquiv_mk (f : ↥T°) :
    topologicalNilradicalResidueEquiv (Ideal.Quotient.mk _ f)
      = residueRingHom (PowerBounded.topologicalNilradical ℤ)
          isOpen_topologicalNilradical f := by
  rw [topologicalNilradicalResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

end ResidueEquiv

end MvPowerSeries.Restricted
