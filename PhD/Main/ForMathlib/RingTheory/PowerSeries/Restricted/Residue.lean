/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.Analysis.Normed.Ring.PowerBounded
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.TopologicallyNilpotentIso

/-! # Residue maps of the power-bounded subring of the Tate algebra

Let `R` be a normed commutative ring with ultrametric distance, multiplicative norm, `‖1‖ = 1`
and non-isolated origin, and write `R°` for its power-bounded subring and `T°` for the
power-bounded subring of the Tate algebra `Restricted R 1`.  For an ideal `I ⊆ R°` that is open
(equivalently, contains a ball around `0`), the coefficients of an element of `T°` eventually
lie in `I`, so reduction of coefficients modulo `I` produces a *polynomial* over `R° ⧸ I`.

* `PowerSeries.Restricted.powerBoundedCoeff`: the coefficients of an element of `T°`, as
  elements of `R°`.  By `powerBoundedCoeff_eq` these are the coefficients of the image under
  the isomorphism `PowerSeries.Restricted.powerBoundedEquiv : ↥T° ≃+* Restricted R° 1`.

* `PowerSeries.Restricted.residueRingHom I hI : ↥T° →+* Polynomial (↥R° ⧸ I)`: the reduction
  ring homomorphism for an open ideal `I`.

* `PowerSeries.Restricted.toPowerBounded : Polynomial ↥R° →+* ↥T°`: polynomials over `R°` are
  power-bounded restricted power series, obtained by composing `Polynomial.toRestricted` with
  the isomorphism `powerBoundedEquiv⁻¹`.  `residueRingHom_toPowerBounded` identifies their
  residues with coefficientwise reduction.

* `PowerSeries.Restricted.residueRingHom_eq_zero_iff`: the kernel of `residueRingHom I hI`
  consists of the series with all coefficients in `I`.  For the ball ideals this becomes a norm
  bound: `residueRingHom_closedBall_ideal_eq_zero_iff` (`‖f‖ ≤ ε`) and
  `residueRingHom_ball_ideal_eq_zero_iff` (`‖f‖ < ε`).

* `PowerSeries.Restricted.residueEquiv I hI`: the residue map is surjective
  (`residueRingHom_surjective`) with kernel `(coeffIdeal 1 I).comap powerBoundedEquiv`
  (`ker_residueRingHom`), so by the first isomorphism theorem the quotient of `T°` by this
  kernel is the polynomial ring over `R° ⧸ I`.  For the ball ideals the kernel is the
  corresponding ball ideal of `T°` (`closedBallResidueEquiv`, `ballResidueEquiv`), and for the
  topological nilradical — the open unit ball — it is the topological nilradical of `T°`:
  `topologicalNilradicalResidueEquiv : ↥T° ⧸ T°° ≃+* Polynomial (↥R° ⧸ R°°)`.
-/

open Filter PowerBounded
open scoped Topology

namespace PowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  [NeBot (𝓝[≠] (0 : R))]

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)

/-- The `v`-th coefficient of a power-bounded restricted power series, as an element of the
power-bounded subring `R°`. -/
noncomputable def powerBoundedCoeff (f : ↥T°) (v : ℕ) : ↥R° :=
  ⟨coeff v (f : Restricted R 1).1, isPowerBounded_coeff 1 le_rfl f.2 v⟩

@[simp]
lemma powerBoundedCoeff_coe (f : ↥T°) (v : ℕ) :
    (powerBoundedCoeff f v : R) = coeff v (f : Restricted R 1).1 := rfl

/-- The coefficients of `f ∈ T°` are exactly the coefficients of its image under the isomorphism
`powerBoundedEquiv : ↥T° ≃+* Restricted R° 1`. -/
lemma powerBoundedCoeff_eq (f : ↥T°) (v : ℕ) :
    powerBoundedCoeff f v = coeff v (powerBoundedEquiv f).1 :=
  Subtype.ext (coe_coeff_powerBoundedEquiv f v).symm

lemma powerBoundedCoeff_add (f g : ↥T°) (v : ℕ) :
    powerBoundedCoeff (f + g) v = powerBoundedCoeff f v + powerBoundedCoeff g v :=
  Subtype.ext rfl

lemma powerBoundedCoeff_mul (f g : ↥T°) (v : ℕ) :
    powerBoundedCoeff (f * g) v
      = ∑ p ∈ Finset.antidiagonal v, powerBoundedCoeff f p.1 * powerBoundedCoeff g p.2 := by
  apply Subtype.ext
  push_cast
  simp [PowerSeries.coeff_mul]

@[simp]
lemma powerBoundedCoeff_zero (v : ℕ) : powerBoundedCoeff (0 : ↥T°) v = 0 := rfl

@[simp]
lemma powerBoundedCoeff_one_zero : powerBoundedCoeff (1 : ↥T°) 0 = 1 :=
  Subtype.ext (by simp)

@[simp]
lemma powerBoundedCoeff_one_of_ne_zero {v : ℕ} (hv : v ≠ 0) :
    powerBoundedCoeff (1 : ↥T°) v = 0 :=
  Subtype.ext (by simp [PowerSeries.coeff_one, hv])

section Residue

/-- For an open ideal `I ⊆ R°`, the coefficients of `f ∈ T°` eventually lie in `I`, so the
reduced coefficients have finite support. -/
private lemma support_mk_powerBoundedCoeff_finite (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°))
    (f : ↥T°) :
    (Function.support fun v ↦ Ideal.Quotient.mk I (powerBoundedCoeff f v)).Finite := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hI 0 I.zero_mem
  obtain ⟨N, hN⟩ : ∃ N, ∀ v ≥ N, ‖coeff v (f : Restricted R 1).1‖ < δ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (by simpa using (isRestricted_iff' 1 (f : Restricted R 1).1).mp (f : Restricted R 1).2) δ hδ
    exact ⟨N, fun v hv ↦ by simpa [abs_of_nonneg (norm_nonneg _)] using hN v hv⟩
  refine Set.Finite.subset (Set.finite_Iio N) fun v hv ↦ ?_
  by_contra hvN
  refine hv (Ideal.Quotient.eq_zero_iff_mem.mpr (hball ?_))
  rw [Metric.mem_ball, dist_zero_right]
  exact hN v (Nat.le_of_not_lt hvN)

/-- The residue of `f ∈ T°` modulo an open ideal `I ⊆ R°`, as a polynomial over `R° ⧸ I`. -/
private noncomputable def residuePolynomial (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°))
    (f : ↥T°) : Polynomial (↥R° ⧸ I) :=
  ⟨⟨Finsupp.ofSupportFinite _ (support_mk_powerBoundedCoeff_finite I hI f)⟩⟩

private lemma coeff_residuePolynomial (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) (f : ↥T°)
    (v : ℕ) :
    (residuePolynomial I hI f).coeff v = Ideal.Quotient.mk I (powerBoundedCoeff f v) := rfl

/-- Reduction of coefficients modulo an open ideal `I ⊆ R°`, as a ring homomorphism from `T°`
to polynomials over the quotient. -/
noncomputable def residueRingHom (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) :
    ↥T° →+* Polynomial (↥R° ⧸ I) where
  toFun := residuePolynomial I hI
  map_zero' := by
    apply Polynomial.ext
    simp [coeff_residuePolynomial]
  map_one' := by
    apply Polynomial.ext
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp [coeff_residuePolynomial]
    · simp [coeff_residuePolynomial, hv, Polynomial.coeff_one]
  map_add' f g := by
    apply Polynomial.ext
    simp [coeff_residuePolynomial, powerBoundedCoeff_add]
  map_mul' f g := by
    apply Polynomial.ext
    intro v
    rw [coeff_residuePolynomial, Polynomial.coeff_mul, powerBoundedCoeff_mul, map_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by rw [map_mul, coeff_residuePolynomial,
      coeff_residuePolynomial]

@[simp]
lemma coeff_residueRingHom (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) (f : ↥T°) (v : ℕ) :
    (residueRingHom I hI f).coeff v = Ideal.Quotient.mk I (powerBoundedCoeff f v) := rfl

/-- The kernel of the residue map consists of the series with all coefficients in `I`. -/
lemma residueRingHom_eq_zero_iff (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) (f : ↥T°) :
    residueRingHom I hI f = 0 ↔ ∀ v, powerBoundedCoeff f v ∈ I := by
  simp [Polynomial.ext_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The residue of `f` modulo the closed ball ideal of radius `ε` vanishes if and only if
`‖f‖ ≤ ε`. -/
lemma residueRingHom_closedBall_ideal_eq_zero_iff {ε : ℝ} (hε : 0 < ε) (f : ↥T°) :
    residueRingHom (closedBall_ideal hε.le) (isOpen_closedBall_ideal hε) f = 0
      ↔ ‖(f : Restricted R 1)‖ ≤ ε := by
  rw [residueRingHom_eq_zero_iff, norm_le_iff]
  simp

/-- The residue of `f` modulo the open ball ideal of radius `ε` vanishes if and only if
`‖f‖ < ε`. -/
lemma residueRingHom_ball_ideal_eq_zero_iff {ε : ℝ} (hε : 0 < ε) (f : ↥T°) :
    residueRingHom (ball_ideal hε) (isOpen_ball_ideal hε) f = 0
      ↔ ‖(f : Restricted R 1)‖ < ε := by
  rw [residueRingHom_eq_zero_iff, norm_lt_iff]
  simp

end Residue

/-- A polynomial over `R°` is a power-bounded restricted power series: the ring homomorphism
`R°[X] →+* T°` obtained by composing `Polynomial.toRestricted` with the isomorphism
`powerBoundedEquiv⁻¹`. -/
noncomputable def toPowerBounded : Polynomial ↥R° →+* ↥T° :=
  ofRestrictedRes.comp (Polynomial.toRestricted 1)

@[simp]
lemma coe_toPowerBounded (p : Polynomial ↥R°) :
    (toPowerBounded p : Restricted R 1)
      = Polynomial.toRestricted 1 (p.map (PowerBounded.subring R (S := ℤ)).subtype) := by
  refine Subtype.ext (PowerSeries.ext fun v ↦ ?_)
  show (PowerBounded.subring R (S := ℤ)).subtype (coeff v (Polynomial.toRestricted 1 p).1)
    = coeff v (Polynomial.toRestricted 1 (p.map R°.subtype)).1
  simp [Polynomial.coeff_coe]

/-- The residue of a polynomial over `R°` is its coefficientwise reduction. -/
lemma residueRingHom_toPowerBounded {I : Ideal ↥R°} (hI : IsOpen (I : Set ↥R°))
    (p : Polynomial ↥R°) :
    residueRingHom I hI (toPowerBounded p) = p.map (Ideal.Quotient.mk I) := by
  apply Polynomial.ext
  intro v
  rw [coeff_residueRingHom, Polynomial.coeff_map]
  congr 1
  refine Subtype.ext ?_
  simp [Polynomial.coeff_coe]

section ResidueEquiv

/-- The residue map is surjective: every polynomial over `R° ⧸ I` lifts coefficientwise to a
polynomial over `R°`, which is a power-bounded restricted power series. -/
theorem residueRingHom_surjective (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) :
    Function.Surjective (residueRingHom I hI) := fun q ↦ by
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective q
  exact ⟨toPowerBounded p, residueRingHom_toPowerBounded hI p⟩

/-- The kernel of the residue map is the pullback along
`powerBoundedEquiv : ↥T° ≃+* Restricted R° 1` of the ideal of series with coefficients in
`I`. -/
theorem ker_residueRingHom (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) :
    RingHom.ker (residueRingHom I hI) =
      (coeffIdeal 1 I).comap (powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1) := by
  ext f
  rw [RingHom.mem_ker, residueRingHom_eq_zero_iff, Ideal.mem_comap, mem_coeffIdeal]
  exact forall_congr' fun v ↦ by rw [powerBoundedCoeff_eq]

/-- The kernel of the residue map modulo the closed ball ideal of radius `ε` is the closed ball
ideal of radius `ε` of `T°`. -/
theorem ker_residueRingHom_closedBall_ideal {ε : ℝ} (hε : 0 < ε) :
    RingHom.ker (residueRingHom (closedBall_ideal hε.le) (isOpen_closedBall_ideal hε))
      = closedBall_ideal (R := Restricted R 1) hε.le := by
  ext f
  rw [RingHom.mem_ker, residueRingHom_closedBall_ideal_eq_zero_iff hε]
  exact (mem_closedBall_ideal hε.le).symm

/-- The kernel of the residue map modulo the open ball ideal of radius `ε` is the open ball
ideal of radius `ε` of `T°`. -/
theorem ker_residueRingHom_ball_ideal {ε : ℝ} (hε : 0 < ε) :
    RingHom.ker (residueRingHom (ball_ideal hε) (isOpen_ball_ideal hε))
      = ball_ideal (R := Restricted R 1) hε := by
  ext f
  rw [RingHom.mem_ker, residueRingHom_ball_ideal_eq_zero_iff hε]
  exact (mem_ball_ideal hε).symm

/-- The kernel of the residue map modulo the topological nilradical of `R°` is the topological
nilradical of `T°`. -/
theorem ker_residueRingHom_topologicalNilradical :
    RingHom.ker (residueRingHom (R := R) (PowerBounded.topologicalNilradical ℤ)
        isOpen_topologicalNilradical)
      = PowerBounded.topologicalNilradical ℤ := by
  rw [ker_residueRingHom, comap_powerBoundedEquiv_coeffIdeal]

/-- The first-isomorphism-theorem equivalence induced by the residue map: the quotient of `T°`
by the series with coefficients in an open ideal `I ⊆ R°` is the polynomial ring over
`R° ⧸ I`. -/
noncomputable def residueEquiv (I : Ideal ↥R°) (hI : IsOpen (I : Set ↥R°)) :
    (↥T° ⧸ (coeffIdeal 1 I).comap (powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1))
      ≃+* Polynomial (↥R° ⧸ I) :=
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
    (↥T° ⧸ closedBall_ideal (R := Restricted R 1) hε.le)
      ≃+* Polynomial (↥R° ⧸ closedBall_ideal hε.le) :=
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
    (↥T° ⧸ ball_ideal (R := Restricted R 1) hε)
      ≃+* Polynomial (↥R° ⧸ ball_ideal hε) :=
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
      ≃+* Polynomial (↥R° ⧸ PowerBounded.topologicalNilradical ℤ) :=
  (Ideal.quotEquivOfEq (ker_residueRingHom_topologicalNilradical (R := R)).symm).trans
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

end PowerSeries.Restricted
