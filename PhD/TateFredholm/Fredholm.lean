import PhD.TateFredholm.Matrix

/-!
# The Fredholm determinant
([Bel] §II.1.5 architecture under [JN]'s hypotheses; blueprint 6.16–6.17.  See
`Tate.lean` for the development's overview and dictionary.)

Definitions are norm-free given the topology; the theorems carry `[IsTate R]` (through
the compactness criterion) and **no Noetherian hypothesis** — each statement below
strictly generalises its [JN]-file counterpart. -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Fredholm

variable {R}
variable {I : Type*} [DecidableEq I]

/-- The principal `S × S` minor of the matrix of `u`. -/
def minor (u : c(I, R) →L[R] c(I, R)) (S : Finset I) : R :=
  Matrix.det (Matrix.of fun j i : S => matrixCoeff u j i)

/-- Summability of the degree-`n` minors (ultrametric Hadamard bound + row decay). -/
theorem summable_minor [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) (n : ℕ) :
    Summable fun S : {S : Finset I // S.card = n} => minor u (S : Finset I) := by
  sorry

/-- The `n`-th coefficient `cₙ = (−1)ⁿ ∑_{|S| = n} det(minor)` of `det(1 − Tu)`. -/
def charCoeff (u : c(I, R) →L[R] c(I, R)) (n : ℕ) : R :=
  (-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)

/-- The *Fredholm determinant* (characteristic power series) `det(1 − Tu) ∈ R⟦T⟧`. -/
def charPowerSeries (u : c(I, R) →L[R] c(I, R)) : PowerSeries R :=
  PowerSeries.mk (charCoeff u)

@[simp] theorem charPowerSeries_coeff (u : c(I, R) →L[R] c(I, R)) (n : ℕ) :
    PowerSeries.coeff n (charPowerSeries u) = charCoeff u n :=
  PowerSeries.coeff_mk n _

/-- `c₀ = 1`: the determinant is a Fredholm series. -/
@[simp] theorem charCoeff_zero (u : c(I, R) →L[R] c(I, R)) : charCoeff u 0 = 1 := by
  sorry

/-- Entire power series (`R{{T}}`): `‖aₙ‖Cⁿ → 0` for every `C > 0`. -/
def IsEntire (F : PowerSeries R) : Prop :=
  ∀ C : ℝ, 0 < C → Tendsto (fun n => ‖PowerSeries.coeff n F‖ * C ^ n) atTop (𝓝 0)

/-- The Fredholm determinant is entire ([Bel] Lemma II.1.14). -/
theorem charPowerSeries_isEntire [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) : IsEntire (charPowerSeries u) := by
  sorry

/-- **Quantitative continuity** ([Bel] Lemma II.1.15):
`‖cₙ(u) − cₙ(v)‖ ≤ max(‖u‖,‖v‖)^{n−1}‖u − v‖` — the estimate powering every limit
argument in this section. -/
theorem norm_charCoeff_sub_le [IsTate R] (u v : c(I, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) (hv : IsCompletelyContinuous v)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖charCoeff u n - charCoeff v n‖ ≤ max ‖u‖ ‖v‖ ^ (n - 1) * ‖u - v‖ := by
  sorry

/-- Compatibility with the algebraic determinant for row-supported operators
([Bel] (II.1.2); no compactness needed). -/
theorem charCoeff_eq_det_coeff (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (n : ℕ) :
    charCoeff u n =
      (Matrix.det (1 - (Polynomial.X : Polynomial R) •
        Matrix.of fun j i : S => Polynomial.C (matrixCoeff u j i))).coeff n := by
  sorry

/-- **The trace property** ([Bel] Proposition II.1.17), the primitive invariance
statement: `det(1 − T·(u∘v)) = det(1 − T·(v∘u))` for `u` compact, `v` continuous.

*Proof sketch.*  Bellaïche's, verbatim over a Tate ring: truncate `u` and `v`
(`tendsto_truncation_comp`), pass to the limit by `norm_charCoeff_sub_le`, and conclude
by `charCoeff_eq_det_coeff` + `det(1 − AB) = det(1 − BA)` for finite matrices. -/
theorem charPowerSeries_comm [IsTate R] {J : Type*} [DecidableEq J]
    (u : c(I, R) →L[R] c(J, R)) (v : c(J, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) :
    charPowerSeries (u.comp v) = charPowerSeries (v.comp u) := by
  sorry

/-- Basis-, norm- and conjugation-invariance ([Bel] Corollary II.1.18; [Buz07,
Lemma 2.5/Corollary 2.6]) — a formal consequence of the trace property.  This is what
extends `det(1 − Tu)` to compact endomorphisms of potentially ON-able modules. -/
theorem charPowerSeries_conj [IsTate R] {J : Type*} [DecidableEq J]
    (φ : c(I, R) ≃L[R] c(J, R)) (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) :
    charPowerSeries (((φ : c(I, R) →L[R] c(J, R)).comp u).comp
        (φ.symm : c(J, R) →L[R] c(I, R)))
      = charPowerSeries u := by
  sorry

/-- Extension by zero ([Buz07, pp. 72–73]; [Bel] §II.1.6) — with `charPowerSeries_conj`,
the well-definedness of the determinant on modules with property (Pr). -/
theorem charPowerSeries_extendZero [IsTate R] {J : Type*} [DecidableEq J]
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I ⊕ J, R) →L[R] c(I ⊕ J, R))
    (hII : ∀ j i, matrixCoeff v (Sum.inl j) (Sum.inl i) = matrixCoeff u j i)
    (hJrow : ∀ j q, matrixCoeff v (Sum.inr j) q = 0)
    (hJcol : ∀ p j, matrixCoeff v p (Sum.inr j) = 0) :
    charPowerSeries v = charPowerSeries u := by
  sorry

end Fredholm

end TateFredholm

end
