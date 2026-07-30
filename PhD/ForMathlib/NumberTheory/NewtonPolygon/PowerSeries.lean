import PhD.ForMathlib.NumberTheory.NewtonPolygon.Basic
import PhD.ForMathlib.NumberTheory.NewtonPolygon.Construction
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Newton polygon of a power series

Given a power series `f : PowerSeries R` and a `WithTop Γ`-valued function `val` on the
coefficients (a general "valuation-like" map for now; later it will be specialised to an additive
valuation, which sends `0 ↦ ⊤`), we form the coefficient-valuation sequence `coeffSeq val f` and
feed it to the Newton polygon construction from `Construction.lean`.
-/

variable {Γ : Type*} {R : Type*} [Semiring R]

/-- The coefficient-valuation sequence of a power series `f`: apply the `WithTop Γ`-valued function
`val` to each coefficient. This is the input `v : ℕ → WithTop Γ` that the Newton polygon
construction consumes. Specialising `val` to an additive valuation (so `val 0 = ⊤`) recovers the
usual sequence of coefficient valuations. -/
noncomputable def coeffSeq (val : R → WithTop Γ) (f : PowerSeries R) : ℕ → WithTop Γ :=
  fun i => val (PowerSeries.coeff i f)

@[simp] lemma coeffSeq_apply (val : R → WithTop Γ) (f : PowerSeries R) (i : ℕ) :
    coeffSeq val f i = val (PowerSeries.coeff i f) := rfl

variable [CommSemiring Γ] [Algebra Γ ℝ]

/-- The one-sided Newton polygon (`NewtonPolygon₀`) attached to a coefficient-valuation sequence
`v : ℕ → WithTop Γ` by the algorithm in `Construction.lean`: `newtonPolygon_numSegments v` many
segments carrying the constructed slopes and lengths, anchored at the first coefficient of finite
valuation (with the junk anchor `(0, 0)` if there is none). All structure obligations are
discharged by the `numSegments` API from `Construction.lean`. -/
noncomputable def newtonPolygon₀OfSeq (v : ℕ → WithTop Γ) : NewtonPolygon₀ (Γ := Γ) where
  support := newtonPolygon_numSegments v
  slopes := newtonPolygon_slopes v
  slopes_junk := fun _ h => newtonPolygon_slopes_junk v h
  slopes_nonFinal := fun _ h => newtonPolygon_slopes_nonFinal v h
  slopes_final := fun _ h => newtonPolygon_slopes_final v h.1 h.2
  slopes_increasing := newtonPolygon_slopes_mono v
  lengths := newtonPolygon_lengths v
  lengths_junk := fun _ h => newtonPolygon_lengths_junk v h
  lengths_nonFinal := fun _ h => newtonPolygon_lengths_nonFinal v h
  lengths_final := fun _ h => newtonPolygon_lengths_final v h.1 h.2
  starting_point :=
    match findFirstFinite v 0 with
    | some (i, c) => ((i : ℤ), c)
    | none => (0, 0)

/-- The one-sided Newton polygon of a power series `f`: the polygon of its coefficient-valuation
sequence `coeffSeq val f`. -/
noncomputable def newtonPolygon₀OfPowerSeries (val : R → WithTop Γ) (f : PowerSeries R) :
    NewtonPolygon₀ (Γ := Γ) :=
  newtonPolygon₀OfSeq (coeffSeq val f)

/-- The (doubly-infinite) Newton polygon of a power series: its one-sided polygon embedded via
`NewtonPolygon₀.toNewtonPolygon`. -/
noncomputable def newtonPolygonOfPowerSeries (val : R → WithTop Γ) (f : PowerSeries R) :
    NewtonPolygon (Γ := Γ) :=
  (newtonPolygon₀OfPowerSeries val f).toNewtonPolygon
