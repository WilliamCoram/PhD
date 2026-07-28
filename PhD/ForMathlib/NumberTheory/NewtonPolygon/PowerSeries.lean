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

/-- The Newton polygon (as a `NewtonPolygon` from `Basic.lean`) of a power series `f`, built from
its coefficient-valuation sequence `coeffSeq val f` via the construction in `Construction.lean`.

The construction is one-sided: it begins at the first coefficient of finite valuation
(`findFirstFinite`) and only produces segments to the *right*, indexed `0, 1, 2, …`. We embed that
`ℕ`-indexed data into the bi-infinite `ℤ`-indexed `NewtonPolygon` by filling everything to the left
(`n < 0`) with the junk values — `⊥` for slopes, `0` for lengths — and taking `support = (0, m-1)`
where `m` is the number of segments (`newtonPolygon_seq`'s length). If the series has no finite
coefficient at all, the starting point defaults to the junk value `(0, 0)`.

The `Prop` obligations (`support_consistent`, the six junk conditions, `increasing`) are left as
`sorry` for now, to be discharged from the `Construction.lean` API in a follow-up. -/
noncomputable def newtonPolygonOfPowerSeries (val : R → WithTop Γ) (f : PowerSeries R) :
    NewtonPolygon (Γ := Γ) :=
  let v := coeffSeq val f
  { support :=
      (0, match (newtonPolygon_seq v).length' with
          | ⊤ => ⊤
          | (m : ℕ) => ((m - 1 : ℕ) : WithTop ℕ))
    support_left := Or.inl rfl
    slopes := fun n => if n < 0 then ⊥ else newtonPolygon_slopes v n.toNat
    slopes_junk_top := by sorry
    slopes_junk_bot := by sorry
    slopes_junk_interior := by sorry
    lengths := fun n => if n < 0 then 0 else newtonPolygon_lengths v n.toNat
    lengths_junk_top := by sorry
    lengths_junk_bot := by sorry
    lengths_junk_interior := by sorry
    increasing := by sorry
    starting_point :=
      match findFirstFinite v 0 with
      | some (i, c) => ((i : ℤ), c)
      | none => (0, 0) }
