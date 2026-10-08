/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Convex.Function
import PhD.TauCeti.Code.NewtonPolygons.Face

/-!
# The supporting value of a polygon

The **supporting value** of a sequence `h : ℕ → WithTop ℝ` at the slope `m` is the `y`-intercept
`supportValue h m = ⨅ k, (h k - m k)` of the supporting line of slope `m`, an extended real: `⊥`
when no line of slope `m` lies below the points, `⊤` when there are no points, and otherwise the
infimum. It is [Ked07]'s *sloped valuation* `v_r` in height form (with `r = -m` in Kedlaya's
orientation), and it is what the Gauss norm of a series at the radius `b ^ m` computes
(`GaussNorm.lean`). The points and their polygon have the same supporting value; on a face the
infimum is attained at the face's endpoints; between two consecutive unit slopes the supporting
value is affine in `m`; it is concave in `m`; and the polygon is recovered from it as the supremum
of its supporting lines (the Legendre biconjugate).

Roadmap: §2.3.1–§2.3.4 (the polygon-level half). Tau Ceti home: Layer 0's
`TauCeti/NumberTheory/NewtonPolygon/Face.lean`.

## Main definitions

* `NewtonPolygon.toEReal : WithTop ℝ → EReal`, `NewtonPolygon.supportValue h m : EReal`.

## Main results

* `NewtonPolygon.supportValue_newtonPolygon` — the points and the polygon agree;
* `NewtonPolygon.IsConvexSeq.supportValue_eq_faceRight` — attained at the face;
* `NewtonPolygon.IsConvexSeq.supportValue_eq_of_unitSlope_le_le` — piecewise affine;
* `NewtonPolygon.concaveOn_toReal_supportValue` — concave;
* `NewtonPolygon.iSup_supportValue_add` — the biconjugate recovers the polygon.
-/

namespace NewtonPolygon

variable {v h : ℕ → WithTop ℝ}

/-! ### `WithTop ℝ` inside `EReal` -/

/-- The inclusion of `WithTop ℝ` into `EReal = WithBot (WithTop ℝ)`. -/
def toEReal (x : WithTop ℝ) : EReal := WithBot.some x

@[simp] lemma toEReal_coe (r : ℝ) : toEReal (r : WithTop ℝ) = (r : EReal) := rfl

@[simp] lemma toEReal_top : toEReal ⊤ = ⊤ := rfl

lemma toEReal_ne_bot (x : WithTop ℝ) : toEReal x ≠ ⊥ := by sorry

lemma toEReal_le_toEReal {x y : WithTop ℝ} : toEReal x ≤ toEReal y ↔ x ≤ y := by sorry

lemma toEReal_lt_toEReal {x y : WithTop ℝ} : toEReal x < toEReal y ↔ x < y := by sorry

lemma toEReal_injective : Function.Injective toEReal := by sorry

lemma toEReal_eq_top_iff {x : WithTop ℝ} : toEReal x = ⊤ ↔ x = ⊤ := by sorry

lemma toEReal_of_ne_top {x : WithTop ℝ} (hx : x ≠ ⊤) : toEReal x = ((x.untop₀ : ℝ) : EReal) := by
  sorry

/-! ### The supporting value -/

/-- **The supporting value** of `h` at the slope `m`: the `y`-intercept `⨅ k, (h k - m k)` of the
supporting line of slope `m`, as an extended real. -/
noncomputable def supportValue (h : ℕ → WithTop ℝ) (m : ℝ) : EReal :=
  ⨅ k : ℕ, (toEReal (h k) - ((m * k : ℝ) : EReal))

theorem supportValue_le (h : ℕ → WithTop ℝ) (m : ℝ) (k : ℕ) :
    supportValue h m ≤ toEReal (h k) - ((m * k : ℝ) : EReal) := by sorry

theorem le_supportValue_iff {m : ℝ} {a : EReal} :
    a ≤ supportValue h m ↔ ∀ k, a ≤ toEReal (h k) - ((m * k : ℝ) : EReal) := by sorry

/-- A real `y` is below the supporting value exactly when the line `y + m k` lies on or below every
point: the bridge to the line form used in Layer 0. -/
theorem coe_le_supportValue_iff {m y : ℝ} :
    (y : EReal) ≤ supportValue h m ↔ ∀ k : ℕ, ((y + m * k : ℝ) : WithTop ℝ) ≤ h k := by sorry

/-- The supporting value is finite from below exactly when some line of slope `m` lies on or below
every point. -/
theorem supportValue_ne_bot_iff {m : ℝ} :
    supportValue h m ≠ ⊥ ↔ ∃ y : ℝ, ∀ k : ℕ, ((y + m * k : ℝ) : WithTop ℝ) ≤ h k := by sorry

/-- The supporting value is `⊤` exactly when there are no points. -/
theorem supportValue_eq_top_iff {m : ℝ} : supportValue h m = ⊤ ↔ ∀ k, h k = ⊤ := by sorry

theorem supportValue_mono {g : ℕ → WithTop ℝ} (hgh : ∀ k, g k ≤ h k) (m : ℝ) :
    supportValue g m ≤ supportValue h m := by sorry

/-- A sequence is admissible exactly when some supporting value is finite from below. -/
theorem isAdmissible_iff_exists_supportValue_ne_bot :
    IsAdmissible v ↔ ∃ m : ℝ, supportValue v m ≠ ⊥ := by sorry

/-- **The points and their polygon have the same supporting value.** -/
theorem supportValue_newtonPolygon (hv : IsAdmissible v) (m : ℝ) :
    supportValue (newtonPolygon v) m = supportValue v m := by sorry

/-! ### Attained on the face -/

/-- If the line of slope `m` through `(n, h n)` lies below `h`, the supporting value is attained at
`n`. -/
theorem supportValue_eq_of_line_le {n : ℕ} (hn : h n ≠ ⊤) {m : ℝ}
    (hline : ∀ k : ℕ, (((h n).untop₀ + m * ((k : ℝ) - n) : ℝ) : WithTop ℝ) ≤ h k) :
    supportValue h m = toEReal (h n) - ((m * n : ℝ) : EReal) := by sorry

/-- The supporting value is attained at `n` when `m` separates the unit slopes at `n`. -/
theorem IsConvexSeq.supportValue_eq_of_unitSlope (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) {m : ℝ}
    (h₁ : ∀ j, j < n → h j ≠ ⊤ → unitSlope h j ≤ m) (h₂ : ∀ j, n ≤ j → (m : WithTop ℝ) ≤ unitSlope h j) :
    supportValue h m = toEReal (h n) - ((m * n : ℝ) : EReal) := by sorry

/-- **Piecewise affine**: between the consecutive unit slopes at `j` and `j + 1` the supporting value
is the affine function `h (j + 1) - m (j + 1)` of `m`. -/
theorem IsConvexSeq.supportValue_eq_of_unitSlope_le_le (hh : IsConvexSeq h) {j : ℕ}
    (hj : h (j + 1) ≠ ⊤) {m : ℝ} (h₁ : unitSlope h j ≤ m) (h₂ : (m : WithTop ℝ) ≤ unitSlope h (j + 1)) :
    supportValue h m = toEReal (h (j + 1)) - ((m * (j + 1 : ℕ) : ℝ) : EReal) := by sorry

/-- **Attained at the right endpoint of the face** of slope `m`. -/
theorem IsConvexSeq.supportValue_eq_faceRight (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (m : ℝ) :
    supportValue h m = toEReal (h (faceRight h m)) - ((m * faceRight h m : ℝ) : EReal) := by sorry

/-- **Attained at the left endpoint of the face** of slope `m`. -/
theorem IsConvexSeq.supportValue_eq_faceLeft (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (m : ℝ) :
    supportValue h m = toEReal (h (faceLeft h m)) - ((m * faceLeft h m : ℝ) : EReal) := by sorry

theorem IsConvexSeq.supportValue_ne_bot (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    (m : ℝ) : supportValue h m ≠ ⊥ := by sorry

/-- **Attained at a point exactly when a vertex lies on the supporting line** (roadmap §2.3.3). -/
theorem IsNewtonPolygonOf.exists_eq_supportValue_iff (hh : IsNewtonPolygonOf v h)
    (hv : ∃ k, v k ≠ ⊤) {m : ℝ} (hs : supportValue v m ≠ ⊥) :
    (∃ k, toEReal (v k) - ((m * k : ℝ) : EReal) = supportValue v m) ↔
      ∃ k, IsVertex h k ∧ toEReal (h k) - ((m * k : ℝ) : EReal) = supportValue v m := by sorry

/-! ### Concavity and the biconjugate (roadmap §2.3.4) -/

/-- The slopes with a finite supporting value form an interval. -/
theorem convex_setOf_supportValue_ne_bot : Convex ℝ {m : ℝ | supportValue h m ≠ ⊥} := by sorry

/-- **The supporting value is concave in the slope**, being an infimum of affine functions. -/
theorem concaveOn_toReal_supportValue :
    ConcaveOn ℝ {m : ℝ | supportValue h m ≠ ⊥} (fun m ↦ (supportValue h m).toReal) := by sorry

/-- **The biconjugate**: the polygon is the supremum of its supporting lines, so the polygon and the
supporting value function determine each other. -/
theorem iSup_supportValue_add (hv : IsAdmissible v) (k : ℕ) :
    ⨆ m : ℝ, (supportValue v m + ((m * k : ℝ) : EReal)) = toEReal (newtonPolygon v k) := by sorry

end NewtonPolygon
