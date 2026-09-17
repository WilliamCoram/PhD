/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Order.Lattice.Nat
import PhD.TauCeti.Code.NewtonPolygons.ConvexSeq

/-!
# The Newton polygon of a sequence

The Newton polygon of a sequence of points `v : ι → WithTop ℝ` on a discrete linear order `ι` is
the lower convex hull of `{(k, v k) | v k ≠ ⊤}`: the greatest convex sequence lying on or below the
points. Here it is *defined* as that greatest convex minorant — `newtonPolygon v k = ⨆ g, g k` over
all convex minorants `g` — and characterised by the specification `IsNewtonPolygonOf v h`, three
fields with no mention of a first point, so that the same definition serves `ℕ` (polynomials and
power series) and `ℤ` (Laurent series; see `Int.lean`). The polygon is its height function
(roadmap convention 1): its slopes, vertices and faces are derived from it in `Slope.lean` and
`Face.lean`, and the vertex-walk construction of the textbooks is `Construction.lean`, proved equal
to it by uniqueness.

[Ked07, §1]: "form the lower convex hull of these points, i.e., take the intersection of every
closed halfplane lying above some nonvertical line containing all the points. The boundary of this
region is called the Newton polygon of P."

The second half of the file is the one-sided theory on `ℕ`: admissibility as a condition on slopes,
the anchoring facts (the polygon passes through the first point and is `⊤` before it and after the
last one), the *vertical* case — points whose slopes are unbounded below, for which no polygon
exists and the textbooks draw a vertical line — and invariance under affine changes.

Roadmap: §0.2. Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/Basic.lean`.

## Main definitions

* `NewtonPolygon.IsConvexMinorant v h` — `h` is convex and lies on or below the points.
* `NewtonPolygon.IsNewtonPolygonOf v h` — the specification: `h` is convex, lies on or below the
  points, and is the greatest such.
* `NewtonPolygon.newtonPolygon v` — the polygon, as the pointwise supremum of the convex minorants.
* `NewtonPolygon.IsAdmissible v` (on `ℕ`) — from every point some line lies on or below every later
  point; exactly the condition for a polygon to exist.
* `NewtonPolygon.IsVertical v` (on `ℕ`) — `v` has a point but no polygon: "the Newton polygon is the
  vertical line".

## Main results

* `NewtonPolygon.IsNewtonPolygonOf.unique` — uniqueness, on the nose.
* `NewtonPolygon.isNewtonPolygonOf_newtonPolygon` — existence, as soon as one convex minorant
  exists.
* `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`,
  `NewtonPolygon.exists_isNewtonPolygonOf_iff_isAdmissible` — on `ℕ`, admissibility is exactly the
  condition, with the vertical hull `v k = -k²` as the failing example.
-/

open scoped Classical
open Order

namespace NewtonPolygon

section Spec

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι] {v w h g : ι → WithTop ℝ}

/-- `h` is a *convex minorant* of the points `v`. -/
def IsConvexMinorant (v h : ι → WithTop ℝ) : Prop :=
  IsConvexSeq h ∧ ∀ k, h k ≤ v k

/-- **The Newton polygon, specified.** `IsNewtonPolygonOf v h` says `h` is *the* Newton polygon of
the points `(k, v k)`: the greatest convex minorant. There is no anchoring field — on `ℤ` there
may be no first point; on `ℕ` the anchoring facts are theorems (`IsNewtonPolygonOf.anchor_eq`,
`IsNewtonPolygonOf.eq_top_of_forall_eq_top`). -/
structure IsNewtonPolygonOf (v h : ι → WithTop ℝ) : Prop where
  /-- The polygon is convex. -/
  convex : IsConvexSeq h
  /-- The polygon lies on or below every point. -/
  le_points : ∀ k, h k ≤ v k
  /-- It is the greatest convex minorant: every convex minorant lies on or below it. -/
  greatest : ∀ g, IsConvexSeq g → (∀ k, g k ≤ v k) → ∀ k, g k ≤ h k

/-- **Uniqueness**, on the nose: two Newton polygons of the same points are equal. This is
antisymmetry of `greatest` and is where roadmap convention 1 pays. -/
theorem IsNewtonPolygonOf.unique (h₁ : IsNewtonPolygonOf v h) (h₂ : IsNewtonPolygonOf v g) :
    h = g :=
  funext fun k ↦
    le_antisymm (h₂.greatest h h₁.convex h₁.le_points k) (h₁.greatest g h₂.convex h₂.le_points k)

/-- The polygon is one of the convex minorants it dominates. -/
theorem IsNewtonPolygonOf.isConvexMinorant (hh : IsNewtonPolygonOf v h) : IsConvexMinorant v h :=
  ⟨hh.convex, hh.le_points⟩

/-- **A convex sequence is its own polygon**: nothing can be pushed up. -/
theorem isNewtonPolygonOf_self (hv : IsConvexSeq v) : IsNewtonPolygonOf v v :=
  ⟨hv, fun _ ↦ le_rfl, fun _ _ hgv k ↦ hgv k⟩

/-- Below a point the polygon is finite. -/
theorem IsNewtonPolygonOf.ne_top_of_ne_top (hh : IsNewtonPolygonOf v h) {k : ι} (hk : v k ≠ ⊤) :
    h k ≠ ⊤ := ne_top_of_le_ne_top hk (hh.le_points k)

/-- The polygon is finite on the whole interval spanned by the points. -/
theorem IsNewtonPolygonOf.ne_top_of_le_of_le (hh : IsNewtonPolygonOf v h) {a k b : ι}
    (ha : v a ≠ ⊤) (hb : v b ≠ ⊤) (hak : a ≤ k) (hkb : k ≤ b) : h k ≠ ⊤ :=
  mem_finiteSet.1 (hh.convex.ordConnected.out (mem_finiteSet.2 (hh.ne_top_of_ne_top ha))
    (mem_finiteSet.2 (hh.ne_top_of_ne_top hb)) ⟨hak, hkb⟩)

/-! ### The polygon, as the greatest convex minorant -/

/-- **The Newton polygon of a sequence**: the pointwise supremum of all convex minorants of the
points. It satisfies the specification exactly when some convex minorant exists
(`isNewtonPolygonOf_newtonPolygon`, `exists_isNewtonPolygonOf_iff`); otherwise its value is junk.
Every statement in the later files is phrased through the specification, never through this
definition (roadmap §0.2.4). -/
noncomputable def newtonPolygon (v : ι → WithTop ℝ) (k : ι) : WithTop ℝ :=
  ⨆ g : {g : ι → WithTop ℝ // IsConvexMinorant v g}, g.1 k

/-- Every convex minorant lies on or below the polygon. -/
theorem le_newtonPolygon (hg : IsConvexMinorant v g) (k : ι) : g k ≤ newtonPolygon v k :=
  le_ciSup (f := fun g' : {g : ι → WithTop ℝ // IsConvexMinorant v g} ↦ g'.1 k)
    (OrderTop.bddAbove (Set.range fun g' : {g : ι → WithTop ℝ // IsConvexMinorant v g} ↦ g'.1 k))
    ⟨g, hg⟩

/-- The polygon lies on or below the points, as soon as one convex minorant exists. -/
theorem newtonPolygon_le (hne : ∃ g, IsConvexMinorant v g) (k : ι) : newtonPolygon v k ≤ v k := by
  obtain ⟨g, hg⟩ := hne
  have : Nonempty {g : ι → WithTop ℝ // IsConvexMinorant v g} := ⟨⟨g, hg⟩⟩
  exact ciSup_le fun g' ↦ g'.2.2 k

/-- Anything satisfying the specification is `newtonPolygon v`. -/
theorem IsNewtonPolygonOf.eq_newtonPolygon (hh : IsNewtonPolygonOf v h) : h = newtonPolygon v := by
  have : Nonempty {g : ι → WithTop ℝ // IsConvexMinorant v g} := ⟨⟨h, hh.isConvexMinorant⟩⟩
  exact funext fun k ↦ le_antisymm (le_newtonPolygon hh.isConvexMinorant k)
    (ciSup_le fun g' ↦ hh.greatest g'.1 g'.2.1 g'.2.2 k)

/-- A convex sequence is its own polygon (`isNewtonPolygonOf_self`, through the definition). -/
theorem newtonPolygon_eq_self (hv : IsConvexSeq v) : newtonPolygon v = v :=
  (isNewtonPolygonOf_self hv).eq_newtonPolygon.symm

/-- The polygon is monotone in the points. -/
theorem newtonPolygon_mono (hne : ∃ g, IsConvexMinorant v g) (hvw : ∀ k, v k ≤ w k) (k : ι) :
    newtonPolygon v k ≤ newtonPolygon w k := by
  obtain ⟨g, hg⟩ := hne
  have : Nonempty {g : ι → WithTop ℝ // IsConvexMinorant v g} := ⟨⟨g, hg⟩⟩
  exact ciSup_le fun g' ↦ le_newtonPolygon ⟨g'.2.1, fun k ↦ (g'.2.2 k).trans (hvw k)⟩ k

end Spec

section Existence

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι] [IsSuccArchimedean ι] [LocallyFiniteOrder ι]
  [NoMaxOrder ι] {v h : ι → WithTop ℝ}

/-- The polygon is convex, as soon as one convex minorant exists (`IsConvexSeq.iSup`). -/
theorem isConvexSeq_newtonPolygon (hne : ∃ g, IsConvexMinorant v g) :
    IsConvexSeq (newtonPolygon v) := by
  obtain ⟨g, hg⟩ := hne
  have : Nonempty {g : ι → WithTop ℝ // IsConvexMinorant v g} := ⟨⟨g, hg⟩⟩
  exact IsConvexSeq.iSup (f := fun g' : {g : ι → WithTop ℝ // IsConvexMinorant v g} ↦ g'.1)
    fun g' ↦ g'.2.1

/-- **Existence.** As soon as one convex minorant exists, the supremum of the convex minorants is
the Newton polygon. -/
theorem isNewtonPolygonOf_newtonPolygon (hne : ∃ g, IsConvexMinorant v g) :
    IsNewtonPolygonOf v (newtonPolygon v) :=
  ⟨isConvexSeq_newtonPolygon hne, newtonPolygon_le hne,
    fun _ hg hgv k ↦ le_newtonPolygon ⟨hg, hgv⟩ k⟩

/-- **A polygon exists exactly when a convex minorant does** (roadmap §0.2.3, index-agnostic form).
For a sequence with no point at all the constant `⊤` is its polygon. -/
theorem exists_isNewtonPolygonOf_iff :
    (∃ h, IsNewtonPolygonOf v h) ↔ ∃ g, IsConvexMinorant v g :=
  ⟨fun ⟨_, hh⟩ ↦ ⟨_, hh.isConvexMinorant⟩, fun hne ↦ ⟨_, isNewtonPolygonOf_newtonPolygon hne⟩⟩

end Existence

/-! ### The one-sided theory on `ℕ` -/

section Nat

variable {v w h g : ℕ → WithTop ℝ}

/-! #### Slopes between points and admissibility -/

/-- The slope from the point at `i` to the point at `k`, as a real number (junk when either value
is `⊤` or `k ≤ i`). -/
noncomputable def slopeTo (v : ℕ → WithTop ℝ) (i k : ℕ) : ℝ :=
  ((v k).untop₀ - (v i).untop₀) / ((k : ℝ) - i)

/-- The set of slopes from the point at `i` to the later points. -/
def slopeSet (v : ℕ → WithTop ℝ) (i : ℕ) : Set ℝ :=
  {s | ∃ k, i < k ∧ v k ≠ ⊤ ∧ s = slopeTo v i k}

/-- A sequence of points is *admissible* when from every point some line lies on or below every
later point — equivalently (`isAdmissible_iff_bddBelow`), the slopes out of each point are bounded
below; equivalently (`exists_isConvexMinorant_iff_isAdmissible`), a convex minorant exists. This is
exactly the condition for a Newton polygon to exist (roadmap §0.2.3). -/
def IsAdmissible (v : ℕ → WithTop ℝ) : Prop :=
  ∀ i, v i ≠ ⊤ → ∃ s : ℝ, ∀ k, i ≤ k → v i + (k - i : ℕ) • (s : WithTop ℝ) ≤ v k

/-- **Admissibility, as boundedness of the slopes**: a line below every later point is the same as
a lower bound for the chord slopes. -/
theorem isAdmissible_iff_bddBelow :
    IsAdmissible v ↔ ∀ i, v i ≠ ⊤ → BddBelow (slopeSet v i) := by
  constructor
  · intro hv i hi
    obtain ⟨s, hs⟩ := hv i hi
    refine ⟨s, ?_⟩
    rintro t ⟨k, hik, hk, rfl⟩
    have h1 := hs k hik.le
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hi
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hk
    rw [← ha, ← hb, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
      Nat.cast_sub hik.le] at h1
    have hpos : (0 : ℝ) < (k : ℝ) - i := by
      have : (i : ℝ) < (k : ℝ) := Nat.cast_lt.2 hik
      linarith
    rw [slopeTo, ← ha, ← hb]
    simp only [WithTop.untop₀_coe]
    rw [le_div_iff₀ hpos]
    linarith
  · intro hv i hi
    obtain ⟨s, hs⟩ := hv i hi
    refine ⟨s, fun k hik ↦ ?_⟩
    rcases eq_or_lt_of_le hik with rfl | hlt
    · simp only [tsub_self, zero_nsmul, add_zero, Std.le_refl]
    by_cases hk : v k = ⊤
    · rw [hk]
      exact le_top
    have hsl : s ≤ slopeTo v i k := hs ⟨k, hlt, hk, rfl⟩
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hi
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hk
    have hpos : (0 : ℝ) < (k : ℝ) - i := by
      have : (i : ℝ) < (k : ℝ) := Nat.cast_lt.2 hlt
      linarith
    rw [slopeTo, ← ha, ← hb] at hsl
    simp only [WithTop.untop₀_coe] at hsl
    rw [le_div_iff₀ hpos] at hsl
    rw [← ha, ← hb, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
      Nat.cast_sub hik]
    linarith

/-- Points lying on or above a single line form an admissible sequence. -/
theorem isAdmissible_of_line {y σ : ℝ} (hv : ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k) :
    IsAdmissible v := by
  intro i hi
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hi
  refine ⟨σ - (a - (y + σ * i)), fun k hik ↦ ?_⟩
  rcases eq_or_lt_of_le hik with rfl | hlt
  · simp only [tsub_self, WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_add,
      WithTop.coe_mul, WithTop.coe_natCast, zero_nsmul, add_zero, Std.le_refl]
  by_cases hk : v k = ⊤
  · rw [hk]
    exact le_top
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hk
  have hd : 0 ≤ a - (y + σ * i) := by
    have hvi := hv i
    rw [← ha, WithTop.coe_le_coe] at hvi
    linarith
  have hbk : y + σ * k ≤ b := by
    have hvk := hv k
    rw [← hb, WithTop.coe_le_coe] at hvk
    linarith
  have hone : (1 : ℝ) ≤ (k : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith
  rw [← ha, ← hb, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
    Nat.cast_sub hik]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - i - 1) hd]

/-- On `ℕ`, admissibility is the same as the points lying on or above a single line: the line
through the first point does for all the others. -/
theorem isAdmissible_iff_exists_line :
    IsAdmissible v ↔ ∃ y σ : ℝ, ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k := by
  refine ⟨fun hv ↦ ?_, fun ⟨_, _, hline⟩ ↦ isAdmissible_of_line hline⟩
  by_cases hex : ∃ i, v i ≠ ⊤
  · have hi₀ : v (Nat.find hex) ≠ ⊤ := Nat.find_spec hex
    obtain ⟨s, hs⟩ := hv _ hi₀
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hi₀
    refine ⟨a - s * (Nat.find hex : ℝ), s, fun k ↦ ?_⟩
    rcases le_or_gt (Nat.find hex) k with hk | hk
    · by_cases hvk : v k = ⊤
      · rw [hvk]
        exact le_top
      obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hvk
      have h1 := hs k hk
      rw [← ha, ← hb, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
        Nat.cast_sub hk] at h1
      rw [← hb, WithTop.coe_le_coe]
      linarith
    · rw [not_not.1 (Nat.find_min hex hk)]
      exact le_top
  · refine ⟨0, 0, fun k ↦ ?_⟩
    push Not at hex
    rw [hex k]
    exact le_top

/-- **Admissibility is exactly the existence of a convex minorant** on `ℕ`: the admissible line
through the first point, extended by `⊤` before it, is one; conversely a convex minorant bounds the
slopes out of every point below. -/
theorem exists_isConvexMinorant_iff_isAdmissible :
    (∃ g, IsConvexMinorant v g) ↔ IsAdmissible v := by
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨g, hgc, hgv⟩ i hi
    have hgi : g i ≠ ⊤ := ne_top_of_le_ne_top hi (hgv i)
    by_cases hus : unitSlope g i = ⊤
    · -- `g` stops at `i`, so every later point is `⊤` and any slope will do
      have hsucc : g (succ i) = ⊤ := (unitSlope_eq_top_iff.1 hus).elim (absurd · hgi) id
      refine ⟨0, fun k hik ↦ ?_⟩
      rcases eq_or_lt_of_le hik with rfl | hlt
      · simp only [tsub_self, WithTop.coe_zero, nsmul_zero, add_zero, Std.le_refl]
      have hgk : g k = ⊤ := hgc.eq_top_of_le hgi (le_succ i) hsucc (succ_le_of_lt hlt)
      have hvk : v k = ⊤ := by
        rw [← top_le_iff, ← hgk]
        exact hgv k
      rw [hvk]
      exact le_top
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hi
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hgi
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hus
    refine ⟨t - (a - c), fun k hik ↦ ?_⟩
    rcases eq_or_lt_of_le hik with rfl | hlt
    · simp only [tsub_self, WithTop.LinearOrderedAddCommGroup.coe_sub, zero_nsmul, add_zero,
        Std.le_refl]
    by_cases hvk : v k = ⊤
    · rw [hvk]
      exact le_top
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hvk
    have hgk := (hgc.add_nsmul_unitSlope_le hgi hik).trans (hgv k)
    rw [← hc, ← ht, ← hb, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
      Nat.card_Ico, Nat.cast_sub hik] at hgk
    have hac : 0 ≤ a - c := by
      have : c ≤ a := by
        have := hgv i
        rw [← ha, ← hc, WithTop.coe_le_coe] at this
        exact this
      linarith
    have hone : (1 : ℝ) ≤ (k : ℝ) - i := by
      have : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      linarith
    rw [← ha, ← hb, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
      Nat.cast_sub hik]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - i - 1) hac]
  · obtain ⟨y, σ, hline⟩ := isAdmissible_iff_exists_line.1 hv
    exact ⟨_, isConvexSeq_affine y σ, hline⟩

/-- The specification forces admissibility. -/
theorem IsNewtonPolygonOf.isAdmissible (hh : IsNewtonPolygonOf v h) : IsAdmissible v :=
  exists_isConvexMinorant_iff_isAdmissible.1 ⟨h, hh.isConvexMinorant⟩

/-- **Admissibility is exactly the condition for the polygon to exist** on `ℕ` (roadmap §0.2.3). -/
theorem exists_isNewtonPolygonOf_iff_isAdmissible :
    (∃ h, IsNewtonPolygonOf v h) ↔ IsAdmissible v :=
  exists_isNewtonPolygonOf_iff.trans exists_isConvexMinorant_iff_isAdmissible

/-! #### Anchoring -/

/-- At the first point the polygon passes through it: the admissible line through it is a convex
minorant, so the polygon is at least, hence equal to, the point there. -/
theorem IsNewtonPolygonOf.anchor_eq (hh : IsNewtonPolygonOf v h) {i : ℕ} (hi : ∀ k < i, v k = ⊤)
    (hi' : v i ≠ ⊤) : h i = v i := by
  refine le_antisymm (hh.le_points i) ?_
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hi'
  obtain ⟨s, hs⟩ := hh.isAdmissible i hi'
  have hval : ∀ k, i ≤ k → affineFrom i a s k = ((a + s * ((k : ℝ) - i) : ℝ) : WithTop ℝ) := by
    intro k hk
    simp only [affineFrom]
    rw [if_neg (not_lt.2 hk)]
  have hmin : ∀ k, affineFrom i a s k ≤ v k := by
    intro k
    rcases le_or_gt i k with hk | hk
    · have h1 := hs k hk
      rw [← ha, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul, Nat.cast_sub hk] at h1
      rw [hval k hk, show a + s * ((k : ℝ) - i) = a + ((k : ℝ) - i) * s by ring]
      exact h1
    · rw [hi k hk]
      exact le_top
  have hge := hh.greatest _ (isConvexSeq_affineFrom i a s) hmin i
  rw [hval i le_rfl] at hge
  rw [← ha]
  simpa using hge

/-- Before any point has occurred the polygon is `⊤`: a convex minorant can be made arbitrarily
large there by steepening the admissible line to the left of the first point. -/
theorem IsNewtonPolygonOf.eq_top_of_forall_eq_top (hh : IsNewtonPolygonOf v h) {k : ℕ}
    (hk : ∀ j ≤ k, v j = ⊤) : h k = ⊤ := by
  obtain ⟨y, s, hline⟩ := isAdmissible_iff_exists_line.1 hh.isAdmissible
  have key : ∀ c : ℝ, y + s * k ≤ c → ((c : ℝ) : WithTop ℝ) ≤ h k := by
    intro c hc
    have hconv : IsConvexSeq
        (fun j : ℕ ↦ ((c + (s - (c - (y + s * k))) * ((j : ℝ) - k) : ℝ) : WithTop ℝ)) := by
      have heq : (fun j : ℕ ↦ ((c + (s - (c - (y + s * k))) * ((j : ℝ) - k) : ℝ) : WithTop ℝ))
          = fun j : ℕ ↦ (((c - (s - (c - (y + s * k))) * k)
            + (s - (c - (y + s * k))) * j : ℝ) : WithTop ℝ) := by
        funext j
        congr 1
        ring
      rw [heq]
      exact isConvexSeq_affine _ _
    have hmin : ∀ j : ℕ,
        ((c + (s - (c - (y + s * k))) * ((j : ℝ) - k) : ℝ) : WithTop ℝ) ≤ v j := by
      intro j
      rcases lt_or_ge j k with hj | hj
      · rw [hk j hj.le]
        exact le_top
      rcases eq_or_lt_of_le hj with rfl | hj'
      · rw [hk k le_rfl]
        exact le_top
      refine le_trans ?_ (hline j)
      rw [WithTop.coe_le_coe]
      have h1 : (1 : ℝ) ≤ (j : ℝ) - k := by
        have : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj'
        linarith
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c - (y + s * k))
        (by linarith : (0 : ℝ) ≤ (j : ℝ) - k - 1)]
    have hge := hh.greatest _ hconv hmin k
    simpa using hge
  by_contra hne
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hne
  have hmax := key (max (b + 1) (y + s * k)) (le_max_right _ _)
  rw [← hb, WithTop.coe_le_coe] at hmax
  have : b + 1 ≤ max (b + 1) (y + s * k) := le_max_left _ _
  linarith

/-- **The polygon is `⊤` beyond the last point**: if no point occurs at or after `n`, then
`h n = ⊤`.
A convex minorant finite at `n` could be raised and steepened there, contradicting `greatest`. -/
theorem IsNewtonPolygonOf.eq_top_of_forall_le (hh : IsNewtonPolygonOf v h) {n : ℕ}
    (hn : ∀ k, n ≤ k → v k = ⊤) : h n = ⊤ := by
  by_contra hne
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hne
  obtain ⟨σ, hσ⟩ := ((Set.finite_Iio n).image
    fun j : ℕ ↦ (b + 1 - (v j).untop₀) / ((n : ℝ) - j)).bddAbove
  have hconv : IsConvexSeq (fun j : ℕ ↦ ((b + 1 + σ * ((j : ℝ) - n) : ℝ) : WithTop ℝ)) := by
    have heq : (fun j : ℕ ↦ ((b + 1 + σ * ((j : ℝ) - n) : ℝ) : WithTop ℝ))
        = fun j : ℕ ↦ (((b + 1 - σ * n) + σ * j : ℝ) : WithTop ℝ) := by
      funext j
      congr 1
      ring
    rw [heq]
    exact isConvexSeq_affine _ _
  have hmin : ∀ j : ℕ, ((b + 1 + σ * ((j : ℝ) - n) : ℝ) : WithTop ℝ) ≤ v j := by
    intro j
    rcases lt_or_ge j n with hj | hj
    · by_cases hvj : v j = ⊤
      · rw [hvj]
        exact le_top
      obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.1 hvj
      have hpos : (0 : ℝ) < (n : ℝ) - j := by
        have : (j : ℝ) < (n : ℝ) := Nat.cast_lt.2 hj
        linarith
      have hle : (b + 1 - (v j).untop₀) / ((n : ℝ) - j) ≤ σ := hσ ⟨j, Set.mem_Iio.2 hj, rfl⟩
      rw [← hw] at hle ⊢
      simp only [WithTop.untop₀_coe] at hle
      rw [div_le_iff₀ hpos] at hle
      rw [WithTop.coe_le_coe]
      nlinarith [hle]
    · rw [hn j hj]
      exact le_top
  have hge := hh.greatest _ hconv hmin n
  rw [← hb] at hge
  simp only [sub_self, mul_zero, add_zero, WithTop.coe_le_coe] at hge
  linarith

/-! #### The vertical case -/

/-- `v` has a point but admits no convex minorant: the slopes out of some point are unbounded below,
the lower convex hull is `−∞` at every later index, and the textbooks draw *a vertical line* at the
first point. There is no polygon object and no `⊥` value (roadmap convention 5): the case is named,
not represented. Layer 4 identifies it with radius of convergence `0`. -/
def IsVertical (v : ℕ → WithTop ℝ) : Prop :=
  (∃ i, v i ≠ ⊤) ∧ ¬ IsAdmissible v

/-- A sequence with points is vertical exactly when it has no convex minorant at all. -/
theorem isVertical_iff_not_exists_isConvexMinorant (hv : ∃ i, v i ≠ ⊤) :
    IsVertical v ↔ ¬ ∃ g, IsConvexMinorant v g := by
  rw [IsVertical, exists_isConvexMinorant_iff_isAdmissible]
  exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hv, hx⟩⟩

/-- A sequence with a point either has a Newton polygon or is vertical. -/
theorem exists_isNewtonPolygonOf_or_isVertical (hv : ∃ i, v i ≠ ⊤) :
    (∃ h, IsNewtonPolygonOf v h) ∨ IsVertical v := by
  rcases Classical.em (IsAdmissible v) with hadm | hadm
  · exact Or.inl (exists_isNewtonPolygonOf_iff_isAdmissible.2 hadm)
  · exact Or.inr ⟨hv, hadm⟩

/-- The vertical hull: `v k = -k²` has no line below it, so it is not admissible. -/
theorem not_isAdmissible_neg_sq :
    ¬ IsAdmissible fun k : ℕ ↦ ((-(k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  intro hv
  obtain ⟨s, hs⟩ := hv 0 WithTop.coe_ne_top
  obtain ⟨k, hk⟩ := exists_nat_gt (|s| + 1)
  have h1 := hs k (Nat.zero_le k)
  rw [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
    Nat.sub_zero] at h1
  norm_num at h1
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ |s| := abs_nonneg s
    linarith
  have habs : -|s| ≤ s := neg_abs_le s
  have hsk : s ≤ -(k : ℝ) := by nlinarith [h1, hkpos]
  linarith

/-- The downward parabola `-k²` is vertical: the roadmap's example of a sequence with no polygon. -/
theorem isVertical_neg_sq : IsVertical fun k : ℕ ↦ ((-(k : ℝ) ^ 2 : ℝ) : WithTop ℝ) :=
  ⟨⟨0, WithTop.coe_ne_top⟩, not_isAdmissible_neg_sq⟩

/-- No convex minorant exists for `v k = -k²`: the specification is unsatisfiable. -/
theorem not_exists_isNewtonPolygonOf_neg_sq :
    ¬ ∃ h, IsNewtonPolygonOf (fun k : ℕ ↦ ((-(k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) h := fun hh ↦
  not_isAdmissible_neg_sq (exists_isNewtonPolygonOf_iff_isAdmissible.1 hh)

/-! #### Invariance -/

/-- Adding an affine sequence to the points shears the polygon by the same affine sequence
(roadmap §0.2.5). -/
theorem newtonPolygon_add_affine (hv : IsAdmissible v) (y σ : ℝ) :
    newtonPolygon (fun k ↦ v k + ((y + σ * k : ℝ) : WithTop ℝ))
      = fun k ↦ newtonPolygon v k + ((y + σ * k : ℝ) : WithTop ℝ) := by
  have hne : ∃ g, IsConvexMinorant v g := exists_isConvexMinorant_iff_isAdmissible.2 hv
  have hcancel : ∀ (x : WithTop ℝ) (c d : ℝ), c + d = 0 →
      x + ((c : ℝ) : WithTop ℝ) + ((d : ℝ) : WithTop ℝ) = x := by
    intro x c d hcd
    rw [add_assoc, ← WithTop.coe_add, hcd, WithTop.coe_zero, add_zero]
  have hneg : ∀ j : ℕ, ((-y + (-σ) * j : ℝ) : WithTop ℝ) = ((-(y + σ * j) : ℝ) : WithTop ℝ) := by
    intro j
    congr 1
    ring
  have hspec : IsNewtonPolygonOf (fun k ↦ v k + ((y + σ * k : ℝ) : WithTop ℝ))
      (fun k ↦ newtonPolygon v k + ((y + σ * k : ℝ) : WithTop ℝ)) := by
    refine ⟨(isConvexSeq_newtonPolygon hne).add_affine y σ,
      fun k ↦ add_le_add (newtonPolygon_le hne k) le_rfl, fun g hgc hgv k ↦ ?_⟩
    have hg' : ∀ j, g j + ((-y + (-σ) * j : ℝ) : WithTop ℝ) ≤ v j := by
      intro j
      calc g j + ((-y + (-σ) * j : ℝ) : WithTop ℝ)
          ≤ v j + ((y + σ * j : ℝ) : WithTop ℝ) + ((-y + (-σ) * j : ℝ) : WithTop ℝ) :=
            add_le_add (hgv j) le_rfl
        _ = v j := by
            rw [hneg j]
            exact hcancel (v j) (y + σ * j) (-(y + σ * j)) (by ring)
    have hle := le_newtonPolygon ⟨hgc.add_affine (-y) (-σ), hg'⟩ k
    calc g k = g k + ((-y + (-σ) * k : ℝ) : WithTop ℝ) + ((y + σ * k : ℝ) : WithTop ℝ) := by
          rw [hneg k]
          exact (hcancel (g k) (-(y + σ * k)) (y + σ * k) (by ring)).symm
      _ ≤ newtonPolygon v k + ((y + σ * k : ℝ) : WithTop ℝ) := add_le_add hle le_rfl
  exact hspec.eq_newtonPolygon.symm

/-- Adding a constant to the points translates the polygon by that constant. -/
theorem newtonPolygon_add_const (hv : IsAdmissible v) (c : ℝ) :
    newtonPolygon (fun k ↦ v k + (c : WithTop ℝ))
      = fun k ↦ newtonPolygon v k + (c : WithTop ℝ) := by
  have hmain := newtonPolygon_add_affine hv c 0
  simp only [zero_mul, add_zero] at hmain
  exact hmain

end Nat

end NewtonPolygon
