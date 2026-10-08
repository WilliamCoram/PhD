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
the anchoring fact that the polygon passes through the first point (that it is `⊤` before the
first point and after the last one holds on any index type), the *vertical* case — points whose slopes are unbounded below, for which no polygon
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
the points `(k, v k)`: the greatest convex minorant. -/
structure IsNewtonPolygonOf (v h : ι → WithTop ℝ) : Prop where
  /-- The polygon is convex. -/
  convex : IsConvexSeq h
  /-- The polygon lies on or below every point. -/
  le_points : ∀ k, h k ≤ v k
  /-- It is the greatest convex minorant: every convex minorant lies on or below it. -/
  greatest : ∀ g, IsConvexSeq g → (∀ k, g k ≤ v k) → ∀ k, g k ≤ h k

theorem IsNewtonPolygonOf.unique (h₁ : IsNewtonPolygonOf v h) (h₂ : IsNewtonPolygonOf v g) :
    h = g := funext fun k ↦
  le_antisymm (h₂.greatest h h₁.convex h₁.le_points k) (h₁.greatest g h₂.convex h₂.le_points k)

theorem IsNewtonPolygonOf.isConvexMinorant (hh : IsNewtonPolygonOf v h) : IsConvexMinorant v h :=
  ⟨hh.convex, hh.le_points⟩

theorem isNewtonPolygonOf_self (hv : IsConvexSeq v) : IsNewtonPolygonOf v v :=
  ⟨hv, fun _ ↦ le_rfl, fun _ _ hgv k ↦ hgv k⟩

theorem IsNewtonPolygonOf.ne_top_of_ne_top (hh : IsNewtonPolygonOf v h) {k : ι} (hk : v k ≠ ⊤) :
  h k ≠ ⊤ := ne_top_of_le_ne_top hk (hh.le_points k)

theorem IsNewtonPolygonOf.ne_top_of_le_of_le (hh : IsNewtonPolygonOf v h) {a k b : ι}
    (ha : v a ≠ ⊤) (hb : v b ≠ ⊤) (hak : a ≤ k) (hkb : k ≤ b) : h k ≠ ⊤ :=
  hh.convex.ne_top_of_le_of_le (hh.ne_top_of_ne_top ha) (hh.ne_top_of_ne_top hb) hak hkb

theorem IsNewtonPolygonOf.eq_top_of_forall_eq_top (hh : IsNewtonPolygonOf v h) {k : ι}
    (hk : ∀ j ≤ k, v j = ⊤) : h k = ⊤ :=
  top_le_iff.1 <| (Set.piecewise_eq_of_notMem (Set.Ioi k) h ⊤ (lt_irrefl k)).symm.trans_le <|
    hh.greatest ((Set.Ioi k).piecewise h ⊤) (hh.convex.piecewise_top Set.ordConnected_Ioi)
      (fun j ↦ (le_or_gt j k).elim (fun hj ↦ le_top.trans_eq (hk j hj).symm)
        fun hj ↦ (Set.piecewise_eq_of_mem (Set.Ioi k) h ⊤ hj).trans_le (hh.le_points j)) k

theorem IsNewtonPolygonOf.eq_top_of_forall_le (hh : IsNewtonPolygonOf v h) {n : ι}
    (hn : ∀ k, n ≤ k → v k = ⊤) : h n = ⊤ :=
  top_le_iff.1 <| (Set.piecewise_eq_of_notMem (Set.Iio n) h ⊤ (lt_irrefl n)).symm.trans_le <|
    hh.greatest ((Set.Iio n).piecewise h ⊤) (hh.convex.piecewise_top Set.ordConnected_Iio)
      (fun j ↦ (lt_or_ge j n).elim
        (fun hj ↦ (Set.piecewise_eq_of_mem (Set.Iio n) h ⊤ hj).trans_le (hh.le_points j))
        fun hj ↦ le_top.trans_eq (hn j hj).symm) n

/-! ### The polygon, as the greatest convex minorant -/

/-- **The Newton polygon of a sequence**: the pointwise supremum of all convex minorants of the
points. It satisfies the specification exactly when some convex minorant exists
(`isNewtonPolygonOf_newtonPolygon`, `exists_isNewtonPolygonOf_iff`); otherwise its value is junk.
Every statement in the later files is phrased through the specification, never through this
definition (roadmap §0.2.4). -/
noncomputable
def newtonPolygon (v : ι → WithTop ℝ) (k : ι) : WithTop ℝ :=
  ⨆ g : {g : ι → WithTop ℝ // IsConvexMinorant v g}, g.1 k

theorem le_newtonPolygon (hg : IsConvexMinorant v g) (k : ι) : g k ≤ newtonPolygon v k :=
  le_ciSup (f := fun g' : {g : ι → WithTop ℝ // IsConvexMinorant v g} ↦ g'.1 k)
    (OrderTop.bddAbove (Set.range fun g' : {g : ι → WithTop ℝ // IsConvexMinorant v g} ↦ g'.1 k))
    ⟨g, hg⟩

theorem newtonPolygon_le_of_forall (hne : ∃ g, IsConvexMinorant v g) {k : ι} {a : WithTop ℝ}
    (ha : ∀ g, IsConvexMinorant v g → g k ≤ a) : newtonPolygon v k ≤ a :=
  have := nonempty_subtype.2 hne
  ciSup_le fun g ↦ ha g.1 g.2

theorem newtonPolygon_le (hne : ∃ g, IsConvexMinorant v g) (k : ι) : newtonPolygon v k ≤ v k :=
  newtonPolygon_le_of_forall hne fun _ hg ↦ hg.2 k

theorem IsNewtonPolygonOf.eq_newtonPolygon (hh : IsNewtonPolygonOf v h) : h = newtonPolygon v :=
  funext fun k ↦ le_antisymm (le_newtonPolygon hh.isConvexMinorant k)
    (newtonPolygon_le_of_forall ⟨h, hh.isConvexMinorant⟩ fun g hg ↦ hh.greatest g hg.1 hg.2 k)

theorem newtonPolygon_eq_self (hv : IsConvexSeq v) : newtonPolygon v = v :=
  (isNewtonPolygonOf_self hv).eq_newtonPolygon.symm

theorem newtonPolygon_mono (hne : ∃ g, IsConvexMinorant v g) (hvw : ∀ k, v k ≤ w k) (k : ι) :
    newtonPolygon v k ≤ newtonPolygon w k :=
  newtonPolygon_le_of_forall hne fun _ hg ↦
    le_newtonPolygon ⟨hg.1, fun k ↦ (hg.2 k).trans (hvw k)⟩ k

end Spec

section Existence

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι] [LocallyFiniteOrder ι] [NoMaxOrder ι]
  {v h : ι → WithTop ℝ}

theorem isConvexSeq_newtonPolygon (hne : ∃ g, IsConvexMinorant v g) :
    IsConvexSeq (newtonPolygon v) :=
  have := nonempty_subtype.2 hne
  IsConvexSeq.iSup (f := fun g' : {g : ι → WithTop ℝ // IsConvexMinorant v g} ↦ g'.1)
    fun g' ↦ g'.2.1

theorem isNewtonPolygonOf_newtonPolygon (hne : ∃ g, IsConvexMinorant v g) :
    IsNewtonPolygonOf v (newtonPolygon v) :=
  ⟨isConvexSeq_newtonPolygon hne, newtonPolygon_le hne,
    fun _ hg hgv k ↦ le_newtonPolygon ⟨hg, hgv⟩ k⟩

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
noncomputable
def slopeTo (v : ℕ → WithTop ℝ) (i k : ℕ) : ℝ :=
  ((v k).untop₀ - (v i).untop₀) / ((k : ℝ) - i)

/-- The set of slopes from the point at `i` to the later points. -/
def slopeSet (v : ℕ → WithTop ℝ) (i : ℕ) : Set ℝ :=
  {s | ∃ k, i < k ∧ v k ≠ ⊤ ∧ s = slopeTo v i k}

/-- A sequence of points is *admissible* when from every point some line lies on or below every
later point — equivalently (`isAdmissible_iff_bddBelow`), the slopes out of the index `0` are
bounded below; equivalently (`exists_isConvexMinorant_iff_isAdmissible`), a convex minorant exists.
This is exactly the condition for a Newton polygon to exist (roadmap §0.2.3). -/
def IsAdmissible (v : ℕ → WithTop ℝ) : Prop :=
  ∀ i, v i ≠ ⊤ → ∃ s : ℝ, ∀ k, i ≤ k → v i + (k - i : ℕ) • (s : WithTop ℝ) ≤ v k

theorem isAdmissible_of_line {y σ : ℝ} (hv : ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k) :
    IsAdmissible v := by
  intro i hi
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hi
  refine ⟨y + σ * (i + 1) - a, fun k hik ↦ ?_⟩  -- intersect y + σ * k at i + 1
  rcases eq_or_lt_of_le hik with rfl | hlt
  · simp
  refine le_trans ?_ (hv k)
  have hd : y + σ * i ≤ a := by
    have := hv i
    rwa [← ha, WithTop.coe_le_coe] at this
  have hone : (i : ℝ) + 1 ≤ k := by exact_mod_cast hlt
  rw [← ha, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
    Nat.cast_sub hik]
  have key : y + σ * k - (a + (k - i) * (y + σ * (i + 1) - a))
      = (k - (i + 1)) * (a - (y + σ * i)) := by ring
  have := mul_nonneg (sub_nonneg.2 hone) (sub_nonneg.2 hd)
  linarith

theorem IsAdmissible.exists_line (hv : IsAdmissible v) :
    ∃ y σ : ℝ, ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k := by
  by_cases hex : ∃ i, v i ≠ ⊤
  · set i₀ := Nat.find hex
    obtain ⟨s, hs⟩ := hv i₀ (Nat.find_spec hex)
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (Nat.find_spec hex)
    -- y-intercept and slope from the obtained line at i₀
    refine ⟨a - s * i₀, s, fun k ↦ ?_⟩
    rcases le_or_gt i₀ k with hk | hk
    · convert hs k hk using 1
      rw [← ha, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul, Nat.cast_sub hk]
      grind
    · exact le_top.trans_eq (not_not.1 (Nat.find_min hex hk)).symm
  · push Not at hex
    exact ⟨0, 0, fun k ↦ (hex k).symm ▸ le_top⟩

theorem isAdmissible_iff_exists_line :
    IsAdmissible v ↔ ∃ y σ : ℝ, ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k :=
  ⟨IsAdmissible.exists_line, fun ⟨_, _, hline⟩ ↦ isAdmissible_of_line hline⟩

theorem IsAdmissible.bddBelow_slopeSet (hv : IsAdmissible v) (i : ℕ) :
    BddBelow (slopeSet v i) := by
  obtain ⟨y, σ, hline⟩ := hv.exists_line
  refine ⟨σ - |y + σ * i - (v i).untop₀|, ?_⟩
  rintro t ⟨k, hik, hk, rfl⟩
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hk
  have hbk := hline k
  rw [← hb, WithTop.coe_le_coe] at hbk
  have hone : (1 : ℝ) ≤ (k : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hik
    linarith
  rw [slopeTo, ← hb, WithTop.untop₀_coe, le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (abs_nonneg (y + σ * i - (v i).untop₀)) (by linarith : 0 ≤ (k : ℝ) - i - 1),
    neg_abs_le (y + σ * i - (v i).untop₀)]

theorem isAdmissible_of_bddBelow (hv : BddBelow (slopeSet v 0)) : IsAdmissible v := by
  obtain ⟨s, hs⟩ := hv
  refine isAdmissible_of_line (y := (v 0).untop₀) (σ := s) fun k ↦ ?_
  by_cases hk : v k = ⊤
  · simp [hk]
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [← hb]
  have hsl : s ≤ slopeTo v 0 k := hs ⟨k, hpos, hk, rfl⟩
  rw [slopeTo, ← hb, WithTop.untop₀_coe, Nat.cast_zero, sub_zero,
    le_div_iff₀ (Nat.cast_pos.2 hpos)] at hsl
  rw [← hb, WithTop.coe_le_coe]
  linarith

theorem isAdmissible_iff_bddBelow : IsAdmissible v ↔ BddBelow (slopeSet v 0) :=
  ⟨fun hv ↦ hv.bddBelow_slopeSet 0, isAdmissible_of_bddBelow⟩

theorem IsConvexSeq.isAdmissible (hg : IsConvexSeq g) : IsAdmissible g := by
  intro i hi
  by_cases hus : unitSlope g i = ⊤
  · refine ⟨0, fun k hik ↦ ?_⟩
    rcases eq_or_lt_of_le hik with rfl | hlt
    · simp
    exact le_top.trans_eq (hg.eq_top_of_unitSlope_eq_top hi hus hlt).symm
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hus
  refine ⟨t, fun k hik ↦ ?_⟩
  simpa [Nat.card_Ico, ht] using hg.add_nsmul_unitSlope_le hi hik

theorem IsAdmissible.mono (hg : IsAdmissible g) (hgv : ∀ k, g k ≤ v k) : IsAdmissible v := by
  obtain ⟨_, _, hline⟩ := hg.exists_line
  exact isAdmissible_of_line fun k ↦ (hline k).trans (hgv k)

theorem IsConvexMinorant.isAdmissible (hg : IsConvexMinorant v g) : IsAdmissible v :=
  hg.1.isAdmissible.mono hg.2

theorem IsAdmissible.exists_isConvexMinorant (hv : IsAdmissible v) :
    ∃ g, IsConvexMinorant v g :=
  let ⟨y, σ, hline⟩ := hv.exists_line
  ⟨_, isConvexSeq_affine y σ, hline⟩

theorem exists_isConvexMinorant_iff_isAdmissible :
    (∃ g, IsConvexMinorant v g) ↔ IsAdmissible v :=
  ⟨fun ⟨_, hg⟩ ↦ hg.isAdmissible, IsAdmissible.exists_isConvexMinorant⟩


theorem IsNewtonPolygonOf.isAdmissible (hh : IsNewtonPolygonOf v h) : IsAdmissible v :=
  hh.isConvexMinorant.isAdmissible

theorem exists_isNewtonPolygonOf_iff_isAdmissible :
    (∃ h, IsNewtonPolygonOf v h) ↔ IsAdmissible v :=
  exists_isNewtonPolygonOf_iff.trans exists_isConvexMinorant_iff_isAdmissible

/-! #### Anchoring -/

theorem IsNewtonPolygonOf.anchor_eq (hh : IsNewtonPolygonOf v h) {i : ℕ} (hi : ∀ k < i, v k = ⊤)
    (hi' : v i ≠ ⊤) : h i = v i := by
  refine le_antisymm (hh.le_points i) ?_
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hi'
  obtain ⟨s, hs⟩ := hh.isAdmissible i hi'
  suffices ∀ k, affineFrom i a s k ≤ v k by
    convert hh.greatest _ (isConvexSeq_affineFrom i a s) this i
    aesop
  intro k
  rcases le_or_gt i k with hk | hk
  · specialize hs k hk
    rw [← ha, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul, Nat.cast_sub hk] at hs
    rwa [affineFrom_of_le hk, show a + s * ((k : ℝ) - i) = a + ((k : ℝ) - i) * s by ring]
  · simp [hi k hk]

/-! #### The vertical case -/

/-- `v` has a point but admits no convex minorant: the slopes out of some point are unbounded below,
the lower convex hull is `−∞` at every later index, and the textbooks draw *a vertical line* at the
first point. There is no polygon object and no `⊥` value (roadmap convention 5): the case is named,
not represented. Layer 4 identifies it with radius of convergence `0`. -/
def IsVertical (v : ℕ → WithTop ℝ) : Prop :=
  (∃ i, v i ≠ ⊤) ∧ ¬ IsAdmissible v

theorem isVertical_iff_not_exists_isConvexMinorant (hv : ∃ i, v i ≠ ⊤) :
    IsVertical v ↔ ¬ ∃ g, IsConvexMinorant v g := by
  rw [IsVertical, exists_isConvexMinorant_iff_isAdmissible]
  exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hv, hx⟩⟩

theorem exists_isNewtonPolygonOf_or_isVertical (hv : ∃ i, v i ≠ ⊤) :
    (∃ h, IsNewtonPolygonOf v h) ∨ IsVertical v := by
  rcases Classical.em (IsAdmissible v) with hadm | hadm
  · exact Or.inl (exists_isNewtonPolygonOf_iff_isAdmissible.2 hadm)
  · exact Or.inr ⟨hv, hadm⟩

/- Example: v k = - k ^ 2 -/

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

theorem isVertical_neg_sq : IsVertical fun k : ℕ ↦ ((-(k : ℝ) ^ 2 : ℝ) : WithTop ℝ) :=
  ⟨⟨0, WithTop.coe_ne_top⟩, not_isAdmissible_neg_sq⟩

theorem not_exists_isNewtonPolygonOf_neg_sq :
    ¬ ∃ h, IsNewtonPolygonOf (fun k : ℕ ↦ ((-(k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) h := fun hh ↦
  not_isAdmissible_neg_sq (exists_isNewtonPolygonOf_iff_isAdmissible.1 hh)

/-! #### Invariance -/

theorem IsConvexMinorant.add_affine (hg : IsConvexMinorant v g) (y σ : ℝ) :
    IsConvexMinorant (fun k ↦ v k + ((y + σ * k : ℝ) : WithTop ℝ))
      fun k ↦ g k + ((y + σ * k : ℝ) : WithTop ℝ) :=
  ⟨hg.1.add_affine y σ, fun k ↦ add_le_add (hg.2 k) le_rfl⟩

private
theorem add_coe_add_coe_of_add_eq_zero (x : WithTop ℝ) {a b : ℝ} (hab : a + b = 0) :
    x + (a : WithTop ℝ) + (b : WithTop ℝ) = x := by
  simp [add_assoc, ← WithTop.coe_add, hab]

theorem IsNewtonPolygonOf.add_affine (hh : IsNewtonPolygonOf v h) (y σ : ℝ) :
    IsNewtonPolygonOf (fun k ↦ v k + ((y + σ * k : ℝ) : WithTop ℝ))
      fun k ↦ h k + ((y + σ * k : ℝ) : WithTop ℝ) where
  convex := hh.convex.add_affine y σ
  le_points k := add_le_add (hh.le_points k) le_rfl
  greatest g hgc hgv k := by
    calc g k = g k + ((-y + -σ * k : ℝ) : WithTop ℝ) + ((y + σ * k : ℝ) : WithTop ℝ) :=
          (add_coe_add_coe_of_add_eq_zero _ (by ring)).symm
      _ ≤ h k + ((y + σ * k : ℝ) : WithTop ℝ) := add_le_add (hh.greatest _
      (hgc.add_affine (-y) (-σ)) (fun j ↦ (add_le_add (hgv j) le_rfl).trans_eq
      (add_coe_add_coe_of_add_eq_zero _ (by ring))) k) le_rfl

theorem newtonPolygon_add_affine (hv : IsAdmissible v) (y σ : ℝ) :
    newtonPolygon (fun k ↦ v k + ((y + σ * k : ℝ) : WithTop ℝ))
      = fun k ↦ newtonPolygon v k + ((y + σ * k : ℝ) : WithTop ℝ) :=
  ((isNewtonPolygonOf_newtonPolygon (exists_isConvexMinorant_iff_isAdmissible.2 hv)).add_affine
    y σ).eq_newtonPolygon.symm

theorem newtonPolygon_add_const (hv : IsAdmissible v) (c : ℝ) :
    newtonPolygon (fun k ↦ v k + (c : WithTop ℝ)) =
    fun k ↦ newtonPolygon v k + (c : WithTop ℝ) := by
  convert newtonPolygon_add_affine hv c 0
  all_goals aesop

end Nat

end NewtonPolygon
