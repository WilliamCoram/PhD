/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Set.Card
import PhD.TauCeti.Code.NewtonPolygons.Basic

/-!
# Slopes, vertices, segments and the slope multiset

The data a Newton polygon is usually presented by — its vertices, its segments with their slopes
and lengths, the multiset of slopes — is derived here from the height function (roadmap
convention 1). The vertices are the indices where the unit slope strictly increases, together with
the anchor; a segment is the stretch between consecutive vertices, on which the polygon is affine;
the slope multiset is the multiset of unit slopes.

[Kob84, §IV.3 p. 97]: "By the vertices of the Newton polygon we mean the points
`(i_j, ord_p a_{i_j})` where the slopes change." [Ked07, §1]: "form the multiset consisting of the
slopes of the polygon, each occurring with multiplicity equal to the width of the corresponding
segment."

Roadmap: §0.4. Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/Slope.lean`.

## Main definitions

* `NewtonPolygon.anchor h` — the first finite index.
* `NewtonPolygon.IsVertex h k`, `NewtonPolygon.IsSegment h a b` — vertices and segments.
* `NewtonPolygon.slopeMultiset h` — the multiset of unit slopes, for a polygon with finitely many.
* `NewtonPolygon.IsPure h m`, `NewtonPolygon.HasFirstBreak h m l` — purity and the first break.
* `NewtonPolygon.truncate v n` — the points with index at most `n`.
* `NewtonPolygon.EndsInRay h m` — the polygon ends in a ray of slope `m`: the face of infinite
  length.

## Main results

* `NewtonPolygon.IsNewtonPolygonOf.eq_of_isVertex` — **a vertex is a point of the sequence**.
* `NewtonPolygon.IsConvexSeq.eq_add_nsmul_of_isSegment` — the polygon is affine on each segment.
* `NewtonPolygon.IsNewtonPolygonOf.hasFirstBreak_iff` — the first break, read off the points.
* `NewtonPolygon.IsConvexSeq.endsInRay_iff` — a terminal ray is an attained slope that no slope
  exceeds.
* `NewtonPolygon.newtonPolygon_truncate_eq` — truncating the points does not change the polygon up
  to the last vertex retained.
-/

open scoped Classical

namespace NewtonPolygon

variable {v h : ℕ → WithTop ℝ}

/-! ### The anchor and the vertices -/

/-- The first finite index of `h` (junk `0` if there is none). -/
noncomputable def anchor (h : ℕ → WithTop ℝ) : ℕ := sInf (finiteSet h)

/-- The anchor carries a point. -/
theorem anchor_mem (hne : ∃ i, h i ≠ ⊤) : h (anchor h) ≠ ⊤ :=
  mem_finiteSet.1 (Nat.sInf_mem (hne.imp fun _ hi ↦ mem_finiteSet.2 hi))

/-- The anchor is the first index carrying a point. -/
theorem anchor_le {i : ℕ} (hi : h i ≠ ⊤) : anchor h ≤ i := Nat.sInf_le (mem_finiteSet.2 hi)

/-- Before the anchor there is nothing. -/
theorem eq_top_of_lt_anchor {k : ℕ} (hk : k < anchor h) : h k = ⊤ :=
  not_not.1 (Nat.notMem_of_lt_sInf hk)

/-- The anchor of a Newton polygon is the first index carrying a point. -/
theorem IsNewtonPolygonOf.anchor_eq_sInf (hh : IsNewtonPolygonOf v h) (hv : ∃ i, v i ≠ ⊤) :
    anchor h = sInf (finiteSet v) := by
  have hvne : (finiteSet v).Nonempty := hv.imp fun _ hi ↦ mem_finiteSet.2 hi
  have hi₀ : v (sInf (finiteSet v)) ≠ ⊤ := mem_finiteSet.1 (Nat.sInf_mem hvne)
  refine le_antisymm (anchor_le (hh.ne_top_of_ne_top hi₀)) ?_
  by_contra hc
  rw [not_le] at hc
  exact anchor_mem ⟨_, hh.ne_top_of_ne_top hi₀⟩
    (hh.eq_top_of_forall_eq_top fun j hj ↦
      not_not.1 (Nat.notMem_of_lt_sInf (lt_of_le_of_lt hj hc)))

/-- `k` is a *vertex* of `h`: a finite index at which the unit slope strictly increases, or the
anchor. The last finite index is a vertex, since the unit slope there is `⊤`. -/
def IsVertex (h : ℕ → WithTop ℝ) (k : ℕ) : Prop :=
  h k ≠ ⊤ ∧ (k = anchor h ∨ unitSlope h (k - 1) < unitSlope h k)

/-- The anchor is a vertex. -/
theorem isVertex_anchor (hne : ∃ i, h i ≠ ⊤) : IsVertex h (anchor h) :=
  ⟨anchor_mem hne, Or.inl rfl⟩

/-- The last finite index is a vertex. -/
theorem isVertex_of_succ_eq_top (hh : IsConvexSeq h) {k : ℕ} (hk : h k ≠ ⊤) (hk1 : h (k + 1) = ⊤) :
    IsVertex h k := by
  refine ⟨hk, ?_⟩
  rcases eq_or_lt_of_le (anchor_le hk) with heq | hlt
  · exact Or.inl heq.symm
  refine Or.inr ?_
  have htop : unitSlope h k = ⊤ := by
    rw [unitSlope_eq_top_iff, Order.succ_eq_add_one]
    exact Or.inr hk1
  have hprev : h (k - 1) ≠ ⊤ := mem_finiteSet.1 (hh.ordConnected.out
    (mem_finiteSet.2 (anchor_mem ⟨k, hk⟩)) (mem_finiteSet.2 hk) ⟨by omega, by omega⟩)
  have hne' : unitSlope h (k - 1) ≠ ⊤ := by
    rw [Ne, unitSlope_eq_top_iff, Order.succ_eq_add_one, show k - 1 + 1 = k by omega]
    push Not
    exact ⟨hprev, hk⟩
  rw [htop]
  exact lt_of_le_of_ne le_top hne'

/-- **A vertex of the Newton polygon is a point of the sequence** (roadmap §0.4.1): raising the
polygon at a vertex by a small amount would still give a convex minorant, contradicting
`greatest`. -/
theorem IsNewtonPolygonOf.eq_of_isVertex (hh : IsNewtonPolygonOf v h) {k : ℕ}
    (hk : IsVertex h k) : h k = v k := by
  obtain ⟨hkf, hcase⟩ := hk
  have hv : ∃ i, v i ≠ ⊤ := by
    by_contra hc
    push Not at hc
    exact hkf (hh.eq_top_of_forall_eq_top fun j _ ↦ hc j)
  have hvne : (finiteSet v).Nonempty := hv.imp fun _ hi ↦ mem_finiteSet.2 hi
  rcases hcase with heq | hlt
  · -- the anchor: the polygon passes through the first point
    subst heq
    rw [hh.anchor_eq_sInf hv]
    exact hh.anchor_eq (fun j hj ↦ not_not.1 (Nat.notMem_of_lt_sInf hj))
      (mem_finiteSet.1 (Nat.sInf_mem hvne))
  -- a genuine break: bump the polygon at `k` and contradict maximality
  by_contra hne
  have hlt' : h k < v k := lt_of_le_of_ne (hh.le_points k) hne
  have hkpos : 1 ≤ k := by
    by_contra hc
    have : k = 0 := by omega
    subst this
    simp only [Nat.zero_sub] at hlt
    exact absurd hlt (lt_irrefl _)
  have hprevslope : unitSlope h (k - 1) ≠ ⊤ := fun hc ↦ (hc ▸ hlt).not_gt (lt_of_le_of_ne le_top
    (fun hx ↦ by rw [hc, hx] at hlt; exact absurd hlt (lt_irrefl _)))
  have hprev : h (k - 1) ≠ ⊤ := fun hc ↦ hprevslope (unitSlope_eq_top_iff.2 (Or.inl hc))
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hkf
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.1 hprev
  have hsucc_prev : k - 1 + 1 = k := by omega
  -- room above the polygon at `k`, and the convexity gap there
  obtain ⟨ε, hε0, hεv, hεmid⟩ : ∃ ε : ℝ, 0 < ε ∧ (h k + (ε : WithTop ℝ) ≤ v k) ∧
      ∀ j, j + 1 = k → (h k + (ε : WithTop ℝ)) + (h k + (ε : WithTop ℝ)) ≤ h j + h (k + 1) := by
    obtain ⟨r, hr0, hrv⟩ : ∃ r : ℝ, 0 < r ∧ h k + (r : WithTop ℝ) ≤ v k := by
      by_cases hvk : v k = ⊤
      · exact ⟨1, one_pos, by rw [hvk]; exact le_top⟩
      obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.1 hvk
      rw [← hc, ← hd, WithTop.coe_lt_coe] at hlt'
      refine ⟨d - c, by linarith, ?_⟩
      rw [← hc, ← hd, ← WithTop.coe_add, WithTop.coe_le_coe]
      linarith
    by_cases hnext : h (k + 1) = ⊤
    · refine ⟨r, hr0, hrv, fun j hj ↦ ?_⟩
      rw [hnext, add_top]
      exact le_top
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hnext
    have hgap : 2 * c < p + q := by
      rw [unitSlope_of_ne_top hprev (by rw [Order.succ_eq_add_one, hsucc_prev]; exact hkf),
        unitSlope_of_ne_top hkf (by rw [Order.succ_eq_add_one]; exact hnext),
        WithTop.coe_lt_coe, Order.succ_eq_add_one, Order.succ_eq_add_one, hsucc_prev,
        ← hc, ← hp, ← hq] at hlt
      simp only [WithTop.untop₀_coe] at hlt
      linarith
    refine ⟨min r ((p + q - 2 * c) / 2), lt_min hr0 (by linarith), ?_, fun j hj ↦ ?_⟩
    · refine le_trans (add_le_add le_rfl ?_) hrv
      rw [WithTop.coe_le_coe]
      exact min_le_left _ _
    · have hjk : j = k - 1 := by omega
      subst hjk
      rw [← hc, ← hp, ← hq, ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_le_coe]
      have : min r ((p + q - 2 * c) / 2) ≤ (p + q - 2 * c) / 2 := min_le_right _ _
      linarith
  -- the bumped competitor
  have hεtop : (0 : WithTop ℝ) ≤ ((ε : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_zero, WithTop.coe_le_coe]
    exact hε0.le
  set g : ℕ → WithTop ℝ := fun j ↦ if j = k then h j + (ε : WithTop ℝ) else h j with hgdef
  have hgval : ∀ j, j ≠ k → g j = h j := fun j hj ↦ by
    simp only [hgdef]
    rw [if_neg hj]
  have hgk : g k = h k + (ε : WithTop ℝ) := by
    simp only [hgdef, ↓reduceIte]
  have hgle : ∀ j, h j ≤ g j := by
    intro j
    by_cases hj : j = k
    · subst hj
      rw [hgk]
      simpa using add_le_add (le_refl (h j)) hεtop
    · rw [hgval j hj]
  have hgfs : finiteSet g = finiteSet h := by
    ext j
    by_cases hj : j = k
    · subst hj
      simp only [mem_finiteSet, hgk, ne_eq, WithTop.add_eq_top, not_or]
      exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, WithTop.coe_ne_top⟩⟩
    · rw [mem_finiteSet, mem_finiteSet, hgval j hj]
  have hgconv : IsConvexSeq g := by
    refine (isConvexSeq_iff_midpoint (by rw [hgfs]; exact hh.convex.ordConnected)).2 fun j ↦ ?_
    simp only [Order.succ_eq_add_one]
    by_cases hj1 : j + 1 = k
    · have hj0 : j ≠ k := by omega
      have hj2 : j + 1 + 1 ≠ k := by omega
      rw [hgval j hj0, hgval (j + 1 + 1) hj2, hj1, hgk]
      exact hεmid j hj1
    · by_cases hj0 : j = k
      · have ha : j + 1 ≠ k := by omega
        have hb : j + 1 + 1 ≠ k := by omega
        rw [hgval (j + 1) ha, hgval (j + 1 + 1) hb]
        exact le_trans (hh.convex.midpoint j) (by
          simp only [Order.succ_eq_add_one]
          exact add_le_add (hgle j) le_rfl)
      · by_cases hj2 : j + 1 + 1 = k
        · have ha : j + 1 ≠ k := by omega
          rw [hgval j hj0, hgval (j + 1) ha]
          exact le_trans (hh.convex.midpoint j) (by
            simp only [Order.succ_eq_add_one]
            exact add_le_add le_rfl (hgle (j + 1 + 1)))
        · rw [hgval j hj0, hgval (j + 1) hj1, hgval (j + 1 + 1) hj2]
          simpa only [Order.succ_eq_add_one] using hh.convex.midpoint j
  have hgmin : ∀ j, g j ≤ v j := by
    intro j
    by_cases hj : j = k
    · subst hj
      rw [hgk]
      exact hεv
    · rw [hgval j hj]
      exact hh.le_points j
  have hge := hh.greatest g hgconv hgmin k
  rw [hgk, ← hc, ← WithTop.coe_add, WithTop.coe_le_coe] at hge
  linarith

/-! ### Segments -/

/-- `a` and `b` bound a *segment* of `h`: they are consecutive vertices. -/
def IsSegment (h : ℕ → WithTop ℝ) (a b : ℕ) : Prop :=
  IsVertex h a ∧ IsVertex h b ∧ a < b ∧ ∀ k, a < k → k < b → ¬ IsVertex h k

/-- On a segment the unit slope is constant. -/
theorem IsConvexSeq.unitSlope_eq_of_isSegment (hh : IsConvexSeq h) {a b : ℕ}
    (hab : IsSegment h a b) {j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    unitSlope h j = unitSlope h a := by
  obtain ⟨⟨haf, -⟩, ⟨hbf, -⟩, hab', hnov⟩ := hab
  have hfin : ∀ m : ℕ, a ≤ m → m ≤ b → h m ≠ ⊤ := fun m h1 h2 ↦
    mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 haf) (mem_finiteSet.2 hbf) ⟨h1, h2⟩)
  induction j, haj using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      have hmb : m < b := by omega
      have heq := ih hmb
      have hmono : unitSlope h m ≤ unitSlope h (m + 1) :=
        hh.monotoneOn (mem_finiteSet.2 (hfin m hm hmb.le))
          (mem_finiteSet.2 (hfin (m + 1) (by omega) (by omega))) (by omega)
      refine le_antisymm ?_ (heq ▸ hmono)
      by_contra hcon
      rw [not_le] at hcon
      refine hnov (m + 1) (by omega) hjb ⟨hfin (m + 1) (by omega) (by omega), Or.inr ?_⟩
      rw [show m + 1 - 1 = m by omega]
      exact heq ▸ hcon

/-- On a segment the polygon is affine, with the segment's slope. -/
theorem IsConvexSeq.eq_add_nsmul_of_isSegment (hh : IsConvexSeq h) {a b : ℕ}
    (hab : IsSegment h a b) {k : ℕ} (hak : a ≤ k) (hkb : k ≤ b) :
    h k = h a + (k - a : ℕ) • unitSlope h a := by
  have haf : h a ≠ ⊤ := hab.1.1
  have hbf : h b ≠ ⊤ := hab.2.1.1
  have hab' : a < b := hab.2.2.1
  have hsucc : h (a + 1) ≠ ⊤ := mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 haf)
    (mem_finiteSet.2 hbf) ⟨by omega, by omega⟩)
  have hus : unitSlope h a ≠ ⊤ := by
    rw [Ne, unitSlope_eq_top_iff, Order.succ_eq_add_one]
    push Not
    exact ⟨haf, hsucc⟩
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.1 hus
  have hmain := eq_add_nsmul_of_forall_unitSlope_eq (σ := σ) hak
    fun j haj hjk ↦ by
      rw [hh.unitSlope_eq_of_isSegment hab haj (lt_of_lt_of_le hjk hkb), ← hσ]
  rw [Nat.card_Ico] at hmain
  rw [hmain, ← hσ]

/-! ### The slope multiset -/

/-- The indices carrying a finite unit slope. -/
def slopeIndices (h : ℕ → WithTop ℝ) : Set ℕ := {j | unitSlope h j ≠ ⊤}

/-- An index contributes a slope exactly when it and its successor both carry points. -/
theorem mem_slopeIndices_iff {j : ℕ} :
    j ∈ slopeIndices h ↔ h j ≠ ⊤ ∧ h (j + 1) ≠ ⊤ := by
  constructor
  · intro hj
    have hx : unitSlope h j ≠ ⊤ := hj
    rw [ne_eq, unitSlope_eq_top_iff, Order.succ_eq_add_one, not_or] at hx
    exact hx
  · intro hj
    show unitSlope h j ≠ ⊤
    rw [ne_eq, unitSlope_eq_top_iff, Order.succ_eq_add_one, not_or]
    exact hj

/-- The unit slopes of a convex sequence occupy an initial segment from the anchor. -/
theorem IsConvexSeq.slopeIndices_eq_Ico (hh : IsConvexSeq h) (hfin : (slopeIndices h).Finite)
    (hne : ∃ i, h i ≠ ⊤) :
    slopeIndices h = Set.Ico (anchor h) (anchor h + (slopeIndices h).ncard) := by
  have hAle : ∀ j ∈ slopeIndices h, anchor h ≤ j := fun j hj ↦
    anchor_le (mem_slopeIndices_iff.1 hj).1
  have hconn : ∀ j ∈ slopeIndices h, ∀ l ∈ slopeIndices h, ∀ m, j ≤ m → m ≤ l →
      m ∈ slopeIndices h := by
    intro j hj l hl m hjm hml
    refine mem_slopeIndices_iff.2 ⟨?_, ?_⟩
    · exact mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 (mem_slopeIndices_iff.1 hj).1)
        (mem_finiteSet.2 (mem_slopeIndices_iff.1 hl).1) ⟨hjm, hml⟩)
    · exact mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 (mem_slopeIndices_iff.1 hj).1)
        (mem_finiteSet.2 (mem_slopeIndices_iff.1 hl).2) ⟨by omega, by omega⟩)
  rcases Set.eq_empty_or_nonempty (slopeIndices h) with hS | hS
  · rw [hS, Set.ncard_empty, add_zero, Set.Ico_self]
  obtain ⟨j₀, hj₀⟩ := hS
  have hAj : anchor h ≤ j₀ := hAle j₀ hj₀
  have hA : anchor h ∈ slopeIndices h := mem_slopeIndices_iff.2 ⟨anchor_mem hne,
    mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 (anchor_mem hne))
      (mem_finiteSet.2 (mem_slopeIndices_iff.1 hj₀).2) ⟨by omega, by omega⟩)⟩
  have hL : sSup (slopeIndices h) ∈ slopeIndices h := Nat.sSup_mem ⟨j₀, hj₀⟩ hfin.bddAbove
  have hAL : anchor h ≤ sSup (slopeIndices h) := hAle _ hL
  have hSeq : slopeIndices h = Set.Icc (anchor h) (sSup (slopeIndices h)) := by
    refine Set.Subset.antisymm (fun m hm ↦ ⟨hAle m hm, le_csSup hfin.bddAbove hm⟩) ?_
    intro m hm
    exact hconn _ hA _ hL m hm.1 hm.2
  have hcard : (slopeIndices h).ncard = sSup (slopeIndices h) + 1 - anchor h := by
    conv_lhs => rw [hSeq]
    rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
  rw [hcard]
  ext m
  constructor
  · intro hm
    have h1 := hAle m hm
    have h2 := le_csSup hfin.bddAbove hm
    exact Set.mem_Ico.2 ⟨h1, by omega⟩
  · intro hm
    rw [Set.mem_Ico] at hm
    exact hconn _ hA _ hL m hm.1 (by omega)

/-- **The slope multiset** of a polygon with finitely many unit slopes: each unit slope, with
multiplicity the number of unit intervals carrying it. Junk `0` when there are infinitely many. -/
noncomputable def slopeMultiset (h : ℕ → WithTop ℝ) : Multiset ℝ :=
  if hfin : (slopeIndices h).Finite then hfin.toFinset.val.map fun j ↦ (unitSlope h j).untop₀
  else 0

/-- The slope multiset has one entry per contributing index. -/
theorem card_slopeMultiset (hfin : (slopeIndices h).Finite) :
    (slopeMultiset h).card = (slopeIndices h).ncard := by
  rw [slopeMultiset, dif_pos hfin, Multiset.card_map, Set.ncard_eq_toFinset_card _ hfin]
  rfl

/-- The multiplicity of `σ` in the slope multiset is the number of unit intervals of slope `σ`. -/
theorem count_slopeMultiset (hfin : (slopeIndices h).Finite) (σ : ℝ) :
    (slopeMultiset h).count σ = Set.ncard {j | unitSlope h j = σ} := by
  have hsub : {j | unitSlope h j = ((σ : ℝ) : WithTop ℝ)} ⊆ slopeIndices h := fun j hj ↦ by
    show unitSlope h j ≠ ⊤
    rw [show unitSlope h j = ((σ : ℝ) : WithTop ℝ) from hj]
    exact WithTop.coe_ne_top
  have hfin2 : {j | unitSlope h j = ((σ : ℝ) : WithTop ℝ)}.Finite := hfin.subset hsub
  have hfeq : hfin.toFinset.filter (fun a ↦ σ = (unitSlope h a).untop₀) = hfin2.toFinset := by
    ext j
    rw [Finset.mem_filter, hfin.mem_toFinset, hfin2.mem_toFinset]
    constructor
    · rintro ⟨hj, hσ⟩
      have hjne : unitSlope h j ≠ ⊤ := hj
      show unitSlope h j = ((σ : ℝ) : WithTop ℝ)
      rw [← WithTop.coe_untop₀_of_ne_top hjne, hσ]
    · intro hσ
      have hσ' : unitSlope h j = ((σ : ℝ) : WithTop ℝ) := hσ
      exact ⟨hsub hσ, by rw [hσ', WithTop.untop₀_coe]⟩
  rw [slopeMultiset, dif_pos hfin, Multiset.count_map, ← Finset.filter_val, hfeq,
    Set.ncard_eq_toFinset_card _ hfin2]
  rfl

/-- The slopes sum to the total height gain over the polygon. -/
theorem IsConvexSeq.anchor_add_sum_slopeMultiset (hh : IsConvexSeq h)
    (hfin : (slopeIndices h).Finite) (hne : ∃ i, h i ≠ ⊤) :
    h (anchor h) + (((slopeMultiset h).sum : ℝ) : WithTop ℝ)
      = h (anchor h + (slopeMultiset h).card) := by
  have hIco := hh.slopeIndices_eq_Ico hfin hne
  rw [card_slopeMultiset hfin]
  have hmemIco : ∀ j, j ∈ slopeIndices h ↔
      j ∈ Set.Ico (anchor h) (anchor h + (slopeIndices h).ncard) := by
    intro j
    constructor
    · intro hj
      have hx : j ∈ Set.Ico (anchor h) (anchor h + (slopeIndices h).ncard) := by
        rw [← hIco]
        exact hj
      exact hx
    · intro hj
      have hx : j ∈ slopeIndices h := by
        rw [hIco]
        exact hj
      exact hx
  have htoFinset : hfin.toFinset = Finset.Ico (anchor h) (anchor h + (slopeIndices h).ncard) := by
    ext j
    rw [Set.Finite.mem_toFinset, Finset.mem_Ico, ← Set.mem_Ico]
    exact hmemIco j
  have hmset : (slopeMultiset h).sum
      = ∑ j ∈ Finset.Ico (anchor h) (anchor h + (slopeIndices h).ncard),
          (unitSlope h j).untop₀ := by
    rw [slopeMultiset, dif_pos hfin, htoFinset]
    rfl
  rcases Nat.eq_zero_or_pos (slopeIndices h).ncard with hn | hn
  · rw [hmset, hn, add_zero, Finset.Ico_self, Finset.sum_empty, WithTop.coe_zero, add_zero]
  have hfinval : ∀ j, anchor h ≤ j → j ≤ anchor h + (slopeIndices h).ncard → h j ≠ ⊤ := by
    intro j h1 h2
    rcases lt_or_ge j (anchor h + (slopeIndices h).ncard) with hj | hj
    · exact (mem_slopeIndices_iff.1 ((hmemIco j).2 (Set.mem_Ico.2 ⟨h1, hj⟩))).1
    · have hjval : j = anchor h + (slopeIndices h).ncard := by omega
      subst hjval
      have hlast : anchor h + (slopeIndices h).ncard - 1 ∈ slopeIndices h :=
        (hmemIco _).2 (Set.mem_Ico.2 ⟨by omega, by omega⟩)
      have hx := (mem_slopeIndices_iff.1 hlast).2
      rwa [show anchor h + (slopeIndices h).ncard - 1 + 1
        = anchor h + (slopeIndices h).ncard by omega] at hx
  have htel := eq_add_sum_unitSlope (h := h) (a := anchor h)
    (k := anchor h + (slopeIndices h).ncard) (by omega) hfinval
  rw [htel, hmset]

/-- A finitely supported sequence has a polygon with finitely many unit slopes, exactly
`last - anchor` of them. -/
theorem IsNewtonPolygonOf.slopeIndices_finite (hh : IsNewtonPolygonOf v h)
    (hfin : (finiteSet v).Finite) : (slopeIndices h).Finite := by
  rcases Set.eq_empty_or_nonempty (finiteSet v) with hv | hv
  · have htop : ∀ k, h k = ⊤ := fun k ↦ hh.eq_top_of_forall_eq_top fun j _ ↦ by
      by_contra hc
      exact Set.eq_empty_iff_forall_notMem.1 hv j (mem_finiteSet.2 hc)
    refine Set.Finite.subset (Set.finite_empty) ?_
    intro j hj
    exact absurd (htop j) (mem_slopeIndices_iff.1 hj).1
  · refine Set.Finite.subset (Set.finite_Iio (sSup (finiteSet v) + 1)) ?_
    intro j hj
    by_contra hc
    rw [Set.mem_Iio, not_lt] at hc
    refine (mem_slopeIndices_iff.1 hj).1 (hh.eq_top_of_forall_le (n := j) fun k hk ↦ ?_)
    by_contra hvk
    have : k ≤ sSup (finiteSet v) := le_csSup hfin.bddAbove (mem_finiteSet.2 hvk)
    omega

/-! ### Purity and the first break -/

/-- `h` is *pure of slope `m`*: it has at least one unit slope, and every unit slope is `m`.
Equivalently, the polygon is a single segment of slope `m`. -/
def IsPure (h : ℕ → WithTop ℝ) (m : ℝ) : Prop :=
  (∃ j, unitSlope h j ≠ ⊤) ∧ ∀ j, unitSlope h j ≠ ⊤ → unitSlope h j = m

/-- **Purity, on the multiset**: a polygon has a single slope exactly when its slope multiset is a
nonempty constant multiset. -/
theorem isPure_iff_slopeMultiset (hfin : (slopeIndices h).Finite) (m : ℝ) :
    IsPure h m ↔ 0 < (slopeMultiset h).card ∧
      slopeMultiset h = Multiset.replicate (slopeMultiset h).card m := by
  have hmem : ∀ b : ℝ, b ∈ slopeMultiset h ↔ ∃ j ∈ hfin.toFinset, (unitSlope h j).untop₀ = b := by
    intro b
    rw [slopeMultiset, dif_pos hfin, Multiset.mem_map]
    exact ⟨fun ⟨j, hj, hb⟩ ↦ ⟨j, hj, hb⟩, fun ⟨j, hj, hb⟩ ↦ ⟨j, hj, hb⟩⟩
  rw [Multiset.eq_replicate]
  constructor
  · rintro ⟨⟨j, hj⟩, hall⟩
    refine ⟨Multiset.card_pos_iff_exists_mem.2
      ⟨_, (hmem ((unitSlope h j).untop₀)).2 ⟨j, hfin.mem_toFinset.2 hj, rfl⟩⟩, rfl,
      fun b hb ↦ ?_⟩
    obtain ⟨i, hi, hb'⟩ := (hmem b).1 hb
    have hine : unitSlope h i ≠ ⊤ := hfin.mem_toFinset.1 hi
    rw [← hb', hall i hine, WithTop.untop₀_coe]
  · rintro ⟨hpos, -, hall⟩
    obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
    obtain ⟨j, hj, -⟩ := (hmem b).1 hb
    refine ⟨⟨j, hfin.mem_toFinset.1 hj⟩, fun i hi ↦ ?_⟩
    have hval := hall _ ((hmem ((unitSlope h i).untop₀)).2 ⟨i, hfin.mem_toFinset.2 hi, rfl⟩)
    rw [← hval, WithTop.coe_untop₀_of_ne_top hi]

/-- `h` has *first break* of slope `m` and length `l`: its first `l` unit slopes are `m`, and the
next one is not. -/
def HasFirstBreak (h : ℕ → WithTop ℝ) (m : ℝ) (l : ℕ) : Prop :=
  0 < l ∧ (∀ j < l, unitSlope h (anchor h + j) = m) ∧ unitSlope h (anchor h + l) ≠ m

/-- **The first break, read off the points** (roadmap §0.4.4): the Newton polygon of `v` has first
break of slope `m` and length `l` exactly when the line of slope `m` through the anchor lies on or
below every point, passes through the point `l` steps later, and some *strictly steeper* line
through that point lies on or below every later point.

⚠ The roadmap's clause asks only that later points lie strictly above the first line; that is not
enough — points approaching the line asymptotically (`v k = m k + 1/k`) satisfy it while the polygon
is an infinite ray of slope `m` with no break. The steeper line is the honest condition. -/
theorem IsNewtonPolygonOf.hasFirstBreak_iff (hh : IsNewtonPolygonOf v h) (hv : ∃ i, v i ≠ ⊤)
    (m : ℝ) (l : ℕ) :
    HasFirstBreak h m l ↔ 0 < l ∧
      (∀ k, anchor h ≤ k → v (anchor h) + (k - anchor h : ℕ) • (m : WithTop ℝ) ≤ v k) ∧
      v (anchor h + l) = v (anchor h) + l • (m : WithTop ℝ) ∧
      ∃ m' : ℝ, m < m' ∧ ∀ k, anchor h + l ≤ k →
        v (anchor h + l) + (k - (anchor h + l) : ℕ) • (m' : WithTop ℝ) ≤ v k := by
  have hhne : ∃ i, h i ≠ ⊤ := hv.imp fun _ hi ↦ hh.ne_top_of_ne_top hi
  have hAf : h (anchor h) ≠ ⊤ := anchor_mem hhne
  have hA : h (anchor h) = v (anchor h) := hh.eq_of_isVertex (isVertex_anchor hhne)
  have hvAf : v (anchor h) ≠ ⊤ := by
    rw [← hA]
    exact hAf
  obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 hvAf
  have hAy : h (anchor h) = ((y : ℝ) : WithTop ℝ) := hA.trans hy.symm
  constructor
  · rintro ⟨hl, hslopes, hbreak⟩
    have hsA : unitSlope h (anchor h) = ((m : ℝ) : WithTop ℝ) := by
      have hx := hslopes 0 hl
      rwa [add_zero] at hx
    have hcond2 : ∀ k, anchor h ≤ k →
        v (anchor h) + (k - anchor h : ℕ) • ((m : ℝ) : WithTop ℝ) ≤ v k := by
      intro k hk
      refine le_trans ?_ (hh.le_points k)
      rw [← hA, ← hsA, ← Nat.card_Ico]
      exact hh.convex.add_nsmul_unitSlope_le hAf hk
    have hslopes' : ∀ j, anchor h ≤ j → j < anchor h + l →
        unitSlope h j = ((m : ℝ) : WithTop ℝ) := by
      intro j h1 h2
      have hx := hslopes (j - anchor h) (by omega)
      rwa [show anchor h + (j - anchor h) = j by omega] at hx
    have hAl : h (anchor h + l) = h (anchor h) + l • ((m : ℝ) : WithTop ℝ) := by
      have hx := eq_add_nsmul_of_forall_unitSlope_eq (by omega : anchor h ≤ anchor h + l) hslopes'
      rwa [Nat.card_Ico, show anchor h + l - anchor h = l by omega] at hx
    have hAlf : h (anchor h + l) ≠ ⊤ := by
      rw [hAl, hAy, ← WithTop.coe_nsmul, ← WithTop.coe_add]
      exact WithTop.coe_ne_top
    have hprevslope : unitSlope h (anchor h + l - 1) = ((m : ℝ) : WithTop ℝ) :=
      hslopes' _ (by omega) (by omega)
    have hprevf : h (anchor h + l - 1) ≠ ⊤ := by
      intro hc
      rw [unitSlope_eq_top_iff.2 (Or.inl hc)] at hprevslope
      exact WithTop.coe_ne_top hprevslope.symm
    have hstrict : ((m : ℝ) : WithTop ℝ) < unitSlope h (anchor h + l) := by
      have hmono : unitSlope h (anchor h + l - 1) ≤ unitSlope h (anchor h + l) :=
        hh.convex.monotoneOn (mem_finiteSet.2 hprevf) (mem_finiteSet.2 hAlf) (by omega)
      rw [hprevslope] at hmono
      exact lt_of_le_of_ne hmono (Ne.symm hbreak)
    have hvertex : IsVertex h (anchor h + l) := by
      refine ⟨hAlf, Or.inr ?_⟩
      rw [hprevslope]
      exact hstrict
    refine ⟨hl, hcond2, ?_, ?_⟩
    · rw [← hh.eq_of_isVertex hvertex, hAl, hA]
    · by_cases hslopeAl : unitSlope h (anchor h + l) = ⊤
      · refine ⟨m + 1, by linarith, fun k hk ↦ ?_⟩
        rcases eq_or_lt_of_le hk with rfl | hlt
        · simp only [tsub_self, WithTop.coe_add, WithTop.coe_one, zero_nsmul, add_zero,
            Std.le_refl]
        · have hsucc : h (anchor h + l + 1) = ⊤ := by
            rcases unitSlope_eq_top_iff.1 hslopeAl with hx | hx
            · exact absurd hx hAlf
            · rwa [Order.succ_eq_add_one] at hx
          have hhk : h k = ⊤ := hh.convex.eq_top_of_le hAlf (by omega) hsucc (by omega)
          have hvk : v k = ⊤ := by
            rw [← top_le_iff, ← hhk]
            exact hh.le_points k
          rw [hvk]
          exact le_top
      · obtain ⟨m'', hm''⟩ := WithTop.ne_top_iff_exists.1 hslopeAl
        refine ⟨m'', ?_, fun k hk ↦ ?_⟩
        · rw [← hm'', WithTop.coe_lt_coe] at hstrict
          exact hstrict
        · refine le_trans ?_ (hh.le_points k)
          rw [← hh.eq_of_isVertex hvertex, hm'', ← Nat.card_Ico]
          exact hh.convex.add_nsmul_unitSlope_le hAlf hk
  · rintro ⟨hl, hcond2, hcond3, m', hmm', hcond4⟩
    have hvtop : ∀ k, k < anchor h → v k = ⊤ := by
      intro k hk
      rw [hh.anchor_eq_sInf hv] at hk
      exact not_not.1 (Nat.notMem_of_lt_sInf hk)
    have hline1 : ∀ k : ℕ, ((y + m * ((k : ℝ) - anchor h) : ℝ) : WithTop ℝ) ≤ v k := by
      intro k
      rcases le_or_gt (anchor h) k with hk | hk
      · have hx := hcond2 k hk
        rw [← hy, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul, Nat.cast_sub hk] at hx
        calc ((y + m * ((k : ℝ) - anchor h) : ℝ) : WithTop ℝ)
            = ((y + (((k : ℝ) - anchor h)) * m : ℝ) : WithTop ℝ) := by
              congr 1
              ring
          _ ≤ v k := hx
      · rw [hvtop k hk]
        exact le_top
    have hconv1 : IsConvexSeq (fun k : ℕ ↦ ((y + m * ((k : ℝ) - anchor h) : ℝ) : WithTop ℝ)) := by
      have heq : (fun k : ℕ ↦ ((y + m * ((k : ℝ) - anchor h) : ℝ) : WithTop ℝ))
          = fun k : ℕ ↦ (((y - m * anchor h) + m * k : ℝ) : WithTop ℝ) := by
        funext k
        congr 1
        ring
      rw [heq]
      exact isConvexSeq_affine _ _
    have hge1 : ∀ k : ℕ, ((y + m * ((k : ℝ) - anchor h) : ℝ) : WithTop ℝ) ≤ h k :=
      fun k ↦ hh.greatest _ hconv1 hline1 k
    have hvAl : v (anchor h + l) = ((y + m * l : ℝ) : WithTop ℝ) := by
      rw [hcond3, ← hy, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
      congr 1
      ring
    have hAlf : h (anchor h + l) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [hvAl]; exact WithTop.coe_ne_top) (hh.le_points _)
    have hAll : h (anchor h + l) = ((y + m * l : ℝ) : WithTop ℝ) := by
      refine le_antisymm (by rw [← hvAl]; exact hh.le_points _) ?_
      have hx := hge1 (anchor h + l)
      rwa [show ((y + m * (((anchor h + l : ℕ) : ℝ) - anchor h) : ℝ) : WithTop ℝ)
        = ((y + m * l : ℝ) : WithTop ℝ) by congr 1; push_cast; ring] at hx
    have hfinAl : ∀ j, anchor h ≤ j → j ≤ anchor h + l → h j ≠ ⊤ := fun j h1 h2 ↦
      mem_finiteSet.1 (hh.convex.ordConnected.out (mem_finiteSet.2 hAf) (mem_finiteSet.2 hAlf)
        ⟨h1, h2⟩)
    have hslopefin : ∀ j, anchor h ≤ j → j < anchor h + l → unitSlope h j ≠ ⊤ := by
      intro j h1 h2
      rw [ne_eq, unitSlope_eq_top_iff, Order.succ_eq_add_one, not_or]
      exact ⟨hfinAl j h1 (by omega), hfinAl (j + 1) (by omega) (by omega)⟩
    have hsAle : m ≤ (unitSlope h (anchor h)).untop₀ := by
      have hstep : h (anchor h) + unitSlope h (anchor h) = h (anchor h + 1) := by
        rw [← Order.succ_eq_add_one]
        exact add_unitSlope hAf
      have hx := hge1 (anchor h + 1)
      rw [← hstep, hAy,
        ← WithTop.coe_untop₀_of_ne_top (hslopefin (anchor h) le_rfl (by omega)),
        ← WithTop.coe_add, show ((y + m * (((anchor h + 1 : ℕ) : ℝ) - anchor h) : ℝ) : WithTop ℝ)
          = ((y + m : ℝ) : WithTop ℝ) by congr 1; push_cast; ring, WithTop.coe_le_coe] at hx
      linarith
    have hmono : ∀ j, anchor h ≤ j → j < anchor h + l → m ≤ (unitSlope h j).untop₀ := by
      intro j h1 h2
      refine le_trans hsAle (WithTop.untop₀_le_untop₀ (hslopefin j h1 h2) ?_)
      exact hh.convex.monotoneOn (mem_finiteSet.2 hAf) (mem_finiteSet.2 (hfinAl j h1 (by omega))) h1
    have hsum : (∑ j ∈ Finset.Ico (anchor h) (anchor h + l), (unitSlope h j).untop₀) = l * m := by
      have htel := eq_add_sum_unitSlope (a := anchor h) (k := anchor h + l) (by omega) hfinAl
      rw [hAll, hAy, ← WithTop.coe_add, WithTop.coe_inj] at htel
      linarith
    have hterm : ∀ j ∈ Finset.Ico (anchor h) (anchor h + l), (unitSlope h j).untop₀ = m := by
      have hzero : ∑ j ∈ Finset.Ico (anchor h) (anchor h + l),
          ((unitSlope h j).untop₀ - m) = 0 := by
        rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Nat.card_Ico,
          show anchor h + l - anchor h = l by omega, nsmul_eq_mul]
        ring
      have hnn : ∀ j ∈ Finset.Ico (anchor h) (anchor h + l), 0 ≤ (unitSlope h j).untop₀ - m := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        have := hmono j hj.1 hj.2
        linarith
      intro j hj
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero j hj
      linarith
    have hslopes : ∀ j, j < l → unitSlope h (anchor h + j) = ((m : ℝ) : WithTop ℝ) := by
      intro j hj
      have hmemj : anchor h + j ∈ Finset.Ico (anchor h) (anchor h + l) :=
        Finset.mem_Ico.2 ⟨by omega, by omega⟩
      rw [← WithTop.coe_untop₀_of_ne_top (hslopefin _ (by omega) (by omega)), hterm _ hmemj]
    refine ⟨hl, hslopes, ?_⟩
    intro hcon
    -- the steeper line through `(anchor h + l, y + m l)`
    have hline2 : ∀ k : ℕ,
        (((y + m * l) + m' * ((k : ℝ) - (anchor h + l)) : ℝ) : WithTop ℝ) ≤ v k := by
      intro k
      rcases le_or_gt (anchor h + l) k with hk | hk
      · have hx := hcond4 k hk
        rw [hvAl, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul, Nat.cast_sub hk] at hx
        refine le_trans (le_of_eq ?_) hx
        congr 1
        push_cast
        ring
      · refine le_trans ?_ (hline1 k)
        rw [WithTop.coe_le_coe]
        have hkl : (k : ℝ) - (anchor h + l) < 0 := by
          have hx : (k : ℝ) < ((anchor h + l : ℕ) : ℝ) := Nat.cast_lt.2 hk
          push_cast at hx
          linarith
        nlinarith [mul_nonneg (sub_nonneg.2 hmm'.le) (neg_nonneg.2 hkl.le)]
    have hconv2 : IsConvexSeq
        (fun k : ℕ ↦ (((y + m * l) + m' * ((k : ℝ) - (anchor h + l)) : ℝ) : WithTop ℝ)) := by
      have heq : (fun k : ℕ ↦ (((y + m * l) + m' * ((k : ℝ) - (anchor h + l)) : ℝ) : WithTop ℝ))
          = fun k : ℕ ↦ ((((y + m * l) - m' * (anchor h + l)) + m' * k : ℝ) : WithTop ℝ) := by
        funext k
        congr 1
        ring
      rw [heq]
      exact isConvexSeq_affine _ _
    have hgesup := hh.greatest _ (hconv1.sup hconv2)
      (fun k ↦ by
        simp only [Pi.sup_apply]
        exact sup_le (hline1 k) (hline2 k)) (anchor h + l + 1)
    have hright : (((y + m * l) + m' : ℝ) : WithTop ℝ) ≤ h (anchor h + l + 1) := by
      refine le_trans (le_of_eq ?_) (le_trans (le_sup_right (a :=
        ((y + m * (((anchor h + l + 1 : ℕ) : ℝ) - anchor h) : ℝ) : WithTop ℝ))) hgesup)
      congr 1
      push_cast
      ring
    have hleft : h (anchor h + l + 1) = (((y + m * l) + m : ℝ) : WithTop ℝ) := by
      have hstep : h (anchor h + l) + unitSlope h (anchor h + l) = h (anchor h + l + 1) := by
        rw [← Order.succ_eq_add_one]
        exact add_unitSlope hAlf
      rw [← hstep, hcon, hAll, ← WithTop.coe_add]
    rw [hleft, WithTop.coe_le_coe] at hright
    linarith

/-! ### The terminal ray -/

/-- `h` *ends in a ray of slope `m`*: its unit slopes are eventually the constant `m` (roadmap
§0.3.2). This is the face of infinite length: `faceLeft h m` is honest and `faceRight h m` is junk
exactly here, and for the polygon of a power series it is the case of finite radius of convergence
`b ^ m` with the supremum of the slopes attained. -/
def EndsInRay (h : ℕ → WithTop ℝ) (m : ℝ) : Prop := ∃ N, ∀ j, N ≤ j → unitSlope h j = m

/-- A sequence ending in a ray is finite from the ray on. -/
theorem EndsInRay.ne_top {m : ℝ} (hm : EndsInRay h m) : ∃ N, ∀ j, N ≤ j → h j ≠ ⊤ := by
  obtain ⟨N, hN⟩ := hm
  refine ⟨N, fun j hj hc ↦ ?_⟩
  have hx : unitSlope h j = ⊤ := unitSlope_eq_top_iff.2 (Or.inl hc)
  rw [hN j hj] at hx
  exact WithTop.coe_ne_top hx

/-- A convex sequence ends in a ray of slope `m` exactly when `m` is a unit slope and no unit slope
at a finite index exceeds `m`. (The unit slopes before the anchor are `⊤`, hence the finiteness
hypothesis.) -/
theorem IsConvexSeq.endsInRay_iff (hh : IsConvexSeq h) (m : ℝ) :
    EndsInRay h m ↔ (∀ j, h j ≠ ⊤ → unitSlope h j ≤ m) ∧ ∃ j, unitSlope h j = m := by
  constructor
  · rintro ⟨N, hN⟩
    have hfinN : ∀ j, N ≤ j → h j ≠ ⊤ := by
      intro j hj hc
      have hx : unitSlope h j = ⊤ := unitSlope_eq_top_iff.2 (Or.inl hc)
      rw [hN j hj] at hx
      exact WithTop.coe_ne_top hx
    refine ⟨fun j hj ↦ ?_, ⟨N, hN N le_rfl⟩⟩
    rcases le_or_gt N j with hjN | hjN
    · exact le_of_eq (hN j hjN)
    · exact (hh.monotoneOn (mem_finiteSet.2 hj) (mem_finiteSet.2 (hfinN N le_rfl)) hjN.le).trans
        (le_of_eq (hN N le_rfl))
  · rintro ⟨hbound, j₀, hj₀⟩
    have hj₀ne : h j₀ ≠ ⊤ := by
      intro hc
      rw [unitSlope_eq_top_iff.2 (Or.inl hc)] at hj₀
      exact WithTop.coe_ne_top hj₀.symm
    have hfin : ∀ i, j₀ ≤ i → h i ≠ ⊤ := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base => exact hj₀ne
      | succ p hp ih =>
          intro hc
          have hx : unitSlope h p = ⊤ := by
            rw [unitSlope_eq_top_iff, Order.succ_eq_add_one]
            exact Or.inr hc
          have hy := hbound p ih
          rw [hx] at hy
          exact WithTop.coe_ne_top (top_le_iff.1 hy)
    refine ⟨j₀, fun j hj ↦ le_antisymm (hbound j (hfin j hj)) ?_⟩
    rw [← hj₀]
    exact hh.monotoneOn (mem_finiteSet.2 hj₀ne) (mem_finiteSet.2 (hfin j hj)) hj

/-- On a terminal ray of slope `m`, no unit slope at a finite index exceeds `m`. -/
theorem EndsInRay.unitSlope_le (hh : IsConvexSeq h) {m : ℝ} (hm : EndsInRay h m) {j : ℕ}
    (hj : h j ≠ ⊤) : unitSlope h j ≤ m := ((hh.endsInRay_iff m).1 hm).1 j hj

/-- For a sequence anchored at `0` ending in a ray of slope `m`, the set defining `faceRight h m` is
empty: the face of slope `m` has no right endpoint. -/
theorem EndsInRay.setOf_lt_unitSlope_eq_empty (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) {m : ℝ}
    (hm : EndsInRay h m) : {j | (m : WithTop ℝ) < unitSlope h j} = ∅ := by
  obtain ⟨N, hN⟩ := hm.ne_top
  refine Set.eq_empty_iff_forall_notMem.2 fun j hj ↦ ?_
  have hjf : h j ≠ ⊤ := mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 h0)
    (mem_finiteSet.2 (hN (max j N) (le_max_right _ _))) ⟨Nat.zero_le _, le_max_left _ _⟩)
  exact absurd (hm.unitSlope_le hh hjf) (not_le.2 hj)

/-! ### Truncation -/

/-- The points of `v` with index at most `n`. -/
def truncate (v : ℕ → WithTop ℝ) (n : ℕ) : ℕ → WithTop ℝ := fun k ↦ if k ≤ n then v k else ⊤

/-- Removing points can only raise the hull. -/
theorem newtonPolygon_le_newtonPolygon_truncate (hv : IsAdmissible v) (n k : ℕ) :
    newtonPolygon v k ≤ newtonPolygon (truncate v n) k := by
  refine newtonPolygon_mono (exists_isConvexMinorant_iff_isAdmissible.2 hv) (fun j ↦ ?_) k
  simp only [truncate]
  split_ifs with hj
  · exact le_rfl
  · exact le_top

/-- **Truncation does not change the polygon up to a retained vertex** (roadmap §0.4.5,
strengthened: any vertex `V ≤ n`, not only the last): the polygons of `v` and of `truncate v n`
agree at every index `≤ V`, because the truncated polygon is a convex minorant passing below the
vertices of the full one,
hence below its chords, and the full polygon is below the truncated one by monotonicity. -/
theorem newtonPolygon_truncate_eq (hv : IsAdmissible v) {n V : ℕ}
    (hV : IsVertex (newtonPolygon v) V) (hVn : V ≤ n) {k : ℕ} (hk : k ≤ V) :
    newtonPolygon (truncate v n) k = newtonPolygon v k := by
  have hvne : ∃ g, IsConvexMinorant v g := exists_isConvexMinorant_iff_isAdmissible.2 hv
  have hP : IsNewtonPolygonOf v (newtonPolygon v) := isNewtonPolygonOf_newtonPolygon hvne
  have htadm : IsAdmissible (truncate v n) := by
    refine isAdmissible_iff_exists_line.2 ?_
    obtain ⟨y, σ, hline⟩ := isAdmissible_iff_exists_line.1 hv
    refine ⟨y, σ, fun j ↦ ?_⟩
    simp only [truncate]
    split_ifs with hj
    · exact hline j
    · exact le_top
  have hT : IsNewtonPolygonOf (truncate v n) (newtonPolygon (truncate v n)) :=
    isNewtonPolygonOf_newtonPolygon (exists_isConvexMinorant_iff_isAdmissible.2 htadm)
  have hge : ∀ j, newtonPolygon v j ≤ newtonPolygon (truncate v n) j := fun j ↦
    newtonPolygon_le_newtonPolygon_truncate hv n j
  have htrval : ∀ j, j ≤ n → truncate v n j = v j := by
    intro j hj
    simp only [truncate]
    rw [if_pos hj]
  -- the two polygons agree at the retained vertex `V`
  have hPV : newtonPolygon v V = v V := hP.eq_of_isVertex hV
  have hTV : newtonPolygon (truncate v n) V = newtonPolygon v V := by
    refine le_antisymm ?_ (hge V)
    rw [hPV, ← htrval V hVn]
    exact hT.le_points V
  -- glue: the truncated polygon up to `V`, the full polygon after it
  set g : ℕ → WithTop ℝ :=
    fun j ↦ if j ≤ V then newtonPolygon (truncate v n) j else newtonPolygon v j with hgdef
  have hglow : ∀ j, j ≤ V → g j = newtonPolygon (truncate v n) j := fun j hj ↦ by
    simp only [hgdef]
    rw [if_pos hj]
  have hghigh : ∀ j, V < j → g j = newtonPolygon v j := fun j hj ↦ by
    simp only [hgdef]
    rw [if_neg (not_le.2 hj)]
  have hgP : ∀ j, newtonPolygon v j ≤ g j := by
    intro j
    rcases le_or_gt j V with hj | hj
    · rw [hglow j hj]
      exact hge j
    · rw [hghigh j hj]
  have hgmin : ∀ j, g j ≤ v j := by
    intro j
    rcases le_or_gt j V with hj | hj
    · rw [hglow j hj, ← htrval j (hj.trans hVn)]
      exact hT.le_points j
    · rw [hghigh j hj]
      exact hP.le_points j
  have hTVne : newtonPolygon (truncate v n) V ≠ ⊤ := by
    rw [hTV]
    exact hV.1
  have hgconv : IsConvexSeq g := by
    have hord : (finiteSet g).OrdConnected := by
      constructor
      intro a ha c hc b hb
      refine mem_finiteSet.2 ?_
      rcases le_or_gt b V with hbV | hbV
      · rw [hglow b hbV]
        have haT : newtonPolygon (truncate v n) a ≠ ⊤ := by
          have hx := mem_finiteSet.1 ha
          rwa [hglow a (hb.1.trans hbV)] at hx
        exact mem_finiteSet.1 (hT.convex.ordConnected.out (mem_finiteSet.2 haT)
          (mem_finiteSet.2 hTVne) ⟨hb.1, hbV⟩)
      · rw [hghigh b hbV]
        exact mem_finiteSet.1 (hP.convex.ordConnected.out
          (mem_finiteSet.2 (ne_top_of_le_ne_top (mem_finiteSet.1 ha) (hgP a)))
          (mem_finiteSet.2 (ne_top_of_le_ne_top (mem_finiteSet.1 hc) (hgP c))) hb)
    refine (isConvexSeq_iff_midpoint hord).2 fun j ↦ ?_
    simp only [Order.succ_eq_add_one]
    rcases le_or_gt (j + 1 + 1) V with hj2 | hj2
    · rw [hglow j (by omega), hglow (j + 1) (by omega), hglow (j + 1 + 1) hj2]
      simpa only [Order.succ_eq_add_one] using hT.convex.midpoint j
    rcases le_or_gt (j + 1) V with hj1 | hj1
    · -- `j + 1 ≤ V < j + 2`, so `j + 1 = V`
      have hjV : j + 1 = V := by omega
      rw [hglow j (by omega), hglow (j + 1) hj1, hghigh (j + 1 + 1) hj2, hjV, hTV]
      have hmid := hP.convex.midpoint j
      simp only [Order.succ_eq_add_one] at hmid
      rw [hjV] at hmid
      exact le_trans hmid (add_le_add (hge j) le_rfl)
    · -- `V < j + 1`
      rcases le_or_gt j V with hjV | hjV
      · have hjV' : j = V := by omega
        rw [hglow j hjV, hghigh (j + 1) hj1, hghigh (j + 1 + 1) (by omega), hjV', hTV, ← hjV']
        simpa only [Order.succ_eq_add_one] using hP.convex.midpoint j
      · rw [hghigh j hjV, hghigh (j + 1) hj1, hghigh (j + 1 + 1) (by omega)]
        simpa only [Order.succ_eq_add_one] using hP.convex.midpoint j
  refine le_antisymm ?_ (hge k)
  rw [← hglow k hk]
  exact hP.greatest g hgconv hgmin k

end NewtonPolygon
