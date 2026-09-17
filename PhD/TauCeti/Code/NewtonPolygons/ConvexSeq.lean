/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Convex sequences of extended reals

A *convex sequence* is a function `h : ι → WithTop ℝ` on a discrete linear order `ι` — `ℕ` for
polynomials and power series, `ℤ` for Laurent series — whose finiteness set `{j | h j ≠ ⊤}` is an
interval and whose increments `h (succ j) - h j` are monotone on it. The value `⊤` means "nothing
here", so a convex sequence is a convex function on an interval of `ι`, extended by `⊤` on both
sides. This is the discrete convexity that Newton polygons are made of, stated with no reference to
them.

The index type is abstract: `[LinearOrder ι] [SuccOrder ι]` for the definitions, and additionally
`[IsSuccArchimedean ι] [LocallyFiniteOrder ι] [NoMaxOrder ι]` wherever a proof walks along
successors or sums over an interval. `ℕ` and `ℤ` satisfy all five; on both, `Order.succ j = j + 1`
and `(Finset.Ico a c).card` is `c - a` (`Nat.card_Ico`, `Int.card_Ico`). Statements that need a
coordinate on the index type (affine sequences, the `ConvexOn` bridge) are stated for `ℕ` at the
end of the file and for `ℤ` in `Int.lean`.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §0.1. Tau Ceti home:
`TauCeti/Analysis/Convex/Sequence.lean`.

## Main definitions

* `NewtonPolygon.unitSlope h j` — the increment `h (succ j) - h j`, taken to be `⊤` as soon as
  either value is `⊤`.
* `NewtonPolygon.finiteSet h` — the finiteness set `{j | h j ≠ ⊤}`.
* `NewtonPolygon.IsConvexSeq h` — the finiteness set is order-connected and the unit slopes are
  monotone on it.

## Main results

* `NewtonPolygon.isConvexSeq_iff_midpoint` — the midpoint form
  `h (succ k) + h (succ k) ≤ h k + h (succ (succ k))`.
* `NewtonPolygon.IsConvexSeq.le_chord` — the chord inequality (discrete Jensen), division-free.
* `NewtonPolygon.IsConvexSeq.iSup` — the pointwise supremum of a family of convex sequences is
  convex: the fact that makes the greatest convex minorant exist.
* `NewtonPolygon.IsConvexSeq.exists_convexOn` — the bridge to Mathlib's `ConvexOn`, on `ℕ`.
-/

open scoped Classical
open Order

namespace NewtonPolygon

section Defs

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι] {h g : ι → WithTop ℝ}

/-! ### Unit slopes and the finiteness set -/

/-- The `j`-th *unit slope* of `h`: the increment `h (succ j) - h j`, with the convention that it is
`⊤` as soon as either end is `⊤`. On the finiteness interval of a convex sequence these are its
slopes on the unit intervals; `⊤` marks the last finite index. -/
noncomputable def unitSlope (h : ι → WithTop ℝ) (j : ι) : WithTop ℝ :=
  if h j = ⊤ ∨ h (succ j) = ⊤ then ⊤ else (((h (succ j)).untop₀ - (h j).untop₀ : ℝ) : WithTop ℝ)

/-- The finiteness set of `h`. -/
def finiteSet (h : ι → WithTop ℝ) : Set ι := {j | h j ≠ ⊤}

omit [LinearOrder ι] [SuccOrder ι] in
/-- Membership in the finiteness set is finiteness of the value. -/
@[simp] theorem mem_finiteSet {j : ι} : j ∈ finiteSet h ↔ h j ≠ ⊤ := Iff.rfl

/-- The unit slope is `⊤` exactly when one of the two points it joins is missing. -/
theorem unitSlope_eq_top_iff {j : ι} : unitSlope h j = ⊤ ↔ h j = ⊤ ∨ h (succ j) = ⊤ := by
  rw [unitSlope]
  split_ifs with hc
  · exact iff_of_true rfl hc
  · exact iff_of_false WithTop.coe_ne_top hc

/-- Between two points the unit slope is the difference of the heights. -/
theorem unitSlope_of_ne_top {j : ι} (hj : h j ≠ ⊤) (hj1 : h (succ j) ≠ ⊤) :
    unitSlope h j = (((h (succ j)).untop₀ - (h j).untop₀ : ℝ) : WithTop ℝ) := by
  rw [unitSlope, if_neg (not_or.2 ⟨hj, hj1⟩)]

/-- The increment identity: stepping one unit right adds the unit slope. -/
theorem add_unitSlope {j : ι} (hj : h j ≠ ⊤) : h j + unitSlope h j = h (succ j) := by
  by_cases hj1 : h (succ j) = ⊤
  · rw [hj1, unitSlope_eq_top_iff.2 (Or.inr hj1), add_top]
  · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hj
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 hj1
    rw [unitSlope_of_ne_top hj hj1, ← hx, ← hy]
    simp only [WithTop.untop₀_coe, ← WithTop.coe_add, WithTop.coe_inj]
    ring

/-- The converse of `add_unitSlope`: a one-step increment by a real identifies the unit slope. -/
theorem unitSlope_eq_of_succ_eq_add {j : ι} {c : ℝ} (hj : h j ≠ ⊤)
    (hc : h (succ j) = h j + (c : WithTop ℝ)) : unitSlope h j = (c : WithTop ℝ) := by
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hj
  rw [unitSlope_of_ne_top hj (by rw [hc, ← hx, ← WithTop.coe_add]; exact WithTop.coe_ne_top), hc,
    ← hx, ← WithTop.coe_add]
  simp only [WithTop.untop₀_coe]
  rw [WithTop.coe_inj]
  ring

/-! ### Convex sequences -/

/-- A sequence of extended reals is *convex* when its finiteness set is an interval and its unit
slopes are monotone on it (roadmap §0.1.1). -/
structure IsConvexSeq (h : ι → WithTop ℝ) : Prop where
  /-- The finiteness set is an interval: no `⊤` strictly between two finite values. -/
  ordConnected : (finiteSet h).OrdConnected
  /-- The unit slopes are monotone on the finiteness set. -/
  monotoneOn : MonotoneOn (unitSlope h) (finiteSet h)

/-- Once the sequence is `⊤` to the right of a finite value it stays `⊤`. -/
theorem IsConvexSeq.eq_top_of_le (hh : IsConvexSeq h) {a i j : ι} (ha : h a ≠ ⊤) (hai : a ≤ i)
    (hi : h i = ⊤) (hij : i ≤ j) : h j = ⊤ := by
  by_contra hj
  exact hh.ordConnected.out (mem_finiteSet.2 ha) (mem_finiteSet.2 hj) ⟨hai, hij⟩ hi

/-- The midpoint inequality, valid at every index (the `⊤` cases are vacuous or excluded by
order-connectedness). -/
theorem IsConvexSeq.midpoint (hh : IsConvexSeq h) (k : ι) :
    h (succ k) + h (succ k) ≤ h k + h (succ (succ k)) := by
  by_cases hk : h k = ⊤
  · rw [hk, top_add]
    exact le_top
  by_cases hk2 : h (succ (succ k)) = ⊤
  · rw [hk2, add_top]
    exact le_top
  have hk1 : h (succ k) ≠ ⊤ :=
    mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 hk) (mem_finiteSet.2 hk2)
      ⟨le_succ k, le_succ (succ k)⟩)
  have hmono := hh.monotoneOn (mem_finiteSet.2 hk) (mem_finiteSet.2 hk1) (le_succ k)
  rw [unitSlope_of_ne_top hk hk1, unitSlope_of_ne_top hk1 hk2, WithTop.coe_le_coe] at hmono
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hk
  obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 hk1
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hk2
  rw [← hx, ← hy, ← hz] at hmono ⊢
  simp only [WithTop.untop₀_coe] at hmono
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

/-- The constant sequence `⊤` is convex. -/
theorem isConvexSeq_top : IsConvexSeq fun _ : ι ↦ (⊤ : WithTop ℝ) := by
  have hfs : finiteSet (fun _ : ι ↦ (⊤ : WithTop ℝ)) = ∅ := by
    ext j
    simp only [finiteSet, ne_eq, not_true_eq_false, Set.ofPred_false, Set.mem_empty_iff_false]
  refine ⟨by rw [hfs]; exact Set.ordConnected_empty, ?_⟩
  rw [hfs]
  intro a ha
  exact absurd ha (Set.notMem_empty a)

end Defs

section Sums

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι] [IsSuccArchimedean ι] [LocallyFiniteOrder ι]
  [NoMaxOrder ι] {h g : ι → WithTop ℝ}

/-- On a stretch of equal unit slopes a sequence is affine (no convexity needed). -/
theorem eq_add_nsmul_of_forall_unitSlope_eq {a k : ι} {σ : ℝ} (hak : a ≤ k)
    (hσ : ∀ j, a ≤ j → j < k → unitSlope h j = σ) :
    h k = h a + (Finset.Ico a k).card • (σ : WithTop ℝ) := by
  revert hσ
  induction hak using Succ.rec with
  | rfl =>
      intro _
      simp only [Std.le_refl, Finset.Ico_eq_empty_of_le, Finset.card_empty, zero_nsmul, add_zero]
  | succ n hn ih =>
      intro hσ
      have hun : unitSlope h n = ((σ : ℝ) : WithTop ℝ) := hσ n hn (lt_succ n)
      have hn' : h n ≠ ⊤ := by
        intro hc
        rw [unitSlope_eq_top_iff.2 (Or.inl hc)] at hun
        exact WithTop.coe_ne_top hun.symm
      rw [Finset.Ico_succ_right_eq_Icc, Finset.Icc_eq_cons_Ico hn, Finset.card_cons,
        ← add_unitSlope hn', ih fun j hj hj' ↦ hσ j hj (hj'.trans (lt_succ n)), hun, succ_nsmul,
        add_assoc]

/-- Telescoping: the value at `k` is the value at `a` plus the unit slopes in between, when every
value in between is finite. (Finiteness of `h k` alone is not enough: `(0, ⊤, 5)` has `h 2 ≠ ⊤` and
the sum formula fails at `2`; for a convex sequence the finiteness follows from
`IsConvexSeq.eq_top_of_le`.) -/
theorem eq_add_sum_unitSlope {a k : ι} (hak : a ≤ k) (hfin : ∀ j, a ≤ j → j ≤ k → h j ≠ ⊤) :
    h k = h a + ((∑ j ∈ Finset.Ico a k, (unitSlope h j).untop₀ : ℝ) : WithTop ℝ) := by
  revert hfin
  induction hak using Succ.rec with
  | rfl =>
      intro _
      simp only [Std.le_refl, Finset.Ico_eq_empty_of_le, Finset.sum_empty, WithTop.coe_zero,
        add_zero]
  | succ n hn ih =>
      intro hfin
      have hn' : h n ≠ ⊤ := hfin n hn (le_succ n)
      have hsn : h (succ n) ≠ ⊤ := hfin (succ n) (hn.trans (le_succ n)) le_rfl
      have hu : unitSlope h n ≠ ⊤ := fun hc ↦ (unitSlope_eq_top_iff.1 hc).elim hn' hsn
      have hsum : (∑ j ∈ Finset.Ico a (succ n), (unitSlope h j).untop₀)
          = (unitSlope h n).untop₀ + ∑ j ∈ Finset.Ico a n, (unitSlope h j).untop₀ := by
        rw [Finset.Ico_succ_right_eq_Icc, Finset.Icc_eq_cons_Ico hn, Finset.sum_cons]
      rw [hsum, ← add_unitSlope hn', ih fun j hj hj' ↦ hfin j hj (hj'.trans (le_succ n)),
        WithTop.coe_add, WithTop.coe_untop₀_of_ne_top hu, add_assoc,
        add_comm (unitSlope h n)]

/-- A convex sequence is determined by one finite value and its unit slopes. (Order-connectedness of
both sequences is needed: `(0, ⊤, 3)` and `(5, ⊤, 3)` share the finite value at `2` and have all
unit slopes `⊤`.) -/
theorem IsConvexSeq.eq_of_unitSlope_eq (hh : IsConvexSeq h) (hg : IsConvexSeq g) {i₀ : ι}
    (h₀ : h i₀ ≠ ⊤) (hg₀ : h i₀ = g i₀) (hs : ∀ j, unitSlope h j = unitSlope g j) : h = g := by
  have hg₀' : g i₀ ≠ ⊤ := hg₀ ▸ h₀
  funext j
  rcases le_total i₀ j with hj | hj
  · induction hj using Succ.rec with
    | rfl => exact hg₀
    | succ n hn ih =>
        by_cases hn' : h n = ⊤
        · have hgn : g n = ⊤ := ih ▸ hn'
          rw [hh.eq_top_of_le h₀ hn hn' (le_succ n), hg.eq_top_of_le hg₀' hn hgn (le_succ n)]
        · have hgn : g n ≠ ⊤ := ih ▸ hn'
          rw [← add_unitSlope hn', ← add_unitSlope hgn, ih, hs n]
  · -- to the left of `i₀`: the two sequences are `⊤` at the same indices, and where both are finite
    -- the telescoping sums from `j` to `i₀` agree
    have key : ∀ u v : ι → WithTop ℝ, IsConvexSeq v → u i₀ ≠ ⊤ → v i₀ ≠ ⊤ →
        (∀ k, unitSlope u k = unitSlope v k) → u j = ⊤ → v j = ⊤ := by
      intro u v hv hu₀ hv₀ hsuv huj
      by_contra hvj
      have hji : j < i₀ := lt_of_le_of_ne hj fun hc ↦ hu₀ (hc ▸ huj)
      have hvs : v (succ j) ≠ ⊤ :=
        hv.ordConnected.out (mem_finiteSet.2 hvj) (mem_finiteSet.2 hv₀)
          ⟨le_succ j, succ_le_of_lt hji⟩
      have hvtop : unitSlope v j = ⊤ := by
        rw [← hsuv j]
        exact unitSlope_eq_top_iff.2 (Or.inl huj)
      exact (unitSlope_eq_top_iff.1 hvtop).elim hvj hvs
    by_cases hjh : h j = ⊤
    · rw [hjh, key h g hg h₀ hg₀' hs hjh]
    · have hjg : g j ≠ ⊤ := fun hc ↦ hjh (key g h hh hg₀' h₀ (fun k ↦ (hs k).symm) hc)
      have eh := eq_add_sum_unitSlope hj fun k hk1 hk2 ↦
        hh.ordConnected.out (mem_finiteSet.2 hjh) (mem_finiteSet.2 h₀) ⟨hk1, hk2⟩
      have eg := eq_add_sum_unitSlope hj fun k hk1 hk2 ↦
        hg.ordConnected.out (mem_finiteSet.2 hjg) (mem_finiteSet.2 hg₀') ⟨hk1, hk2⟩
      have hsum : (∑ k ∈ Finset.Ico j i₀, (unitSlope h k).untop₀)
          = ∑ k ∈ Finset.Ico j i₀, (unitSlope g k).untop₀ :=
        Finset.sum_congr rfl fun k _ ↦ by rw [hs k]
      rw [hg₀, eg, hsum] at eh
      exact (WithTop.add_right_cancel WithTop.coe_ne_top eh).symm

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
/-- **The midpoint form of convexity.** A sequence with order-connected finiteness set is convex
if and only if it satisfies the midpoint inequality everywhere. -/
theorem isConvexSeq_iff_midpoint (hord : (finiteSet h).OrdConnected) :
    IsConvexSeq h ↔ ∀ k, h (succ k) + h (succ k) ≤ h k + h (succ (succ k)) := by
  refine ⟨fun hh ↦ hh.midpoint, fun hmid ↦ ⟨hord, ?_⟩⟩
  have step : ∀ k, h k ≠ ⊤ → h (succ k) ≠ ⊤ → unitSlope h k ≤ unitSlope h (succ k) := by
    intro k hk hk1
    by_cases hk2 : h (succ (succ k)) = ⊤
    · rw [unitSlope_eq_top_iff.2 (Or.inr hk2)]
      exact le_top
    have hmk := hmid k
    rw [unitSlope_of_ne_top hk hk1, unitSlope_of_ne_top hk1 hk2, WithTop.coe_le_coe]
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hk
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 hk1
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hk2
    rw [← hx, ← hy, ← hz, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hmk
    rw [← hx, ← hy, ← hz]
    simp only [WithTop.untop₀_coe]
    linarith
  intro i hi j hj hij
  revert hj
  induction hij using Succ.rec with
  | rfl => intro _; exact le_rfl
  | succ n hn ih =>
      intro hjn
      have hnm : n ∈ finiteSet h := hord.out hi hjn ⟨hn, le_succ n⟩
      exact (ih hnm).trans (step n (mem_finiteSet.1 hnm) (mem_finiteSet.1 hjn))

/-- **The chord inequality** (discrete Jensen), division-free: for `a ≤ b ≤ c` the value at `b`
lies on or below the chord through `(a, h a)` and `(c, h c)`. The coefficients are the numbers of
unit steps, `(Finset.Ico a c).card = c - a` on `ℕ` and `ℤ`. -/
theorem IsConvexSeq.le_chord (hh : IsConvexSeq h) {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c) :
    (Finset.Ico a c).card • h b ≤ (Finset.Ico b c).card • h a + (Finset.Ico a b).card • h c := by
  have htop : ∀ m : ℕ, 0 < m → m • (⊤ : WithTop ℝ) = ⊤ := by
    intro m hm
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [succ_nsmul, add_top]
  have hcard : (Finset.Ico a c).card = (Finset.Ico a b).card + (Finset.Ico b c).card := by
    rw [← Finset.Ico_union_Ico_eq_Ico hab hbc]
    exact Finset.card_union_of_disjoint (Finset.Ico_disjoint_Ico_consecutive a b c)
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp only [Std.le_refl, Finset.Ico_eq_empty_of_le, Finset.card_empty, zero_nsmul, add_zero]
  rcases eq_or_lt_of_le hbc with rfl | hbc'
  · simp only [Std.le_refl, Finset.Ico_eq_empty_of_le, Finset.card_empty, zero_nsmul, zero_add]
  have hn1 : 0 < (Finset.Ico a b).card := Finset.card_pos.2 ⟨a, Finset.mem_Ico.2 ⟨le_rfl, hab'⟩⟩
  have hn2 : 0 < (Finset.Ico b c).card := Finset.card_pos.2 ⟨b, Finset.mem_Ico.2 ⟨le_rfl, hbc'⟩⟩
  by_cases ha : h a = ⊤
  · rw [ha, htop _ hn2, top_add]
    exact le_top
  by_cases hc : h c = ⊤
  · rw [hc, htop _ hn1, add_top]
    exact le_top
  have hfin : ∀ j, a ≤ j → j ≤ c → h j ≠ ⊤ := fun j h1 h2 ↦
    mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 ha) (mem_finiteSet.2 hc) ⟨h1, h2⟩)
  have hb : h b ≠ ⊤ := hfin b hab hbc
  have hfinu : ∀ j, a ≤ j → j < c → unitSlope h j ≠ ⊤ := by
    intro j h1 h2 hcc
    rcases unitSlope_eq_top_iff.1 hcc with hx | hx
    · exact hfin j h1 h2.le hx
    · exact hfin (succ j) (h1.trans (le_succ j)) (succ_le_of_lt h2) hx
  have hut : unitSlope h b ≠ ⊤ := hfinu b hab hbc'
  have hub : ∀ j ∈ Finset.Ico a b, (unitSlope h j).untop₀ ≤ (unitSlope h b).untop₀ := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact WithTop.untop₀_le_untop₀ hut
      (hh.monotoneOn (mem_finiteSet.2 (hfin j hj.1 (hj.2.le.trans hbc))) (mem_finiteSet.2 hb)
        hj.2.le)
  have hlb : ∀ j ∈ Finset.Ico b c, (unitSlope h b).untop₀ ≤ (unitSlope h j).untop₀ := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact WithTop.untop₀_le_untop₀ (hfinu j (hab.trans hj.1) hj.2)
      (hh.monotoneOn (mem_finiteSet.2 hb)
        (mem_finiteSet.2 (hfin j (hab.trans hj.1) hj.2.le)) hj.1)
  have hS1le : (∑ j ∈ Finset.Ico a b, (unitSlope h j).untop₀)
      ≤ ((Finset.Ico a b).card : ℝ) * (unitSlope h b).untop₀ := by
    calc (∑ j ∈ Finset.Ico a b, (unitSlope h j).untop₀)
        ≤ ∑ _j ∈ Finset.Ico a b, (unitSlope h b).untop₀ := Finset.sum_le_sum hub
      _ = ((Finset.Ico a b).card : ℝ) * (unitSlope h b).untop₀ := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hS2ge : ((Finset.Ico b c).card : ℝ) * (unitSlope h b).untop₀
      ≤ ∑ j ∈ Finset.Ico b c, (unitSlope h j).untop₀ := by
    calc ((Finset.Ico b c).card : ℝ) * (unitSlope h b).untop₀
        = ∑ _j ∈ Finset.Ico b c, (unitSlope h b).untop₀ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Ico b c, (unitSlope h j).untop₀ := Finset.sum_le_sum hlb
  have key : ((Finset.Ico b c).card : ℝ) * (∑ j ∈ Finset.Ico a b, (unitSlope h j).untop₀)
      ≤ ((Finset.Ico a b).card : ℝ) * ∑ j ∈ Finset.Ico b c, (unitSlope h j).untop₀ := by
    have h1 := mul_le_mul_of_nonneg_left hS1le
      (by positivity : (0 : ℝ) ≤ ((Finset.Ico b c).card : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hS2ge
      (by positivity : (0 : ℝ) ≤ ((Finset.Ico a b).card : ℝ))
    nlinarith [h1, h2]
  obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.1 ha
  obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.1 hb
  obtain ⟨C, hC⟩ := WithTop.ne_top_iff_exists.1 hc
  have e1 : B = A + ∑ j ∈ Finset.Ico a b, (unitSlope h j).untop₀ := by
    have hte := eq_add_sum_unitSlope hab fun j h1 h2 ↦ hfin j h1 (h2.trans hbc)
    rw [← hA, ← hB, ← WithTop.coe_add, WithTop.coe_inj] at hte
    exact hte
  have e2 : C = B + ∑ j ∈ Finset.Ico b c, (unitSlope h j).untop₀ := by
    have hte := eq_add_sum_unitSlope hbc fun j h1 h2 ↦ hfin j (hab.trans h1) h2
    rw [← hB, ← hC, ← WithTop.coe_add, WithTop.coe_inj] at hte
    exact hte
  rw [← hA, ← hB, ← hC, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
    ← WithTop.coe_add, WithTop.coe_le_coe, hcard, e2, e1]
  simp only [nsmul_eq_mul]
  push_cast
  nlinarith [key]

/-- A convex sequence lies on or above the extension of each of its increments to the right. -/
theorem IsConvexSeq.add_nsmul_unitSlope_le (hh : IsConvexSeq h) {i k : ι} (hi : h i ≠ ⊤)
    (hik : i ≤ k) : h i + (Finset.Ico i k).card • unitSlope h i ≤ h k := by
  induction hik using Succ.rec with
  | rfl =>
      simp only [Std.le_refl, Finset.Ico_eq_empty_of_le, Finset.card_empty, zero_nsmul, add_zero]
  | succ n hn ih =>
      by_cases hsn : h (succ n) = ⊤
      · rw [hsn]
        exact le_top
      have hnm : n ∈ finiteSet h :=
        hh.ordConnected.out (mem_finiteSet.2 hi) (mem_finiteSet.2 hsn) ⟨hn, le_succ n⟩
      have hmono : unitSlope h i ≤ unitSlope h n :=
        hh.monotoneOn (mem_finiteSet.2 hi) hnm hn
      rw [Finset.Ico_succ_right_eq_Icc, Finset.Icc_eq_cons_Ico hn, Finset.card_cons, succ_nsmul,
        ← add_unitSlope (mem_finiteSet.1 hnm), ← add_assoc]
      exact add_le_add ih hmono

/-- A convex sequence lies on or above the extension of each of its increments to the left. -/
theorem IsConvexSeq.le_add_nsmul_unitSlope (hh : IsConvexSeq h) {i k : ι} (hi1 : h (succ i) ≠ ⊤)
    (hki : k ≤ i) : h (succ i) ≤ h k + (Finset.Ico k (succ i)).card • unitSlope h i := by
  by_cases hk : h k = ⊤
  · rw [hk, top_add]
    exact le_top
  have hfin : ∀ j, k ≤ j → j ≤ succ i → h j ≠ ⊤ := fun j h1 h2 ↦
    mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 hk) (mem_finiteSet.2 hi1) ⟨h1, h2⟩)
  have hi0 : h i ≠ ⊤ := hfin i hki (le_succ i)
  have hu : unitSlope h i ≠ ⊤ := fun hc ↦ (unitSlope_eq_top_iff.1 hc).elim hi0 hi1
  have hbound : ∀ j ∈ Finset.Ico k (succ i), (unitSlope h j).untop₀ ≤ (unitSlope h i).untop₀ := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact WithTop.untop₀_le_untop₀ hu
      (hh.monotoneOn (mem_finiteSet.2 (hfin j hj.1 hj.2.le)) (mem_finiteSet.2 hi0)
        (le_of_lt_succ hj.2))
  have hsum : (∑ j ∈ Finset.Ico k (succ i), (unitSlope h j).untop₀)
      ≤ ((Finset.Ico k (succ i)).card : ℝ) * (unitSlope h i).untop₀ := by
    calc (∑ j ∈ Finset.Ico k (succ i), (unitSlope h j).untop₀)
        ≤ ∑ _j ∈ Finset.Ico k (succ i), (unitSlope h i).untop₀ := Finset.sum_le_sum hbound
      _ = ((Finset.Ico k (succ i)).card : ℝ) * (unitSlope h i).untop₀ := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc h (succ i)
      = h k + ((∑ j ∈ Finset.Ico k (succ i), (unitSlope h j).untop₀ : ℝ) : WithTop ℝ) :=
        eq_add_sum_unitSlope (hki.trans (le_succ i)) hfin
    _ ≤ h k + ((((Finset.Ico k (succ i)).card : ℝ) * (unitSlope h i).untop₀ : ℝ) : WithTop ℝ) :=
        add_le_add le_rfl (WithTop.coe_le_coe.2 hsum)
    _ = h k + (Finset.Ico k (succ i)).card • unitSlope h i := by
        rw [← nsmul_eq_mul, WithTop.coe_nsmul, WithTop.coe_untop₀_of_ne_top hu]

omit [IsSuccArchimedean ι] in
/-- Steepening: a convex sequence cut off at a finite index `n` and continued affinely with a slope
at least every earlier unit slope is convex. This is the competitor that forces the polygon to be
`⊤` beyond its last point. -/
theorem IsConvexSeq.extend_affine (hh : IsConvexSeq h) {n : ι} (hn : h n ≠ ⊤) {M : ℝ}
    (hM : ∀ j, j < n → h j ≠ ⊤ → unitSlope h j ≤ M) :
    IsConvexSeq fun k ↦ if k ≤ n then h k else h n + (Finset.Ico n k).card • (M : WithTop ℝ) := by
  set f : ι → WithTop ℝ :=
    fun k ↦ if k ≤ n then h k else h n + (Finset.Ico n k).card • (M : WithTop ℝ) with hf
  have hfle : ∀ k, k ≤ n → f k = h k := fun k hk ↦ by
    simp only [hf]
    rw [if_pos hk]
  have hfgt : ∀ k, n < k → f k = h n + (Finset.Ico n k).card • (M : WithTop ℝ) := fun k hk ↦ by
    simp only [hf]
    rw [if_neg (not_le.2 hk)]
  have hfne : ∀ k, n < k → f k ≠ ⊤ := by
    intro k hk
    rw [hfgt k hk, ← WithTop.coe_nsmul, Ne, WithTop.add_eq_top]
    exact fun hc ↦ hc.elim hn WithTop.coe_ne_top
  have hord : (finiteSet f).OrdConnected := by
    constructor
    intro a ha b _ c hc
    rcases le_or_gt c n with hcn | hcn
    · have hha : h a ≠ ⊤ := by
        rw [← hfle a (hc.1.trans hcn)]
        exact mem_finiteSet.1 ha
      refine mem_finiteSet.2 ?_
      rw [hfle c hcn]
      exact mem_finiteSet.1
        (hh.ordConnected.out (mem_finiteSet.2 hha) (mem_finiteSet.2 hn) ⟨hc.1, hcn⟩)
    · exact mem_finiteSet.2 (hfne c hcn)
  have hulow : ∀ j, j < n → unitSlope f j = unitSlope h j := by
    intro j hj
    simp only [unitSlope, hfle j hj.le, hfle (succ j) (succ_le_of_lt hj)]
  have huhigh : ∀ j, n ≤ j → unitSlope f j = ((M : ℝ) : WithTop ℝ) := by
    intro j hj
    have hfj : f j ≠ ⊤ := by
      rcases eq_or_lt_of_le hj with rfl | hlt
      · rw [hfle n le_rfl]
        exact hn
      · exact hfne j hlt
    refine unitSlope_eq_of_succ_eq_add hfj ?_
    rcases eq_or_lt_of_le hj with rfl | hlt
    · rw [hfle n le_rfl, hfgt (succ n) (lt_succ n), Finset.Ico_succ_right_eq_Icc, Finset.Icc_self,
        Finset.card_singleton, one_nsmul]
    · rw [hfgt j hlt, hfgt (succ j) (hlt.trans (lt_succ j)), Finset.Ico_succ_right_eq_Icc,
        Finset.Icc_eq_cons_Ico hlt.le, Finset.card_cons, succ_nsmul, add_assoc]
  refine ⟨hord, fun a ha b hb hab ↦ ?_⟩
  rcases lt_or_ge a n with han | han
  · rcases lt_or_ge b n with hbn | hbn
    · rw [hulow a han, hulow b hbn]
      refine hh.monotoneOn (mem_finiteSet.2 ?_) (mem_finiteSet.2 ?_) hab
      · rw [← hfle a han.le]
        exact mem_finiteSet.1 ha
      · rw [← hfle b hbn.le]
        exact mem_finiteSet.1 hb
    · rw [hulow a han, huhigh b hbn]
      exact hM a han (by rw [← hfle a han.le]; exact mem_finiteSet.1 ha)
  · rw [huhigh a han, huhigh b (han.trans hab)]

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
/-- The pointwise maximum of two convex sequences is convex. -/
theorem IsConvexSeq.sup (hh : IsConvexSeq h) (hg : IsConvexSeq g) : IsConvexSeq (h ⊔ g) := by
  have hsup : ∀ j, (h ⊔ g) j = ⊤ ↔ h j = ⊤ ∨ g j = ⊤ := by
    intro j
    simp only [Pi.sup_apply]
    rcases le_total (h j) (g j) with hle | hle
    · rw [sup_eq_right.2 hle]
      exact ⟨Or.inr, fun hc ↦ hc.elim (fun hx ↦ top_le_iff.1 (hx ▸ hle)) id⟩
    · rw [sup_eq_left.2 hle]
      exact ⟨Or.inl, fun hc ↦ hc.elim id fun hx ↦ top_le_iff.1 (hx ▸ hle)⟩
  have hfs : finiteSet (h ⊔ g) = finiteSet h ∩ finiteSet g := by
    ext j
    simp only [mem_finiteSet, Set.mem_inter_iff, hsup j, not_or, ne_eq]
  refine (isConvexSeq_iff_midpoint (by rw [hfs]; exact hh.ordConnected.inter hg.ordConnected)).2 ?_
  intro k
  simp only [Pi.sup_apply]
  rcases le_total (h (succ k)) (g (succ k)) with hle | hle
  · rw [sup_eq_right.2 hle]
    calc g (succ k) + g (succ k) ≤ g k + g (succ (succ k)) := hg.midpoint k
      _ ≤ h k ⊔ g k + (h (succ (succ k)) ⊔ g (succ (succ k))) :=
          add_le_add le_sup_right le_sup_right
  · rw [sup_eq_left.2 hle]
    calc h (succ k) + h (succ k) ≤ h k + h (succ (succ k)) := hh.midpoint k
      _ ≤ h k ⊔ g k + (h (succ (succ k)) ⊔ g (succ (succ k))) :=
          add_le_add le_sup_left le_sup_left

/-- **The pointwise supremum of a family of convex sequences is convex** (roadmap §0.1.3). No
boundedness hypothesis is needed in `WithTop ℝ`: an unbounded family has supremum `⊤`. -/
theorem IsConvexSeq.iSup {κ : Type*} [Nonempty κ] {f : κ → ι → WithTop ℝ}
    (hf : ∀ i, IsConvexSeq (f i)) : IsConvexSeq fun k ↦ ⨆ i, f i k := by
  have hle : ∀ (i : κ) (k : ι), f i k ≤ ⨆ j, f j k := fun i k ↦
    le_ciSup (f := fun j ↦ f j k) (OrderTop.bddAbove (Set.range fun j ↦ f j k)) i
  have hord : (finiteSet fun k ↦ ⨆ i, f i k).OrdConnected := by
    constructor
    intro a ha c hc b hb
    refine mem_finiteSet.2 ?_
    have hA : (⨆ i, f i a) ≠ ⊤ := mem_finiteSet.1 ha
    have hC : (⨆ i, f i c) ≠ ⊤ := mem_finiteSet.1 hc
    rcases eq_or_lt_of_le (hb.1.trans hb.2) with rfl | hac
    · rw [le_antisymm hb.2 hb.1]
      exact hA
    obtain ⟨A, hAv⟩ := WithTop.ne_top_iff_exists.1 hA
    obtain ⟨C, hCv⟩ := WithTop.ne_top_iff_exists.1 hC
    have hNpos : 0 < ((Finset.Ico a c).card : ℝ) := by
      have : 0 < (Finset.Ico a c).card :=
        Finset.card_pos.2 ⟨a, Finset.mem_Ico.2 ⟨le_rfl, hac⟩⟩
      positivity
    have hbound : ∀ i, f i b ≤ (((((Finset.Ico b c).card : ℝ) * A + ((Finset.Ico a b).card : ℝ) * C)
        / ((Finset.Ico a c).card : ℝ) : ℝ) : WithTop ℝ) := by
      intro i
      have hfa : f i a ≤ ((A : ℝ) : WithTop ℝ) := by rw [hAv]; exact hle i a
      have hfc : f i c ≤ ((C : ℝ) : WithTop ℝ) := by rw [hCv]; exact hle i c
      have hfane : f i a ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hfa
      have hfcne : f i c ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hfc
      have hfbne : f i b ≠ ⊤ :=
        mem_finiteSet.1 ((hf i).ordConnected.out (mem_finiteSet.2 hfane) (mem_finiteSet.2 hfcne) hb)
      have hchord := (hf i).le_chord hb.1 hb.2
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 hfbne
      obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hfane
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hfcne
      rw [← hv, ← hx, ← hz, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
        ← WithTop.coe_add, WithTop.coe_le_coe] at hchord
      rw [← hx, WithTop.coe_le_coe] at hfa
      rw [← hz, WithTop.coe_le_coe] at hfc
      rw [← hv, WithTop.coe_le_coe, le_div_iff₀ hNpos]
      simp only [nsmul_eq_mul] at hchord
      nlinarith [hchord, hfa, hfc,
        (by positivity : (0 : ℝ) ≤ ((Finset.Ico b c).card : ℝ)),
        (by positivity : (0 : ℝ) ≤ ((Finset.Ico a b).card : ℝ))]
    exact ne_top_of_le_ne_top WithTop.coe_ne_top (ciSup_le hbound)
  refine (isConvexSeq_iff_midpoint hord).2 fun k ↦ ?_
  by_cases hk : (⨆ i, f i k) = ⊤
  · rw [hk, top_add]
    exact le_top
  by_cases hk2 : (⨆ i, f i (succ (succ k))) = ⊤
  · rw [hk2, add_top]
    exact le_top
  obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.1 hk
  obtain ⟨C, hC⟩ := WithTop.ne_top_iff_exists.1 hk2
  have hhalf : (⨆ i, f i (succ k)) ≤ (((A + C) / 2 : ℝ) : WithTop ℝ) := by
    refine ciSup_le fun i ↦ ?_
    have hfk : f i k ≤ ((A : ℝ) : WithTop ℝ) := by rw [hA]; exact hle i k
    have hfk2 : f i (succ (succ k)) ≤ ((C : ℝ) : WithTop ℝ) := by
      rw [hC]
      exact hle i (succ (succ k))
    have hfkne : f i k ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hfk
    have hfk2ne : f i (succ (succ k)) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hfk2
    have hmid := (hf i).midpoint k
    have hune : f i (succ k) ≠ ⊤ := by
      intro hcc
      rw [hcc, top_add, top_le_iff, WithTop.add_eq_top] at hmid
      exact hmid.elim hfkne hfk2ne
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 hune
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hfkne
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hfk2ne
    rw [← hu, ← hx, ← hz, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hmid
    rw [← hx, WithTop.coe_le_coe] at hfk
    rw [← hz, WithTop.coe_le_coe] at hfk2
    rw [← hu, WithTop.coe_le_coe]
    linarith
  calc (⨆ i, f i (succ k)) + (⨆ i, f i (succ k))
      ≤ (((A + C) / 2 : ℝ) : WithTop ℝ) + (((A + C) / 2 : ℝ) : WithTop ℝ) := add_le_add hhalf hhalf
    _ = ((A : ℝ) : WithTop ℝ) + ((C : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj]
        ring
    _ = (⨆ i, f i k) + ⨆ i, f i (succ (succ k)) := by rw [hA, hC]

omit [IsSuccArchimedean ι] [LocallyFiniteOrder ι] [NoMaxOrder ι] in
/-- An everywhere-finite convex sequence with bounded unit slopes has a limiting slope
(roadmap §0.1.5). -/
theorem IsConvexSeq.tendsto_unitSlope (hh : IsConvexSeq h) (hfin : ∀ k, h k ≠ ⊤)
    (hb : BddAbove (Set.range fun j ↦ (unitSlope h j).untop₀)) :
    Filter.Tendsto (fun j ↦ (unitSlope h j).untop₀) Filter.atTop
      (nhds (⨆ j, (unitSlope h j).untop₀)) := by
  refine tendsto_atTop_ciSup (fun i j hij ↦ ?_) hb
  exact WithTop.untop₀_le_untop₀
    (fun hc ↦ (unitSlope_eq_top_iff.1 hc).elim (hfin j) (hfin (succ j)))
    (hh.monotoneOn (mem_finiteSet.2 (hfin i)) (mem_finiteSet.2 (hfin j)) hij)

omit [IsSuccArchimedean ι] [LocallyFiniteOrder ι] [NoMaxOrder ι] in
/-- A convex sequence is eventually monotone: either it is non-increasing on its finiteness set, or
from some index on it is non-decreasing. (The first disjunct cannot be stated everywhere: past the
last finite index the value is `⊤`.) -/
theorem IsConvexSeq.antitone_or_eventually_monotone (hh : IsConvexSeq h) :
    (∀ k, h (succ k) ≠ ⊤ → h (succ k) ≤ h k) ∨ ∃ N, ∀ k, N ≤ k → h k ≤ h (succ k) := by
  by_cases hex : ∃ N, h N ≠ ⊤ ∧ h (succ N) ≠ ⊤ ∧ (0 : WithTop ℝ) ≤ unitSlope h N
  · obtain ⟨N, hN, -, hslope⟩ := hex
    refine Or.inr ⟨N, fun k hk ↦ ?_⟩
    by_cases hkt : h k = ⊤
    · rw [hkt, top_le_iff]
      exact hh.eq_top_of_le hN hk hkt (le_succ k)
    have hmono : (0 : WithTop ℝ) ≤ unitSlope h k :=
      hslope.trans (hh.monotoneOn (mem_finiteSet.2 hN) (mem_finiteSet.2 hkt) hk)
    calc h k = h k + 0 := (add_zero _).symm
      _ ≤ h k + unitSlope h k := add_le_add le_rfl hmono
      _ = h (succ k) := add_unitSlope hkt
  · push Not at hex
    refine Or.inl fun k hk1 ↦ ?_
    by_cases hk : h k = ⊤
    · rw [hk]
      exact le_top
    have hneg : unitSlope h k ≤ 0 := le_of_lt (by simpa using hex k hk hk1)
    calc h (succ k) = h k + unitSlope h k := (add_unitSlope hk).symm
      _ ≤ h k + 0 := add_le_add le_rfl hneg
      _ = h k := add_zero _

end Sums

/-! ### Sequences indexed by `ℕ`: affine sequences and the bridge to `ConvexOn`

These need a coordinate on the index type; the `ℤ` versions are in `Int.lean`. -/

section Nat

variable {h : ℕ → WithTop ℝ}

/-- On `ℕ` the generic unit slope is the familiar `h (j + 1) - h j`. -/
theorem unitSlope_nat (h : ℕ → WithTop ℝ) (j : ℕ) :
    unitSlope h j =
      if h j = ⊤ ∨ h (j + 1) = ⊤ then ⊤
      else (((h (j + 1)).untop₀ - (h j).untop₀ : ℝ) : WithTop ℝ) := by
  rw [unitSlope, Order.succ_eq_add_one]

/-- Affine sequences are convex. -/
theorem isConvexSeq_affine (y σ : ℝ) : IsConvexSeq fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ) := by
  have hu : ∀ j : ℕ,
      unitSlope (fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ)) j = ((σ : ℝ) : WithTop ℝ) := by
    intro j
    refine unitSlope_eq_of_succ_eq_add WithTop.coe_ne_top ?_
    show ((y + σ * ((succ j : ℕ) : ℝ) : ℝ) : WithTop ℝ)
        = ((y + σ * j : ℝ) : WithTop ℝ) + ((σ : ℝ) : WithTop ℝ)
    rw [← WithTop.coe_add, WithTop.coe_inj, Order.succ_eq_add_one]
    push_cast
    ring
  have hfs : finiteSet (fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ)) = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ mem_finiteSet.2 WithTop.coe_ne_top
  exact ⟨by rw [hfs]; exact Set.ordConnected_univ, fun a _ b _ _ ↦ by rw [hu, hu]⟩

/-- The affine sequence of slope `s` through `(i₀, y)`, and `⊤` before `i₀`: the basic convex
minorant of a sequence whose first point is `(i₀, y)`. -/
noncomputable def affineFrom (i₀ : ℕ) (y s : ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ if k < i₀ then ⊤ else ((y + s * ((k : ℝ) - i₀) : ℝ) : WithTop ℝ)

/-- The affine sequence extended by `⊤` to the left is convex. -/
theorem isConvexSeq_affineFrom (i₀ : ℕ) (y s : ℝ) : IsConvexSeq (affineFrom i₀ y s) := by
  have hval : ∀ k, i₀ ≤ k → affineFrom i₀ y s k = ((y + s * ((k : ℝ) - i₀) : ℝ) : WithTop ℝ) := by
    intro k hk
    simp only [affineFrom]
    rw [if_neg (not_lt.2 hk)]
  have hu : ∀ j, i₀ ≤ j → unitSlope (affineFrom i₀ y s) j = ((s : ℝ) : WithTop ℝ) := by
    intro j hj
    refine unitSlope_eq_of_succ_eq_add (by rw [hval j hj]; exact WithTop.coe_ne_top) ?_
    rw [hval (succ j) (hj.trans (le_succ j)), hval j hj, ← WithTop.coe_add, WithTop.coe_inj,
      Order.succ_eq_add_one]
    push_cast
    ring
  have hfs : finiteSet (affineFrom i₀ y s) = Set.Ici i₀ := by
    ext k
    rcases le_or_gt i₀ k with hk | hk
    · exact iff_of_true (mem_finiteSet.2 (by rw [hval k hk]; exact WithTop.coe_ne_top)) hk
    · have htop : affineFrom i₀ y s k = ⊤ := by
        simp only [affineFrom]
        rw [if_pos hk]
      refine iff_of_false (by simp only [mem_finiteSet, htop, ne_eq, not_true_eq_false,
        not_false_eq_true]) hk.not_ge
  refine ⟨by rw [hfs]; exact Set.ordConnected_Ici, fun a ha b hb _ ↦ ?_⟩
  rw [hfs] at ha hb
  rw [hu a ha, hu b hb]

/-- Adding an affine sequence preserves convexity. -/
theorem IsConvexSeq.add_affine (hh : IsConvexSeq h) (y σ : ℝ) :
    IsConvexSeq fun k ↦ h k + ((y + σ * k : ℝ) : WithTop ℝ) := by
  have htop : ∀ j : ℕ, (h j + ((y + σ * j : ℝ) : WithTop ℝ) = ⊤) ↔ h j = ⊤ := by
    intro j
    rw [WithTop.add_eq_top]
    exact ⟨fun hc ↦ hc.elim id fun hx ↦ absurd hx WithTop.coe_ne_top, Or.inl⟩
  have hu : ∀ j : ℕ, unitSlope (fun k : ℕ ↦ h k + ((y + σ * k : ℝ) : WithTop ℝ)) j
      = unitSlope h j + ((σ : ℝ) : WithTop ℝ) := by
    intro j
    by_cases hj : h j = ⊤
    · have e1 : unitSlope (fun k : ℕ ↦ h k + ((y + σ * k : ℝ) : WithTop ℝ)) j = ⊤ :=
        unitSlope_eq_top_iff.2 (Or.inl ((htop j).2 hj))
      have e2 : unitSlope h j = ⊤ := unitSlope_eq_top_iff.2 (Or.inl hj)
      rw [e1, e2, top_add]
    by_cases hj1 : h (succ j) = ⊤
    · have e1 : unitSlope (fun k : ℕ ↦ h k + ((y + σ * k : ℝ) : WithTop ℝ)) j = ⊤ :=
        unitSlope_eq_top_iff.2 (Or.inr ((htop (succ j)).2 hj1))
      have e2 : unitSlope h j = ⊤ := unitSlope_eq_top_iff.2 (Or.inr hj1)
      rw [e1, e2, top_add]
    have hus : unitSlope h j ≠ ⊤ := fun hc ↦ (unitSlope_eq_top_iff.1 hc).elim hj hj1
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hus
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hj
    rw [← ht, ← WithTop.coe_add]
    refine unitSlope_eq_of_succ_eq_add (fun hc ↦ hj ((htop j).1 hc)) ?_
    show h (succ j) + ((y + σ * ((succ j : ℕ) : ℝ) : ℝ) : WithTop ℝ)
        = h j + ((y + σ * j : ℝ) : WithTop ℝ) + ((t + σ : ℝ) : WithTop ℝ)
    rw [← add_unitSlope hj, ← ht, ← hx, Order.succ_eq_add_one]
    simp only [← WithTop.coe_add]
    rw [WithTop.coe_inj]
    push_cast
    ring
  have hfs : finiteSet (fun k : ℕ ↦ h k + ((y + σ * k : ℝ) : WithTop ℝ)) = finiteSet h := by
    ext j
    simp only [mem_finiteSet, ne_eq, htop j]
  refine ⟨by rw [hfs]; exact hh.ordConnected, fun a ha b hb hab ↦ ?_⟩
  rw [hfs] at ha hb
  rw [hu a, hu b]
  exact add_le_add (hh.monotoneOn ha hb hab) le_rfl

/-- **The sliding inequality**: moving the two ends of an interval one step towards each other does
not increase the sum of the values. This is convexity in the form the min-convolution needs
(`Minkowski.lean`). -/
theorem IsConvexSeq.succ_add_pred_le (hh : IsConvexSeq h) {p q : ℕ} (hpq : p < q) :
    h (p + 1) + h (q - 1) ≤ h p + h q := by
  by_cases hp : h p = ⊤
  · rw [hp, top_add]
    exact le_top
  by_cases hq : h q = ⊤
  · rw [hq, add_top]
    exact le_top
  have hfin : ∀ j, p ≤ j → j ≤ q → h j ≠ ⊤ := fun j h1 h2 ↦
    mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 hp) (mem_finiteSet.2 hq) ⟨h1, h2⟩)
  have hmono : unitSlope h p ≤ unitSlope h (q - 1) :=
    hh.monotoneOn (mem_finiteSet.2 hp) (mem_finiteSet.2 (hfin (q - 1) (by omega) (by omega)))
      (by omega)
  have hsp : unitSlope h p ≠ ⊤ := by
    rw [ne_eq, unitSlope_eq_top_iff, Order.succ_eq_add_one, not_or]
    exact ⟨hp, hfin (p + 1) (by omega) (by omega)⟩
  have hsq : unitSlope h (q - 1) ≠ ⊤ := by
    rw [ne_eq, unitSlope_eq_top_iff, Order.succ_eq_add_one, show q - 1 + 1 = q by omega, not_or]
    exact ⟨hfin (q - 1) (by omega) (by omega), hq⟩
  have hstepp : h p + unitSlope h p = h (p + 1) := by
    rw [← Order.succ_eq_add_one]
    exact add_unitSlope hp
  have hstepq : h (q - 1) + unitSlope h (q - 1) = h q := by
    rw [← show q - 1 + 1 = q by omega, ← Order.succ_eq_add_one]
    exact add_unitSlope (hfin (q - 1) (by omega) (by omega))
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 hp
  obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 (hfin (q - 1) (by omega) (by omega))
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hsp
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hsq
  rw [← hstepp, ← hstepq, ← hA, ← hB, ← hs, ← ht, ← WithTop.coe_add, ← WithTop.coe_add,
    ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  rw [← hs, ← ht, WithTop.coe_le_coe] at hmono
  linarith

/-- The pointwise minimum of two convex sequences need not be convex: `k ↦ min k (2 - k)` takes
the values `0, 1, 0` at `0, 1, 2`. -/
theorem not_isConvexSeq_inf :
    ¬ IsConvexSeq ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) :=
    by
  intro hcx
  have v0 : ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 0
      = ((0 : ℝ) : WithTop ℝ) := by
    show ((((0 : ℕ) : ℝ) : WithTop ℝ)) ⊓ (((2 - ((0 : ℕ) : ℝ) : ℝ)) : WithTop ℝ)
        = ((0 : ℝ) : WithTop ℝ)
    rw [inf_eq_left.2 (WithTop.coe_le_coe.2 (by norm_num))]
    norm_num
  have v1 : ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 1
      = ((1 : ℝ) : WithTop ℝ) := by
    show ((((1 : ℕ) : ℝ) : WithTop ℝ)) ⊓ (((2 - ((1 : ℕ) : ℝ) : ℝ)) : WithTop ℝ)
        = ((1 : ℝ) : WithTop ℝ)
    rw [inf_eq_left.2 (WithTop.coe_le_coe.2 (by norm_num))]
    norm_num
  have v2 : ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 2
      = ((0 : ℝ) : WithTop ℝ) := by
    show ((((2 : ℕ) : ℝ) : WithTop ℝ)) ⊓ (((2 - ((2 : ℕ) : ℝ) : ℝ)) : WithTop ℝ)
        = ((0 : ℝ) : WithTop ℝ)
    rw [inf_eq_right.2 (WithTop.coe_le_coe.2 (by norm_num))]
    norm_num
  have hu0 : unitSlope
      ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 0
      = ((1 : ℝ) : WithTop ℝ) := by
    refine unitSlope_eq_of_succ_eq_add (by rw [v0]; exact WithTop.coe_ne_top) ?_
    show ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 1
        = ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 0
          + ((1 : ℝ) : WithTop ℝ)
    rw [v0, v1, ← WithTop.coe_add]
    norm_num
  have hu1 : unitSlope
      ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 1
      = ((-1 : ℝ) : WithTop ℝ) := by
    refine unitSlope_eq_of_succ_eq_add (by rw [v1]; exact WithTop.coe_ne_top) ?_
    show ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 2
        = ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) 1
          + ((-1 : ℝ) : WithTop ℝ)
    rw [v1, v2, ← WithTop.coe_add]
    norm_num
  have hmono := hcx.monotoneOn (mem_finiteSet.2 (by rw [v0]; exact WithTop.coe_ne_top))
    (mem_finiteSet.2 (by rw [v1]; exact WithTop.coe_ne_top)) zero_le_one
  rw [hu0, hu1, WithTop.coe_le_coe] at hmono
  norm_num at hmono

/-- An everywhere-finite convex sequence is the restriction to `ℕ` of a function convex on
`[0, ∞)` (roadmap §0.1.4): the supremum of its supporting lines. -/
theorem IsConvexSeq.exists_convexOn (hh : IsConvexSeq h) (hfin : ∀ k, h k ≠ ⊤) :
    ∃ H : ℝ → ℝ, ConvexOn ℝ (Set.Ici (0 : ℝ)) H ∧ ∀ k : ℕ, H k = (h k).untop₀ := by
  have hsne : ∀ j : ℕ, unitSlope h j ≠ ⊤ := fun j hc ↦
    (unitSlope_eq_top_iff.1 hc).elim (hfin j) (hfin (succ j))
  have htel : ∀ a k : ℕ, a ≤ k →
      (h k).untop₀ = (h a).untop₀ + ∑ j ∈ Finset.Ico a k, (unitSlope h j).untop₀ := by
    intro a k hak
    have hE := eq_add_sum_unitSlope hak fun j _ _ ↦ hfin j
    obtain ⟨xa, hxa⟩ := WithTop.ne_top_iff_exists.1 (hfin a)
    obtain ⟨xk, hxk⟩ := WithTop.ne_top_iff_exists.1 (hfin k)
    rw [← hxa, ← hxk, ← WithTop.coe_add, WithTop.coe_inj] at hE
    rw [← hxa, ← hxk]
    simpa only [WithTop.untop₀_coe] using hE
  have hsmono : Monotone fun j : ℕ ↦ (unitSlope h j).untop₀ := fun i j hij ↦
    WithTop.untop₀_le_untop₀ (hsne j)
      (hh.monotoneOn (mem_finiteSet.2 (hfin i)) (mem_finiteSet.2 (hfin j)) hij)
  have hline : ∀ j k : ℕ,
      (h j).untop₀ + (unitSlope h j).untop₀ * ((k : ℝ) - j) ≤ (h k).untop₀ := by
    intro j k
    rcases le_total j k with hjk | hkj
    · have h1 := htel j k hjk
      have h2 : ((Finset.Ico j k).card : ℝ) * (unitSlope h j).untop₀
          ≤ ∑ i ∈ Finset.Ico j k, (unitSlope h i).untop₀ := by
        calc ((Finset.Ico j k).card : ℝ) * (unitSlope h j).untop₀
            = ∑ _i ∈ Finset.Ico j k, (unitSlope h j).untop₀ := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ i ∈ Finset.Ico j k, (unitSlope h i).untop₀ :=
              Finset.sum_le_sum fun i hi ↦ hsmono (Finset.mem_Ico.1 hi).1
      rw [Nat.card_Ico, Nat.cast_sub hjk] at h2
      linarith
    · have h1 := htel k j hkj
      have h2 : (∑ i ∈ Finset.Ico k j, (unitSlope h i).untop₀)
          ≤ ((Finset.Ico k j).card : ℝ) * (unitSlope h j).untop₀ := by
        calc (∑ i ∈ Finset.Ico k j, (unitSlope h i).untop₀)
            ≤ ∑ _i ∈ Finset.Ico k j, (unitSlope h j).untop₀ :=
              Finset.sum_le_sum fun i hi ↦ hsmono (Finset.mem_Ico.1 hi).2.le
          _ = ((Finset.Ico k j).card : ℝ) * (unitSlope h j).untop₀ := by
              rw [Finset.sum_const, nsmul_eq_mul]
      rw [Nat.card_Ico, Nat.cast_sub hkj] at h2
      linarith
  have hbdda : ∀ x : ℝ, 0 ≤ x →
      BddAbove (Set.range fun j : ℕ ↦ (h j).untop₀ + (unitSlope h j).untop₀ * (x - j)) := by
    intro x hx
    obtain ⟨m, hm⟩ := exists_nat_ge x
    refine ⟨max ((h 0).untop₀) ((h m).untop₀), ?_⟩
    rintro y ⟨j, rfl⟩
    rcases le_or_gt 0 ((unitSlope h j).untop₀) with hsj | hsj
    · refine le_trans (le_trans ?_ (hline j m)) (le_max_right _ _)
      have hxm : x - (j : ℝ) ≤ (m : ℝ) - j := by linarith
      nlinarith
    · refine le_trans (le_trans ?_ (hline j 0)) (le_max_left _ _)
      have hx0 : ((0 : ℕ) : ℝ) - j ≤ x - j := by
        push_cast
        linarith
      nlinarith
  refine ⟨fun x ↦ ⨆ j : ℕ, ((h j).untop₀ + (unitSlope h j).untop₀ * (x - j)),
    ⟨convex_Ici 0, fun x hx y hy a b ha hb hab ↦ ?_⟩, fun k ↦ ?_⟩
  · refine ciSup_le fun j ↦ ?_
    have hjx : (h j).untop₀ + (unitSlope h j).untop₀ * (x - j)
        ≤ ⨆ i : ℕ, ((h i).untop₀ + (unitSlope h i).untop₀ * (x - i)) :=
      le_ciSup (hbdda x hx) j
    have hjy : (h j).untop₀ + (unitSlope h j).untop₀ * (y - j)
        ≤ ⨆ i : ℕ, ((h i).untop₀ + (unitSlope h i).untop₀ * (y - i)) :=
      le_ciSup (hbdda y hy) j
    have hexp : (h j).untop₀ + (unitSlope h j).untop₀ * ((a • x + b • y) - j)
        = a * ((h j).untop₀ + (unitSlope h j).untop₀ * (x - j))
          + b * ((h j).untop₀ + (unitSlope h j).untop₀ * (y - j)) := by
      simp only [smul_eq_mul]
      have hba : a = 1 - b := by linarith
      subst hba
      ring
    rw [hexp]
    simp only [smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hjx ha) (mul_le_mul_of_nonneg_left hjy hb)
  · refine le_antisymm (ciSup_le fun j ↦ hline j k) ?_
    refine le_trans ?_ (le_ciSup (hbdda (k : ℝ) (Nat.cast_nonneg k)) k)
    simp only [sub_self, mul_zero, add_zero, Std.le_refl]

/-- The restriction to `ℕ` of a function convex on `[0, ∞)` is a convex sequence. -/
theorem isConvexSeq_of_convexOn {H : ℝ → ℝ} (hH : ConvexOn ℝ (Set.Ici (0 : ℝ)) H) :
    IsConvexSeq fun k : ℕ ↦ ((H k : ℝ) : WithTop ℝ) := by
  have hu : ∀ j : ℕ, unitSlope (fun k : ℕ ↦ ((H k : ℝ) : WithTop ℝ)) j
      = ((H ((j : ℝ) + 1) - H (j : ℝ) : ℝ) : WithTop ℝ) := by
    intro j
    refine unitSlope_eq_of_succ_eq_add WithTop.coe_ne_top ?_
    show ((H ((succ j : ℕ) : ℝ) : ℝ) : WithTop ℝ)
        = ((H (j : ℝ) : ℝ) : WithTop ℝ) + ((H ((j : ℝ) + 1) - H (j : ℝ) : ℝ) : WithTop ℝ)
    rw [← WithTop.coe_add, WithTop.coe_inj, Order.succ_eq_add_one]
    push_cast
    ring
  have hmono : Monotone fun j : ℕ ↦ H ((j : ℝ) + 1) - H (j : ℝ) := by
    refine monotone_nat_of_le_succ fun j ↦ ?_
    have h1 : (j : ℝ) ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici]
      positivity
    have h2 : ((j : ℝ) + 2) ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici]
      positivity
    have hadj := hH.slope_mono_adjacent h1 h2 (by linarith : (j : ℝ) < (j : ℝ) + 1)
      (by linarith : (j : ℝ) + 1 < (j : ℝ) + 2)
    have hd1 : ((j : ℝ) + 1) - (j : ℝ) = 1 := by ring
    have hd2 : ((j : ℝ) + 2) - ((j : ℝ) + 1) = 1 := by ring
    rw [hd1, hd2, div_one, div_one] at hadj
    push_cast
    rw [show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring]
    linarith
  have hfs : finiteSet (fun k : ℕ ↦ ((H k : ℝ) : WithTop ℝ)) = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ mem_finiteSet.2 WithTop.coe_ne_top
  refine ⟨by rw [hfs]; exact Set.ordConnected_univ, fun a _ b _ hab ↦ ?_⟩
  rw [hu a, hu b, WithTop.coe_le_coe]
  exact hmono hab

end Nat

end NewtonPolygon
