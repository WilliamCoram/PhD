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

A *convex sequence* is a function `h : ι → WithTop ℝ` whose finiteness set `{j | h j ≠ ⊤}` is an
interval and whose increments `h (succ j) - h j` are monotone on it. The value `⊤` means "nothing
here", so a convex sequence is a convex function on an interval of `ι`, extended by `⊤` on both
sides.

The index type is abstract: `[LinearOrder ι] [SuccOrder ι]` for the definitions, additionally
`[LocallyFiniteOrder ι] [NoMaxOrder ι]` wherever a proof sums over an interval, and
`[IsSuccArchimedean ι]` (which `LocallyFiniteOrder` implies on a linear order) where a proof only
walks along successors. `ℕ` and `ℤ` satisfy all of these; on both, `Order.succ j = j + 1` and
`(Finset.Ico a c).card` i `c - a` (`Nat.card_Ico`, `Int.card_Ico`). Statements that need a
coordinate on the index type (affine sequences, the `ConvexOn` bridge) are stated for `ℕ` at the end
of the file and for `ℤ` in `Int.lean`.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §0.1. Tau Ceti home:
`TauCeti/Analysis/Convex/Sequence.lean`.

## Main definitions

* `NewtonPolygon.unitSlope h j` — the increment `h (succ j) - h j`, taken to be `⊤` as soon as
  either value is `⊤`.
* `NewtonPolygon.finiteSupport h` — the finiteness set `{j | h j ≠ ⊤}`.
* `NewtonPolygon.IsConvexSeq h` — the finiteness set is order-connected and the unit slopes are
  monotone on it.

## Main results

* `NewtonPolygon.monotoneOn_unitSlope_iff_midpoint`, `NewtonPolygon.isConvexSeq_iff_midpoint` —
  the midpoint form `h (succ k) + h (succ k) ≤ h k + h (succ (succ k))`.
* `NewtonPolygon.IsConvexSeq.le_chord` — the chord inequality (discrete Jensen), division-free.
* `NewtonPolygon.IsConvexSeq.exists_update_of_unitSlope_lt` — at a strict break a convex sequence
  can be raised at that index alone and stay convex.
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

/-- The `j`-th *unit slope* of `h`: the increment `h (succ j) - h j`. On the finiteness interval of
a convex sequence these are its slopes on the unit intervals. -/
noncomputable
def unitSlope (h : ι → WithTop ℝ) (j : ι) : WithTop ℝ := h (succ j) - h j

/-- The finiteness set of `h`. -/
def finiteSupport (h : ι → WithTop ℝ) : Set ι := {j | h j ≠ ⊤}

omit [LinearOrder ι] [SuccOrder ι] in
@[simp]
theorem mem_finiteSupport {j : ι} : j ∈ finiteSupport h ↔ h j ≠ ⊤ := Iff.rfl

omit [LinearOrder ι] [SuccOrder ι] in
theorem finiteSupport_sup : finiteSupport (h ⊔ g) = finiteSupport h ∩ finiteSupport g := by
  aesop

omit [LinearOrder ι] [SuccOrder ι] in
theorem finiteSupport_add : finiteSupport (h + g) = finiteSupport h ∩ finiteSupport g := by
  aesop

omit [LinearOrder ι] [SuccOrder ι] in
theorem finiteSupport_update [DecidableEq ι] {k : ι} {c : WithTop ℝ} (hk : h k ≠ ⊤)
    (hc : c ≠ ⊤) : finiteSupport (Function.update h k c) = finiteSupport h := by
  ext j
  by_cases hj : j = k <;> simp [hj, hk, hc]

theorem unitSlope_eq_top_iff {j : ι} : unitSlope h j = ⊤ ↔ h j = ⊤ ∨ h (succ j) = ⊤ := by
  rw [unitSlope, WithTop.LinearOrderedAddCommGroup.sub_eq_top_iff, or_comm]

theorem unitSlope_ne_top_iff {j : ι} : unitSlope h j ≠ ⊤ ↔ h j ≠ ⊤ ∧ h (succ j) ≠ ⊤ := by
  rw [ne_eq, unitSlope_eq_top_iff, not_or]

theorem unitSlope_ne_top {j : ι} (hj : h j ≠ ⊤) (hj1 : h (succ j) ≠ ⊤) : unitSlope h j ≠ ⊤ :=
  unitSlope_ne_top_iff.2 ⟨hj, hj1⟩

theorem unitSlope_of_ne_top {j : ι} (hj : h j ≠ ⊤) (hj1 : h (succ j) ≠ ⊤) :
    unitSlope h j = (((h (succ j)).untop₀ - (h j).untop₀ : ℝ) : WithTop ℝ) := by
  rw [unitSlope]
  lift h j to ℝ using hj with a
  lift h (succ j) to ℝ using hj1 with b
  simp

theorem add_unitSlope {j : ι} (hj : h j ≠ ⊤) : h j + unitSlope h j = h (succ j) := by
  rw [unitSlope]
  by_cases hj1 : h (succ j) = ⊤
  · simp [hj1]
  · lift h j to ℝ using hj with a
    lift h (succ j) to ℝ using hj1 with b
    norm_cast
    ring

theorem unitSlope_eq_of_succ_eq_add {j : ι} {c : ℝ} (hj : h j ≠ ⊤)
    (hc : h (succ j) = h j + (c : WithTop ℝ)) : unitSlope h j = (c : WithTop ℝ) := by
  rw [unitSlope, hc]
  lift h j to ℝ using hj with a
  norm_cast
  ring

@[simp]
theorem unitSlope_coe (c : ι → ℝ) (j : ι) :
    unitSlope (fun k ↦ ((c k : ℝ) : WithTop ℝ)) j = ((c (succ j) - c j : ℝ) : WithTop ℝ) :=
  (WithTop.LinearOrderedAddCommGroup.coe_sub ..).symm

omit [LinearOrder ι] [SuccOrder ι] in
@[simp]
theorem finiteSupport_coe (c : ι → ℝ) :
    finiteSupport (fun k ↦ ((c k : ℝ) : WithTop ℝ)) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ WithTop.coe_ne_top

theorem unitSlope_add (h g : ι → WithTop ℝ) (j : ι) :
    unitSlope (h + g) j = unitSlope h j + unitSlope g j := by
  simp only [unitSlope, Pi.add_apply]
  cases h (succ j) <;> cases h j <;> cases g (succ j) <;> cases g j <;> try simp
  norm_cast
  ring

/-! ### Convex sequences -/

/-- A sequence of extended reals is *convex* when its finiteness set is an interval and its unit
slopes are monotone on it (roadmap §0.1.1). -/
structure IsConvexSeq (h : ι → WithTop ℝ) : Prop where
  /-- The finiteness set is an interval: no `⊤` strictly between two finite values. -/
  ordConnected : (finiteSupport h).OrdConnected
  /-- The unit slopes are monotone on the finiteness set. -/
  monotoneOn : MonotoneOn (unitSlope h) (finiteSupport h)

theorem isConvexSeq_coe_iff {c : ι → ℝ} :
    IsConvexSeq (fun k ↦ ((c k : ℝ) : WithTop ℝ)) ↔ Monotone fun j ↦ c (succ j) - c j := by
  refine ⟨fun hc a b hab ↦ ?_, fun hc ↦ ⟨by simp [Set.ordConnected_univ], fun a _ b _ hab ↦ ?_⟩⟩
  · have h := hc.monotoneOn (by simp) (by simp) hab
    rwa [unitSlope_coe, unitSlope_coe, WithTop.coe_le_coe] at h
  · rw [unitSlope_coe, unitSlope_coe, WithTop.coe_le_coe]
    exact hc hab

theorem IsConvexSeq.ne_top_of_le_of_le (hh : IsConvexSeq h) {a i j : ι} (ha : h a ≠ ⊤)
    (hj : h j ≠ ⊤) (hai : a ≤ i) (hij : i ≤ j) : h i ≠ ⊤ :=
  hh.ordConnected.out ha hj ⟨hai, hij⟩

-- the a is here to guarentee we are on the right of the interval
theorem IsConvexSeq.eq_top_of_le (hh : IsConvexSeq h) {a i j : ι} (ha : h a ≠ ⊤) (hai : a ≤ i)
    (hi : h i = ⊤) (hij : i ≤ j) : h j = ⊤ :=
  by_contra fun hj ↦ hh.ne_top_of_le_of_le ha hj hai hij hi

theorem IsConvexSeq.eq_top_of_unitSlope_eq_top (hh : IsConvexSeq h) {i k : ι} (hi : h i ≠ ⊤)
    (hus : unitSlope h i = ⊤) (hik : i < k) : h k = ⊤ :=
  hh.eq_top_of_le hi (le_succ i) ((unitSlope_eq_top_iff.1 hus).resolve_left hi) (succ_le_of_lt hik)

theorem IsConvexSeq.succ_add_le_add_succ (hh : IsConvexSeq h) {a b : ι} (hab : a ≤ b) :
    h (succ a) + h b ≤ h a + h (succ b) := by
  by_cases ha : h a = ⊤
  · simp [ha]
  by_cases hb1 : h (succ b) = ⊤
  · simp [hb1]
  calc _ = h a + unitSlope h a + h b := by rw [add_unitSlope ha]
    _ ≤ h a + unitSlope h b + h b := by
      gcongr
      exact hh.monotoneOn (mem_finiteSupport.2 ha) (mem_finiteSupport.2
        (hh.ne_top_of_le_of_le ha hb1 hab (le_succ b))) hab
    _ = h a + h (succ b) := by rw [add_assoc, add_comm (unitSlope h b),
      add_unitSlope (hh.ne_top_of_le_of_le ha hb1 hab (le_succ b))]

theorem IsConvexSeq.midpoint (hh : IsConvexSeq h) (k : ι) :
    h (succ k) + h (succ k) ≤ h k + h (succ (succ k)) :=
  hh.succ_add_le_add_succ (le_succ k)

theorem midpoint_lt_of_unitSlope_lt {j : ι} (hlt : unitSlope h j < unitSlope h (succ j)) :
    h (succ j) + h (succ j) < h j + h (succ (succ j)) := by
  obtain ⟨hj, hj1⟩ := unitSlope_ne_top_iff.1 hlt.ne_top
  by_cases hj2 : h (succ (succ j)) = ⊤
  · simpa only [hj2, add_top] using (WithTop.add_ne_top.2 ⟨hj1, hj1⟩).lt_top
  rw [unitSlope_of_ne_top hj hj1, unitSlope_of_ne_top hj1 hj2, WithTop.coe_lt_coe] at hlt
  lift h j to ℝ using hj with x
  lift h (succ j) to ℝ using hj1 with y
  lift h (succ (succ j)) to ℝ using hj2 with z
  simp only [WithTop.untop₀_coe] at hlt
  norm_cast
  linarith

-- TODO move when we create this all in relevant TauCeti files
lemma _root_.MonotoneOn.empty {a b : Type*} [Preorder a] [Preorder b] (f : a → b) :
    MonotoneOn f ∅ := by
  grind [MonotoneOn]

-- TODO move to `Mathlib.Algebra.Order.Monoid.Unbundled.WithTop`
theorem _root_.WithTop.nsmul_top {α : Type*} [AddMonoid α] {n : ℕ} (hn : n ≠ 0) :
    n • (⊤ : WithTop α) = ⊤ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rfl

-- TODO move to `Mathlib.Analysis.Convex.Function`, next to `ConvexOn.sup`
theorem _root_.convexOn_ciSup {𝕜 E κ : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [SMul 𝕜 E] [SMul 𝕜 ℝ] [PosSMulMono 𝕜 ℝ] [Nonempty κ] {s : Set E} {f : κ → E → ℝ}
    (hf : ∀ i, ConvexOn 𝕜 s (f i)) (hbdd : ∀ x ∈ s, BddAbove (Set.range fun i ↦ f i x)) :
    ConvexOn 𝕜 s fun x ↦ ⨆ i, f i x :=
  ⟨(hf (Classical.arbitrary κ)).1, fun x hx y hy _ _ ha hb hab ↦ ciSup_le fun i ↦
    ((hf i).2 hx hy ha hb hab).trans (add_le_add
      (smul_le_smul_of_nonneg_left (le_ciSup (hbdd x hx) i) ha)
      (smul_le_smul_of_nonneg_left (le_ciSup (hbdd y hy) i) hb))⟩

-- TODO move to `Mathlib.Analysis.Convex.Slope`, next to `ConvexOn.slope_mono_adjacent`
theorem _root_.ConvexOn.add_one_sub_le_add_two_sub {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜} (hf : ConvexOn 𝕜 s f) {x : 𝕜} (hx : x ∈ s)
    (hx2 : x + 2 ∈ s) : f (x + 1) - f x ≤ f (x + 2) - f (x + 1) := by
  have h := hf.slope_mono_adjacent hx hx2 (lt_add_one x) (by linarith : x + 1 < x + 2)
  rwa [add_sub_cancel_left, show x + 2 - (x + 1) = 1 by ring, div_one, div_one] at h

omit [LinearOrder ι] [SuccOrder ι] in
theorem nsmul_iSup_le{κ : Type*} [Nonempty κ] {u : κ → WithTop ℝ} {c : WithTop ℝ} {n : ℕ}
    (hu : ∀ i, n • u i ≤ c) : n • ⨆ i, u i ≤ c := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using hu (Classical.arbitrary κ)
  induction c with
  | top => exact le_top
  | coe c =>
    suffices ⨆ i, u i ≤ ((c / n : ℝ) : WithTop ℝ) by
      calc _ ≤ n • ((c / n : ℝ) : WithTop ℝ) := nsmul_le_nsmul_right this n
        _ = c := by rw [← WithTop.coe_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (by aesop)]
    refine ciSup_le fun i ↦ ?_
    cases hx : u i with
    | top => simpa [hx, WithTop.nsmul_top hn] using hu i
    | coe x =>
      simpa [hx, ← WithTop.coe_nsmul, le_div_iff₀', pos_of_ne_zero hn, ← nsmul_eq_mul] using hu i

theorem isConvexSeq_top : IsConvexSeq fun _ : ι ↦ (⊤ : WithTop ℝ) := by
  have : finiteSupport (fun _ : ι ↦ (⊤ : WithTop ℝ)) = ∅ := by
    aesop
  refine {ordConnected := ?_, monotoneOn := ?_ }
  · simpa [this] using Set.ordConnected_empty
  · simpa [this] using MonotoneOn.empty _

theorem IsConvexSeq.add (hh : IsConvexSeq h) (hg : IsConvexSeq g) : IsConvexSeq (h + g) := by
  refine ⟨finiteSupport_add ▸ hh.ordConnected.inter hg.ordConnected, fun a ha b hb hab ↦ ?_⟩
  rw [finiteSupport_add] at ha hb
  simpa [unitSlope_add, unitSlope_add] using add_le_add (hh.monotoneOn ha.1 hb.1 hab)
    (hg.monotoneOn ha.2 hb.2 hab)

omit [LinearOrder ι] [SuccOrder ι] in
@[simp]
theorem finiteSupport_piecewise_top {S : Set ι} [∀ j, Decidable (j ∈ S)] :
    finiteSupport (S.piecewise h ⊤) = finiteSupport h ∩ S := by
  ext j
  by_cases hj : j ∈ S <;> simp [hj]

theorem IsConvexSeq.piecewise_top (hh : IsConvexSeq h) {S : Set ι} [∀ j, Decidable (j ∈ S)]
    (hS : S.OrdConnected) :
    IsConvexSeq (S.piecewise h ⊤) := by
  refine ⟨finiteSupport_piecewise_top (h := h) (S := S) ▸ hh.ordConnected.inter hS,
    fun a ha b hb hab ↦ ?_⟩
  rw [finiteSupport_piecewise_top] at ha hb
  by_cases hb' : (succ b : ι) ∈ S
  · simpa [unitSlope, ha.2, hS.out ha.2 hb' ⟨le_succ a, succ_le_succ hab⟩, hb.2, hb'] using
      hh.monotoneOn ha.1 hb.1 hab
  · exact le_top.trans_eq
      (unitSlope_eq_top_iff.2 (Or.inr (Set.piecewise_eq_of_notMem _ _ _ hb'))).symm

end Defs

section Sums

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι] [LocallyFiniteOrder ι] [NoMaxOrder ι]
  {h g : ι → WithTop ℝ}

theorem eq_add_nsmul_of_forall_unitSlope_eq {a k : ι} {σ : ℝ} (hak : a ≤ k)
    (hσ : ∀ j, a ≤ j → j < k → unitSlope h j = σ) :
    h k = h a + (Finset.Ico a k).card • (σ : WithTop ℝ) := by
  induction s : (Finset.Ico a k).card generalizing a with
  | zero =>
    suffices a = k by simp [this]
    exact le_antisymm hak (by simpa [← not_lt, ← Finset.Ico_eq_empty_iff, ← Finset.card_eq_zero])
  | succ n ih =>
    have hlt : a < k := Finset.nonempty_Ico.1 (Finset.card_pos.1 (by omega))
    rw [← Finset.insert_Ico_succ_left_eq_Ico hlt, Finset.card_insert_of_notMem (by simp)] at s
    rw [ih (succ_le_of_lt hlt) (fun j hj ↦ hσ j ((le_succ a).trans hj)) (by omega),
      ← add_unitSlope (unitSlope_ne_top_iff.1 ((hσ a le_rfl hlt).trans_ne WithTop.coe_ne_top)).1,
      hσ a le_rfl hlt, succ_nsmul', add_assoc]

theorem unitSlope_add_nsmul_card_Ico {c : WithTop ℝ} (hc : c ≠ ⊤) {n j : ι} (hj : n ≤ j) (σ : ℝ) :
    unitSlope (fun k ↦ c + (Finset.Ico n k).card • (σ : WithTop ℝ)) j = σ := by
  refine unitSlope_eq_of_succ_eq_add ?_ ?_
  · rw [← WithTop.coe_nsmul]
    exact WithTop.add_ne_top.2 ⟨hc, WithTop.coe_ne_top⟩
  · rw [Finset.Ico_succ_right_eq_Icc, Finset.Icc_eq_cons_Ico hj, Finset.card_cons, succ_nsmul,
      add_assoc]

theorem eq_add_sum_unitSlope {a k : ι} (hak : a ≤ k) (hfin : ∀ j, a ≤ j → j ≤ k → h j ≠ ⊤) :
    h k = h a + ((∑ j ∈ Finset.Ico a k, (unitSlope h j).untop₀ : ℝ) : WithTop ℝ) := by
  induction s : (Finset.Ico a k).card generalizing a with
  | zero =>
    suffices a = k by simp [this]
    exact le_antisymm hak (by simpa [← not_lt, ← Finset.Ico_eq_empty_iff, ← Finset.card_eq_zero])
  | succ n ih =>
    have hlt : a < k := Finset.nonempty_Ico.1 (Finset.card_pos.1 (by omega))
    rw [← Finset.insert_Ico_succ_left_eq_Ico hlt, Finset.card_insert_of_notMem (by simp)] at s
    rw [← Finset.insert_Ico_succ_left_eq_Ico hlt, Finset.sum_insert (by simp),
      ih (succ_le_of_lt hlt) (fun j hj ↦ hfin j ((le_succ a).trans hj)) (by omega),
      ← add_unitSlope (hfin a le_rfl hlt.le), WithTop.coe_add, WithTop.coe_untop₀_of_ne_top
      (unitSlope_ne_top (hfin a le_rfl hlt.le) (hfin _ (le_succ a) (succ_le_of_lt hlt))), add_assoc]

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
theorem IsConvexSeq.finiteSupport_subset_of_unitSlope_eq [IsSuccArchimedean ι] (hh : IsConvexSeq h)
    {i₀ : ι} (h₀ : h i₀ ≠ ⊤) (hg₀ : g i₀ ≠ ⊤) (hs : ∀ j, unitSlope h j = unitSlope g j) :
    finiteSupport h ⊆ finiteSupport g := by
  intro j hj
  rw [mem_finiteSupport] at hj ⊢
  rcases lt_or_ge j i₀ with hji | hij
  · exact (unitSlope_ne_top_iff.1 ((hs j).symm.trans_ne (unitSlope_ne_top hj
      (hh.ne_top_of_le_of_le hj h₀ (le_succ j) (succ_le_of_lt hji))))).1
  · obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hij
    cases n with
    | zero => exact hg₀
    | succ m =>
      rw [Function.iterate_succ_apply'] at hj ⊢
      exact (unitSlope_ne_top_iff.1 ((hs _).symm.trans_ne (unitSlope_ne_top
        (hh.ne_top_of_le_of_le h₀ hj (le_succ_iterate m i₀) (le_succ _)) hj))).2

theorem IsConvexSeq.eq_of_unitSlope_eq (hh : IsConvexSeq h) (hg : IsConvexSeq g) {i₀ : ι}
    (h₀ : h i₀ ≠ ⊤) (hg₀ : h i₀ = g i₀) (hs : ∀ j, unitSlope h j = unitSlope g j) : h = g := by
  have hsum (a b : ι) : (∑ k ∈ Finset.Ico a b, (unitSlope h k).untop₀)
      = ∑ k ∈ Finset.Ico a b, (unitSlope g k).untop₀ :=
    Finset.sum_congr rfl fun k _ ↦ by rw [hs k]
  ext j
  have htop := not_iff_not.1 (Set.ext_iff.1 ((hh.finiteSupport_subset_of_unitSlope_eq h₀ (hg₀ ▸ h₀)
    hs).antisymm (hg.finiteSupport_subset_of_unitSlope_eq (hg₀ ▸ h₀) h₀ fun k ↦ (hs k).symm)) j)
  by_cases hj : h j = ⊤
  · rw [hj, htop.1 hj]
  rcases le_or_gt i₀ j with hij | hji
  · rw [eq_add_sum_unitSlope hij fun k hk1 hk2 ↦ hh.ne_top_of_le_of_le h₀ hj hk1 hk2,
      eq_add_sum_unitSlope hij fun k hk1 hk2 ↦ hg.ne_top_of_le_of_le (hg₀ ▸ h₀) (mt htop.2 hj)
      hk1 hk2, hg₀, hsum]
  · have eh := eq_add_sum_unitSlope hji.le fun k hk1 hk2 ↦ hh.ne_top_of_le_of_le hj h₀ hk1 hk2
    rw [hg₀, eq_add_sum_unitSlope hji.le fun k hk1 hk2 ↦ hg.ne_top_of_le_of_le (mt htop.2 hj)
      (hg₀ ▸ h₀) hk1 hk2, hsum] at eh
    exact (WithTop.add_right_cancel WithTop.coe_ne_top eh).symm

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
theorem monotoneOn_unitSlope_iff_midpoint [IsSuccArchimedean ι]
    (hord : (finiteSupport h).OrdConnected) :
    MonotoneOn (unitSlope h) (finiteSupport h) ↔
      ∀ k, h (succ k) + h (succ k) ≤ h k + h (succ (succ k)) := by
  refine ⟨fun hmono ↦ IsConvexSeq.midpoint ⟨hord, hmono⟩, fun hmid a ha b hb hab ↦ ?_⟩
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab
  induction n generalizing a with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hb ⊢
    have : succ a ∈ finiteSupport h := hord.out ha hb ⟨le_succ a, le_succ_iterate n _⟩
    refine le_trans ?_ (ih _ this hb (le_succ_iterate n _))
    by_cases ha2 : h (succ (succ a)) = ⊤
    · exact le_top.trans_eq (unitSlope_eq_top_iff.2 (Or.inr ha2)).symm
    have hmk := hmid a
    simp_rw [unitSlope]
    lift h a to ℝ using ha with x
    lift h (succ a) to ℝ using this with y
    lift h (succ (succ a)) to ℝ using ha2 with z
    norm_cast at hmk ⊢
    linarith

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
theorem isConvexSeq_iff_midpoint [IsSuccArchimedean ι] :
    IsConvexSeq h ↔ (finiteSupport h).OrdConnected ∧
      ∀ k, h (succ k) + h (succ k) ≤ h k + h (succ (succ k)) :=
  ⟨fun hh ↦ ⟨hh.ordConnected, (monotoneOn_unitSlope_iff_midpoint hh.ordConnected).1 hh.monotoneOn⟩,
    fun ⟨hord, hmid⟩ ↦ ⟨hord, (monotoneOn_unitSlope_iff_midpoint hord).2 hmid⟩⟩

theorem IsConvexSeq.add_nsmul_unitSlope_le (hh : IsConvexSeq h) {i k : ι} (hi : h i ≠ ⊤)
    (hik : i ≤ k) : h i + (Finset.Ico i k).card • unitSlope h i ≤ h k := by
  induction s : (Finset.Ico i k).card generalizing i with
  | zero =>
    obtain rfl :=
      le_antisymm hik (by simpa [← not_lt, ← Finset.Ico_eq_empty_iff, ← Finset.card_eq_zero])
    simp
  | succ n ih =>
    have hlt : i < k := Finset.nonempty_Ico.1 (Finset.card_pos.1 (by omega))
    rw [← Finset.insert_Ico_succ_left_eq_Ico hlt, Finset.card_insert_of_notMem (by simp)] at s
    by_cases hsi : h (succ i) = ⊤
    · simp [hh.eq_top_of_le hi (le_succ i) hsi (succ_le_of_lt hlt)]
    calc h i + (n + 1) • unitSlope h i = h (succ i) + n • unitSlope h i := by
          rw [succ_nsmul', ← add_assoc, add_unitSlope hi]
      _ ≤ h (succ i) + n • unitSlope h (succ i) := add_le_add le_rfl (nsmul_le_nsmul_right
        (hh.monotoneOn (mem_finiteSupport.2 hi) (mem_finiteSupport.2 hsi) (le_succ i)) n)
      _ ≤ h k := ih hsi (succ_le_of_lt hlt) (by omega)

theorem IsConvexSeq.le_add_nsmul_unitSlope (hh : IsConvexSeq h) {i k : ι} (hi1 : h (succ i) ≠ ⊤)
    (hki : k ≤ i) : h (succ i) ≤ h k + (Finset.Ico k (succ i)).card • unitSlope h i := by
  by_cases hk : h k = ⊤
  · simp [hk, top_add]
  have hfin (j : ι) (h1 : k ≤ j) (h2 : j ≤ succ i) : h j ≠ ⊤ := hh.ne_top_of_le_of_le hk hi1 h1 h2
  have hbound (j : ι) (hj : j ∈ Finset.Ico k (succ i)) :
    (unitSlope h j).untop₀ ≤ (unitSlope h i).untop₀ := by
    rw [Finset.mem_Ico] at hj
    exact WithTop.untop₀_le_untop₀ (unitSlope_ne_top (hfin i hki (le_succ i)) hi1)
      (hh.monotoneOn (mem_finiteSupport.2 (hfin j hj.1 hj.2.le))
      (mem_finiteSupport.2 ( hfin i hki (le_succ i))) (le_of_lt_succ hj.2))
  calc _ = h k + ((∑ j ∈ Finset.Ico k (succ i), (unitSlope h j).untop₀ : ℝ) : WithTop ℝ) :=
        eq_add_sum_unitSlope (hki.trans (le_succ i)) hfin
    _ ≤ h k + ((((Finset.Ico k (succ i)).card : ℝ) * (unitSlope h i).untop₀ : ℝ) : WithTop ℝ) :=
        add_le_add le_rfl (WithTop.coe_le_coe.2 (by simpa using Finset.sum_le_sum hbound))
    _ = h k + (Finset.Ico k (succ i)).card • unitSlope h i := by
        rw [← nsmul_eq_mul, WithTop.coe_nsmul,
        WithTop.coe_untop₀_of_ne_top (unitSlope_ne_top (hfin i hki (le_succ i)) hi1)]

theorem IsConvexSeq.le_add_nsmul_unitSlope_self (hh : IsConvexSeq h) {a b : ι} (hab : a ≤ b) :
    h b ≤ h a + (Finset.Ico a b).card • unitSlope h b := by
  induction s : (Finset.Ico a b).card generalizing a with
  | zero =>
    obtain rfl : a = b :=
      le_antisymm hab (by simpa [← not_lt, ← Finset.Ico_eq_empty_iff, ← Finset.card_eq_zero])
    simp
  | succ n ih =>
    have hlt : a < b := Finset.nonempty_Ico.1 (Finset.card_pos.1 (by omega))
    rw [← Finset.insert_Ico_succ_left_eq_Ico hlt, Finset.card_insert_of_notMem (by simp)] at s
    by_cases ha : h a = ⊤
    · simp [ha]
    by_cases hb : h b = ⊤
    · simp [unitSlope_eq_top_iff.2 (Or.inl hb), WithTop.nsmul_top n.succ_ne_zero]
    calc h b ≤ h (succ a) + n • unitSlope h b := ih (succ_le_of_lt hlt) (by omega)
      _ = h a + unitSlope h a + n • unitSlope h b := by rw [add_unitSlope ha]
      _ ≤ h a + unitSlope h b + n • unitSlope h b :=
          add_le_add (add_le_add le_rfl (hh.monotoneOn (mem_finiteSupport.2 ha)
          (mem_finiteSupport.2 hb) hab)) le_rfl
      _ = h a + (n + 1) • unitSlope h b := by rw [succ_nsmul', add_assoc]

/-- **The chord inequality** (discrete Jensen). -/
theorem IsConvexSeq.le_chord (hh : IsConvexSeq h) {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c) :
    (Finset.Ico a c).card • h b ≤ (Finset.Ico b c).card • h a + (Finset.Ico a b).card • h c := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  rcases hbc.eq_or_lt with rfl | hbc'
  · simp
  by_cases hac : h a = ⊤ ∨ h c = ⊤
  · rcases hac with h | h <;> simp [h, WithTop.nsmul_top (Finset.nonempty_Ico.2 hab').card_pos.ne',
    WithTop.nsmul_top (Finset.nonempty_Ico.2 hbc').card_pos.ne']
  rw [not_or] at hac
  calc _ = (Finset.Ico b c).card • h b + (Finset.Ico a b).card • h b := by
        rw [← add_nsmul, add_comm, ← Finset.card_union_of_disjoint
          (Finset.Ico_disjoint_Ico_consecutive a b c), Finset.Ico_union_Ico_eq_Ico hab hbc]
    _ ≤ (Finset.Ico b c).card • (h a + (Finset.Ico a b).card • unitSlope h b) +
          (Finset.Ico a b).card • h b :=
        add_le_add (nsmul_le_nsmul_right (hh.le_add_nsmul_unitSlope_self hab) _) le_rfl
    _ = (Finset.Ico b c).card • h a + (Finset.Ico a b).card •
          (h b + (Finset.Ico b c).card • unitSlope h b) := by
        rw [nsmul_add, nsmul_add, add_assoc, add_comm (_ • _ • unitSlope h b), nsmul_left_comm]
    _ ≤ (Finset.Ico b c).card • h a + (Finset.Ico a b).card • h c :=
        add_le_add le_rfl (nsmul_le_nsmul_right (hh.add_nsmul_unitSlope_le
        (hh.ne_top_of_le_of_le hac.1 hac.2 hab hbc) hbc) _)

omit [SuccOrder ι] [LocallyFiniteOrder ι] [NoMaxOrder ι] in
private
theorem isUpperSet_finiteSupport_of_eq_on_Iic_aux (hh : (finiteSupport h).OrdConnected)
    {n : ι} (hn : h n ≠ ⊤) {f : ι → WithTop ℝ} (hfle : ∀ k, k ≤ n → f k = h k)
    (hfne : ∀ k, n < k → f k ≠ ⊤) : IsUpperSet (finiteSupport f) := by
  intro a b hab ha
  rcases le_or_gt b n with hbn | hbn
  · simpa [mem_finiteSupport, hfle b hbn] using hh.out
      (by rw [mem_finiteSupport, ← hfle a (hab.trans hbn)]; exact ha) hn ⟨hab, hbn⟩
  · exact hfne b hbn

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
private
theorem monotoneOn_of_eq_unitSlope_of_eq_const_aux
    (hh : MonotoneOn (unitSlope h) (finiteSupport h)) {n : ι} {M : ℝ}
    (hM : ∀ j, j < n → h j ≠ ⊤ → unitSlope h j ≤ M) {u : ι → WithTop ℝ} {s : Set ι}
    (hulow : ∀ j, j < n → u j = unitSlope h j) (huhigh : ∀ j, n ≤ j → u j = M)
    (hs : ∀ j ∈ s, j < n → h j ≠ ⊤) : MonotoneOn u s := by
  intro a ha b hb hab
  rcases lt_or_ge a n with han | han
  · rcases lt_or_ge b n with hbn | hbn
    · aesop
    · aesop
  · rw [huhigh a han, huhigh b (han.trans hab)]

theorem IsConvexSeq.extend_affine (hh : IsConvexSeq h) {n : ι} (hn : h n ≠ ⊤) {M : ℝ}
    (hM : ∀ j, j < n → h j ≠ ⊤ → unitSlope h j ≤ M) :
    IsConvexSeq fun k ↦ if k ≤ n then h k else h n + (Finset.Ico n k).card • (M : WithTop ℝ) := by
  set f : ι → WithTop ℝ :=
    fun k ↦ if k ≤ n then h k else h n + (Finset.Ico n k).card • (M : WithTop ℝ)
  have hfle (k : ι) (hk : k ≤ n) : f k = h k := if_pos hk
  have hfge (k : ι) (hk : n ≤ k) : f k = h n + (Finset.Ico n k).card • (M : WithTop ℝ) := by
    rcases hk.eq_or_lt with rfl | hk
    · rw [hfle _ le_rfl, Finset.Ico_self, Finset.card_empty, zero_nsmul, add_zero]
    · grind
  refine ⟨(isUpperSet_finiteSupport_of_eq_on_Iic_aux hh.ordConnected hn hfle
    fun k hk ↦ ?_).ordConnected, monotoneOn_of_eq_unitSlope_of_eq_const_aux hh.monotoneOn hM
    (fun j hj ↦ ?_) (fun j hj ↦ ?_) fun j hj hjn ↦ ?_⟩
  · simpa only [hfge k hk.le, ← WithTop.coe_nsmul] using WithTop.add_ne_top.2
      ⟨hn, WithTop.coe_ne_top⟩
  · simp only [unitSlope, hfle j hj.le, hfle (succ j) (succ_le_of_lt hj)]
  · simpa [unitSlope, hfge j hj, hfge (succ j) (hj.trans (le_succ j))] using
      unitSlope_add_nsmul_card_Ico hn hj M
  · simpa [← hfle j hjn.le]

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
theorem IsConvexSeq.sup [IsSuccArchimedean ι] (hh : IsConvexSeq h) (hg : IsConvexSeq g) :
    IsConvexSeq (h ⊔ g) := by
  refine isConvexSeq_iff_midpoint.2
    ⟨finiteSupport_sup ▸ hh.ordConnected.inter hg.ordConnected, fun k ↦ ?_⟩
  simp only [Pi.sup_apply]
  rcases le_total (h (succ k)) (g (succ k)) with hle | hle
  · simpa [sup_eq_right.2 hle] using (hg.midpoint k).trans (add_le_add le_sup_right le_sup_right)
  · simpa [sup_eq_left.2 hle] using (hh.midpoint k).trans (add_le_add le_sup_left le_sup_left)

theorem ordConnected_finiteSupport_iSup {κ : Type*} [Nonempty κ] {f : κ → ι → WithTop ℝ}
    (hf : ∀ i, IsConvexSeq (f i)) : (finiteSupport fun k ↦ ⨆ i, f i k).OrdConnected := by
  refine ⟨fun a ha c hc b hb hbtop ↦ ?_⟩
  rw [mem_finiteSupport] at ha hc
  rcases (hb.1.trans hb.2).eq_or_lt with rfl | hac
  · exact ha (le_antisymm hb.2 hb.1 ▸ hbtop)
  have hle (i : κ) (k : ι) : f i k ≤ ⨆ j, f j k :=
    le_ciSup (f := fun j ↦ f j k) (OrderTop.bddAbove _) i
  have hchord := nsmul_iSup_le fun i ↦ ((hf i).le_chord hb.1 hb.2).trans (add_le_add
    (nsmul_le_nsmul_right (hle i a) _) (nsmul_le_nsmul_right (hle i c) _))
  simp_rw [hbtop, WithTop.nsmul_top (Finset.nonempty_Ico.2 hac).card_pos.ne', top_le_iff,
    WithTop.add_eq_top] at hchord
  lift (⨆ i, f i a) to ℝ using ha with A
  lift (⨆ i, f i c) to ℝ using hc with C
  simp only [← WithTop.coe_nsmul, WithTop.coe_ne_top, or_self] at hchord

theorem IsConvexSeq.iSup {κ : Type*} [Nonempty κ] {f : κ → ι → WithTop ℝ}
    (hf : ∀ i, IsConvexSeq (f i)) : IsConvexSeq fun k ↦ ⨆ i, f i k := by
  have hle (i : κ) (k : ι) : f i k ≤ ⨆ j, f j k :=
    le_ciSup (f := fun j ↦ f j k) (OrderTop.bddAbove _) i
  refine isConvexSeq_iff_midpoint.2 ⟨ordConnected_finiteSupport_iSup hf, fun k ↦ ?_⟩
  simpa [← two_nsmul] using nsmul_iSup_le fun i ↦ (two_nsmul _).trans_le (((hf i).midpoint k).trans
    (add_le_add (hle i k) (hle i _)))

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
theorem IsConvexSeq.tendsto_unitSlope (hh : IsConvexSeq h) (hfin : ∀ k, h k ≠ ⊤)
    (hb : BddAbove (Set.range fun j ↦ (unitSlope h j).untop₀)) : Filter.Tendsto
    (fun j ↦ (unitSlope h j).untop₀) Filter.atTop (nhds (⨆ j, (unitSlope h j).untop₀)) := by
  refine tendsto_atTop_ciSup (fun i j hij ↦ ?_) hb
  exact WithTop.untop₀_le_untop₀ (unitSlope_ne_top (hfin j) (hfin (succ j)))
    (hh.monotoneOn (mem_finiteSupport.2 (hfin i)) (mem_finiteSupport.2 (hfin j)) hij)

omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in
theorem IsConvexSeq.antitone_or_eventually_monotone (hh : IsConvexSeq h) :
    (∀ k, h (succ k) ≠ ⊤ → h (succ k) ≤ h k) ∨ ∃ N, ∀ k, N ≤ k → h k ≤ h (succ k) := by
  by_cases hex : ∃ N, h N ≠ ⊤ ∧ h (succ N) ≠ ⊤ ∧ (0 : WithTop ℝ) ≤ unitSlope h N
  · obtain ⟨N, hN, -, hslope⟩ := hex
    refine Or.inr ⟨N, fun k hk ↦ ?_⟩
    by_cases hkt : h k = ⊤
    · simpa [hkt, top_le_iff] using hh.eq_top_of_le hN hk hkt (le_succ k)
    calc _ = h k + 0 := (add_zero _).symm
      _ ≤ h k + unitSlope h k := add_le_add le_rfl (hslope.trans (hh.monotoneOn
        (mem_finiteSupport.2 hN) (mem_finiteSupport.2 hkt) hk))
      _ = h (succ k) := add_unitSlope hkt
  · push Not at hex
    refine Or.inl fun k hk1 ↦ ?_
    by_cases hk : h k = ⊤
    · simp [hk]
    calc _ = h k + unitSlope h k := (add_unitSlope hk).symm
      _ ≤ h k + 0 := add_le_add le_rfl (le_of_lt (by simpa using hex k hk hk1))
      _ = h k := add_zero _

end Sums

/-! ### Sequences indexed by `ℕ`: affine sequences and the bridge to `ConvexOn` -/

section Nat

variable {h : ℕ → WithTop ℝ}

theorem unitSlope_nat (h : ℕ → WithTop ℝ) (j : ℕ) : unitSlope h j = h (j + 1) - h j := by
  rw [unitSlope, Order.succ_eq_add_one]

theorem isConvexSeq_affine (y σ : ℝ) : IsConvexSeq fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ) :=
  isConvexSeq_coe_iff.2 fun a b _ ↦ by
    simp only [Order.succ_eq_add_one]
    push_cast
    linarith

theorem isConvexSeq_affine_sub (y s i₀ : ℝ) :
    IsConvexSeq fun k : ℕ ↦ ((y + s * ((k : ℝ) - i₀) : ℝ) : WithTop ℝ) := by
  convert isConvexSeq_affine (y - s * i₀) s using 3 with k; ring

/-- The affine sequence of slope `s` through `(i₀, y)`, and `⊤` before `i₀`: the basic convex
minorant of a sequence whose first point is `(i₀, y)`. -/
noncomputable
def affineFrom (i₀ : ℕ) (y s : ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ if k < i₀ then ⊤ else ((y + s * ((k : ℝ) - i₀) : ℝ) : WithTop ℝ)

@[simp]
theorem affineFrom_of_le {i₀ k : ℕ} (hk : i₀ ≤ k) (y s : ℝ) :
    affineFrom i₀ y s k = ((y + s * ((k : ℝ) - i₀) : ℝ) : WithTop ℝ) :=
  if_neg (not_lt.2 hk)

@[simp]
theorem affineFrom_of_lt {i₀ k : ℕ} (hk : k < i₀) (y s : ℝ) : affineFrom i₀ y s k = ⊤ :=
  if_pos hk

@[simp]
theorem affineFrom_self (i₀ : ℕ) (y s : ℝ) : affineFrom i₀ y s i₀ = ((y : ℝ) : WithTop ℝ) := by
  rw [affineFrom_of_le le_rfl, sub_self, mul_zero, add_zero]

@[simp]
theorem affineFrom_eq_top_iff {i₀ k : ℕ} {y s : ℝ} : affineFrom i₀ y s k = ⊤ ↔ k < i₀ := by
  refine ⟨fun h ↦ lt_of_not_ge fun hk ↦ ?_, fun hk ↦ affineFrom_of_lt hk y s⟩
  rw [affineFrom_of_le hk] at h
  exact WithTop.coe_ne_top h

@[simp]
theorem finiteSupport_affineFrom (i₀ : ℕ) (y s : ℝ) :
    finiteSupport (affineFrom i₀ y s) = Set.Ici i₀ := by
  aesop

theorem unitSlope_affineFrom {i₀ j : ℕ} (hj : i₀ ≤ j) (y s : ℝ) :
    unitSlope (affineFrom i₀ y s) j = ((s : ℝ) : WithTop ℝ) := by
  refine unitSlope_eq_of_succ_eq_add (affineFrom_eq_top_iff.not.2 hj.not_gt) ?_
  rw [affineFrom_of_le (hj.trans (le_succ j)), affineFrom_of_le hj, ← WithTop.coe_add,
    WithTop.coe_inj, Order.succ_eq_add_one]
  grind

theorem isConvexSeq_affineFrom (i₀ : ℕ) (y s : ℝ) : IsConvexSeq (affineFrom i₀ y s) := by
  refine ⟨by rw [finiteSupport_affineFrom]; exact Set.ordConnected_Ici, fun a ha b hb _ ↦ ?_⟩
  rw [finiteSupport_affineFrom] at ha hb
  rw [unitSlope_affineFrom ha, unitSlope_affineFrom hb]

theorem IsConvexSeq.add_affine (hh : IsConvexSeq h) (y σ : ℝ) :
    IsConvexSeq fun k ↦ h k + ((y + σ * k : ℝ) : WithTop ℝ) :=
  hh.add (isConvexSeq_affine y σ)

theorem IsConvexSeq.succ_add_pred_le (hh : IsConvexSeq h) {p q : ℕ} (hpq : p < q) :
    h (p + 1) + h (q - 1) ≤ h p + h q := by
  simpa [Nat.sub_add_cancel (Nat.one_le_of_lt hpq)] using
    hh.succ_add_le_add_succ (Nat.le_sub_one_of_lt hpq)

theorem IsConvexSeq.update (hh : IsConvexSeq h) {k : ℕ} {c : WithTop ℝ} (hc : c ≠ ⊤)
    (hkc : h (k + 1) ≤ c) (hchord : c + c ≤ h k + h (k + 2)) :
    IsConvexSeq (Function.update h (k + 1) c) := by
  refine isConvexSeq_iff_midpoint.2 ⟨?_, fun j ↦ ?_⟩
  · simpa [finiteSupport_update (ne_top_of_le_ne_top hc hkc) hc] using hh.ordConnected
  · have hmid := hh.midpoint j
    simp only [succ_eq_add_one] at hmid ⊢
    rcases eq_or_ne j k with hjk | hjk
    · simpa [hjk, Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        Function.update_of_ne (show k + 1 + 1 ≠ k + 1 by omega)]
    · rw [Function.update_of_ne (show j + 1 ≠ k + 1 by omega)]
      exact hmid.trans (add_le_add ((le_update_iff.2 ⟨hkc, fun _ _ ↦ le_rfl⟩) j)
        ((le_update_iff.2 ⟨hkc, fun _ _ ↦ le_rfl⟩) (j + 1 + 1)))

theorem IsConvexSeq.exists_update_of_unitSlope_lt (hh : IsConvexSeq h) {k : ℕ}
    (hlt : unitSlope h k < unitSlope h (k + 1)) {b : WithTop ℝ} (hb : h (k + 1) < b) :
    ∃ c, h (k + 1) < c ∧ c ≤ b ∧ IsConvexSeq (Function.update h (k + 1) c) := by
  have hgap := midpoint_lt_of_unitSlope_lt (h := h) (j := k) (by rwa [succ_eq_add_one])
  simp only [succ_eq_add_one] at hgap
  obtain ⟨y, hy1, hy2⟩ := WithTop.lt_iff_exists_coe_btwn.1 hgap
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hb.ne_top
  have h1 : h (k + 1) < ((y / 2 : ℝ) : WithTop ℝ) := by
    simp_rw [← hx, ← WithTop.coe_add, WithTop.coe_lt_coe] at *
    linarith
  refine ⟨min _ b, lt_min h1 hb, min_le_right _ _,
    hh.update (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)) (le_min h1.le hb.le) ?_⟩
  calc _ ≤ ((y / 2 : ℝ) : WithTop ℝ) + ((y / 2 : ℝ) : WithTop ℝ) :=
      add_le_add (min_le_left _ _) (min_le_left _ _)
    _ = ((y : ℝ) : WithTop ℝ) := by rw [← WithTop.coe_add, add_halves]
    _ ≤ h k + h (k + 2) := hy2.le

/-- The pointwise minimum of two convex sequences need not be convex: `k ↦ min k (2 - k)` takes
the values `0, 1, 0` at `0, 1, 2`. -/
theorem not_isConvexSeq_inf :
    ¬ IsConvexSeq ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ)) :=
    fun hcx ↦ by
  have h := hcx.succ_add_pred_le (p := 0) (q := 2) two_pos
  simp only [Pi.inf_apply, ← WithTop.coe_min, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  norm_num at h

theorem IsConvexSeq.untop₀_add_mul_le (hh : IsConvexSeq h) {j k : ℕ} (hj : h j ≠ ⊤)
    (hj1 : h (j + 1) ≠ ⊤) (hk : h k ≠ ⊤) :
    (h j).untop₀ + (unitSlope h j).untop₀ * ((k : ℝ) - j) ≤ (h k).untop₀ := by
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hj
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hk
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.1 (unitSlope_ne_top hj (by aesop))
  simp only [← hx, ← hz, ← hσ, WithTop.untop₀_coe]
  rcases le_total j k with hjk | hkj
  · have hle := hh.add_nsmul_unitSlope_le hj hjk
    rw [← hx, ← hz, ← hσ, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe,
      Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hjk] at hle
    linarith
  · have hle := hh.le_add_nsmul_unitSlope_self hkj
    rw [← hx, ← hz, ← hσ, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe,
      Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hkj] at hle
    linarith

private
theorem bddAbove_range_line_aux {c s : ℕ → ℝ}
    (hline : ∀ j k : ℕ, c j + s j * ((k : ℝ) - j) ≤ c k) {x : ℝ} (hx : 0 ≤ x) :
    BddAbove (Set.range fun j : ℕ ↦ c j + s j * (x - j)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge x
  refine ⟨max (c 0) (c m), ?_⟩
  rintro _ ⟨j, rfl⟩
  rcases le_or_gt 0 (s j) with hsj | hsj
  · exact le_max_of_le_right (le_trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (by linarith) hsj)) (hline j m))
  · exact le_max_of_le_left (le_trans (add_le_add le_rfl
      (mul_le_mul_of_nonpos_left (by push_cast; linarith) hsj.le)) (hline j 0))

theorem exists_convexOn_of_forall_line_le {c s : ℕ → ℝ}
    (hline : ∀ j k : ℕ, c j + s j * ((k : ℝ) - j) ≤ c k) :
    ∃ H : ℝ → ℝ, ConvexOn ℝ (Set.Ici (0 : ℝ)) H ∧ ∀ k : ℕ, H k = c k := by
  refine ⟨fun x ↦ ⨆ j : ℕ, (c j + s j * (x - j)), convexOn_ciSup (fun j ↦ ?_) fun x hx ↦
    bddAbove_range_line_aux hline hx, fun k ↦ le_antisymm (ciSup_le fun j ↦ hline j k) ?_⟩
  · refine ⟨convex_Ici 0, fun x _ y _ a b _ _ hab ↦ le_of_eq ?_⟩
    simp only [smul_eq_mul]
    linear_combination (s j * j - c j) * hab
  · exact le_trans (by simp) (le_ciSup (bddAbove_range_line_aux hline k.cast_nonneg) k)

theorem IsConvexSeq.exists_convexOn (hh : IsConvexSeq h) (hfin : ∀ k, h k ≠ ⊤) :
    ∃ H : ℝ → ℝ, ConvexOn ℝ (Set.Ici (0 : ℝ)) H ∧ ∀ k : ℕ, H k = (h k).untop₀ :=
  exists_convexOn_of_forall_line_le fun j k ↦
    hh.untop₀_add_mul_le (hfin j) (hfin (j + 1)) (hfin k)

theorem isConvexSeq_of_convexOn {H : ℝ → ℝ} (hH : ConvexOn ℝ (Set.Ici (0 : ℝ)) H) :
    IsConvexSeq fun k : ℕ ↦ ((H k : ℝ) : WithTop ℝ) :=
  isConvexSeq_coe_iff.2 <| monotone_nat_of_le_succ fun j ↦ by
    simpa [add_assoc, one_add_one_eq_two] using
      hH.add_one_sub_le_add_two_sub (x := (j : ℝ)) (Set.mem_Ici.2 j.cast_nonneg)
        (Set.mem_Ici.2 (by positivity))

end Nat

end NewtonPolygon
