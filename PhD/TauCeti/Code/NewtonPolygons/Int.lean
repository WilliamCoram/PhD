/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.SuccPred
import PhD.TauCeti.Code.NewtonPolygons.Basic

/-!
# Newton polygons indexed by `ℤ`

The definition of `Basic.lean` is index-agnostic, so a sequence of points indexed by `ℤ` — the
coefficient valuations of a Laurent series — has a Newton polygon in exactly the same sense: the
greatest convex minorant. What is new on `ℤ` is the possibility of a *left ray* (points running to
`−∞` with slopes bounded above); nothing else changes, and no `⊥` value is needed (roadmap
convention 5: `⊤` means "no polygon here" on both sides).

This file does two things and deliberately no more (roadmap §0.2.6).

* **Reduction.** A `ℕ`-indexed sequence `v` extended by `⊤` on the negatives has, as a `ℤ`-indexed
  sequence, the `ℤ`-polygon that is the extension of its `ℕ`-polygon (`newtonPolygon_extendTop`).
  So every statement about `ℕ`-polygons is a statement about `ℤ`-polygons of left-bounded point
  sets, and the one-sided theory of the later files applies to them after a shift.
* **Existence on `ℤ`.** A convex minorant exists exactly when the points lie on or above a single
  line (`exists_isConvexMinorant_iff_exists_line`). ⚠ The pointwise condition "slopes bounded below
  to the right and above to the left from every point" is **not** sufficient: `v k = -|k|` satisfies
  it at every point and has no convex minorant (`not_exists_isConvexMinorant_neg_abs`) — its hull is
  `−∞` everywhere.

The one-sided API (vertices, faces, the slope multiset, Minkowski sums, the vertex walk) is not
developed on `ℤ`.

Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/Int.lean`.
-/

open scoped Classical
open Order

namespace NewtonPolygon

variable {v h : ℕ → WithTop ℝ}

/-! ### Reduction: `ℕ`-indexed sequences as `ℤ`-indexed ones -/

/-- Extend a `ℕ`-indexed sequence by `⊤` on the negative integers. -/
noncomputable def extendTop (v : ℕ → WithTop ℝ) : ℤ → WithTop ℝ :=
  fun k ↦ if 0 ≤ k then v k.toNat else ⊤

/-- On the nonnegative integers the extension is the original sequence. -/
@[simp] theorem extendTop_natCast (v : ℕ → WithTop ℝ) (n : ℕ) : extendTop v n = v n := by
  simp only [extendTop, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]

/-- Below `0` the extension is `⊤`. -/
theorem extendTop_of_neg (v : ℕ → WithTop ℝ) {k : ℤ} (hk : k < 0) : extendTop v k = ⊤ := by
  simp only [extendTop]
  rw [if_neg (not_le.2 hk)]

/-- At a nonnegative index the extension is the original sequence at its natural-number form. -/
theorem extendTop_of_nonneg (v : ℕ → WithTop ℝ) {k : ℤ} (hk : 0 ≤ k) :
    extendTop v k = v k.toNat := by
  simp only [extendTop]
  rw [if_pos hk]

/-- The extension carries points only at nonnegative indices. -/
theorem nonneg_of_extendTop_ne_top (v : ℕ → WithTop ℝ) {k : ℤ} (hk : extendTop v k ≠ ⊤) :
    0 ≤ k := by
  by_contra hc
  exact hk (extendTop_of_neg v (not_le.1 hc))

/-- The successor of a cast natural number is the cast of its successor. -/
theorem succ_natCast (n : ℕ) : succ (n : ℤ) = ((n + 1 : ℕ) : ℤ) := by
  rw [Order.succ_eq_add_one]
  push_cast
  ring

/-- The unit slopes of the restriction of a `ℤ`-indexed sequence to the naturals are its unit slopes
at the naturals. -/
theorem unitSlope_comp_natCast (G : ℤ → WithTop ℝ) (n : ℕ) :
    unitSlope (fun m : ℕ ↦ G (m : ℤ)) n = unitSlope G n := by
  simp only [unitSlope, Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one]

/-- The unit slopes of the extension at nonnegative indices are those of the original sequence. -/
theorem unitSlope_extendTop_natCast (h : ℕ → WithTop ℝ) (n : ℕ) :
    unitSlope (extendTop h) n = unitSlope h n := by
  rw [← unitSlope_comp_natCast (extendTop h) n]
  simp only [unitSlope, extendTop_natCast]

/-- The restriction of a convex `ℤ`-indexed sequence to the naturals is convex. -/
theorem IsConvexSeq.comp_natCast {G : ℤ → WithTop ℝ} (hG : IsConvexSeq G) :
    IsConvexSeq fun n : ℕ ↦ G (n : ℤ) := by
  refine ⟨⟨fun a ha c hc b hb ↦ ?_⟩, fun a ha b hb hab ↦ ?_⟩
  · exact mem_finiteSet.2 (mem_finiteSet.1 (hG.ordConnected.out
      (mem_finiteSet.2 (mem_finiteSet.1 ha)) (mem_finiteSet.2 (mem_finiteSet.1 hc))
      ⟨Nat.cast_le.2 hb.1, Nat.cast_le.2 hb.2⟩))
  · rw [unitSlope_comp_natCast, unitSlope_comp_natCast]
    exact hG.monotoneOn (mem_finiteSet.2 (mem_finiteSet.1 ha))
      (mem_finiteSet.2 (mem_finiteSet.1 hb)) (Nat.cast_le.2 hab)

/-- The extension is convex exactly when the original sequence is. -/
theorem isConvexSeq_extendTop_iff : IsConvexSeq (extendTop h) ↔ IsConvexSeq h := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ ⟨⟨fun a ha c hc' b hb ↦ ?_⟩, fun a ha b hb hab ↦ ?_⟩⟩
  · have := hc.comp_natCast
    simpa only [extendTop_natCast] using this
  · have ha0 : 0 ≤ a := nonneg_of_extendTop_ne_top h (mem_finiteSet.1 ha)
    have hb0 : 0 ≤ b := ha0.trans hb.1
    refine mem_finiteSet.2 ?_
    rw [extendTop_of_nonneg h hb0]
    refine mem_finiteSet.1 (hc.ordConnected.out (mem_finiteSet.2 ?_) (mem_finiteSet.2 ?_)
      ⟨Int.toNat_le_toNat hb.1, Int.toNat_le_toNat hb.2⟩)
    · rw [← extendTop_of_nonneg h ha0]
      exact mem_finiteSet.1 ha
    · rw [← extendTop_of_nonneg h (hb0.trans hb.2)]
      exact mem_finiteSet.1 hc'
  · have ha0 : 0 ≤ a := nonneg_of_extendTop_ne_top h (mem_finiteSet.1 ha)
    have hb0 : 0 ≤ b := nonneg_of_extendTop_ne_top h (mem_finiteSet.1 hb)
    have hua : unitSlope (extendTop h) a = unitSlope h a.toNat := by
      conv_lhs => rw [← Int.toNat_of_nonneg ha0]
      rw [unitSlope_extendTop_natCast]
    have hub : unitSlope (extendTop h) b = unitSlope h b.toNat := by
      conv_lhs => rw [← Int.toNat_of_nonneg hb0]
      rw [unitSlope_extendTop_natCast]
    rw [hua, hub]
    refine hc.monotoneOn (mem_finiteSet.2 ?_) (mem_finiteSet.2 ?_) (Int.toNat_le_toNat hab)
    · rw [← extendTop_of_nonneg h ha0]
      exact mem_finiteSet.1 ha
    · rw [← extendTop_of_nonneg h hb0]
      exact mem_finiteSet.1 hb

/-- Convex minorants transport along the extension. -/
theorem isConvexMinorant_extendTop_iff :
    IsConvexMinorant (extendTop v) (extendTop h) ↔ IsConvexMinorant v h := by
  rw [IsConvexMinorant, IsConvexMinorant, isConvexSeq_extendTop_iff]
  refine and_congr_right fun _ ↦ ⟨fun hle k ↦ ?_, fun hle k ↦ ?_⟩
  · rw [← extendTop_natCast h k, ← extendTop_natCast v k]
    exact hle k
  · rcases le_or_gt 0 k with hk | hk
    · rw [extendTop_of_nonneg h hk, extendTop_of_nonneg v hk]
      exact hle _
    · rw [extendTop_of_neg h hk, extendTop_of_neg v hk]

/-- The polygon transports along the extension: this is the reduction of `ℤ` to `ℕ`. -/
theorem isNewtonPolygonOf_extendTop_iff :
    IsNewtonPolygonOf (extendTop v) (extendTop h) ↔ IsNewtonPolygonOf v h := by
  constructor
  · intro hh
    refine ⟨isConvexSeq_extendTop_iff.1 hh.convex, fun k ↦ ?_, fun g hgc hgv k ↦ ?_⟩
    · rw [← extendTop_natCast h k, ← extendTop_natCast v k]
      exact hh.le_points k
    · have hmin : IsConvexMinorant (extendTop v) (extendTop g) :=
        isConvexMinorant_extendTop_iff.2 ⟨hgc, hgv⟩
      have hle := hh.greatest (extendTop g) hmin.1 hmin.2 (k : ℤ)
      rwa [extendTop_natCast, extendTop_natCast] at hle
  · intro hh
    refine ⟨isConvexSeq_extendTop_iff.2 hh.convex,
      (isConvexMinorant_extendTop_iff.2 hh.isConvexMinorant).2, fun G hGc hGv k ↦ ?_⟩
    rcases le_or_gt 0 k with hk | hk
    · have hGnv : ∀ m : ℕ, G (m : ℤ) ≤ v m := by
        intro m
        have hx := hGv (m : ℤ)
        rwa [extendTop_natCast] at hx
      have hle := hh.greatest _ hGc.comp_natCast hGnv k.toNat
      rw [extendTop_of_nonneg h hk]
      rwa [Int.toNat_of_nonneg hk] at hle
    · rw [extendTop_of_neg h hk]
      exact le_top

/-- **The reduction**: the `ℤ`-polygon of a left-bounded point set is the extension of its
`ℕ`-polygon. -/
theorem newtonPolygon_extendTop (hv : IsAdmissible v) :
    newtonPolygon (extendTop v) = extendTop (newtonPolygon v) :=
  (isNewtonPolygonOf_extendTop_iff.2
    (isNewtonPolygonOf_newtonPolygon
      (exists_isConvexMinorant_iff_isAdmissible.2 hv))).eq_newtonPolygon.symm

/-! ### Existence on `ℤ` -/

/-- Affine sequences on `ℤ` are convex. -/
theorem isConvexSeq_affine_int (y σ : ℝ) :
    IsConvexSeq fun k : ℤ ↦ ((y + σ * k : ℝ) : WithTop ℝ) := by
  have hu : ∀ j : ℤ,
      unitSlope (fun k : ℤ ↦ ((y + σ * k : ℝ) : WithTop ℝ)) j = ((σ : ℝ) : WithTop ℝ) := by
    intro j
    refine unitSlope_eq_of_succ_eq_add WithTop.coe_ne_top ?_
    show ((y + σ * ((succ j : ℤ) : ℝ) : ℝ) : WithTop ℝ)
        = ((y + σ * j : ℝ) : WithTop ℝ) + ((σ : ℝ) : WithTop ℝ)
    rw [← WithTop.coe_add, WithTop.coe_inj, Order.succ_eq_add_one]
    push_cast
    ring
  have hfs : finiteSet (fun k : ℤ ↦ ((y + σ * k : ℝ) : WithTop ℝ)) = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ mem_finiteSet.2 WithTop.coe_ne_top
  exact ⟨by rw [hfs]; exact Set.ordConnected_univ, fun a _ b _ _ ↦ by rw [hu, hu]⟩

/-- **A convex minorant exists exactly when the points lie on or above a single line.** The line is
a convex minorant; conversely a convex minorant finite at `i` lies above the line of its unit slope
at `i` through `(i, g i)`, on both sides. -/
theorem exists_isConvexMinorant_iff_exists_line {v : ℤ → WithTop ℝ} :
    (∃ g, IsConvexMinorant v g) ↔ ∃ y σ : ℝ, ∀ k : ℤ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k := by
  refine ⟨?_, fun ⟨y, σ, hline⟩ ↦ ⟨_, isConvexSeq_affine_int y σ, hline⟩⟩
  rintro ⟨g, hgc, hgv⟩
  have hcardcast : ∀ {p q : ℤ}, p ≤ q → (((Finset.Ico p q).card : ℕ) : ℝ) = (q : ℝ) - p := by
    intro p q hpq
    rw [Int.card_Ico]
    have htn : (((q - p).toNat : ℕ) : ℤ) = q - p := Int.toNat_of_nonneg (sub_nonneg.2 hpq)
    calc (((q - p).toNat : ℕ) : ℝ) = ((((q - p).toNat : ℕ) : ℤ) : ℝ) := by push_cast; ring
      _ = ((q - p : ℤ) : ℝ) := by rw [htn]
      _ = (q : ℝ) - p := by push_cast; ring
  have htopv : ∀ k : ℤ, g k = ⊤ → v k = ⊤ := by
    intro k hkt
    refine top_le_iff.1 ?_
    rw [← hkt]
    exact hgv k
  by_cases hall : ∀ k : ℤ, g k = ⊤
  · refine ⟨0, 0, fun k ↦ ?_⟩
    rw [htopv k (hall k)]
    exact le_top
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 hi
  set s : ℝ := if unitSlope g i = ⊤ then (unitSlope g (i - 1)).untop₀
    else (unitSlope g i).untop₀ with hsdef
  have hsucc_pred : succ (i - 1) = i := by
    rw [Order.succ_eq_add_one]
    ring
  refine ⟨a - s * (i : ℝ), s, fun k ↦ ?_⟩
  have hshift : ((a - s * (i : ℝ) + s * k : ℝ) : WithTop ℝ)
      = ((a + s * ((k : ℝ) - i) : ℝ) : WithTop ℝ) := by
    congr 1
    ring
  rw [hshift]
  rcases lt_or_ge k i with hk | hk
  · -- to the left of `i`, via the unit slope at `i - 1`
    by_cases husm : unitSlope g (i - 1) = ⊤
    · have hgm : g (i - 1) = ⊤ := by
        rcases unitSlope_eq_top_iff.1 husm with hx | hx
        · exact hx
        · rw [hsucc_pred] at hx
          exact absurd hx hi
      have hgk : g k = ⊤ := by
        by_contra hc
        exact (mem_finiteSet.1 (hgc.ordConnected.out (mem_finiteSet.2 hc) (mem_finiteSet.2 hi)
          ⟨by omega, by omega⟩)) hgm
      rw [htopv k hgk]
      exact le_top
    by_cases hgk : g k = ⊤
    · rw [htopv k hgk]
      exact le_top
    obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 hgk
    obtain ⟨sm, hsm⟩ := WithTop.ne_top_iff_exists.1 husm
    have hsmle : sm ≤ s := by
      by_cases hus : unitSlope g i = ⊤
      · rw [hsdef, if_pos hus, ← hsm, WithTop.untop₀_coe]
      · rw [hsdef, if_neg hus]
        have hgm : g (i - 1) ≠ ⊤ := fun hx ↦ husm (unitSlope_eq_top_iff.2 (Or.inl hx))
        have hmono := hgc.monotoneOn (mem_finiteSet.2 hgm) (mem_finiteSet.2 hi) (by omega)
        have hfin := WithTop.untop₀_le_untop₀ hus hmono
        rw [← hsm] at hfin
        simpa using hfin
    have hbound := hgc.le_add_nsmul_unitSlope (i := i - 1) (k := k)
      (by rw [hsucc_pred]; exact hi) (by omega)
    rw [hsucc_pred, ← hA, ← hB, ← hsm, ← WithTop.coe_nsmul, ← WithTop.coe_add,
      WithTop.coe_le_coe, nsmul_eq_mul, hcardcast (by omega : k ≤ i)] at hbound
    refine le_trans ?_ (hgv k)
    rw [← hB, WithTop.coe_le_coe]
    have hik : (k : ℝ) < (i : ℝ) := by exact_mod_cast hk
    nlinarith [hbound, mul_le_mul_of_nonneg_left hsmle (by linarith : (0 : ℝ) ≤ (i : ℝ) - k)]
  · -- to the right of `i`, via the unit slope at `i`
    by_cases hus : unitSlope g i = ⊤
    · rcases eq_or_lt_of_le hk with rfl | hlt
      · rw [show ((a + s * ((i : ℝ) - i) : ℝ) : WithTop ℝ) = ((a : ℝ) : WithTop ℝ) by congr 1; ring,
          hA]
        exact hgv i
      · have hgsucc : g (i + 1) = ⊤ := by
          rcases unitSlope_eq_top_iff.1 hus with hx | hx
          · exact absurd hx hi
          · rwa [Order.succ_eq_add_one] at hx
        have hgk : g k = ⊤ :=
          hgc.eq_top_of_le hi (by omega : i ≤ i + 1) hgsucc (by omega : i + 1 ≤ k)
        rw [htopv k hgk]
        exact le_top
    · have hs' : s = (unitSlope g i).untop₀ := by rw [hsdef, if_neg hus]
      obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 hus
      by_cases hgk : g k = ⊤
      · rw [htopv k hgk]
        exact le_top
      obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 hgk
      have hbound := hgc.add_nsmul_unitSlope_le hi hk
      rw [← hA, ← hB, ← hu, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe,
        nsmul_eq_mul, hcardcast hk] at hbound
      refine le_trans ?_ (hgv k)
      rw [← hB, WithTop.coe_le_coe, hs', ← hu]
      simp only [WithTop.untop₀_coe]
      nlinarith [hbound]

/-- A `ℤ`-indexed polygon is `⊤` to the left of every point. -/
theorem IsNewtonPolygonOf.eq_top_of_forall_lt {v h : ℤ → WithTop ℝ} (hh : IsNewtonPolygonOf v h)
    {k : ℤ} (hk : ∀ j ≤ k, v j = ⊤) : h k = ⊤ := by
  obtain ⟨y, s, hline⟩ := exists_isConvexMinorant_iff_exists_line.1 ⟨h, hh.isConvexMinorant⟩
  have key : ∀ c : ℝ, y + s * k ≤ c → ((c : ℝ) : WithTop ℝ) ≤ h k := by
    intro c hc
    have hconv : IsConvexSeq
        (fun j : ℤ ↦ ((c + (s - (c - (y + s * k))) * ((j : ℝ) - k) : ℝ) : WithTop ℝ)) := by
      have heq : (fun j : ℤ ↦ ((c + (s - (c - (y + s * k))) * ((j : ℝ) - k) : ℝ) : WithTop ℝ))
          = fun j : ℤ ↦ (((c - (s - (c - (y + s * k))) * k)
            + (s - (c - (y + s * k))) * j : ℝ) : WithTop ℝ) := by
        funext j
        congr 1
        ring
      rw [heq]
      exact isConvexSeq_affine_int _ _
    have hmin : ∀ j : ℤ,
        ((c + (s - (c - (y + s * k))) * ((j : ℝ) - k) : ℝ) : WithTop ℝ) ≤ v j := by
      intro j
      rcases le_or_gt j k with hj | hj
      · rw [hk j hj]
        exact le_top
      refine le_trans ?_ (hline j)
      rw [WithTop.coe_le_coe]
      have h1 : (1 : ℝ) ≤ (j : ℝ) - k := by
        have : (k : ℝ) + 1 ≤ (j : ℝ) := by
          have : k + 1 ≤ j := by omega
          exact_mod_cast this
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

/-- The pointwise two-sided slope condition does not suffice on `ℤ`: `v k = -|k|` has its slopes
bounded below to the right and above to the left from every point, and no convex minorant. -/
theorem not_exists_isConvexMinorant_neg_abs :
    ¬ ∃ g, IsConvexMinorant (fun k : ℤ ↦ ((-|(k : ℝ)| : ℝ) : WithTop ℝ)) g := by
  intro hg
  obtain ⟨y, σ, hline⟩ := exists_isConvexMinorant_iff_exists_line.1 hg
  obtain ⟨m, hm⟩ := exists_nat_gt (|y| + 1)
  have h1 := hline (m : ℤ)
  have h2 := hline (-(m : ℤ))
  rw [WithTop.coe_le_coe] at h1 h2
  push_cast at h1 h2
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))] at h1
  rw [abs_of_nonpos (neg_nonpos.2 (by positivity : (0 : ℝ) ≤ (m : ℝ)))] at h2
  have habs : -|y| ≤ y := neg_abs_le y
  linarith

end NewtonPolygon
