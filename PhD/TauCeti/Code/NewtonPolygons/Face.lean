/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.Slope

/-!
# Supporting lines, faces, and the competitor lemma

Two ways of reading a Newton polygon through lines. The *competitor lemma*: a convex broken line
lying on or below every point lies on or below the polygon — the instance of maximality the
arithmetic layers consume, with a single line as the special case (the *supporting-line lemma*).
And the *faces*: for a real `σ`, the face of slope `σ` is the segment on which the supporting line
of slope `σ` touches the polygon; its endpoints `faceLeft h σ` and `faceRight h σ` count the unit
slopes `< σ` and `≤ σ`, so the multiplicity of `σ` as a slope is their difference.

[Ked07, §2]: "`v_r` is the `y`-intercept of the supporting line of the Newton polygon of slope `r`";
[Ked07, proof of Cor. 2]: "the left and right endpoints of the segment of slope `r` in the Newton
polygon are the points where the support lines of slightly smaller and slightly larger slope,
respectively, touch the polygon."

Face endpoints are indices counted from `0`, so the face statements assume the polygon is anchored
at `0` (`h 0 ≠ ⊤`), which is the case for every polygon the arithmetic layers produce
(`coeff 0 = 1`); a polygon anchored elsewhere is handled by translation.

Roadmap: §0.5. Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/Face.lean`.

## Main results

* `NewtonPolygon.IsNewtonPolygonOf.line_le` — the supporting-line lemma.
* `NewtonPolygon.IsNewtonPolygonOf.twoSlope_le` — the competitor lemma.
* `NewtonPolygon.IsConvexSeq.line_le_iff` — a line through `(n, h n)` lies below `h` iff its slope
  separates the unit slopes at `n`.
* `NewtonPolygon.faceRight_sub_faceLeft` — the multiplicity of a slope is the width of its face.
* `NewtonPolygon.IsConvexSeq.slopesUnbounded_or_endsInRay_or_tendsto` — the trichotomy: unbounded
  slopes, a terminal ray, or an unattained supremum.
-/

open scoped Classical

namespace NewtonPolygon

variable {v h : ℕ → WithTop ℝ}

/-! ### Supporting lines and the competitor lemma -/

/-- **The supporting-line lemma** (roadmap §0.5.1): a line on or below every point lies on or below
the Newton polygon. The workhorse of the arithmetic layers. -/
theorem IsNewtonPolygonOf.line_le (hh : IsNewtonPolygonOf v h) {y σ : ℝ}
    (hle : ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k) (k : ℕ) :
    ((y + σ * k : ℝ) : WithTop ℝ) ≤ h k :=
  hh.greatest _ (isConvexSeq_affine y σ) hle k

/-- The two-slope broken line through `(0, y)`: slope `σ` on `[0, N]`, slope `τ` afterwards. -/
noncomputable def twoSlope (y σ τ : ℝ) (N : ℕ) : ℕ → WithTop ℝ :=
  fun k ↦ ((y + σ * min (k : ℝ) N + τ * ((k : ℝ) - min (k : ℝ) N) : ℝ) : WithTop ℝ)

/-- A two-slope sequence is convex as soon as the first slope is the smaller one. -/
theorem isConvexSeq_twoSlope (y : ℝ) {σ τ : ℝ} (hστ : σ ≤ τ) (N : ℕ) :
    IsConvexSeq (twoSlope y σ τ N) := by
  have hu : ∀ j : ℕ, unitSlope (twoSlope y σ τ N) j
      = ((if j < N then σ else τ : ℝ) : WithTop ℝ) := by
    intro j
    refine unitSlope_eq_of_succ_eq_add WithTop.coe_ne_top ?_
    rw [Order.succ_eq_add_one]
    simp only [twoSlope, ← WithTop.coe_add, WithTop.coe_inj]
    split_ifs with hj
    · rw [min_eq_left (by exact_mod_cast hj.le : (j : ℝ) ≤ (N : ℝ)),
        min_eq_left (by exact_mod_cast (by omega : j + 1 ≤ N) : (((j + 1 : ℕ) : ℝ)) ≤ (N : ℝ))]
      push_cast
      ring
    · rw [min_eq_right (by exact_mod_cast (by omega : N ≤ j) : (N : ℝ) ≤ (j : ℝ)),
        min_eq_right (by exact_mod_cast (by omega : N ≤ j + 1) : (N : ℝ) ≤ (((j + 1 : ℕ) : ℝ)))]
      push_cast
      ring
  have hfs : finiteSet (twoSlope y σ τ N) = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ mem_finiteSet.2 WithTop.coe_ne_top
  refine ⟨by rw [hfs]; exact Set.ordConnected_univ, fun a _ b _ hab ↦ ?_⟩
  rw [hu a, hu b, WithTop.coe_le_coe]
  split_ifs with ha hb hb
  · exact le_rfl
  · exact hστ
  · omega
  · exact le_rfl

/-- **The competitor lemma** (roadmap §0.5.2): a two-slope broken line on or below every point lies
on or below the Newton polygon. -/
theorem IsNewtonPolygonOf.twoSlope_le (hh : IsNewtonPolygonOf v h) (y : ℝ) {σ τ : ℝ}
    (hστ : σ ≤ τ) (N : ℕ) (hle : ∀ k, twoSlope y σ τ N k ≤ v k) (k : ℕ) :
    twoSlope y σ τ N k ≤ h k :=
  hh.greatest _ (isConvexSeq_twoSlope y hστ N) hle k

/-- **The supporting line at an index**, from convexity alone: the line of slope `σ` through
`(n, h n)` lies on or below `h` if and only if `σ` separates the unit slopes at `n`. -/
theorem IsConvexSeq.line_le_iff (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) (σ : ℝ) :
    (∀ k : ℕ, (((h n).untop₀ + σ * ((k : ℝ) - n) : ℝ) : WithTop ℝ) ≤ h k) ↔
      (∀ j, j < n → h j ≠ ⊤ → unitSlope h j ≤ σ) ∧
        ∀ j, n ≤ j → (σ : WithTop ℝ) ≤ unitSlope h j := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hn
  have hna : (h n).untop₀ = a := by rw [← ha, WithTop.untop₀_coe]
  constructor
  · intro hline
    refine ⟨fun j hj hjf ↦ ?_, fun j hj ↦ ?_⟩
    · by_cases hsj : unitSlope h j = ⊤
      · exfalso
        have hsucc : h (j + 1) = ⊤ := by
          rcases unitSlope_eq_top_iff.1 hsj with hx | hx
          · exact absurd hx hjf
          · rwa [Order.succ_eq_add_one] at hx
        exact hn (hh.eq_top_of_le hjf (by omega) hsucc (by omega))
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hsj
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hjf
      have hb := hh.add_nsmul_unitSlope_le hjf hj.le
      rw [← hc, ← hs, ← ha, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe,
        nsmul_eq_mul, Nat.card_Ico, Nat.cast_sub hj.le] at hb
      have hl := hline j
      rw [hna, ← hc, WithTop.coe_le_coe] at hl
      rw [← hs, WithTop.coe_le_coe]
      have hpos : (0 : ℝ) < (n : ℝ) - j := by
        have hx : (j : ℝ) < (n : ℝ) := Nat.cast_lt.2 hj
        linarith
      nlinarith [hb, hl, hpos]
    · by_cases hsj : unitSlope h j = ⊤
      · rw [hsj]
        exact le_top
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hsj
      have hjf : h j ≠ ⊤ ∧ h (j + 1) ≠ ⊤ := mem_slopeIndices_iff.1 hsj
      obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.1 hjf.2
      have hb := hh.le_add_nsmul_unitSlope (i := j) (k := n)
        (by rw [Order.succ_eq_add_one]; exact hjf.2) hj
      rw [Order.succ_eq_add_one, ← hd, ← ha, ← hs, ← WithTop.coe_nsmul, ← WithTop.coe_add,
        WithTop.coe_le_coe, nsmul_eq_mul, Nat.card_Ico, Nat.cast_sub (by omega : n ≤ j + 1)] at hb
      have hl := hline (j + 1)
      rw [hna, ← hd, WithTop.coe_le_coe] at hl
      rw [← hs, WithTop.coe_le_coe]
      have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) - n := by
        have hx : (n : ℝ) < ((j + 1 : ℕ) : ℝ) := Nat.cast_lt.2 (by omega)
        linarith
      push_cast at hb hl hpos
      nlinarith [hb, hl, hpos]
  · rintro ⟨h₁, h₂⟩ k
    rcases lt_trichotomy k n with hk | rfl | hk
    · by_cases hkt : h k = ⊤
      · rw [hkt]
        exact le_top
      obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hkt
      have hprev : h (n - 1) ≠ ⊤ := mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 hkt)
        (mem_finiteSet.2 hn) ⟨by omega, by omega⟩)
      have hsle := h₁ (n - 1) (by omega) hprev
      have hsne : unitSlope h (n - 1) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hsle
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hsne
      have hbnd := hh.le_add_nsmul_unitSlope (i := n - 1) (k := k)
        (by rw [Order.succ_eq_add_one, show n - 1 + 1 = n by omega]; exact hn) (by omega)
      rw [Order.succ_eq_add_one, show n - 1 + 1 = n by omega, ← ha, ← hb, ← hs,
        ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul, Nat.card_Ico,
        Nat.cast_sub hk.le] at hbnd
      rw [hna, ← hb, WithTop.coe_le_coe]
      rw [← hs, WithTop.coe_le_coe] at hsle
      have hpos : (0 : ℝ) ≤ (n : ℝ) - k := by
        have hx : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hk.le
        linarith
      nlinarith [hbnd, hsle, hpos]
    · rw [hna, ← ha]
      simp only [sub_self, mul_zero, add_zero, Std.le_refl]
    · calc (((h n).untop₀ + σ * ((k : ℝ) - n) : ℝ) : WithTop ℝ)
          = h n + (k - n : ℕ) • ((σ : ℝ) : WithTop ℝ) := by
            rw [hna, ← ha, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
              Nat.cast_sub hk.le]
            congr 1
            ring
        _ ≤ h n + (k - n : ℕ) • unitSlope h n :=
            add_le_add le_rfl (nsmul_le_nsmul_right (h₂ n le_rfl) _)
        _ ≤ h k := by
            rw [← Nat.card_Ico]
            exact hh.add_nsmul_unitSlope_le hn hk.le

/-- Strictly to the left of `n`, a line whose slope exceeds every earlier unit slope is strictly
below `h`. -/
theorem IsConvexSeq.line_lt_of_unitSlope_lt (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) {σ : ℝ}
    (h₁ : ∀ j, j < n → h j ≠ ⊤ → unitSlope h j < σ) {k : ℕ} (hk : k < n) (hkfin : h k ≠ ⊤) :
    (((h n).untop₀ + σ * ((k : ℝ) - n) : ℝ) : WithTop ℝ) < h k := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hn
  have hna : (h n).untop₀ = a := by rw [← ha, WithTop.untop₀_coe]
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hkfin
  have hprev : h (n - 1) ≠ ⊤ := mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 hkfin)
    (mem_finiteSet.2 hn) ⟨by omega, by omega⟩)
  have hslt := h₁ (n - 1) (by omega) hprev
  have hsne : unitSlope h (n - 1) ≠ ⊤ := ne_top_of_lt hslt
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hsne
  have hbnd := hh.le_add_nsmul_unitSlope (i := n - 1) (k := k)
    (by rw [Order.succ_eq_add_one, show n - 1 + 1 = n by omega]; exact hn) (by omega)
  rw [Order.succ_eq_add_one, show n - 1 + 1 = n by omega, ← ha, ← hb, ← hs,
    ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul, Nat.card_Ico,
    Nat.cast_sub hk.le] at hbnd
  rw [← hs, WithTop.coe_lt_coe] at hslt
  rw [hna, ← hb, WithTop.coe_lt_coe]
  have hpos : (0 : ℝ) < (n : ℝ) - k := by
    have hx : (k : ℝ) < (n : ℝ) := Nat.cast_lt.2 hk
    linarith
  nlinarith [hbnd, mul_pos hpos (sub_pos.2 hslt)]

/-- Strictly to the right of `n`, a line whose slope is below every later unit slope is strictly
below `h`. -/
theorem IsConvexSeq.line_lt_of_lt_unitSlope (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) {σ : ℝ}
    (h₂ : ∀ j, n ≤ j → (σ : WithTop ℝ) < unitSlope h j) {k : ℕ} (hk : n < k) :
    (((h n).untop₀ + σ * ((k : ℝ) - n) : ℝ) : WithTop ℝ) < h k := by
  by_cases hkt : h k = ⊤
  · rw [hkt]
    exact WithTop.coe_lt_top _
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hn
  have hna : (h n).untop₀ = a := by rw [← ha, WithTop.untop₀_coe]
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hkt
  have hsne : unitSlope h n ≠ ⊤ := by
    intro hc
    have hsucc : h (n + 1) = ⊤ := by
      rcases unitSlope_eq_top_iff.1 hc with hx | hx
      · exact absurd hx hn
      · rwa [Order.succ_eq_add_one] at hx
    exact hkt (hh.eq_top_of_le hn (by omega) hsucc (by omega))
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hsne
  have hslt := h₂ n le_rfl
  rw [← hs, WithTop.coe_lt_coe] at hslt
  have hbnd := hh.add_nsmul_unitSlope_le hn hk.le
  rw [← ha, ← hb, ← hs, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe,
    nsmul_eq_mul, Nat.card_Ico, Nat.cast_sub hk.le] at hbnd
  rw [hna, ← hb, WithTop.coe_lt_coe]
  have hpos : (0 : ℝ) < (k : ℝ) - n := by
    have hx : (n : ℝ) < (k : ℝ) := Nat.cast_lt.2 hk
    linarith
  nlinarith [hbnd, mul_pos hpos (sub_pos.2 hslt)]

/-! ### Unbounded slopes -/

/-- The unit slopes are *unbounded*: every real is exceeded by some unit slope (`⊤` counts). The
polygon is finite, or its slopes tend to `+∞`. This is the hypothesis the product formula cannot
do without (roadmap §0.5.4). -/
def SlopesUnbounded (h : ℕ → WithTop ℝ) : Prop := ∀ σ : ℝ, ∃ j, (σ : WithTop ℝ) < unitSlope h j

/-- A polygon with finitely many unit slopes has unbounded slopes. -/
theorem slopesUnbounded_of_finite (hfin : (slopeIndices h).Finite) : SlopesUnbounded h := by
  intro σ
  obtain ⟨j, hj⟩ := hfin.infinite_compl.nonempty
  refine ⟨j, ?_⟩
  rw [not_not.1 hj]
  exact WithTop.coe_lt_top σ

/-- The polygon of a finitely supported sequence has unbounded slopes. -/
theorem IsNewtonPolygonOf.slopesUnbounded_of_finite (hh : IsNewtonPolygonOf v h)
    (hfin : (finiteSet v).Finite) : SlopesUnbounded h :=
  NewtonPolygon.slopesUnbounded_of_finite (hh.slopeIndices_finite hfin)

/-- If the points lie on or above some line of every slope, the slopes are unbounded. -/
theorem IsNewtonPolygonOf.slopesUnbounded_of_forall_line (hh : IsNewtonPolygonOf v h)
    (hl : ∀ σ : ℝ, ∃ y : ℝ, ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k) : SlopesUnbounded h := by
  intro σ
  by_contra hcon
  push Not at hcon
  have hfin : ∀ j, h j ≠ ⊤ := by
    intro j hjt
    have hx := hcon j
    rw [unitSlope_eq_top_iff.2 (Or.inl hjt)] at hx
    exact WithTop.coe_ne_top (top_le_iff.1 hx)
  have hsne : ∀ j, unitSlope h j ≠ ⊤ := fun j ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (hcon j)
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (hfin 0)
  obtain ⟨y, hy⟩ := hl (σ + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (c - y)
  have hup : h N = ((c + ∑ j ∈ Finset.Ico 0 N, (unitSlope h j).untop₀ : ℝ) : WithTop ℝ) := by
    have htel := eq_add_sum_unitSlope (h := h) (a := 0) (k := N) (Nat.zero_le N)
      (fun j _ _ ↦ hfin j)
    rw [htel, ← hc, ← WithTop.coe_add]
  have hsum : (∑ j ∈ Finset.Ico 0 N, (unitSlope h j).untop₀) ≤ (N : ℝ) * σ := by
    calc (∑ j ∈ Finset.Ico 0 N, (unitSlope h j).untop₀)
        ≤ ∑ _j ∈ Finset.Ico 0 N, σ := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          have hx := hcon j
          rw [← WithTop.coe_untop₀_of_ne_top (hsne j), WithTop.coe_le_coe] at hx
          exact hx
      _ = (N : ℝ) * σ := by rw [Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
  have hlow := hh.line_le hy N
  rw [hup, WithTop.coe_le_coe] at hlow
  nlinarith [hlow, hsum, hN]

/-- If `v k / k → ∞`, the slopes are unbounded. -/
theorem IsNewtonPolygonOf.slopesUnbounded_of_tendsto (hh : IsNewtonPolygonOf v h)
    (hfin : ∀ k, v k ≠ ⊤)
    (hl : Filter.Tendsto (fun k : ℕ ↦ (v k).untop₀ / k) Filter.atTop Filter.atTop) :
    SlopesUnbounded h := by
  refine hh.slopesUnbounded_of_forall_line fun σ ↦ ?_
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hl σ)
  obtain ⟨y₀, hy₀⟩ := ((Set.finite_Iio (max K 1)).image
    fun k : ℕ ↦ (v k).untop₀ - σ * k).bddBelow
  refine ⟨min y₀ 0, fun k ↦ ?_⟩
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.1 (hfin k)
  have hwv : (v k).untop₀ = w := by rw [← hw, WithTop.untop₀_coe]
  rw [← hw, WithTop.coe_le_coe]
  rcases lt_or_ge k (max K 1) with hk | hk
  · have hx : min y₀ 0 ≤ (v k).untop₀ - σ * k :=
      le_trans (min_le_left _ _) (hy₀ ⟨k, Set.mem_Iio.2 hk, rfl⟩)
    rw [hwv] at hx
    linarith
  · have hk1 : 1 ≤ k := le_trans (le_max_right K 1) hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have : (0 : ℕ) < k := by omega
      exact_mod_cast this
    have hdiv := hK k (le_trans (le_max_left K 1) hk)
    rw [hwv, le_div_iff₀ hkpos] at hdiv
    have hmin : min y₀ 0 ≤ 0 := min_le_right _ _
    linarith

/-- A sequence anchored at `0` that ends in a ray has bounded slopes. -/
theorem EndsInRay.not_slopesUnbounded (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) {m : ℝ}
    (hm : EndsInRay h m) : ¬ SlopesUnbounded h := by
  intro hu
  obtain ⟨j, hj⟩ := hu m
  exact Set.eq_empty_iff_forall_notMem.1 (hm.setOf_lt_unitSlope_eq_empty hh h0) j hj

/-- **Trichotomy** for the unit slopes of a convex sequence anchored at `0`: they are unbounded
(finitely many points, or slopes tending to `+∞`); or the sequence ends in a ray; or the slopes stay
strictly below their supremum and tend to it (infinitely many faces accumulating at a slope that is
never attained). For the polygon of a power series these are: polynomial or entire; finite radius of
convergence with a face at the boundary slope; finite radius with no face there. -/
theorem IsConvexSeq.slopesUnbounded_or_endsInRay_or_tendsto (hh : IsConvexSeq h) :
    SlopesUnbounded h ∨ (∃ m, EndsInRay h m) ∨
      ∃ m : ℝ, (∀ j, unitSlope h j < m) ∧
        Filter.Tendsto (fun j ↦ (unitSlope h j).untop₀) Filter.atTop (nhds m) := by
  by_cases hu : SlopesUnbounded h
  · exact Or.inl hu
  simp only [SlopesUnbounded, not_forall, not_exists, not_lt] at hu
  obtain ⟨σ, hσ⟩ := hu
  have hfin : ∀ j, h j ≠ ⊤ := by
    intro j hjt
    have hx := hσ j
    rw [unitSlope_eq_top_iff.2 (Or.inl hjt)] at hx
    exact WithTop.coe_ne_top (top_le_iff.1 hx)
  have hsne : ∀ j, unitSlope h j ≠ ⊤ := fun j ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (hσ j)
  have hbdd : BddAbove (Set.range fun j ↦ (unitSlope h j).untop₀) := by
    refine ⟨σ, ?_⟩
    rintro z ⟨j, rfl⟩
    have hx := hσ j
    rw [← WithTop.coe_untop₀_of_ne_top (hsne j), WithTop.coe_le_coe] at hx
    exact hx
  have htend := hh.tendsto_unitSlope hfin hbdd
  by_cases hex : ∃ j, (unitSlope h j).untop₀ = ⨆ i, (unitSlope h i).untop₀
  · refine Or.inr (Or.inl ⟨⨆ i, (unitSlope h i).untop₀, (hh.endsInRay_iff _).2 ⟨fun j _ ↦ ?_, ?_⟩⟩)
    · rw [← WithTop.coe_untop₀_of_ne_top (hsne j), WithTop.coe_le_coe]
      exact le_ciSup hbdd j
    · obtain ⟨j, hj⟩ := hex
      exact ⟨j, by rw [← WithTop.coe_untop₀_of_ne_top (hsne j), hj]⟩
  · refine Or.inr (Or.inr ⟨⨆ i, (unitSlope h i).untop₀, fun j ↦ ?_, htend⟩)
    push Not at hex
    rw [← WithTop.coe_untop₀_of_ne_top (hsne j), WithTop.coe_lt_coe]
    exact lt_of_le_of_ne (le_ciSup hbdd j) (hex j)

/-! ### Faces -/

/-- The left endpoint of the face of slope `σ`: the first unit interval whose slope is `≥ σ`,
equivalently the number of unit slopes `< σ` (for a polygon anchored at `0`). Junk `0` if no unit
slope is `≥ σ`. -/
noncomputable def faceLeft (h : ℕ → WithTop ℝ) (σ : ℝ) : ℕ :=
  sInf {j | (σ : WithTop ℝ) ≤ unitSlope h j}

/-- The right endpoint of the face of slope `σ`: the first unit interval whose slope is `> σ`,
equivalently the number of unit slopes `≤ σ` (for a polygon anchored at `0`). Junk `0` if no unit
slope is `> σ`. -/
noncomputable def faceRight (h : ℕ → WithTop ℝ) (σ : ℝ) : ℕ :=
  sInf {j | (σ : WithTop ℝ) < unitSlope h j}

/-- With unbounded slopes, `faceLeft σ` carries a unit slope `≥ σ`. -/
theorem le_unitSlope_faceLeft (hu : SlopesUnbounded h) (σ : ℝ) :
    (σ : WithTop ℝ) ≤ unitSlope h (faceLeft h σ) := by
  obtain ⟨j, hj⟩ := hu σ
  exact Nat.sInf_mem (s := {j | (σ : WithTop ℝ) ≤ unitSlope h j}) ⟨j, hj.le⟩

/-- With unbounded slopes, `faceRight σ` carries a unit slope `> σ`. -/
theorem lt_unitSlope_faceRight (hu : SlopesUnbounded h) (σ : ℝ) :
    (σ : WithTop ℝ) < unitSlope h (faceRight h σ) :=
  Nat.sInf_mem (s := {j | (σ : WithTop ℝ) < unitSlope h j}) (hu σ)

/-- The face endpoints are honest exactly when the slopes are unbounded. -/
theorem slopesUnbounded_iff_forall_lt_unitSlope_faceRight :
    SlopesUnbounded h ↔ ∀ σ : ℝ, (σ : WithTop ℝ) < unitSlope h (faceRight h σ) :=
  ⟨fun hu σ ↦ lt_unitSlope_faceRight hu σ, fun hx σ ↦ ⟨faceRight h σ, hx σ⟩⟩

/-- On a terminal ray of slope `m` the left endpoint of the face of slope `m` is honest, although
the slopes are bounded. -/
theorem EndsInRay.le_unitSlope_faceLeft {m : ℝ} (hm : EndsInRay h m) :
    (m : WithTop ℝ) ≤ unitSlope h (faceLeft h m) := by
  obtain ⟨N, hN⟩ := hm
  exact Nat.sInf_mem (s := {j | (m : WithTop ℝ) ≤ unitSlope h j}) ⟨N, le_of_eq (hN N le_rfl).symm⟩

/-- Before a face the unit slopes are strictly smaller than its slope. -/
theorem unitSlope_lt_of_lt_faceLeft {σ : ℝ} {j : ℕ} (hj : j < faceLeft h σ) :
    unitSlope h j < σ := not_le.1 (Nat.notMem_of_lt_sInf hj)

/-- Before the right end of a face the unit slopes are at most its slope. -/
theorem unitSlope_le_of_lt_faceRight {σ : ℝ} {j : ℕ} (hj : j < faceRight h σ) :
    unitSlope h j ≤ σ := not_lt.1 (Nat.notMem_of_lt_sInf hj)

/-- From the left end of a face on, the unit slopes are at least its slope. -/
theorem IsConvexSeq.le_unitSlope_of_faceLeft_le (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) {σ : ℝ} {j : ℕ} (hj : faceLeft h σ ≤ j) :
    (σ : WithTop ℝ) ≤ unitSlope h j := by
  by_cases hjt : h j = ⊤
  · rw [unitSlope_eq_top_iff.2 (Or.inl hjt)]
    exact le_top
  have hfl : h (faceLeft h σ) ≠ ⊤ := mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 h0)
    (mem_finiteSet.2 hjt) ⟨Nat.zero_le _, hj⟩)
  exact le_trans (le_unitSlope_faceLeft hu σ)
    (hh.monotoneOn (mem_finiteSet.2 hfl) (mem_finiteSet.2 hjt) hj)

/-- From the right end of a face on, the unit slopes are strictly larger than its slope. -/
theorem IsConvexSeq.lt_unitSlope_of_faceRight_le (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) {σ : ℝ} {j : ℕ} (hj : faceRight h σ ≤ j) :
    (σ : WithTop ℝ) < unitSlope h j := by
  by_cases hjt : h j = ⊤
  · rw [unitSlope_eq_top_iff.2 (Or.inl hjt)]
    exact WithTop.coe_lt_top σ
  have hfr : h (faceRight h σ) ≠ ⊤ := mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 h0)
    (mem_finiteSet.2 hjt) ⟨Nat.zero_le _, hj⟩)
  exact lt_of_lt_of_le (lt_unitSlope_faceRight hu σ)
    (hh.monotoneOn (mem_finiteSet.2 hfr) (mem_finiteSet.2 hjt) hj)

/-- `faceLeft σ` counts the unit slopes `< σ`. -/
theorem IsConvexSeq.faceLeft_eq_ncard (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    (σ : ℝ) : faceLeft h σ = Set.ncard {j | unitSlope h j < σ} := by
  have hset : {j | unitSlope h j < ((σ : ℝ) : WithTop ℝ)} = Set.Iio (faceLeft h σ) := by
    ext j
    constructor
    · intro hj
      rw [Set.mem_Iio]
      by_contra hc
      exact absurd (hh.le_unitSlope_of_faceLeft_le h0 hu (not_lt.1 hc)) (not_le.2 hj)
    · intro hj
      exact unitSlope_lt_of_lt_faceLeft (Set.mem_Iio.1 hj)
  rw [hset, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- `faceRight σ` counts the unit slopes `≤ σ`. -/
theorem IsConvexSeq.faceRight_eq_ncard (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (σ : ℝ) : faceRight h σ = Set.ncard {j | unitSlope h j ≤ σ} := by
  have hset : {j | unitSlope h j ≤ ((σ : ℝ) : WithTop ℝ)} = Set.Iio (faceRight h σ) := by
    ext j
    constructor
    · intro hj
      rw [Set.mem_Iio]
      by_contra hc
      exact absurd (hh.lt_unitSlope_of_faceRight_le h0 hu (not_lt.1 hc)) (not_lt.2 hj)
    · intro hj
      exact unitSlope_le_of_lt_faceRight (Set.mem_Iio.1 hj)
  rw [hset, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- A face begins at or before it ends. -/
theorem faceLeft_le_faceRight (hu : SlopesUnbounded h) (σ : ℝ) : faceLeft h σ ≤ faceRight h σ :=
  Nat.sInf_le (s := {j | (σ : WithTop ℝ) ≤ unitSlope h j}) (lt_unitSlope_faceRight hu σ).le

/-- The face is a single point exactly when `σ` is not a slope. -/
theorem IsConvexSeq.faceLeft_eq_faceRight_iff (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (σ : ℝ) :
    faceLeft h σ = faceRight h σ ↔ ∀ j, unitSlope h j ≠ σ := by
  constructor
  · intro heq j hj
    have h1 : faceLeft h σ ≤ j := by
      by_contra hc
      exact absurd (unitSlope_lt_of_lt_faceLeft (not_le.1 hc)) (by rw [hj]; exact lt_irrefl _)
    have h2 : j < faceRight h σ := by
      by_contra hc
      exact absurd (hh.lt_unitSlope_of_faceRight_le h0 hu (not_lt.1 hc))
        (by rw [hj]; exact lt_irrefl _)
    omega
  · intro hne
    refine le_antisymm (faceLeft_le_faceRight hu σ) ?_
    refine Nat.sInf_le (s := {j | (σ : WithTop ℝ) < unitSlope h j}) ?_
    exact lt_of_le_of_ne (le_unitSlope_faceLeft hu σ) (Ne.symm (hne _))

/-- Faces of increasing slopes are ordered. -/
theorem faceRight_le_faceLeft_of_lt (hu : SlopesUnbounded h) {σ τ : ℝ} (hστ : σ < τ) :
    faceRight h σ ≤ faceLeft h τ :=
  Nat.sInf_le (s := {j | (σ : WithTop ℝ) < unitSlope h j})
    (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hστ) (le_unitSlope_faceLeft hu τ))

/-- On the face of slope `σ` the polygon is the line of slope `σ` through the left endpoint. -/
theorem IsConvexSeq.eq_add_nsmul_of_mem_face (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) {σ : ℝ} {k : ℕ} (h1 : faceLeft h σ ≤ k) (h2 : k ≤ faceRight h σ) :
    h k = h (faceLeft h σ) + (k - faceLeft h σ : ℕ) • (σ : WithTop ℝ) := by
  have hslopes : ∀ j, faceLeft h σ ≤ j → j < k → unitSlope h j = ((σ : ℝ) : WithTop ℝ) :=
    fun j hj1 hj2 ↦ le_antisymm
      (unitSlope_le_of_lt_faceRight (lt_of_lt_of_le hj2 h2))
      (hh.le_unitSlope_of_faceLeft_le h0 hu hj1)
  have hx := eq_add_nsmul_of_forall_unitSlope_eq (h := h) (σ := σ) h1 hslopes
  rwa [Nat.card_Ico] at hx

/-- The left endpoint of a face is a finite index: the unit slope just before it is finite. -/
theorem ne_top_faceLeft (h0 : h 0 ≠ ⊤) (σ : ℝ) : h (faceLeft h σ) ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos (faceLeft h σ) with hF | hF
  · rw [hF]
    exact h0
  · have hprev := unitSlope_lt_of_lt_faceLeft (h := h) (σ := σ) (j := faceLeft h σ - 1) (by omega)
    have hx := (mem_slopeIndices_iff.1 (ne_top_of_lt hprev)).2
    rwa [show faceLeft h σ - 1 + 1 = faceLeft h σ by omega] at hx

/-- The right endpoint of a face is a finite index. -/
theorem ne_top_faceRight (h0 : h 0 ≠ ⊤) (σ : ℝ) : h (faceRight h σ) ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos (faceRight h σ) with hF | hF
  · rw [hF]
    exact h0
  · have hprev := unitSlope_le_of_lt_faceRight (h := h) (σ := σ) (j := faceRight h σ - 1) (by omega)
    have hx := (mem_slopeIndices_iff.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hprev)).2
    rwa [show faceRight h σ - 1 + 1 = faceRight h σ by omega] at hx

/-- The supporting line of slope `σ` through the left endpoint of its face lies on or below the
polygon. -/
theorem IsConvexSeq.faceLeft_line_le (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    (σ : ℝ) (k : ℕ) :
    (((h (faceLeft h σ)).untop₀ + σ * ((k : ℝ) - faceLeft h σ) : ℝ) : WithTop ℝ) ≤ h k :=
  (hh.line_le_iff (ne_top_faceLeft h0 σ) σ).2
    ⟨fun _ hj _ ↦ (unitSlope_lt_of_lt_faceLeft hj).le,
      fun _ hj ↦ hh.le_unitSlope_of_faceLeft_le h0 hu hj⟩ k

/-- Strictly left of the face, the supporting line is strictly below the polygon. -/
theorem IsConvexSeq.faceLeft_line_lt (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    {σ : ℝ} {k : ℕ} (hk : k < faceLeft h σ) :
    (((h (faceLeft h σ)).untop₀ + σ * ((k : ℝ) - faceLeft h σ) : ℝ) : WithTop ℝ) < h k := by
  have hkfin : h k ≠ ⊤ := mem_finiteSet.1 (hh.ordConnected.out (mem_finiteSet.2 h0)
    (mem_finiteSet.2 (ne_top_faceLeft h0 σ)) ⟨Nat.zero_le _, hk.le⟩)
  exact hh.line_lt_of_unitSlope_lt (ne_top_faceLeft h0 σ)
    (fun _ hj _ ↦ unitSlope_lt_of_lt_faceLeft hj) hk hkfin

/-- Strictly right of the face, the supporting line is strictly below the polygon. -/
theorem IsConvexSeq.faceRight_line_lt (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    {σ : ℝ} {k : ℕ} (hk : faceRight h σ < k) :
    (((h (faceRight h σ)).untop₀ + σ * ((k : ℝ) - faceRight h σ) : ℝ) : WithTop ℝ) < h k :=
  hh.line_lt_of_lt_unitSlope (ne_top_faceRight h0 σ)
    (fun _ hj ↦ hh.lt_unitSlope_of_faceRight_le h0 hu hj) hk

/-- The supporting line of slope `σ` through the right endpoint of its face lies on or below the
polygon. -/
theorem IsConvexSeq.faceRight_line_le (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    (σ : ℝ) (k : ℕ) :
    (((h (faceRight h σ)).untop₀ + σ * ((k : ℝ) - faceRight h σ) : ℝ) : WithTop ℝ) ≤ h k :=
  (hh.line_le_iff (ne_top_faceRight h0 σ) σ).2
    ⟨fun _ ht _ ↦ unitSlope_le_of_lt_faceRight ht,
      fun _ ht ↦ (hh.lt_unitSlope_of_faceRight_le h0 hu ht).le⟩ k

/-- **The multiplicity of `σ` as a slope is the width of its face** (roadmap §0.5.5). -/
theorem IsConvexSeq.faceRight_sub_faceLeft (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (σ : ℝ) :
    faceRight h σ - faceLeft h σ = Set.ncard {j | unitSlope h j = σ} := by
  have hset : {j | unitSlope h j = ((σ : ℝ) : WithTop ℝ)}
      = Set.Ico (faceLeft h σ) (faceRight h σ) := by
    ext j
    constructor
    · intro hj
      have hjx : unitSlope h j = ((σ : ℝ) : WithTop ℝ) := hj
      refine Set.mem_Ico.2 ⟨?_, ?_⟩
      · by_contra hc
        exact absurd (unitSlope_lt_of_lt_faceLeft (not_le.1 hc)) (by rw [hjx]; exact lt_irrefl _)
      · by_contra hc
        exact absurd (hh.lt_unitSlope_of_faceRight_le h0 hu (not_lt.1 hc))
          (by rw [hjx]; exact lt_irrefl _)
    · intro hj
      rw [Set.mem_Ico] at hj
      exact le_antisymm (unitSlope_le_of_lt_faceRight hj.2)
        (hh.le_unitSlope_of_faceLeft_le h0 hu hj.1)
  rw [hset, ← Finset.coe_Ico, Set.ncard_coe_finset, Nat.card_Ico]

/-- **The length of a face counts its slope**: the multiplicity of `σ` in the slope multiset is the
length of the face of slope `σ`. -/
theorem IsConvexSeq.count_slopeMultiset_eq (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    (hfin : (slopeIndices h).Finite) (σ : ℝ) :
    (slopeMultiset h).count σ = faceRight h σ - faceLeft h σ := by
  rw [count_slopeMultiset hfin,
    hh.faceRight_sub_faceLeft h0 (NewtonPolygon.slopesUnbounded_of_finite hfin)]

/-- `faceRight` is right-continuous: it is constant on a small interval to the right of `σ`. -/
theorem exists_faceRight_eq (hu : SlopesUnbounded h) (σ : ℝ) :
    ∃ δ > 0, ∀ τ, σ ≤ τ → τ < σ + δ → faceRight h τ = faceRight h σ := by
  by_cases hRt : unitSlope h (faceRight h σ) = ⊤
  · refine ⟨1, one_pos, fun τ hστ _ ↦ le_antisymm ?_ ?_⟩
    · refine Nat.sInf_le (s := {j | (τ : WithTop ℝ) < unitSlope h j}) ?_
      show (τ : WithTop ℝ) < unitSlope h (faceRight h σ)
      rw [hRt]
      exact WithTop.coe_lt_top τ
    · exact Nat.sInf_le (s := {j | (σ : WithTop ℝ) < unitSlope h j})
        (lt_of_le_of_lt (WithTop.coe_le_coe.2 hστ) (lt_unitSlope_faceRight hu τ))
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hRt
    have hσr : σ < r := by
      have hx := lt_unitSlope_faceRight hu σ
      rwa [← hr, WithTop.coe_lt_coe] at hx
    refine ⟨r - σ, by linarith, fun τ hστ hτ ↦ le_antisymm ?_ ?_⟩
    · refine Nat.sInf_le (s := {j | (τ : WithTop ℝ) < unitSlope h j}) ?_
      show (τ : WithTop ℝ) < unitSlope h (faceRight h σ)
      rw [← hr, WithTop.coe_lt_coe]
      linarith
    · exact Nat.sInf_le (s := {j | (σ : WithTop ℝ) < unitSlope h j})
        (lt_of_le_of_lt (WithTop.coe_le_coe.2 hστ) (lt_unitSlope_faceRight hu τ))

/-- The left endpoint of a face of the Newton polygon is a point of the sequence. -/
theorem IsNewtonPolygonOf.eq_of_faceLeft (hh : IsNewtonPolygonOf v h) (h0 : v 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (σ : ℝ) : h (faceLeft h σ) = v (faceLeft h σ) := by
  have hh0 : h 0 ≠ ⊤ := hh.ne_top_of_ne_top h0
  refine hh.eq_of_isVertex ⟨ne_top_faceLeft hh0 σ, ?_⟩
  rcases Nat.eq_zero_or_pos (faceLeft h σ) with hF | hF
  · exact Or.inl (by rw [hF, Nat.le_zero.1 (anchor_le hh0)])
  · refine Or.inr (lt_of_lt_of_le (unitSlope_lt_of_lt_faceLeft ?_)
      (hh.convex.le_unitSlope_of_faceLeft_le hh0 hu le_rfl))
    omega

/-- The right endpoint of a face of the Newton polygon is a point of the sequence. -/
theorem IsNewtonPolygonOf.eq_of_faceRight (hh : IsNewtonPolygonOf v h) (h0 : v 0 ≠ ⊤)
    (hu : SlopesUnbounded h) (σ : ℝ) : h (faceRight h σ) = v (faceRight h σ) := by
  have hh0 : h 0 ≠ ⊤ := hh.ne_top_of_ne_top h0
  refine hh.eq_of_isVertex ⟨ne_top_faceRight hh0 σ, ?_⟩
  rcases Nat.eq_zero_or_pos (faceRight h σ) with hF | hF
  · exact Or.inl (by rw [hF, Nat.le_zero.1 (anchor_le hh0)])
  · exact Or.inr (lt_of_le_of_lt
      (unitSlope_le_of_lt_faceRight (by omega : faceRight h σ - 1 < faceRight h σ))
      (hh.convex.lt_unitSlope_of_faceRight_le hh0 hu le_rfl))

end NewtonPolygon
