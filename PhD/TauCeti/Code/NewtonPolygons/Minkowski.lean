/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.Face

/-!
# Minkowski sums of Newton polygons

The *Minkowski sum* of two polygons anchored at `0` is the min-convolution of their height
functions, `minkowski h₁ h₂ n = min_{i+j=n} (h₁ i + h₂ j)`. It is the polygon whose slope multiset
is the sum of the two slope multisets, and it is what the Newton polygon of a product of power
series turns out to be (roadmap Layer 5). This file is pure convexity: the subgradient property
(a supporting line of the sum is a sum of supporting lines with a common slope), the additivity of
the face endpoints, and the uniqueness of the minimising split at the endpoints of a face.

[Ked07, proof of Prop. 1]: "let `i₀` and `j₀` be the smallest values of `i` and `j` which minimize
`ri + v(P_i)` and `rj + v(Q_j)`, respectively; then (1) achieves its minimum for `h = 0, i = i₀,
j = j₀` but not for any other `h, i, j` with `i + j = i₀ + j₀`."

Roadmap: §0.6. Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/Minkowski.lean`.
-/

open scoped Classical

namespace NewtonPolygon

variable {h₁ h₂ h₃ : ℕ → WithTop ℝ}

/-- **The Minkowski sum** of two height functions: the least `h₁ i + h₂ j` over the splits
`i + j = n`, a finite infimum (`WithTop ℝ` is not a complete lattice). -/
noncomputable def minkowski (h₁ h₂ : ℕ → WithTop ℝ) (n : ℕ) : WithTop ℝ :=
  (Finset.range (n + 1)).inf fun i ↦ h₁ i + h₂ (n - i)

/-- The Minkowski sum is at most the value of every split. -/
theorem minkowski_le {n i : ℕ} (hi : i ≤ n) : minkowski h₁ h₂ n ≤ h₁ i + h₂ (n - i) :=
  Finset.inf_le (Finset.mem_range.2 (by omega))

/-- A lower bound for the Minkowski sum is one for every split. -/
theorem le_minkowski_iff {n : ℕ} {a : WithTop ℝ} :
    a ≤ minkowski h₁ h₂ n ↔ ∀ i, i ≤ n → a ≤ h₁ i + h₂ (n - i) := by
  rw [minkowski, Finset.le_inf_iff]
  exact ⟨fun hx i hi ↦ hx i (Finset.mem_range.2 (by omega)),
    fun hx i hi ↦ hx i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))⟩

/-- The minimum is attained by some split. -/
theorem exists_minkowski_eq (n : ℕ) :
    ∃ i, i ≤ n ∧ minkowski h₁ h₂ n = h₁ i + h₂ (n - i) := by
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf (Finset.range (n + 1))
    ⟨0, Finset.mem_range.2 (by omega)⟩ fun i ↦ h₁ i + h₂ (n - i)
  exact ⟨i, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), heq⟩

/-- The Minkowski sum is commutative. -/
theorem minkowski_comm (n : ℕ) : minkowski h₁ h₂ n = minkowski h₂ h₁ n := by
  refine le_antisymm (le_minkowski_iff.2 fun i hi ↦ ?_) (le_minkowski_iff.2 fun i hi ↦ ?_)
  · calc minkowski h₁ h₂ n ≤ h₁ (n - i) + h₂ (n - (n - i)) := minkowski_le (by omega)
      _ = h₂ i + h₁ (n - i) := by
          rw [show n - (n - i) = i by omega, add_comm]
  · calc minkowski h₂ h₁ n ≤ h₂ (n - i) + h₁ (n - (n - i)) := minkowski_le (by omega)
      _ = h₁ i + h₂ (n - i) := by
          rw [show n - (n - i) = i by omega, add_comm]

/-- The Minkowski sum is associative. -/
theorem minkowski_assoc (n : ℕ) :
    minkowski (minkowski h₁ h₂) h₃ n = minkowski h₁ (minkowski h₂ h₃) n := by
  refine le_antisymm (le_minkowski_iff.2 fun i hi ↦ ?_) (le_minkowski_iff.2 fun i hi ↦ ?_)
  · obtain ⟨j, hj, heq⟩ := exists_minkowski_eq (h₁ := h₂) (h₂ := h₃) (n - i)
    have h1 : minkowski h₁ h₂ (i + j) ≤ h₁ i + h₂ j := by
      have hx := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := i + j) (i := i) (by omega)
      rwa [Nat.add_sub_cancel_left] at hx
    calc minkowski (minkowski h₁ h₂) h₃ n
        ≤ minkowski h₁ h₂ (i + j) + h₃ (n - (i + j)) := minkowski_le (by omega)
      _ ≤ h₁ i + h₂ j + h₃ (n - i - j) := by
          rw [show n - (i + j) = n - i - j by omega]
          exact add_le_add h1 le_rfl
      _ = h₁ i + (h₂ j + h₃ (n - i - j)) := add_assoc _ _ _
      _ = h₁ i + minkowski h₂ h₃ (n - i) := by rw [heq]
  · obtain ⟨j, hj, heq⟩ := exists_minkowski_eq (h₁ := h₁) (h₂ := h₂) i
    calc minkowski h₁ (minkowski h₂ h₃) n
        ≤ h₁ j + minkowski h₂ h₃ (n - j) := minkowski_le (by omega)
      _ ≤ h₁ j + (h₂ (i - j) + h₃ (n - i)) := by
          refine add_le_add le_rfl ?_
          have hx := minkowski_le (h₁ := h₂) (h₂ := h₃) (n := n - j) (i := i - j) (by omega)
          rwa [show n - j - (i - j) = n - i by omega] at hx
      _ = h₁ j + h₂ (i - j) + h₃ (n - i) := (add_assoc _ _ _).symm
      _ = minkowski h₁ h₂ i + h₃ (n - i) := by rw [heq]

/-- At `0` the only split is the trivial one. -/
@[simp] theorem minkowski_zero : minkowski h₁ h₂ 0 = h₁ 0 + h₂ 0 := by
  rw [minkowski, Finset.range_one, Finset.inf_singleton]

/-- The Minkowski sum of two convex sequences anchored at `0` is convex. -/
theorem isConvexSeq_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) : IsConvexSeq (minkowski h₁ h₂) := by
  have hdown₁ : ∀ p q : ℕ, p ≤ q → h₁ q ≠ ⊤ → h₁ p ≠ ⊤ := fun p q hpq hq ↦
    mem_finiteSet.1 (hh₁.ordConnected.out (mem_finiteSet.2 h0₁) (mem_finiteSet.2 hq)
      ⟨Nat.zero_le _, hpq⟩)
  have hdown₂ : ∀ p q : ℕ, p ≤ q → h₂ q ≠ ⊤ → h₂ p ≠ ⊤ := fun p q hpq hq ↦
    mem_finiteSet.1 (hh₂.ordConnected.out (mem_finiteSet.2 h0₂) (mem_finiteSet.2 hq)
      ⟨Nat.zero_le _, hpq⟩)
  have hMdown : ∀ b c : ℕ, b ≤ c → minkowski h₁ h₂ c ≠ ⊤ → minkowski h₁ h₂ b ≠ ⊤ := by
    intro b c hbc hc
    obtain ⟨q, hq, heq⟩ := exists_minkowski_eq (h₁ := h₁) (h₂ := h₂) c
    rw [heq, Ne, WithTop.add_eq_top, not_or] at hc
    refine ne_top_of_le_ne_top ?_ (minkowski_le (h₁ := h₁) (h₂ := h₂) (n := b) (i := min q b)
      (by omega))
    rw [Ne, WithTop.add_eq_top, not_or]
    exact ⟨hdown₁ _ q (by omega) hc.1, hdown₂ _ (c - q) (by omega) hc.2⟩
  refine (isConvexSeq_iff_midpoint ⟨fun a ha c hc b hb ↦ ?_⟩).2 fun n ↦ ?_
  · exact mem_finiteSet.2 (hMdown b c hb.2 (mem_finiteSet.1 hc))
  · simp only [Order.succ_eq_add_one]
    obtain ⟨a, ha, heqa⟩ := exists_minkowski_eq (h₁ := h₁) (h₂ := h₂) n
    obtain ⟨b, hb, heqb⟩ := exists_minkowski_eq (h₁ := h₁) (h₂ := h₂) (n + 2)
    rcases lt_or_ge a b with hab | hab
    · have hle₁ : minkowski h₁ h₂ (n + 1) ≤ h₁ (a + 1) + h₂ (n - a) := by
        have hx := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := n + 1) (i := a + 1) (by omega)
        rwa [show n + 1 - (a + 1) = n - a by omega] at hx
      have hle₂ : minkowski h₁ h₂ (n + 1) ≤ h₁ (b - 1) + h₂ (n + 2 - b) := by
        have hx := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := n + 1) (i := b - 1) (by omega)
        rwa [show n + 1 - (b - 1) = n + 2 - b by omega] at hx
      calc minkowski h₁ h₂ (n + 1) + minkowski h₁ h₂ (n + 1)
          ≤ (h₁ (a + 1) + h₂ (n - a)) + (h₁ (b - 1) + h₂ (n + 2 - b)) := add_le_add hle₁ hle₂
        _ = (h₁ (a + 1) + h₁ (b - 1)) + (h₂ (n - a) + h₂ (n + 2 - b)) := add_add_add_comm _ _ _ _
        _ ≤ (h₁ a + h₁ b) + (h₂ (n - a) + h₂ (n + 2 - b)) :=
            add_le_add (hh₁.succ_add_pred_le hab) le_rfl
        _ = (h₁ a + h₂ (n - a)) + (h₁ b + h₂ (n + 2 - b)) := add_add_add_comm _ _ _ _
        _ = minkowski h₁ h₂ n + minkowski h₁ h₂ (n + 2) := by rw [heqa, heqb]
    · have hcd : n - a < n + 2 - b := by omega
      have hle₁ : minkowski h₁ h₂ (n + 1) ≤ h₁ a + h₂ (n - a + 1) := by
        have hx := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := n + 1) (i := a) (by omega)
        rwa [show n + 1 - a = n - a + 1 by omega] at hx
      have hle₂ : minkowski h₁ h₂ (n + 1) ≤ h₁ b + h₂ (n + 2 - b - 1) := by
        have hx := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := n + 1) (i := b) (by omega)
        rwa [show n + 1 - b = n + 2 - b - 1 by omega] at hx
      calc minkowski h₁ h₂ (n + 1) + minkowski h₁ h₂ (n + 1)
          ≤ (h₁ a + h₂ (n - a + 1)) + (h₁ b + h₂ (n + 2 - b - 1)) := add_le_add hle₁ hle₂
        _ = (h₁ a + h₁ b) + (h₂ (n - a + 1) + h₂ (n + 2 - b - 1)) := add_add_add_comm _ _ _ _
        _ ≤ (h₁ a + h₁ b) + (h₂ (n - a) + h₂ (n + 2 - b)) :=
            add_le_add le_rfl (hh₂.succ_add_pred_le hcd)
        _ = (h₁ a + h₂ (n - a)) + (h₁ b + h₂ (n + 2 - b)) := add_add_add_comm _ _ _ _
        _ = minkowski h₁ h₂ n + minkowski h₁ h₂ (n + 2) := by rw [heqa, heqb]

/-! ### The subgradient property -/

/-- **A minimising split has a common subgradient** (roadmap §0.6.2): if `(i₀, n - i₀)` attains the
finite Minkowski sum at `n`, some real `σ` separates the unit slopes of `h₁` at `i₀` and those of
`h₂` at `n - i₀`. -/
theorem exists_subgradient (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) {n i₀ : ℕ} (hi₀ : i₀ ≤ n) (hfin : minkowski h₁ h₂ n ≠ ⊤)
    (heq : minkowski h₁ h₂ n = h₁ i₀ + h₂ (n - i₀)) :
    ∃ σ : ℝ, (∀ t, t < i₀ → unitSlope h₁ t ≤ σ) ∧ (∀ t, i₀ ≤ t → (σ : WithTop ℝ) ≤ unitSlope h₁ t) ∧
      (∀ t, t < n - i₀ → unitSlope h₂ t ≤ σ) ∧
      ∀ t, n - i₀ ≤ t → (σ : WithTop ℝ) ≤ unitSlope h₂ t := by
  rw [heq, Ne, WithTop.add_eq_top, not_or] at hfin
  obtain ⟨hf₁, hf₂⟩ := hfin
  have hdown₁ : ∀ t, t ≤ i₀ → h₁ t ≠ ⊤ := fun t ht ↦
    mem_finiteSet.1 (hh₁.ordConnected.out (mem_finiteSet.2 h0₁) (mem_finiteSet.2 hf₁)
      ⟨Nat.zero_le _, ht⟩)
  have hdown₂ : ∀ t, t ≤ n - i₀ → h₂ t ≠ ⊤ := fun t ht ↦
    mem_finiteSet.1 (hh₂.ordConnected.out (mem_finiteSet.2 h0₂) (mem_finiteSet.2 hf₂)
      ⟨Nat.zero_le _, ht⟩)
  have hmono₁ : ∀ t, t ≤ i₀ → unitSlope h₁ t ≤ unitSlope h₁ i₀ := fun t ht ↦
    hh₁.monotoneOn (mem_finiteSet.2 (hdown₁ t ht)) (mem_finiteSet.2 hf₁) ht
  have hmono₂ : ∀ t, t ≤ n - i₀ → unitSlope h₂ t ≤ unitSlope h₂ (n - i₀) := fun t ht ↦
    hh₂.monotoneOn (mem_finiteSet.2 (hdown₂ t ht)) (mem_finiteSet.2 hf₂) ht
  have hright₁ : ∀ t, i₀ ≤ t → unitSlope h₁ i₀ ≤ unitSlope h₁ t := by
    intro t ht
    by_cases hT : h₁ t = ⊤
    · rw [unitSlope_eq_top_iff.2 (Or.inl hT)]
      exact le_top
    · exact hh₁.monotoneOn (mem_finiteSet.2 hf₁) (mem_finiteSet.2 hT) ht
  have hright₂ : ∀ t, n - i₀ ≤ t → unitSlope h₂ (n - i₀) ≤ unitSlope h₂ t := by
    intro t ht
    by_cases hT : h₂ t = ⊤
    · rw [unitSlope_eq_top_iff.2 (Or.inl hT)]
      exact le_top
    · exact hh₂.monotoneOn (mem_finiteSet.2 hf₂) (mem_finiteSet.2 hT) ht
  -- the two inequalities that minimality of the split provides
  have hminl : 1 ≤ i₀ → unitSlope h₁ (i₀ - 1) ≤ unitSlope h₂ (n - i₀) := by
    intro hi1
    by_cases hT : h₂ (n - i₀ + 1) = ⊤
    · have hx : unitSlope h₂ (n - i₀) = ⊤ :=
        unitSlope_eq_top_iff.2 (Or.inr (by rwa [Order.succ_eq_add_one]))
      rw [hx]
      exact le_top
    have hstep := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := n) (i := i₀ - 1) (by omega)
    rw [heq, show n - (i₀ - 1) = n - i₀ + 1 by omega] at hstep
    obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 hf₁
    obtain ⟨a', hA'⟩ := WithTop.ne_top_iff_exists.1 (hdown₁ (i₀ - 1) (by omega))
    obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 hf₂
    obtain ⟨b', hB'⟩ := WithTop.ne_top_iff_exists.1 hT
    rw [unitSlope_of_ne_top (hdown₁ (i₀ - 1) (by omega))
        (by rw [Order.succ_eq_add_one, show i₀ - 1 + 1 = i₀ by omega]; exact hf₁),
      unitSlope_of_ne_top hf₂ (by rwa [Order.succ_eq_add_one]),
      Order.succ_eq_add_one, Order.succ_eq_add_one, show i₀ - 1 + 1 = i₀ by omega,
      ← hA, ← hA', ← hB, ← hB', WithTop.coe_le_coe]
    rw [← hA, ← hA', ← hB, ← hB', ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hstep
    simp only [WithTop.untop₀_coe]
    linarith
  have hminr : 1 ≤ n - i₀ → unitSlope h₂ (n - i₀ - 1) ≤ unitSlope h₁ i₀ := by
    intro hj1
    by_cases hT : h₁ (i₀ + 1) = ⊤
    · have hx : unitSlope h₁ i₀ = ⊤ :=
        unitSlope_eq_top_iff.2 (Or.inr (by rwa [Order.succ_eq_add_one]))
      rw [hx]
      exact le_top
    have hstep := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := n) (i := i₀ + 1) (by omega)
    rw [heq, show n - (i₀ + 1) = n - i₀ - 1 by omega] at hstep
    obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 hf₁
    obtain ⟨a', hA'⟩ := WithTop.ne_top_iff_exists.1 hT
    obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 hf₂
    obtain ⟨b', hB'⟩ := WithTop.ne_top_iff_exists.1 (hdown₂ (n - i₀ - 1) (by omega))
    rw [unitSlope_of_ne_top (hdown₂ (n - i₀ - 1) (by omega))
        (by rw [Order.succ_eq_add_one, show n - i₀ - 1 + 1 = n - i₀ by omega]; exact hf₂),
      unitSlope_of_ne_top hf₁ (by rwa [Order.succ_eq_add_one]),
      Order.succ_eq_add_one, Order.succ_eq_add_one, show n - i₀ - 1 + 1 = n - i₀ by omega,
      ← hA, ← hA', ← hB, ← hB', WithTop.coe_le_coe]
    rw [← hA, ← hA', ← hB, ← hB', ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hstep
    simp only [WithTop.untop₀_coe]
    linarith
  have hsfL₁ : 1 ≤ i₀ → unitSlope h₁ (i₀ - 1) ≠ ⊤ := by
    intro hi1
    rw [ne_eq, unitSlope_eq_top_iff, Order.succ_eq_add_one, show i₀ - 1 + 1 = i₀ by omega, not_or]
    exact ⟨hdown₁ (i₀ - 1) (by omega), hf₁⟩
  have hsfL₂ : 1 ≤ n - i₀ → unitSlope h₂ (n - i₀ - 1) ≠ ⊤ := by
    intro hj1
    rw [ne_eq, unitSlope_eq_top_iff, Order.succ_eq_add_one,
      show n - i₀ - 1 + 1 = n - i₀ by omega, not_or]
    exact ⟨hdown₂ (n - i₀ - 1) (by omega), hf₂⟩
  have hleftmono₁ : ∀ t, t < i₀ → unitSlope h₁ t ≤ unitSlope h₁ (i₀ - 1) := fun t ht ↦
    hh₁.monotoneOn (mem_finiteSet.2 (hdown₁ t (by omega)))
      (mem_finiteSet.2 (hdown₁ (i₀ - 1) (by omega))) (by omega)
  have hleftmono₂ : ∀ t, t < n - i₀ → unitSlope h₂ t ≤ unitSlope h₂ (n - i₀ - 1) := fun t ht ↦
    hh₂.monotoneOn (mem_finiteSet.2 (hdown₂ t (by omega)))
      (mem_finiteSet.2 (hdown₂ (n - i₀ - 1) (by omega))) (by omega)
  by_cases hminfin : min (unitSlope h₁ i₀) (unitSlope h₂ (n - i₀)) = ⊤
  · -- both right slopes are `⊤`: the two polygons stop here, and the left slopes are finite
    rw [min_eq_top] at hminfin
    obtain ⟨hT₁, hT₂⟩ := hminfin
    have hstop₁ : ∀ t, i₀ ≤ t → unitSlope h₁ t = ⊤ := by
      intro t ht
      refine unitSlope_eq_top_iff.2 (Or.inr ?_)
      rw [Order.succ_eq_add_one]
      have hx : h₁ (i₀ + 1) = ⊤ := by
        rcases unitSlope_eq_top_iff.1 hT₁ with hy | hy
        · exact absurd hy hf₁
        · rwa [Order.succ_eq_add_one] at hy
      exact hh₁.eq_top_of_le hf₁ (by omega) hx (by omega)
    have hstop₂ : ∀ t, n - i₀ ≤ t → unitSlope h₂ t = ⊤ := by
      intro t ht
      refine unitSlope_eq_top_iff.2 (Or.inr ?_)
      rw [Order.succ_eq_add_one]
      have hx : h₂ (n - i₀ + 1) = ⊤ := by
        rcases unitSlope_eq_top_iff.1 hT₂ with hy | hy
        · exact absurd hy hf₂
        · rwa [Order.succ_eq_add_one] at hy
      exact hh₂.eq_top_of_le hf₂ (by omega) hx (by omega)
    refine ⟨max (unitSlope h₁ (i₀ - 1)).untop₀ (unitSlope h₂ (n - i₀ - 1)).untop₀,
      fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · refine le_trans (hleftmono₁ t ht) ?_
      rw [← WithTop.coe_untop₀_of_ne_top (hsfL₁ (by omega)), WithTop.coe_le_coe]
      exact le_max_left _ _
    · rw [hstop₁ t ht]
      exact le_top
    · refine le_trans (hleftmono₂ t ht) ?_
      rw [← WithTop.coe_untop₀_of_ne_top (hsfL₂ (by omega)), WithTop.coe_le_coe]
      exact le_max_right _ _
    · rw [hstop₂ t ht]
      exact le_top
  · -- the minimum of the two right slopes is finite and separates everything
    refine ⟨(min (unitSlope h₁ i₀) (unitSlope h₂ (n - i₀))).untop₀, fun t ht ↦ ?_, fun t ht ↦ ?_,
      fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · rw [WithTop.coe_untop₀_of_ne_top hminfin]
      exact le_trans (hleftmono₁ t ht)
        (le_min (hmono₁ (i₀ - 1) (by omega)) (hminl (by omega)))
    · rw [WithTop.coe_untop₀_of_ne_top hminfin]
      exact le_trans (min_le_left _ _) (hright₁ t ht)
    · rw [WithTop.coe_untop₀_of_ne_top hminfin]
      exact le_trans (hleftmono₂ t ht)
        (le_min (hminr (by omega)) (hmono₂ (n - i₀ - 1) (by omega)))
    · rw [WithTop.coe_untop₀_of_ne_top hminfin]
      exact le_trans (min_le_right _ _) (hright₂ t ht)

/-- **A supporting line of the Minkowski sum**: if `σ` separates the unit slopes of `h₁` at `i₀`
and of `h₂` at `j₀`, the line of slope `σ` through `(i₀ + j₀, h₁ i₀ + h₂ j₀)` lies on or below the
Minkowski sum — the sum of the two supporting lines. -/
theorem subgradient_line_le_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂)
    {i₀ j₀ : ℕ} {σ : ℝ}
    (hP₁ : ∀ t, t < i₀ → unitSlope h₁ t ≤ σ) (hP₂ : ∀ t, i₀ ≤ t → (σ : WithTop ℝ) ≤ unitSlope h₁ t)
    (hQ₁ : ∀ t, t < j₀ → unitSlope h₂ t ≤ σ) (hQ₂ : ∀ t, j₀ ≤ t → (σ : WithTop ℝ) ≤ unitSlope h₂ t)
    {y : ℝ} (hy : h₁ i₀ + h₂ j₀ = (y : WithTop ℝ)) (m : ℕ) :
    ((y + σ * ((m : ℝ) - (i₀ + j₀ : ℕ)) : ℝ) : WithTop ℝ) ≤ minkowski h₁ h₂ m := by
  have hyf : h₁ i₀ + h₂ j₀ ≠ ⊤ := by
    rw [hy]
    exact WithTop.coe_ne_top
  rw [Ne, WithTop.add_eq_top, not_or] at hyf
  obtain ⟨hf₁, hf₂⟩ := hyf
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 hf₁
  obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 hf₂
  have hab : a + b = y := by
    rw [← hA, ← hB, ← WithTop.coe_add, WithTop.coe_inj] at hy
    exact hy
  have hline₁ := (hh₁.line_le_iff hf₁ σ).2 ⟨fun j hj _ ↦ hP₁ j hj, hP₂⟩
  have hline₂ := (hh₂.line_le_iff hf₂ σ).2 ⟨fun j hj _ ↦ hQ₁ j hj, hQ₂⟩
  refine le_minkowski_iff.2 fun i hi ↦ ?_
  have hx₁ := hline₁ i
  have hx₂ := hline₂ (m - i)
  rw [← hA, WithTop.untop₀_coe] at hx₁
  rw [← hB, WithTop.untop₀_coe] at hx₂
  calc ((y + σ * ((m : ℝ) - (i₀ + j₀ : ℕ)) : ℝ) : WithTop ℝ)
      = ((a + σ * ((i : ℝ) - i₀) : ℝ) : WithTop ℝ)
        + ((b + σ * (((m - i : ℕ) : ℝ) - j₀) : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, WithTop.coe_inj, ← hab, Nat.cast_sub hi]
        push_cast
        ring
    _ ≤ h₁ i + h₂ (m - i) := add_le_add hx₁ hx₂

/-! ### Faces of the Minkowski sum -/

/-- Unbounded slopes add: the Minkowski sum of two sequences with unbounded slopes has unbounded
slopes. -/
theorem slopesUnbounded_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) :
    SlopesUnbounded (minkowski h₁ h₂) := by
  intro σ
  by_contra hcon
  push Not at hcon
  have hMconv : IsConvexSeq (minkowski h₁ h₂) := isConvexSeq_minkowski hh₁ hh₂ h0₁ h0₂
  have hMfin : ∀ j, minkowski h₁ h₂ j ≠ ⊤ := by
    intro j hjt
    have hx := hcon j
    rw [unitSlope_eq_top_iff.2 (Or.inl hjt)] at hx
    exact WithTop.coe_ne_top (top_le_iff.1 hx)
  have hMsne : ∀ j, unitSlope (minkowski h₁ h₂) j ≠ ⊤ := fun j ↦
    ne_top_of_le_ne_top WithTop.coe_ne_top (hcon j)
  -- the line of slope `σ + 1` through the two right face endpoints lies below the Minkowski sum
  set i₀ := faceRight h₁ (σ + 1) with hi₀
  set j₀ := faceRight h₂ (σ + 1) with hj₀
  have hf₁ : h₁ i₀ ≠ ⊤ := ne_top_faceRight h0₁ _
  have hf₂ : h₂ j₀ ≠ ⊤ := ne_top_faceRight h0₂ _
  obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1
    (show h₁ i₀ + h₂ j₀ ≠ ⊤ by rw [Ne, WithTop.add_eq_top, not_or]; exact ⟨hf₁, hf₂⟩)
  have hlinele := subgradient_line_le_minkowski hh₁ hh₂
    (fun _ ht ↦ unitSlope_le_of_lt_faceRight ht)
    (fun _ ht ↦ (hh₁.lt_unitSlope_of_faceRight_le h0₁ hu₁ ht).le)
    (fun _ ht ↦ unitSlope_le_of_lt_faceRight ht)
    (fun _ ht ↦ (hh₂.lt_unitSlope_of_faceRight_le h0₂ hu₂ ht).le) hy.symm
  -- the bounded slopes give the opposite growth bound
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (hMfin 0)
  obtain ⟨N, hN⟩ := exists_nat_gt (c - y + (σ + 1) * ((i₀ : ℝ) + j₀))
  have hup : minkowski h₁ h₂ N
      = ((c + ∑ j ∈ Finset.Ico 0 N, (unitSlope (minkowski h₁ h₂) j).untop₀ : ℝ) : WithTop ℝ) := by
    have htel := eq_add_sum_unitSlope (h := minkowski h₁ h₂) (a := 0) (k := N) (Nat.zero_le N)
      (fun j _ _ ↦ hMfin j)
    rw [htel, ← hc, ← WithTop.coe_add]
  have hsum : (∑ j ∈ Finset.Ico 0 N, (unitSlope (minkowski h₁ h₂) j).untop₀) ≤ (N : ℝ) * σ := by
    calc (∑ j ∈ Finset.Ico 0 N, (unitSlope (minkowski h₁ h₂) j).untop₀)
        ≤ ∑ _j ∈ Finset.Ico 0 N, σ := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          have hx := hcon j
          rw [← WithTop.coe_untop₀_of_ne_top (hMsne j), WithTop.coe_le_coe] at hx
          exact hx
      _ = (N : ℝ) * σ := by rw [Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
  have hlow := hlinele N
  rw [hup, WithTop.coe_le_coe] at hlow
  push_cast at hlow
  nlinarith [hlow, hsum, hN]

/-- **The minimising split is unique at the left endpoint of a face** (roadmap §0.6.4): every other
split is strictly worse. -/
theorem lt_of_ne_faceLeft (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) {σ : ℝ} {i j : ℕ}
    (hij : i + j = faceLeft h₁ σ + faceLeft h₂ σ) (hne : i ≠ faceLeft h₁ σ) :
    h₁ (faceLeft h₁ σ) + h₂ (faceLeft h₂ σ) < h₁ i + h₂ j := by
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 (ne_top_faceLeft h0₁ σ)
  obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 (ne_top_faceLeft h0₂ σ)
  have hab : h₁ (faceLeft h₁ σ) + h₂ (faceLeft h₂ σ) = ((a + b : ℝ) : WithTop ℝ) := by
    rw [← hA, ← hB, ← WithTop.coe_add]
  have hna : (h₁ (faceLeft h₁ σ)).untop₀ = a := by rw [← hA, WithTop.untop₀_coe]
  have hnb : (h₂ (faceLeft h₂ σ)).untop₀ = b := by rw [← hB, WithTop.untop₀_coe]
  by_cases hT : h₁ i + h₂ j = ⊤
  · rw [hT, hab]
    exact WithTop.coe_lt_top _
  rw [WithTop.add_eq_top, not_or] at hT
  obtain ⟨p, hP⟩ := WithTop.ne_top_iff_exists.1 hT.1
  obtain ⟨q, hQ⟩ := WithTop.ne_top_iff_exists.1 hT.2
  rw [hab, ← hP, ← hQ, ← WithTop.coe_add, WithTop.coe_lt_coe]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hx₁ := hh₁.faceLeft_line_lt h0₁ hlt
    have hx₂ := hh₂.faceLeft_line_le h0₂ hu₂ σ j
    rw [hna, ← hP, WithTop.coe_lt_coe] at hx₁
    rw [hnb, ← hQ, WithTop.coe_le_coe] at hx₂
    have hsum : ((i : ℝ) - faceLeft h₁ σ) + ((j : ℝ) - faceLeft h₂ σ) = 0 := by
      have hc : (i : ℝ) + j = (faceLeft h₁ σ : ℝ) + faceLeft h₂ σ := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hij
      linarith
    have hσsum : σ * ((i : ℝ) - faceLeft h₁ σ) + σ * ((j : ℝ) - faceLeft h₂ σ) = 0 := by
      rw [← mul_add, hsum, mul_zero]
    linarith [hx₁, hx₂, hσsum]
  · have hx₁ := hh₁.faceLeft_line_le h0₁ hu₁ σ i
    have hx₂ := hh₂.faceLeft_line_lt h0₂ (by omega : j < faceLeft h₂ σ)
    rw [hna, ← hP, WithTop.coe_le_coe] at hx₁
    rw [hnb, ← hQ, WithTop.coe_lt_coe] at hx₂
    have hsum : ((i : ℝ) - faceLeft h₁ σ) + ((j : ℝ) - faceLeft h₂ σ) = 0 := by
      have hc : (i : ℝ) + j = (faceLeft h₁ σ : ℝ) + faceLeft h₂ σ := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hij
      linarith
    have hσsum : σ * ((i : ℝ) - faceLeft h₁ σ) + σ * ((j : ℝ) - faceLeft h₂ σ) = 0 := by
      rw [← mul_add, hsum, mul_zero]
    linarith [hx₁, hx₂, hσsum]

/-- The minimising split is unique at the right endpoint of a face. -/
theorem lt_of_ne_faceRight (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) {σ : ℝ} {i j : ℕ}
    (hij : i + j = faceRight h₁ σ + faceRight h₂ σ) (hne : i ≠ faceRight h₁ σ) :
    h₁ (faceRight h₁ σ) + h₂ (faceRight h₂ σ) < h₁ i + h₂ j := by
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 (ne_top_faceRight h0₁ σ)
  obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 (ne_top_faceRight h0₂ σ)
  have hab : h₁ (faceRight h₁ σ) + h₂ (faceRight h₂ σ) = ((a + b : ℝ) : WithTop ℝ) := by
    rw [← hA, ← hB, ← WithTop.coe_add]
  have hna : (h₁ (faceRight h₁ σ)).untop₀ = a := by rw [← hA, WithTop.untop₀_coe]
  have hnb : (h₂ (faceRight h₂ σ)).untop₀ = b := by rw [← hB, WithTop.untop₀_coe]
  by_cases hT : h₁ i + h₂ j = ⊤
  · rw [hT, hab]
    exact WithTop.coe_lt_top _
  rw [WithTop.add_eq_top, not_or] at hT
  obtain ⟨p, hP⟩ := WithTop.ne_top_iff_exists.1 hT.1
  obtain ⟨q, hQ⟩ := WithTop.ne_top_iff_exists.1 hT.2
  rw [hab, ← hP, ← hQ, ← WithTop.coe_add, WithTop.coe_lt_coe]
  have hsum : ((i : ℝ) - faceRight h₁ σ) + ((j : ℝ) - faceRight h₂ σ) = 0 := by
    have hc : (i : ℝ) + j = (faceRight h₁ σ : ℝ) + faceRight h₂ σ := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hij
    linarith
  have hσsum : σ * ((i : ℝ) - faceRight h₁ σ) + σ * ((j : ℝ) - faceRight h₂ σ) = 0 := by
    rw [← mul_add, hsum, mul_zero]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hx₁ := hh₁.faceRight_line_le h0₁ hu₁ σ i
    have hx₂ := hh₂.faceRight_line_lt h0₂ hu₂ (by omega : faceRight h₂ σ < j)
    rw [hna, ← hP, WithTop.coe_le_coe] at hx₁
    rw [hnb, ← hQ, WithTop.coe_lt_coe] at hx₂
    linarith [hx₁, hx₂, hσsum]
  · have hx₁ := hh₁.faceRight_line_lt h0₁ hu₁ hgt
    have hx₂ := hh₂.faceRight_line_le h0₂ hu₂ σ j
    rw [hna, ← hP, WithTop.coe_lt_coe] at hx₁
    rw [hnb, ← hQ, WithTop.coe_le_coe] at hx₂
    linarith [hx₁, hx₂, hσsum]

/-- **The face endpoints add**: at `faceLeft h₁ σ + faceLeft h₂ σ` the Minkowski sum is attained by
the split of the two left endpoints. -/
theorem minkowski_faceLeft_add (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) (σ : ℝ) :
    minkowski h₁ h₂ (faceLeft h₁ σ + faceLeft h₂ σ) = h₁ (faceLeft h₁ σ) + h₂ (faceLeft h₂ σ) := by
  refine le_antisymm ?_ (le_minkowski_iff.2 fun i hi ↦ ?_)
  · have hx := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := faceLeft h₁ σ + faceLeft h₂ σ)
      (i := faceLeft h₁ σ) (by omega)
    rwa [Nat.add_sub_cancel_left] at hx
  · rcases eq_or_ne i (faceLeft h₁ σ) with rfl | hne
    · rw [Nat.add_sub_cancel_left]
    · exact (lt_of_ne_faceLeft hh₁ hh₂ h0₁ h0₂ hu₁ hu₂ (by omega) hne).le

/-- At the sum of the right ends of two faces of slope `σ`, the Minkowski sum is attained by
splitting there. -/
theorem minkowski_faceRight_add (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) (σ : ℝ) :
    minkowski h₁ h₂ (faceRight h₁ σ + faceRight h₂ σ)
      = h₁ (faceRight h₁ σ) + h₂ (faceRight h₂ σ) := by
  refine le_antisymm ?_ (le_minkowski_iff.2 fun i hi ↦ ?_)
  · have hx := minkowski_le (h₁ := h₁) (h₂ := h₂) (n := faceRight h₁ σ + faceRight h₂ σ)
      (i := faceRight h₁ σ) (by omega)
    rwa [Nat.add_sub_cancel_left] at hx
  · rcases eq_or_ne i (faceRight h₁ σ) with rfl | hne
    · rw [Nat.add_sub_cancel_left]
    · exact (lt_of_ne_faceRight hh₁ hh₂ h0₁ h0₂ hu₁ hu₂ (by omega) hne).le

/-- **Faces add** (roadmap §0.6.3): the left endpoint of the face of slope `σ` of the Minkowski sum
is the sum of the left endpoints of the factors' faces. -/
theorem faceLeft_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) (σ : ℝ) :
    faceLeft (minkowski h₁ h₂) σ = faceLeft h₁ σ + faceLeft h₂ σ := by
  have hMf : h₁ (faceLeft h₁ σ) + h₂ (faceLeft h₂ σ) ≠ ⊤ := by
    rw [Ne, WithTop.add_eq_top, not_or]
    exact ⟨ne_top_faceLeft h0₁ σ, ne_top_faceLeft h0₂ σ⟩
  obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 hMf
  have hMF : minkowski h₁ h₂ (faceLeft h₁ σ + faceLeft h₂ σ) = ((y : ℝ) : WithTop ℝ) := by
    rw [minkowski_faceLeft_add hh₁ hh₂ h0₁ h0₂ hu₁ hu₂ σ, ← hy]
  -- the subgradient line of slope `σ` through the sum of the two left endpoints
  have hlinele := subgradient_line_le_minkowski hh₁ hh₂
    (fun _ ht ↦ (unitSlope_lt_of_lt_faceLeft ht).le)
    (fun _ ht ↦ hh₁.le_unitSlope_of_faceLeft_le h0₁ hu₁ ht)
    (fun _ ht ↦ (unitSlope_lt_of_lt_faceLeft ht).le)
    (fun _ ht ↦ hh₂.le_unitSlope_of_faceLeft_le h0₂ hu₂ ht) hy.symm
  -- strictly below the Minkowski sum to the left of the face
  have hstrict : ∀ j, j < faceLeft h₁ σ + faceLeft h₂ σ →
      ((y + σ * ((j : ℝ) - (faceLeft h₁ σ + faceLeft h₂ σ : ℕ)) : ℝ) : WithTop ℝ)
        < minkowski h₁ h₂ j := by
    intro j hj
    obtain ⟨p, hp, hsplit⟩ := exists_minkowski_eq (h₁ := h₁) (h₂ := h₂) j
    obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 (ne_top_faceLeft h0₁ σ)
    obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 (ne_top_faceLeft h0₂ σ)
    have hab : a + b = y := by
      rw [← hA, ← hB, ← WithTop.coe_add, WithTop.coe_inj] at hy
      exact hy.symm
    have hna : (h₁ (faceLeft h₁ σ)).untop₀ = a := by rw [← hA, WithTop.untop₀_coe]
    have hnb : (h₂ (faceLeft h₂ σ)).untop₀ = b := by rw [← hB, WithTop.untop₀_coe]
    rw [hsplit]
    by_cases hT : h₁ p + h₂ (j - p) = ⊤
    · rw [hT]
      exact WithTop.coe_lt_top _
    rw [WithTop.add_eq_top, not_or] at hT
    obtain ⟨u, hU⟩ := WithTop.ne_top_iff_exists.1 hT.1
    obtain ⟨w, hW⟩ := WithTop.ne_top_iff_exists.1 hT.2
    rw [← hU, ← hW, ← WithTop.coe_add, WithTop.coe_lt_coe]
    have hcast : ((j : ℝ) - ((faceLeft h₁ σ + faceLeft h₂ σ : ℕ) : ℝ))
        = (((p : ℝ) - faceLeft h₁ σ) + (((j - p : ℕ) : ℝ) - faceLeft h₂ σ)) := by
      rw [Nat.cast_sub hp]
      push_cast
      ring
    have hσcast : σ * ((j : ℝ) - ((faceLeft h₁ σ + faceLeft h₂ σ : ℕ) : ℝ))
        = σ * ((p : ℝ) - faceLeft h₁ σ) + σ * (((j - p : ℕ) : ℝ) - faceLeft h₂ σ) := by
      rw [hcast, mul_add]
    rcases lt_or_ge p (faceLeft h₁ σ) with hlt | hge
    · have hx₁ := hh₁.faceLeft_line_lt h0₁ hlt
      have hx₂ := hh₂.faceLeft_line_le h0₂ hu₂ σ (j - p)
      rw [hna, ← hU, WithTop.coe_lt_coe] at hx₁
      rw [hnb, ← hW, WithTop.coe_le_coe] at hx₂
      rw [hσcast]
      linarith [hab]
    · have hlt₂ : j - p < faceLeft h₂ σ := by omega
      have hx₁ := hh₁.faceLeft_line_le h0₁ hu₁ σ p
      have hx₂ := hh₂.faceLeft_line_lt h0₂ hlt₂
      rw [hna, ← hU, WithTop.coe_le_coe] at hx₁
      rw [hnb, ← hW, WithTop.coe_lt_coe] at hx₂
      rw [hσcast]
      linarith [hab]
  have hMconv : IsConvexSeq (minkowski h₁ h₂) := isConvexSeq_minkowski hh₁ hh₂ h0₁ h0₂
  have hM0 : minkowski h₁ h₂ 0 ≠ ⊤ := by
    rw [minkowski_zero, Ne, WithTop.add_eq_top, not_or]
    exact ⟨h0₁, h0₂⟩
  -- the slope at the sum of the endpoints is at least `σ`
  have hge : (σ : WithTop ℝ) ≤ unitSlope (minkowski h₁ h₂) (faceLeft h₁ σ + faceLeft h₂ σ) := by
    by_cases hT : minkowski h₁ h₂ (faceLeft h₁ σ + faceLeft h₂ σ + 1) = ⊤
    · rw [unitSlope_eq_top_iff.2 (Or.inr (by rwa [Order.succ_eq_add_one]))]
      exact le_top
    obtain ⟨w, hW⟩ := WithTop.ne_top_iff_exists.1 hT
    have hline := hlinele (faceLeft h₁ σ + faceLeft h₂ σ + 1)
    rw [← hW, WithTop.coe_le_coe] at hline
    rw [unitSlope_of_ne_top (by rw [hMF]; exact WithTop.coe_ne_top)
        (by rw [Order.succ_eq_add_one]; exact hT),
      Order.succ_eq_add_one, hMF, ← hW, WithTop.coe_le_coe]
    simp only [WithTop.untop₀_coe]
    push_cast at hline
    linarith
  refine le_antisymm (Nat.sInf_le (s := {j | (σ : WithTop ℝ) ≤ unitSlope (minkowski h₁ h₂) j}) hge)
    ?_
  by_contra hc
  rw [not_le] at hc
  -- the slope at `faceLeft M σ` is at least `σ`, so everything from there on is, which forces
  -- the strict line bound to be violated at `faceLeft M σ`
  have hmem : (σ : WithTop ℝ) ≤ unitSlope (minkowski h₁ h₂) (faceLeft (minkowski h₁ h₂) σ) :=
    le_unitSlope_faceLeft (slopesUnbounded_minkowski hh₁ hh₂ h0₁ h0₂ hu₁ hu₂) σ
  set j := faceLeft (minkowski h₁ h₂) σ with hj
  have hjf : minkowski h₁ h₂ j ≠ ⊤ := ne_top_faceLeft hM0 σ
  have hbound := hMconv.add_nsmul_unitSlope_le hjf
    (show j ≤ faceLeft h₁ σ + faceLeft h₂ σ by omega)
  have hstep : minkowski h₁ h₂ j + (Finset.Ico j (faceLeft h₁ σ + faceLeft h₂ σ)).card
      • ((σ : ℝ) : WithTop ℝ) ≤ minkowski h₁ h₂ (faceLeft h₁ σ + faceLeft h₂ σ) :=
    le_trans (add_le_add le_rfl (nsmul_le_nsmul_right hmem _)) hbound
  obtain ⟨m, hM⟩ := WithTop.ne_top_iff_exists.1 hjf
  rw [hMF, ← hM, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
    Nat.card_Ico] at hstep
  have hstr := hstrict j hc
  rw [← hM, WithTop.coe_lt_coe] at hstr
  rw [Nat.cast_sub (show j ≤ faceLeft h₁ σ + faceLeft h₂ σ by omega)] at hstep
  push_cast at hstep hstr
  linarith

/-- **The right ends of faces add** (roadmap §0.6). -/
theorem faceRight_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) (σ : ℝ) :
    faceRight (minkowski h₁ h₂) σ = faceRight h₁ σ + faceRight h₂ σ := by
  have hMf : h₁ (faceRight h₁ σ) + h₂ (faceRight h₂ σ) ≠ ⊤ := by
    rw [Ne, WithTop.add_eq_top, not_or]
    exact ⟨ne_top_faceRight h0₁ σ, ne_top_faceRight h0₂ σ⟩
  obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 hMf
  have hMR : minkowski h₁ h₂ (faceRight h₁ σ + faceRight h₂ σ) = ((y : ℝ) : WithTop ℝ) := by
    rw [minkowski_faceRight_add hh₁ hh₂ h0₁ h0₂ hu₁ hu₂ σ, ← hy]
  have hlinele := subgradient_line_le_minkowski hh₁ hh₂
    (fun _ ht ↦ unitSlope_le_of_lt_faceRight ht)
    (fun _ ht ↦ (hh₁.lt_unitSlope_of_faceRight_le h0₁ hu₁ ht).le)
    (fun _ ht ↦ unitSlope_le_of_lt_faceRight ht)
    (fun _ ht ↦ (hh₂.lt_unitSlope_of_faceRight_le h0₂ hu₂ ht).le) hy.symm
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 (ne_top_faceRight h0₁ σ)
  obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 (ne_top_faceRight h0₂ σ)
  have hab : a + b = y := by
    rw [← hA, ← hB, ← WithTop.coe_add, WithTop.coe_inj] at hy
    exact hy.symm
  have hna : (h₁ (faceRight h₁ σ)).untop₀ = a := by rw [← hA, WithTop.untop₀_coe]
  have hnb : (h₂ (faceRight h₂ σ)).untop₀ = b := by rw [← hB, WithTop.untop₀_coe]
  -- strictly below the Minkowski sum to the right of the face
  have hstrict : ∀ j, faceRight h₁ σ + faceRight h₂ σ < j →
      ((y + σ * ((j : ℝ) - (faceRight h₁ σ + faceRight h₂ σ : ℕ)) : ℝ) : WithTop ℝ)
        < minkowski h₁ h₂ j := by
    intro j hj
    obtain ⟨p, hp, hsplit⟩ := exists_minkowski_eq (h₁ := h₁) (h₂ := h₂) j
    rw [hsplit]
    by_cases hT : h₁ p + h₂ (j - p) = ⊤
    · rw [hT]
      exact WithTop.coe_lt_top _
    rw [WithTop.add_eq_top, not_or] at hT
    obtain ⟨u, hU⟩ := WithTop.ne_top_iff_exists.1 hT.1
    obtain ⟨w, hW⟩ := WithTop.ne_top_iff_exists.1 hT.2
    rw [← hU, ← hW, ← WithTop.coe_add, WithTop.coe_lt_coe]
    have hσcast : σ * ((j : ℝ) - ((faceRight h₁ σ + faceRight h₂ σ : ℕ) : ℝ))
        = σ * ((p : ℝ) - faceRight h₁ σ) + σ * (((j - p : ℕ) : ℝ) - faceRight h₂ σ) := by
      rw [Nat.cast_sub hp]
      push_cast
      ring
    rcases lt_or_ge (faceRight h₁ σ) p with hlt | hge
    · have hx₁ := hh₁.faceRight_line_lt h0₁ hu₁ hlt
      have hx₂ := hh₂.faceRight_line_le h0₂ hu₂ σ (j - p)
      rw [hna, ← hU, WithTop.coe_lt_coe] at hx₁
      rw [hnb, ← hW, WithTop.coe_le_coe] at hx₂
      rw [hσcast]
      linarith [hab]
    · have hlt₂ : faceRight h₂ σ < j - p := by omega
      have hx₁ := hh₁.faceRight_line_le h0₁ hu₁ σ p
      have hx₂ := hh₂.faceRight_line_lt h0₂ hu₂ hlt₂
      rw [hna, ← hU, WithTop.coe_le_coe] at hx₁
      rw [hnb, ← hW, WithTop.coe_lt_coe] at hx₂
      rw [hσcast]
      linarith [hab]
  have hMconv : IsConvexSeq (minkowski h₁ h₂) := isConvexSeq_minkowski hh₁ hh₂ h0₁ h0₂
  have hM0 : minkowski h₁ h₂ 0 ≠ ⊤ := by
    rw [minkowski_zero, Ne, WithTop.add_eq_top, not_or]
    exact ⟨h0₁, h0₂⟩
  have hgt : (σ : WithTop ℝ) < unitSlope (minkowski h₁ h₂) (faceRight h₁ σ + faceRight h₂ σ) := by
    have hstr := hstrict (faceRight h₁ σ + faceRight h₂ σ + 1) (by omega)
    by_cases hT : minkowski h₁ h₂ (faceRight h₁ σ + faceRight h₂ σ + 1) = ⊤
    · rw [unitSlope_eq_top_iff.2 (Or.inr (by rwa [Order.succ_eq_add_one]))]
      exact WithTop.coe_lt_top σ
    obtain ⟨w, hW⟩ := WithTop.ne_top_iff_exists.1 hT
    rw [← hW, WithTop.coe_lt_coe] at hstr
    rw [unitSlope_of_ne_top (by rw [hMR]; exact WithTop.coe_ne_top)
        (by rw [Order.succ_eq_add_one]; exact hT),
      Order.succ_eq_add_one, hMR, ← hW, WithTop.coe_lt_coe]
    simp only [WithTop.untop₀_coe]
    push_cast at hstr
    linarith
  refine le_antisymm
    (Nat.sInf_le (s := {j | (σ : WithTop ℝ) < unitSlope (minkowski h₁ h₂) j}) hgt) ?_
  by_contra hc
  rw [not_le] at hc
  have hmem : (σ : WithTop ℝ) < unitSlope (minkowski h₁ h₂) (faceRight (minkowski h₁ h₂) σ) :=
    lt_unitSlope_faceRight (slopesUnbounded_minkowski hh₁ hh₂ h0₁ h0₂ hu₁ hu₂) σ
  set j := faceRight (minkowski h₁ h₂) σ with hjdef
  have hjf : minkowski h₁ h₂ j ≠ ⊤ := ne_top_faceRight hM0 σ
  have hbound := hMconv.add_nsmul_unitSlope_le hjf
    (show j ≤ faceRight h₁ σ + faceRight h₂ σ by omega)
  have hsne : unitSlope (minkowski h₁ h₂) j ≠ ⊤ := by
    intro hx
    rw [hx] at hbound
    have hcard : 0 < (Finset.Ico j (faceRight h₁ σ + faceRight h₂ σ)).card := by
      rw [Nat.card_Ico]
      omega
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
    rw [hl, succ_nsmul, add_top, add_top, hMR, top_le_iff] at hbound
    exact WithTop.coe_ne_top hbound
  obtain ⟨t, hTs⟩ := WithTop.ne_top_iff_exists.1 hsne
  obtain ⟨m, hM⟩ := WithTop.ne_top_iff_exists.1 hjf
  rw [← hTs, WithTop.coe_lt_coe] at hmem
  rw [hMR, ← hM, ← hTs, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
    Nat.card_Ico, Nat.cast_sub (show j ≤ faceRight h₁ σ + faceRight h₂ σ by omega)] at hbound
  have hline := hlinele j
  rw [← hM, WithTop.coe_le_coe] at hline
  have hjlt : (j : ℝ) < ((faceRight h₁ σ + faceRight h₂ σ : ℕ) : ℝ) := Nat.cast_lt.2 hc
  push_cast at hbound hline hjlt
  nlinarith [hbound, hline, hmem, hjlt]

/-- **Slope multisets add**: the slope multiset of the Minkowski sum is the sum of the two slope
multisets ([Ked07, §2]: "the slope multiset of `PQ` is the union of the slope multisets of `P`
and `Q`"). -/
theorem slopeMultiset_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hfin₁ : (slopeIndices h₁).Finite) (hfin₂ : (slopeIndices h₂).Finite) :
    slopeMultiset (minkowski h₁ h₂) = slopeMultiset h₁ + slopeMultiset h₂ := by
  have hu₁ : SlopesUnbounded h₁ := NewtonPolygon.slopesUnbounded_of_finite hfin₁
  have hu₂ : SlopesUnbounded h₂ := NewtonPolygon.slopesUnbounded_of_finite hfin₂
  have hMconv : IsConvexSeq (minkowski h₁ h₂) := isConvexSeq_minkowski hh₁ hh₂ h0₁ h0₂
  have hM0 : minkowski h₁ h₂ 0 ≠ ⊤ := by
    rw [minkowski_zero, Ne, WithTop.add_eq_top, not_or]
    exact ⟨h0₁, h0₂⟩
  -- the finiteness sets of the factors are finite, hence so are the slope indices of the sum
  have hfs : ∀ {g : ℕ → WithTop ℝ}, IsConvexSeq g → g 0 ≠ ⊤ → (slopeIndices g).Finite →
      ∀ j, sSup (slopeIndices g) + 1 < j → g j = ⊤ := by
    intro g hg hg0 hgfin j hj
    by_contra hx
    have hprev : g (j - 1) ≠ ⊤ := mem_finiteSet.1 (hg.ordConnected.out (mem_finiteSet.2 hg0)
      (mem_finiteSet.2 hx) ⟨Nat.zero_le _, by omega⟩)
    have hmemj : j - 1 ∈ slopeIndices g :=
      mem_slopeIndices_iff.2 ⟨hprev, by rwa [show j - 1 + 1 = j by omega]⟩
    have := le_csSup hgfin.bddAbove hmemj
    omega
  have hMtop : ∀ j, sSup (slopeIndices h₁) + sSup (slopeIndices h₂) + 2 < j →
      minkowski h₁ h₂ j = ⊤ := by
    intro j hj
    refine top_le_iff.1 (le_minkowski_iff.2 fun i hi ↦ ?_)
    rcases lt_or_ge (sSup (slopeIndices h₁) + 1) i with h1 | h1
    · rw [hfs hh₁ h0₁ hfin₁ i h1, top_add]
    · rw [hfs hh₂ h0₂ hfin₂ (j - i) (by omega), add_top]
  have hMfin : (slopeIndices (minkowski h₁ h₂)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio
      (sSup (slopeIndices h₁) + sSup (slopeIndices h₂) + 3)) ?_
    intro j hj
    rw [Set.mem_Iio]
    by_contra hc
    exact (mem_slopeIndices_iff.1 hj).1 (hMtop j (by omega))
  refine Multiset.ext.2 fun σ ↦ ?_
  rw [Multiset.count_add, hMconv.count_slopeMultiset_eq hM0 hMfin σ,
    hh₁.count_slopeMultiset_eq h0₁ hfin₁ σ, hh₂.count_slopeMultiset_eq h0₂ hfin₂ σ,
    faceRight_minkowski hh₁ hh₂ h0₁ h0₂ hu₁ hu₂ σ, faceLeft_minkowski hh₁ hh₂ h0₁ h0₂ hu₁ hu₂ σ]
  have hfl₁ := faceLeft_le_faceRight hu₁ σ
  have hfl₂ := faceLeft_le_faceRight hu₂ σ
  omega

end NewtonPolygon
