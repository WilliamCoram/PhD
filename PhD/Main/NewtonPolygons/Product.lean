/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.NewtonPolygons.Face
import PhD.Main.NewtonPolygons.CoeffVal

/-!
# The Newton polygon of a product

[Ked07, §2]: "for `P, Q ∈ F[T]`, the slope multiset of `PQ` is the union of the slope
multisets of `P` and `Q`."  Equivalently, the Newton polygon of `fg` is the *Minkowski sum* of
the polygons of `f` and `g`: its height at `n` is

  `min_{i + j = n} (height_f i + height_g j)`   (`NewtonPolygon₀.minkowskiHeight`).

The proof is [Ked07, Proposition 1 (Robba) and Corollary 2], read through the faces of
`Face.lean`:

* the ultrametric bound puts every point of `fg` on/above the Minkowski sum
  (`inf_coeffVal_add_le_coeffVal_mul`, [Ked07, (1)]);
* at the endpoints of a face of slope `σ` the minimising split is unique, so the ultrametric
  bound is an equality there (`coeffVal_mul_eq_of_forall_lt`, [Ked07]: "let `i₀` and `j₀` be
  the smallest values of `i` and `j` which minimize ... then (1) achieves its minimum for ...
  but not for any other");
* a supporting line of the Minkowski sum at `n` is the sum of supporting lines of the two
  factors with a common slope (`exists_subgradient`), so `line_le_height` gives
  `minkowskiHeight ≤ height` (`minkowskiHeight_le_height_mul`);
* every `n` lies on a face of the Minkowski sum, whose endpoints are points of `fg`, so the
  chord inequality gives `height ≤ minkowskiHeight` (`height_mul_le_minkowskiHeight`).

The hypotheses are `IsEntireNewtonPolygonOf` for each factor: anchored at the origin, no `⊥`
unit slope, slopes unbounded (polynomials, entire series).  Unbounded slopes cannot be dropped:
`(1 − X) · ∑ Xⁱ = 1`, whose polygon is a point while the Minkowski sum is the horizontal ray.

## Corollaries

* `IsEntireNewtonPolygonOf.height_mul_of_forall_le` — **the initial segment**: if the first `n`
  slopes of `g` are at most every slope of `f`, the polygon of `fg` agrees with that of `g`
  up to `n` (the statement [LWX, §3.23 Step I] uses: the finite factor supplies the first
  `n` slopes).
* `IsEntireNewtonPolygonOf.faceRight_mul` — **multiplicities add** ([Ked07, Cor. 2]): the
  number of slopes `≤ σ` of `fg` is the sum of those of `f` and `g`.
* the same for the constructed polygons `newtonPolygon₀OfPowerSeries negLogNorm _` of series
  restricted at every radius, including the polynomial factor form
  `height_newtonPolygon₀OfPowerSeries_mul_coe`.

## Sources

[Ked07] K. S. Kedlaya, *p-adic differential equations*, 18.787 (MIT, fall 2007), unit "Newton
polygons", §2 (`kskedlaya.org/18.787/newton-poly.pdf`).
[Kob84] N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Ch. IV §4
Lemma 6 (p. 102): the case of a linear factor `(1 − cX) f(X)`.
[LWX] Liu–Wan–Xiao, *The eigencurve over the boundary of weight space*, §3.23 Step I.
-/

open Finset

noncomputable section

namespace NewtonPolygon₀

variable (P Q : NewtonPolygon₀ (Γ := ℝ))

/-- The height at `n` of the **Minkowski sum** `P ⊕ Q` of two one-sided polygons: the least
`height_P i + height_Q j` over the splits `i + j = n` (the infimal convolution of the two
height functions).  `⊤` once every split meets a `⊤` height. -/
def minkowskiHeight (n : ℕ) : WithBotTop ℝ :=
  (range (n + 1)).inf fun i => P.height i + Q.height (n - i)

variable {P Q}

/-! ### Junk-value arithmetic in `WithBotTop ℝ` -/

/-- The coercion `WithTop ℝ → WithBotTop ℝ` is additive. -/
theorem coe_add_coe' (a b : WithTop ℝ) :
    ((a : WithBotTop ℝ) + (b : WithBotTop ℝ)) = ((a + b : WithTop ℝ) : WithBotTop ℝ) :=
  (WithBot.coe_add a b).symm

/-- The coercion `ℝ → WithBotTop ℝ` is additive. -/
theorem coe_add_coe (a b : ℝ) :
    ((a : WithBotTop ℝ) + (b : WithBotTop ℝ)) = ((a + b : ℝ) : WithBotTop ℝ) := rfl

/-- A sum in `WithBotTop ℝ` is `⊥` exactly when a summand is. -/
theorem add_eq_bot_iff {a b : WithBotTop ℝ} : a + b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  induction a using WithBotTop.rec with
  | bot => simp
  | coe x =>
    induction b using WithBotTop.rec with
    | bot => simp
    | coe y => simp [show ((x : WithBotTop ℝ) + (y : WithBotTop ℝ)) = ((x + y : ℝ) : WithBotTop ℝ)
        from rfl]
    | top => simp [show ((x : WithBotTop ℝ) + (⊤ : WithBotTop ℝ)) = ⊤ from rfl]
  | top =>
    induction b using WithBotTop.rec with
    | bot => simp
    | coe y => simp [show ((⊤ : WithBotTop ℝ) + (y : WithBotTop ℝ)) = ⊤ from rfl]
    | top => simp [show ((⊤ : WithBotTop ℝ) + (⊤ : WithBotTop ℝ)) = ⊤ from rfl]

/-- A sum of two non-`⊥` elements of `WithBotTop ℝ` is `⊤` exactly when a summand is. -/
theorem add_eq_top_iff {a b : WithBotTop ℝ} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  induction a using WithBotTop.rec with
  | bot => exact absurd rfl ha
  | coe x =>
    induction b using WithBotTop.rec with
    | bot => exact absurd rfl hb
    | coe y => simp [show ((x : WithBotTop ℝ) + (y : WithBotTop ℝ)) = ((x + y : ℝ) : WithBotTop ℝ)
        from rfl]
    | top => simp [show ((x : WithBotTop ℝ) + (⊤ : WithBotTop ℝ)) = ⊤ from rfl]
  | top =>
    induction b using WithBotTop.rec with
    | bot => exact absurd rfl hb
    | coe y => simp [show ((⊤ : WithBotTop ℝ) + (y : WithBotTop ℝ)) = ⊤ from rfl]
    | top => simp [show ((⊤ : WithBotTop ℝ) + (⊤ : WithBotTop ℝ)) = ⊤ from rfl]

/-- A non-`⊥`, non-`⊤` element of `WithBotTop ℝ` is a real number. -/
theorem exists_coe_of_ne {a : WithBotTop ℝ} (hb : a ≠ ⊥) (ht : a ≠ ⊤) :
    ∃ r : ℝ, a = (r : WithBotTop ℝ) := by
  induction a using WithBotTop.rec with
  | bot => exact absurd rfl hb
  | coe r => exact ⟨r, rfl⟩
  | top => exact absurd rfl ht

/-- A sum of two heights that is a real number splits into two real heights. -/
private lemma exists_coe_of_add_eq_coe {P Q : NewtonPolygon₀ (Γ := ℝ)}
    (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0) {i j : ℕ} {y : ℝ}
    (hy : P.height i + Q.height j = (y : WithBotTop ℝ)) :
    ∃ yP yQ : ℝ, P.height i = (yP : WithBotTop ℝ) ∧ Q.height j = (yQ : WithBotTop ℝ) ∧
      y = yP + yQ := by
  have hbP := P.height_natCast_ne_bot hxP i
  have hbQ := Q.height_natCast_ne_bot hxQ j
  have htop : ¬ (P.height i = ⊤ ∨ Q.height j = ⊤) := fun hc =>
    WithBotTop.coe_ne_top y (hy ▸ (add_eq_top_iff hbP hbQ).2 hc)
  obtain ⟨yP, hyP⟩ := exists_coe_of_ne hbP fun hc => htop (Or.inl hc)
  obtain ⟨yQ, hyQ⟩ := exists_coe_of_ne hbQ fun hc => htop (Or.inr hc)
  refine ⟨yP, yQ, hyP, hyQ, WithBotTop.coe_injective ?_⟩
  rw [← hy, hyP, hyQ]
  rfl

/-- Adding a strict and a non-strict bound below two non-`⊥` values. -/
theorem coe_add_lt_add_left {a b : WithBotTop ℝ} (ha : a ≠ ⊥) (hb : b ≠ ⊥) {u v : ℝ}
    (hu : (u : WithBotTop ℝ) < a) (hv : (v : WithBotTop ℝ) ≤ b) :
    ((u + v : ℝ) : WithBotTop ℝ) < a + b := by
  by_cases hat : a = ⊤
  · rw [hat, (add_eq_top_iff (by simp) hb).2 (Or.inl rfl)]
    exact lt_top_iff_ne_top.2 (WithBotTop.coe_ne_top _)
  by_cases hbt : b = ⊤
  · rw [hbt, (add_eq_top_iff ha (by simp)).2 (Or.inr rfl)]
    exact lt_top_iff_ne_top.2 (WithBotTop.coe_ne_top _)
  obtain ⟨x, hx⟩ := exists_coe_of_ne ha hat
  obtain ⟨w, hw⟩ := exists_coe_of_ne hb hbt
  rw [hx, WithBotTop.coe_lt_coe] at hu
  rw [hw, WithBotTop.coe_le_coe] at hv
  rw [hx, hw, show ((x : WithBotTop ℝ) + (w : WithBotTop ℝ)) = ((x + w : ℝ) : WithBotTop ℝ)
    from rfl, WithBotTop.coe_lt_coe]
  linarith

/-- Adding a non-strict and a strict bound below two non-`⊥` values. -/
theorem coe_add_lt_add_right {a b : WithBotTop ℝ} (ha : a ≠ ⊥) (hb : b ≠ ⊥) {u v : ℝ}
    (hu : (u : WithBotTop ℝ) ≤ a) (hv : (v : WithBotTop ℝ) < b) :
    ((u + v : ℝ) : WithBotTop ℝ) < a + b := by
  rw [add_comm a b, show u + v = v + u from add_comm u v]
  exact coe_add_lt_add_left hb ha hv hu

/-! ### The Minkowski height -/

/-- The Minkowski height is at most each split. -/
theorem minkowskiHeight_le {n i : ℕ} (hi : i ≤ n) :
    P.minkowskiHeight Q n ≤ P.height i + Q.height (n - i) :=
  Finset.inf_le (mem_range.2 (Nat.lt_succ_of_le hi))

/-- A lower bound for the Minkowski height is a lower bound for every split. -/
theorem le_minkowskiHeight_iff {n : ℕ} {a : WithBotTop ℝ} :
    a ≤ P.minkowskiHeight Q n ↔ ∀ i, i ≤ n → a ≤ P.height i + Q.height (n - i) := by
  rw [minkowskiHeight, Finset.le_inf_iff]
  exact ⟨fun h i hi => h i (mem_range.2 (Nat.lt_succ_of_le hi)),
    fun h i hi => h i (Nat.lt_succ_iff.1 (mem_range.1 hi))⟩

/-- The Minkowski height is attained by some split. -/
theorem exists_minkowskiHeight_eq (n : ℕ) :
    ∃ i, i ≤ n ∧ P.minkowskiHeight Q n = P.height i + Q.height (n - i) := by
  obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_inf (range (n + 1)) ⟨0, by simp⟩
    fun i => P.height i + Q.height (n - i)
  exact ⟨i, Nat.lt_succ_iff.1 (mem_range.1 hi), hval⟩

/-- The Minkowski sum is symmetric. -/
theorem minkowskiHeight_comm (n : ℕ) : P.minkowskiHeight Q n = Q.minkowskiHeight P n := by
  refine le_antisymm (le_minkowskiHeight_iff.2 fun i hi => ?_)
    (le_minkowskiHeight_iff.2 fun i hi => ?_) <;>
  · refine le_trans (minkowskiHeight_le (show n - i ≤ n by omega)) (le_of_eq ?_)
    rw [Nat.cast_sub hi, sub_sub_cancel, add_comm]

/-- At `0` the only split is `(0, 0)`. -/
@[simp] theorem minkowskiHeight_zero : P.minkowskiHeight Q 0 = P.height 0 + Q.height 0 := by
  simp [minkowskiHeight]

/-- For polygons anchored at the origin the Minkowski height is never `⊥`. -/
theorem minkowskiHeight_ne_bot (hP : P.starting_point.1 = 0) (hQ : Q.starting_point.1 = 0)
    (n : ℕ) : P.minkowskiHeight Q n ≠ ⊥ := by
  obtain ⟨i, hi, hval⟩ := exists_minkowskiHeight_eq (P := P) (Q := Q) n
  rw [hval, ne_eq, add_eq_bot_iff]
  exact not_or.2 ⟨P.height_natCast_ne_bot hP i,
    Q.height_ne_bot_of_nonneg hQ (by omega : (0 : ℤ) ≤ (n : ℤ) - (i : ℤ))⟩

/-- Once the Minkowski height is `⊤` it stays `⊤` (`height_eq_top_mono` for each factor). -/
theorem minkowskiHeight_eq_top_mono (hP : P.starting_point.1 = 0) (hQ : Q.starting_point.1 = 0)
    {m n : ℕ} (h : P.minkowskiHeight Q m = ⊤) (hmn : m ≤ n) : P.minkowskiHeight Q n = ⊤ := by
  refine top_le_iff.1 (le_minkowskiHeight_iff.2 fun i hi => ?_)
  -- every split of `m` is `⊤`; transport the responsible factor to the split `(i, n - i)` of `n`
  have hsplit : ∀ j, j ≤ m → P.height j + Q.height (m - j) = ⊤ := fun j hj =>
    top_le_iff.1 (h ▸ minkowskiHeight_le hj)
  have hnbQ : Q.height ((n : ℤ) - (i : ℤ)) ≠ ⊥ :=
    Q.height_ne_bot_of_nonneg hQ (by omega)
  have key : P.height i = ⊤ ∨ Q.height ((n : ℤ) - (i : ℤ)) = ⊤ := by
    rcases le_or_gt i m with him | him
    · rcases (add_eq_top_iff (P.height_natCast_ne_bot hP i)
        (Q.height_ne_bot_of_nonneg hQ (by omega : (0 : ℤ) ≤ (m : ℤ) - (i : ℤ)))).1
        (hsplit i him) with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Q.height_eq_top_mono hc (by omega))
    · refine Or.inl (P.height_eq_top_mono ?_ (by omega : (m : ℤ) ≤ (i : ℤ)))
      have hm := hsplit m le_rfl
      rw [sub_self] at hm
      rcases (add_eq_top_iff (P.height_natCast_ne_bot hP m)
        (Q.height_ne_bot_of_nonneg hQ le_rfl)).1 hm with hc | hc
      · exact hc
      · exact absurd hc (Q.height_natCast_zero_ne_top hQ)
  exact top_le_iff.2 ((add_eq_top_iff (P.height_natCast_ne_bot hP i) hnbQ).2 key)

/-- **A supporting line of the Minkowski sum.**  If `σ` separates the unit slopes of `P` at
`i₀` and those of `Q` at `j₀`, the line of slope `σ` through `(i₀ + j₀, height_P i₀ + height_Q j₀)`
lies on/below the Minkowski sum (sum of the two supporting lines of
`line_le_height_of_unitSlope`). -/
theorem subgradient_line_le_minkowskiHeight (hxP : P.starting_point.1 = 0)
    (hxQ : Q.starting_point.1 = 0) (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥)
    {i₀ j₀ : ℕ} {σ : ℝ} (hP₁ : ∀ t, t < i₀ → P.unitSlope t ≤ (σ : WithBotTop ℝ))
    (hP₂ : ∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) ≤ P.unitSlope t)
    (hQ₁ : ∀ t, t < j₀ → Q.unitSlope t ≤ (σ : WithBotTop ℝ))
    (hQ₂ : ∀ t, j₀ ≤ t → (σ : WithBotTop ℝ) ≤ Q.unitSlope t) {y : ℝ}
    (hy : P.height i₀ + Q.height j₀ = (y : WithBotTop ℝ)) (m : ℕ) :
    ((y + σ * ((m : ℝ) - (i₀ + j₀ : ℕ)) : ℝ) : WithBotTop ℝ) ≤ P.minkowskiHeight Q m := by
  obtain ⟨yP, yQ, hyP, hyQ, hysum⟩ := exists_coe_of_add_eq_coe hxP hxQ hy
  refine le_minkowskiHeight_iff.2 fun i hi => ?_
  -- the two supporting lines, added
  have hPline := P.line_le_height_of_unitSlope hxP hbP hP₁ hP₂ hyP i
  have hQline := Q.line_le_height_of_unitSlope hxQ hbQ hQ₁ hQ₂ hyQ (m - i)
  rw [show (((m - i : ℕ) : ℕ) : ℤ) = (m : ℤ) - (i : ℤ) from Nat.cast_sub hi] at hQline
  refine le_trans (le_of_eq ?_) (add_le_add hPline hQline)
  have hcast : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := Nat.cast_sub hi
  rw [show ((yP + σ * ((i : ℝ) - i₀) : ℝ) : WithBotTop ℝ) +
      ((yQ + σ * (((m - i : ℕ) : ℝ) - j₀) : ℝ) : WithBotTop ℝ)
      = (((yP + σ * ((i : ℝ) - i₀)) + (yQ + σ * (((m - i : ℕ) : ℝ) - j₀)) : ℝ) : WithBotTop ℝ)
      from rfl]
  congr 1
  rw [hcast, hysum]
  push_cast
  ring

/-- **A minimising split has a common subgradient.**  If `(i₀, n − i₀)` attains the (finite)
Minkowski height at `n`, there is a real `σ` separating the unit slopes of `P` at `i₀` and those
of `Q` at `n − i₀` (compare the split with its two neighbours). -/
theorem exists_subgradient (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) {n i₀ : ℕ} (hi₀ : i₀ ≤ n)
    {y : ℝ} (hy : P.minkowskiHeight Q n = (y : WithBotTop ℝ))
    (heq : P.height i₀ + Q.height (n - i₀) = (y : WithBotTop ℝ)) :
    ∃ σ : ℝ, (∀ t, t < i₀ → P.unitSlope t ≤ (σ : WithBotTop ℝ)) ∧
      (∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) ≤ P.unitSlope t) ∧
      (∀ t, t < n - i₀ → Q.unitSlope t ≤ (σ : WithBotTop ℝ)) ∧
      (∀ t, n - i₀ ≤ t → (σ : WithBotTop ℝ) ≤ Q.unitSlope t) := by
  classical
  set j₀ : ℕ := n - i₀ with hj₀def
  have hcast : ((j₀ : ℕ) : ℤ) = (n : ℤ) - (i₀ : ℤ) := by rw [hj₀def, Nat.cast_sub hi₀]
  rw [← hcast] at heq
  obtain ⟨yP, yQ, hyP, hyQ, hysum⟩ := exists_coe_of_add_eq_coe hxP hxQ heq
  have hyPtop : P.height (i₀ : ℤ) ≠ ⊤ := by rw [hyP]; exact WithBotTop.coe_ne_top _
  have hyQtop : Q.height (j₀ : ℤ) ≠ ⊤ := by rw [hyQ]; exact WithBotTop.coe_ne_top _
  -- **(a)** the last `Q`-slope before `j₀` is at most the next `P`-slope: otherwise moving one
  -- unit from `Q` to `P` would beat the minimising split
  have hA : 0 < j₀ → Q.unitSlope (j₀ - 1) ≤ P.unitSlope i₀ := by
    intro hj
    have hsplit := minkowskiHeight_le (P := P) (Q := Q) (show i₀ + 1 ≤ n by omega)
    rw [hy, show ((n : ℤ) - ((i₀ + 1 : ℕ) : ℤ)) = ((j₀ - 1 : ℕ) : ℤ) by omega] at hsplit
    by_cases hPtop : P.height ((i₀ + 1 : ℕ) : ℤ) = ⊤
    · obtain ⟨-, -, htop⟩ := P.unitSlope_eq_top_of_height_eq_top hPtop
      rw [hxP, sub_zero, Int.toNat_natCast, Nat.add_sub_cancel] at htop
      rw [htop]; exact le_top
    have hQ1top : Q.height ((j₀ - 1 : ℕ) : ℤ) ≠ ⊤ := fun hc =>
      hyQtop (Q.height_eq_top_mono hc (by omega))
    obtain ⟨a, ha⟩ := exists_coe_of_ne (P.height_natCast_ne_bot hxP (i₀ + 1)) hPtop
    obtain ⟨b, hb⟩ := exists_coe_of_ne (Q.height_natCast_ne_bot hxQ (j₀ - 1)) hQ1top
    rw [P.unitSlope_eq_of_height_eq hxP (hbP i₀) hyP ha,
      Q.unitSlope_eq_of_height_eq hxQ (hbQ (j₀ - 1)) hb
        (by rw [show j₀ - 1 + 1 = j₀ by omega]; exact hyQ),
      WithBotTop.coe_le_coe]
    rw [ha, hb, show ((a : WithBotTop ℝ) + (b : WithBotTop ℝ)) = ((a + b : ℝ) : WithBotTop ℝ)
      from rfl, WithBotTop.coe_le_coe] at hsplit
    linarith
  -- **(b)** the mirror image
  have hB : 0 < i₀ → P.unitSlope (i₀ - 1) ≤ Q.unitSlope j₀ := by
    intro hi
    have hsplit := minkowskiHeight_le (P := P) (Q := Q) (show i₀ - 1 ≤ n by omega)
    rw [hy, show ((n : ℤ) - ((i₀ - 1 : ℕ) : ℤ)) = ((j₀ + 1 : ℕ) : ℤ) by omega] at hsplit
    by_cases hQtop : Q.height ((j₀ + 1 : ℕ) : ℤ) = ⊤
    · obtain ⟨-, -, htop⟩ := Q.unitSlope_eq_top_of_height_eq_top hQtop
      rw [hxQ, sub_zero, Int.toNat_natCast, Nat.add_sub_cancel] at htop
      rw [htop]; exact le_top
    have hP1top : P.height ((i₀ - 1 : ℕ) : ℤ) ≠ ⊤ := fun hc =>
      hyPtop (P.height_eq_top_mono hc (by omega))
    obtain ⟨a, ha⟩ := exists_coe_of_ne (Q.height_natCast_ne_bot hxQ (j₀ + 1)) hQtop
    obtain ⟨b, hb⟩ := exists_coe_of_ne (P.height_natCast_ne_bot hxP (i₀ - 1)) hP1top
    rw [Q.unitSlope_eq_of_height_eq hxQ (hbQ j₀) hyQ ha,
      P.unitSlope_eq_of_height_eq hxP (hbP (i₀ - 1)) hb
        (by rw [show i₀ - 1 + 1 = i₀ by omega]; exact hyP),
      WithBotTop.coe_le_coe]
    rw [ha, hb, show ((b : WithBotTop ℝ) + (a : WithBotTop ℝ)) = ((b + a : ℝ) : WithBotTop ℝ)
      from rfl, WithBotTop.coe_le_coe] at hsplit
    linarith
  -- convexity reduces the four quantified goals to bounds at the two boundary indices
  suffices h : ∃ σ : ℝ, (0 < i₀ → P.unitSlope (i₀ - 1) ≤ (σ : WithBotTop ℝ)) ∧
      ((σ : WithBotTop ℝ) ≤ P.unitSlope i₀) ∧
      (0 < j₀ → Q.unitSlope (j₀ - 1) ≤ (σ : WithBotTop ℝ)) ∧
      ((σ : WithBotTop ℝ) ≤ Q.unitSlope j₀) by
    obtain ⟨σ, h1, h2, h3, h4⟩ := h
    exact ⟨σ, fun t ht => (P.unitSlope_mono (by omega)).trans (h1 (by omega)),
      fun t ht => h2.trans (P.unitSlope_mono ht),
      fun t ht => (Q.unitSlope_mono (by omega)).trans (h3 (by omega)),
      fun t ht => h4.trans (Q.unitSlope_mono ht)⟩
  -- the boundary slopes, where they exist, are real
  have hPa : 0 < i₀ → ∃ r : ℝ, P.unitSlope (i₀ - 1) = (r : WithBotTop ℝ) := fun hi =>
    exists_coe_of_ne (hbP _) (P.unitSlope_ne_top_of_height_natCast hxP hyPtop (by omega))
  have hQb : 0 < j₀ → ∃ r : ℝ, Q.unitSlope (j₀ - 1) = (r : WithBotTop ℝ) := fun hj =>
    exists_coe_of_ne (hbQ _) (Q.unitSlope_ne_top_of_height_natCast hxQ hyQtop (by omega))
  rcases Nat.eq_zero_or_pos i₀ with hi0 | hi0 <;> rcases Nat.eq_zero_or_pos j₀ with hj0 | hj0
  · -- no boundary constraint at all: any sufficiently small slope works
    refine ⟨min (NewtonPolygon.toReal (P.unitSlope 0)) (NewtonPolygon.toReal (Q.unitSlope 0)) - 1,
      by omega, ?_, by omega, ?_⟩
    · rw [hi0]
      rcases eq_or_ne (P.unitSlope 0) ⊤ with hc | hc
      · rw [hc]; exact le_top
      · obtain ⟨r, hr⟩ := exists_coe_of_ne (hbP 0) hc
        rw [hr, WithBotTop.coe_le_coe, NewtonPolygon.toReal_coe]
        have := min_le_left r (NewtonPolygon.toReal (Q.unitSlope 0))
        linarith
    · rw [hj0]
      rcases eq_or_ne (Q.unitSlope 0) ⊤ with hc | hc
      · rw [hc]; exact le_top
      · obtain ⟨r, hr⟩ := exists_coe_of_ne (hbQ 0) hc
        rw [hr, WithBotTop.coe_le_coe, NewtonPolygon.toReal_coe]
        have := min_le_right (NewtonPolygon.toReal (P.unitSlope 0)) r
        linarith
  · -- only `Q` constrains from below
    obtain ⟨r, hr⟩ := hQb hj0
    exact ⟨r, by omega, hr ▸ hA hj0, fun _ => le_of_eq hr,
      hr ▸ Q.unitSlope_mono (by omega)⟩
  · -- only `P` constrains from below
    obtain ⟨r, hr⟩ := hPa hi0
    exact ⟨r, fun _ => le_of_eq hr, hr ▸ P.unitSlope_mono (by omega), by omega,
      hr ▸ hB hi0⟩
  · -- both constrain: take the larger
    obtain ⟨rP, hrP⟩ := hPa hi0
    obtain ⟨rQ, hrQ⟩ := hQb hj0
    refine ⟨max rP rQ, fun _ => ?_, ?_, fun _ => ?_, ?_⟩
    · rw [hrP]; exact WithBotTop.coe_le_coe.2 (le_max_left _ _)
    · rcases max_choice rP rQ with hm | hm <;> rw [hm]
      · exact hrP ▸ P.unitSlope_mono (by omega)
      · exact hrQ ▸ hA hj0
    · rw [hrQ]; exact WithBotTop.coe_le_coe.2 (le_max_right _ _)
    · rcases max_choice rP rQ with hm | hm <;> rw [hm]
      · exact hrP ▸ hB hi0
      · exact hrQ ▸ Q.unitSlope_mono (by omega)

/-! ### The face of slope `σ` of the Minkowski sum

[Ked07, proof of Cor. 2]: the endpoints of the face of slope `σ` of the sum are the sums of the
endpoints of the faces of the factors, and the minimising split is unique there. -/

/-- At `faceLeft_P σ + faceLeft_Q σ` the Minkowski height is attained by the split of the two
left endpoints. -/
theorem minkowskiHeight_faceLeft (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded)
    (hQ : Q.SlopesUnbounded) (σ : ℝ) :
    P.minkowskiHeight Q (P.faceLeft σ + Q.faceLeft σ) =
      P.height (P.faceLeft σ) + Q.height (Q.faceLeft σ) := by
  obtain ⟨yP, hyP⟩ := P.exists_height_faceLeft_eq hxP σ
  obtain ⟨yQ, hyQ⟩ := Q.exists_height_faceLeft_eq hxQ σ
  have hy : P.height (P.faceLeft σ) + Q.height (Q.faceLeft σ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by rw [hyP, hyQ]; rfl
  refine le_antisymm ?_ ?_
  · refine le_trans (minkowskiHeight_le (show P.faceLeft σ ≤ P.faceLeft σ + Q.faceLeft σ by omega))
      (le_of_eq ?_)
    congr 2
    push_cast
    ring
  · have h0 := subgradient_line_le_minkowskiHeight hxP hxQ hbP hbQ
      (fun _ ht => (P.unitSlope_lt_of_lt_faceLeft ht).le)
      (fun _ ht => P.le_unitSlope_of_faceLeft_le hP ht)
      (fun _ ht => (Q.unitSlope_lt_of_lt_faceLeft ht).le)
      (fun _ ht => Q.le_unitSlope_of_faceLeft_le hQ ht) hy (P.faceLeft σ + Q.faceLeft σ)
    simp only [sub_self, mul_zero, add_zero] at h0
    rw [hy]
    exact h0

/-- At `faceLeft_P σ + faceLeft_Q σ` every other split is strictly worse. -/
theorem height_faceLeft_add_lt (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded)
    (hQ : Q.SlopesUnbounded) {σ : ℝ} {i j : ℕ} (hij : i + j = P.faceLeft σ + Q.faceLeft σ)
    (hne : i ≠ P.faceLeft σ) :
    P.height (P.faceLeft σ) + Q.height (Q.faceLeft σ) < P.height i + Q.height j := by
  obtain ⟨yP, hyP⟩ := P.exists_height_faceLeft_eq hxP σ
  obtain ⟨yQ, hyQ⟩ := Q.exists_height_faceLeft_eq hxQ σ
  have hz : ((i : ℝ) - (P.faceLeft σ : ℝ)) + ((j : ℝ) - (Q.faceLeft σ : ℝ)) = 0 := by
    have : (i : ℝ) + (j : ℝ) = (P.faceLeft σ : ℝ) + (Q.faceLeft σ : ℝ) := by exact_mod_cast hij
    linarith
  rw [hyP, hyQ, show ((yP : WithBotTop ℝ) + (yQ : WithBotTop ℝ))
    = ((yP + yQ : ℝ) : WithBotTop ℝ) from rfl]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `i` is left of the face: `P` is strictly above its line there
    refine lt_of_le_of_lt (le_of_eq ?_)
      (coe_add_lt_add_left (P.height_natCast_ne_bot hxP i) (Q.height_natCast_ne_bot hxQ j)
        (P.faceLeft_line_lt_height hxP hbP hyP hlt)
        (Q.faceLeft_line_le_height hxQ hbQ hQ hyQ j))
    congr 1
    linear_combination (-σ) * hz
  · -- `i` is right of the face, so `j` is left of `Q`'s
    refine lt_of_le_of_lt (le_of_eq ?_)
      (coe_add_lt_add_right (P.height_natCast_ne_bot hxP i) (Q.height_natCast_ne_bot hxQ j)
        (P.faceLeft_line_le_height hxP hbP hP hyP i)
        (Q.faceLeft_line_lt_height hxQ hbQ hyQ (show j < Q.faceLeft σ by omega)))
    congr 1
    linear_combination (-σ) * hz

/-- At `faceRight_P σ + faceRight_Q σ` the Minkowski height is attained by the split of the two
right endpoints. -/
theorem minkowskiHeight_faceRight (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded)
    (hQ : Q.SlopesUnbounded) (σ : ℝ) :
    P.minkowskiHeight Q (P.faceRight σ + Q.faceRight σ) =
      P.height (P.faceRight σ) + Q.height (Q.faceRight σ) := by
  obtain ⟨yP, hyP⟩ := P.exists_height_faceRight_eq hxP σ
  obtain ⟨yQ, hyQ⟩ := Q.exists_height_faceRight_eq hxQ σ
  have hy : P.height (P.faceRight σ) + Q.height (Q.faceRight σ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by rw [hyP, hyQ]; rfl
  refine le_antisymm ?_ ?_
  · refine le_trans
      (minkowskiHeight_le (show P.faceRight σ ≤ P.faceRight σ + Q.faceRight σ by omega))
      (le_of_eq ?_)
    congr 2
    push_cast
    ring
  · have h0 := subgradient_line_le_minkowskiHeight hxP hxQ hbP hbQ
      (fun _ ht => P.unitSlope_le_of_lt_faceRight ht)
      (fun _ ht => (P.lt_unitSlope_of_faceRight_le hP ht).le)
      (fun _ ht => Q.unitSlope_le_of_lt_faceRight ht)
      (fun _ ht => (Q.lt_unitSlope_of_faceRight_le hQ ht).le) hy
      (P.faceRight σ + Q.faceRight σ)
    simp only [sub_self, mul_zero, add_zero] at h0
    rw [hy]
    exact h0

/-- At `faceRight_P σ + faceRight_Q σ` every other split is strictly worse. -/
theorem height_faceRight_add_lt (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded)
    (hQ : Q.SlopesUnbounded) {σ : ℝ} {i j : ℕ} (hij : i + j = P.faceRight σ + Q.faceRight σ)
    (hne : i ≠ P.faceRight σ) :
    P.height (P.faceRight σ) + Q.height (Q.faceRight σ) < P.height i + Q.height j := by
  obtain ⟨yP, hyP⟩ := P.exists_height_faceRight_eq hxP σ
  obtain ⟨yQ, hyQ⟩ := Q.exists_height_faceRight_eq hxQ σ
  have hz : ((i : ℝ) - (P.faceRight σ : ℝ)) + ((j : ℝ) - (Q.faceRight σ : ℝ)) = 0 := by
    have : (i : ℝ) + (j : ℝ) = (P.faceRight σ : ℝ) + (Q.faceRight σ : ℝ) := by exact_mod_cast hij
    linarith
  rw [hyP, hyQ, show ((yP : WithBotTop ℝ) + (yQ : WithBotTop ℝ))
    = ((yP + yQ : ℝ) : WithBotTop ℝ) from rfl]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `i` is left of the face, so `j` is right of `Q`'s: `Q` is strictly above its line there
    refine lt_of_le_of_lt (le_of_eq ?_)
      (coe_add_lt_add_right (P.height_natCast_ne_bot hxP i) (Q.height_natCast_ne_bot hxQ j)
        (P.faceRight_line_le_height hxP hbP hP hyP i)
        (Q.faceRight_line_lt_height hxQ hbQ hQ hyQ (show Q.faceRight σ < j by omega)))
    congr 1
    linear_combination (-σ) * hz
  · refine lt_of_le_of_lt (le_of_eq ?_)
      (coe_add_lt_add_left (P.height_natCast_ne_bot hxP i) (Q.height_natCast_ne_bot hxQ j)
        (P.faceRight_line_lt_height hxP hbP hP hyP hgt)
        (Q.faceRight_line_le_height hxQ hbQ hQ hyQ j))
    congr 1
    linear_combination (-σ) * hz

/-- On the face of slope `σ` of the Minkowski sum — the interval between the sums of the left
and of the right endpoints — the Minkowski height is the line of slope `σ`. -/
theorem minkowskiHeight_eq_of_mem_face (hxP : P.starting_point.1 = 0)
    (hxQ : Q.starting_point.1 = 0) (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) (hQ : Q.SlopesUnbounded) {σ y : ℝ}
    (hy : P.minkowskiHeight Q (P.faceLeft σ + Q.faceLeft σ) = (y : WithBotTop ℝ)) {m : ℕ}
    (h1 : P.faceLeft σ + Q.faceLeft σ ≤ m) (h2 : m ≤ P.faceRight σ + Q.faceRight σ) :
    P.minkowskiHeight Q m =
      ((y + σ * ((m : ℝ) - (P.faceLeft σ + Q.faceLeft σ : ℕ)) : ℝ) : WithBotTop ℝ) := by
  obtain ⟨yP, hyP⟩ := P.exists_height_faceLeft_eq hxP σ
  obtain ⟨yQ, hyQ⟩ := Q.exists_height_faceLeft_eq hxQ σ
  have hfl := minkowskiHeight_faceLeft hxP hxQ hbP hbQ hP hQ σ
  rw [hyP, hyQ, coe_add_coe] at hfl
  have hyy : y = yP + yQ := WithBotTop.coe_injective (hy.symm.trans hfl)
  subst hyy
  have hPle := P.faceLeft_le_faceRight hP σ
  have hQle := Q.faceLeft_le_faceRight hQ σ
  have hyadd : P.height (P.faceLeft σ) + Q.height (Q.faceLeft σ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by rw [hyP, hyQ, coe_add_coe]
  refine le_antisymm ?_ ?_
  · -- a split with both halves on their own face realises the line
    set i : ℕ := P.faceLeft σ + min (m - (P.faceLeft σ + Q.faceLeft σ))
      (P.faceRight σ - P.faceLeft σ) with hidef
    have him : i ≤ m := by omega
    have hPv := P.height_eq_of_mem_face hxP hP hyP (show P.faceLeft σ ≤ i by omega)
      (show i ≤ P.faceRight σ by omega)
    have hQv := Q.height_eq_of_mem_face hxQ hQ hyQ (show Q.faceLeft σ ≤ m - i by omega)
      (show m - i ≤ Q.faceRight σ by omega)
    refine le_trans (minkowskiHeight_le him) (le_of_eq ?_)
    rw [show ((m : ℤ) - (i : ℤ)) = ((m - i : ℕ) : ℤ) from (Nat.cast_sub him).symm, hPv, hQv,
      coe_add_coe]
    congr 1
    have hcast : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := Nat.cast_sub him
    rw [hcast]
    push_cast
    ring
  · -- the supporting line of slope `σ` through the left endpoints
    have h0 := subgradient_line_le_minkowskiHeight hxP hxQ hbP hbQ
      (fun _ ht => (P.unitSlope_lt_of_lt_faceLeft ht).le)
      (fun _ ht => P.le_unitSlope_of_faceLeft_le hP ht)
      (fun _ ht => (Q.unitSlope_lt_of_lt_faceLeft ht).le)
      (fun _ ht => Q.le_unitSlope_of_faceLeft_le hQ ht) hyadd m
    exact h0

/-- **Strict growth past the face.**  One step beyond the right endpoint of the face of slope
`σ`, the Minkowski sum has risen by strictly more than `σ`: any split of `m₂ + 1` pushes one
factor strictly past its own face endpoint. -/
theorem lt_minkowskiHeight_faceRight_succ (hxP : P.starting_point.1 = 0)
    (hxQ : Q.starting_point.1 = 0) (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) (hQ : Q.SlopesUnbounded) (σ : ℝ) {yc : ℝ}
    (hyc : P.minkowskiHeight Q (P.faceRight σ + Q.faceRight σ) = (yc : WithBotTop ℝ)) :
    ((yc + σ : ℝ) : WithBotTop ℝ)
      < P.minkowskiHeight Q (P.faceRight σ + Q.faceRight σ + 1) := by
  obtain ⟨yP, hyP⟩ := P.exists_height_faceRight_eq hxP σ
  obtain ⟨yQ, hyQ⟩ := Q.exists_height_faceRight_eq hxQ σ
  have hsum : yc = yP + yQ := by
    have hfr := minkowskiHeight_faceRight hxP hxQ hbP hbQ hP hQ σ
    rw [hyP, hyQ, coe_add_coe] at hfr
    exact WithBotTop.coe_injective (hyc.symm.trans hfr)
  obtain ⟨i, hi, hval⟩ := exists_minkowskiHeight_eq (P := P) (Q := Q)
    (P.faceRight σ + Q.faceRight σ + 1)
  rw [hval, show ((P.faceRight σ + Q.faceRight σ + 1 : ℕ) : ℤ) - (i : ℤ)
    = ((P.faceRight σ + Q.faceRight σ + 1 - i : ℕ) : ℤ) from (Nat.cast_sub hi).symm]
  have hz : ((i : ℝ) - (P.faceRight σ : ℝ))
      + (((P.faceRight σ + Q.faceRight σ + 1 - i : ℕ) : ℝ) - (Q.faceRight σ : ℝ)) = 1 := by
    have hc : ((P.faceRight σ + Q.faceRight σ + 1 - i : ℕ) : ℝ)
        = (P.faceRight σ : ℝ) + (Q.faceRight σ : ℝ) + 1 - (i : ℝ) := by
      have : ((P.faceRight σ + Q.faceRight σ + 1 - i : ℕ) : ℝ)
          = ((P.faceRight σ + Q.faceRight σ + 1 : ℕ) : ℝ) - (i : ℝ) := Nat.cast_sub hi
      push_cast at this ⊢
      linarith
    rw [hc]
    ring
  rcases lt_or_ge (P.faceRight σ) i with hlt | hge
  · refine lt_of_le_of_lt (le_of_eq ?_)
      (coe_add_lt_add_left (P.height_natCast_ne_bot hxP i)
        (Q.height_natCast_ne_bot hxQ _)
        (P.faceRight_line_lt_height hxP hbP hP hyP hlt)
        (Q.faceRight_line_le_height hxQ hbQ hQ hyQ _))
    rw [hsum]
    congr 1
    linear_combination (-σ) * hz
  · refine lt_of_le_of_lt (le_of_eq ?_)
      (coe_add_lt_add_right (P.height_natCast_ne_bot hxP i)
        (Q.height_natCast_ne_bot hxQ _)
        (P.faceRight_line_le_height hxP hbP hP hyP i)
        (Q.faceRight_line_lt_height hxQ hbQ hQ hyQ (show Q.faceRight σ <
          P.faceRight σ + Q.faceRight σ + 1 - i by omega)))
    rw [hsum]
    congr 1
    linear_combination (-σ) * hz

/-- **Strict growth before the face** (mirror of `lt_minkowskiHeight_faceRight_succ`).  One step
before the left endpoint of the face of slope `σ`, the Minkowski sum is strictly higher than the
line of slope `σ` predicts. -/
theorem lt_minkowskiHeight_faceLeft_pred (hxP : P.starting_point.1 = 0)
    (hxQ : Q.starting_point.1 = 0) (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) (hQ : Q.SlopesUnbounded) (σ : ℝ) {y₁ : ℝ}
    (hm : 0 < P.faceLeft σ + Q.faceLeft σ)
    (hy₁ : P.minkowskiHeight Q (P.faceLeft σ + Q.faceLeft σ) = (y₁ : WithBotTop ℝ)) :
    ((y₁ - σ : ℝ) : WithBotTop ℝ)
      < P.minkowskiHeight Q (P.faceLeft σ + Q.faceLeft σ - 1) := by
  obtain ⟨yP, hyP⟩ := P.exists_height_faceLeft_eq hxP σ
  obtain ⟨yQ, hyQ⟩ := Q.exists_height_faceLeft_eq hxQ σ
  have hsum : y₁ = yP + yQ := by
    have hfl := minkowskiHeight_faceLeft hxP hxQ hbP hbQ hP hQ σ
    rw [hyP, hyQ, coe_add_coe] at hfl
    exact WithBotTop.coe_injective (hy₁.symm.trans hfl)
  obtain ⟨i, hi, hval⟩ := exists_minkowskiHeight_eq (P := P) (Q := Q)
    (P.faceLeft σ + Q.faceLeft σ - 1)
  rw [hval, show ((P.faceLeft σ + Q.faceLeft σ - 1 : ℕ) : ℤ) - (i : ℤ)
    = ((P.faceLeft σ + Q.faceLeft σ - 1 - i : ℕ) : ℤ) from (Nat.cast_sub hi).symm]
  have hz : ((i : ℝ) - (P.faceLeft σ : ℝ))
      + (((P.faceLeft σ + Q.faceLeft σ - 1 - i : ℕ) : ℝ) - (Q.faceLeft σ : ℝ)) = -1 := by
    have hc : ((P.faceLeft σ + Q.faceLeft σ - 1 - i : ℕ) : ℝ)
        = (P.faceLeft σ : ℝ) + (Q.faceLeft σ : ℝ) - 1 - (i : ℝ) := by
      have h1 : ((P.faceLeft σ + Q.faceLeft σ - 1 - i : ℕ) : ℝ)
          = ((P.faceLeft σ + Q.faceLeft σ - 1 : ℕ) : ℝ) - (i : ℝ) := Nat.cast_sub hi
      have h2 : ((P.faceLeft σ + Q.faceLeft σ - 1 : ℕ) : ℝ)
          = (P.faceLeft σ : ℝ) + (Q.faceLeft σ : ℝ) - 1 := by
        have := Nat.cast_sub (R := ℝ) (show 1 ≤ P.faceLeft σ + Q.faceLeft σ by omega)
        push_cast at this ⊢
        linarith
      rw [h1, h2]
    rw [hc]
    ring
  rcases lt_or_ge i (P.faceLeft σ) with hlt | hge
  · refine lt_of_le_of_lt (le_of_eq ?_)
      (coe_add_lt_add_left (P.height_natCast_ne_bot hxP i) (Q.height_natCast_ne_bot hxQ _)
        (P.faceLeft_line_lt_height hxP hbP hyP hlt)
        (Q.faceLeft_line_le_height hxQ hbQ hQ hyQ _))
    rw [hsum]
    congr 1
    linear_combination (-σ) * hz
  · refine lt_of_le_of_lt (le_of_eq ?_)
      (coe_add_lt_add_right (P.height_natCast_ne_bot hxP i) (Q.height_natCast_ne_bot hxQ _)
        (P.faceLeft_line_le_height hxP hbP hP hyP i)
        (Q.faceLeft_line_lt_height hxQ hbQ hyQ (show P.faceLeft σ + Q.faceLeft σ - 1 - i
          < Q.faceLeft σ by omega)))
    rw [hsum]
    congr 1
    linear_combination (-σ) * hz

end NewtonPolygon₀

/-! ### The ultrametric bound on the coefficients of a product

[Ked07, Proposition 1, (1)]: `v_r(PQ) ≥ min_{i+j} {v(P_i) + v(Q_j) + r(i + j)}`, and equality
when the minimising pair is unique. -/

variable {K : Type*} [NontriviallyNormedField K]

/-- The ultrametric bound for a finite sum, in additive form: the valuation of a sum is at least
the least valuation of a term. -/
theorem inf_negLogNorm_le_negLogNorm_sum [IsUltrametricDist K] {ι : Type*} (s : Finset ι)
    (l : ι → K) : (s.inf fun i => negLogNorm (l i)) ≤ negLogNorm (∑ i ∈ s, l i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.sum_insert ha]
    exact le_trans (inf_le_inf_left _ ih) le_negLogNorm_add

/-- The ultrametric equality for a finite sum with a strictly dominant term ([Kob84, §IV.3
p. 98]: "the isosceles triangle principle"). -/
theorem negLogNorm_sum_eq_of_forall_lt [IsUltrametricDist K] {ι : Type*} {s : Finset ι}
    {l : ι → K} {k : ι} (hk : k ∈ s) (h : ∀ j ∈ s, j ≠ k → negLogNorm (l k) < negLogNorm (l j)) :
    negLogNorm (∑ i ∈ s, l i) = negLogNorm (l k) := by
  have hnorm : ‖∑ i ∈ s, l i‖ = ‖l k‖ :=
    IsNonarchimedean.apply_sum_eq_of_lt IsUltrametricDist.isNonarchimedean_norm
      (fun a => (norm_neg a).symm) hk fun j hj hjk => negLogNorm_lt_negLogNorm.1 (h j hj hjk)
  simp only [negLogNorm, hnorm]

/-- The coefficient valuation of a product is at least the least `coeffVal f i + coeffVal g j`
over the splits `i + j = n` ([Ked07, (1)]). -/
theorem inf_coeffVal_add_le_coeffVal_mul [IsUltrametricDist K] (f g : PowerSeries K) (n : ℕ) :
    ((range (n + 1)).inf fun i => coeffVal f i + coeffVal g (n - i)) ≤ coeffVal (f * g) n := by
  rw [coeffVal_apply, PowerSeries.coeff_mul]
  refine le_trans (Finset.le_inf fun p hp => ?_)
    (inf_negLogNorm_le_negLogNorm_sum (antidiagonal n)
      fun p => PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g)
  rw [Finset.mem_antidiagonal] at hp
  refine le_trans (Finset.inf_le (mem_range.2 (show p.1 < n + 1 by omega))) (le_of_eq ?_)
  rw [negLogNorm_mul, show n - p.1 = p.2 by omega]
  rfl

/-- When one split is strictly better than all others, the coefficient valuation of the product
is exactly its value ([Ked07, proof of Prop. 1]: "(1) achieves its minimum for ... `i = i₀`,
`j = j₀` but not for any other"). -/
theorem coeffVal_mul_eq_of_forall_lt [IsUltrametricDist K] (f g : PowerSeries K) {n i₀ : ℕ}
    (hi₀ : i₀ ≤ n)
    (h : ∀ i, i ≤ n → i ≠ i₀ →
      coeffVal f i₀ + coeffVal g (n - i₀) < coeffVal f i + coeffVal g (n - i)) :
    coeffVal (f * g) n = coeffVal f i₀ + coeffVal g (n - i₀) := by
  rw [coeffVal_apply, PowerSeries.coeff_mul]
  have hk : (i₀, n - i₀) ∈ antidiagonal n := Finset.mem_antidiagonal.2 (by omega)
  refine (negLogNorm_sum_eq_of_forall_lt hk ?_).trans ?_
  · intro p hp hpk
    rw [Finset.mem_antidiagonal] at hp
    have hp1 : p.1 ≠ i₀ := fun hc => hpk (Prod.ext hc (by omega))
    have hlt := h p.1 (by omega) hp1
    rw [show n - p.1 = p.2 by omega] at hlt
    rw [negLogNorm_mul, negLogNorm_mul]
    exact hlt
  · rw [negLogNorm_mul]
    rfl

/-- Over `Γ = ℝ` the point height is the coercion of the value. -/
theorem pointHeight_eq_coe (v : ℕ → WithTop ℝ) (k : ℕ) :
    pointHeight v k = ((v k : WithTop ℝ) : WithBotTop ℝ) := by
  cases hv : v k <;> simp only [pointHeight, hv] <;> rfl

namespace IsNewtonPolygonOf

variable {f g : PowerSeries K} {Pf Pg Pfg : NewtonPolygon₀ (Γ := ℝ)}

/-- A polygon of `coeffVal f` anchored at the origin has `f` with nonzero constant coefficient. -/
theorem coeff_zero_ne_zero (hf : IsNewtonPolygonOf (coeffVal f) Pf) (hx : Pf.starting_point.1 = 0) :
    PowerSeries.coeff 0 f ≠ 0 := by
  obtain ⟨k, hk, hv⟩ := hf.start_mem
  rw [hx] at hk
  obtain rfl : k = 0 := by exact_mod_cast hk
  exact fun hc => WithTop.coe_ne_top (hv.symm.trans (coeffVal_eq_top_iff.2 hc))

/-- The polygon of a product of two series with nonzero constant coefficients is anchored at
the origin. -/
theorem starting_point_fst_mul (hf : IsNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsNewtonPolygonOf (coeffVal g) Pg) (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg)
    (hxf : Pf.starting_point.1 = 0) (hxg : Pg.starting_point.1 = 0) :
    Pfg.starting_point.1 = 0 := by
  have h0 : PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
  refine hfg.starting_point_fst_eq_zero fun hc => ?_
  rw [coeffVal_eq_top_iff, h0] at hc
  exact mul_ne_zero (hf.coeff_zero_ne_zero hxf) (hg.coeff_zero_ne_zero hxg) hc

/-- **The points of a product lie on/above the Minkowski sum** ([Ked07, (1)] through
`height_le`). -/
theorem minkowskiHeight_le_pointHeight_mul [IsUltrametricDist K]
    (hf : IsNewtonPolygonOf (coeffVal f) Pf) (hg : IsNewtonPolygonOf (coeffVal g) Pg) (n : ℕ) :
    Pf.minkowskiHeight Pg n ≤ pointHeight (coeffVal (f * g)) n := by
  obtain ⟨i, hi, hival⟩ := Finset.exists_mem_eq_inf (range (n + 1)) ⟨0, by simp⟩
    (fun i => coeffVal f i + coeffVal g (n - i))
  have hin : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  have hle := inf_coeffVal_add_le_coeffVal_mul f g n
  rw [hival] at hle
  refine le_trans (NewtonPolygon₀.minkowskiHeight_le hin) ?_
  rw [pointHeight_eq_coe, show ((n : ℤ) - (i : ℤ)) = ((n - i : ℕ) : ℤ) from (Nat.cast_sub hin).symm]
  calc Pf.height ((i : ℕ) : ℤ) + Pg.height ((n - i : ℕ) : ℤ)
      ≤ pointHeight (coeffVal f) i + pointHeight (coeffVal g) (n - i) :=
        add_le_add (hf.height_le i) (hg.height_le (n - i))
    _ = ((coeffVal f i + coeffVal g (n - i) : WithTop ℝ) : WithBotTop ℝ) := by
        rw [pointHeight_eq_coe, pointHeight_eq_coe]
        rfl
    _ ≤ ((coeffVal (f * g) n : WithTop ℝ) : WithBotTop ℝ) := WithBot.coe_le_coe.2 hle

/-- **The Newton polygon of a product lies on/above the Minkowski sum.**  At a finite Minkowski
height, the supporting line through a minimising split (`exists_subgradient`,
`subgradient_line_le_minkowskiHeight`) lies below every point of `fg`, hence below its polygon
(`line_le_height`); at an infinite one, `fg` has no later coefficients and its polygon is `⊤`
(`height_eq_top_of_forall_eq_top`). -/
theorem minkowskiHeight_le_height_mul [IsUltrametricDist K]
    (hf : IsNewtonPolygonOf (coeffVal f) Pf) (hg : IsNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hxf : Pf.starting_point.1 = 0)
    (hxg : Pg.starting_point.1 = 0) (hbf : ∀ j, Pf.unitSlope j ≠ ⊥) (hbg : ∀ j, Pg.unitSlope j ≠ ⊥)
    (n : ℕ) : Pf.minkowskiHeight Pg n ≤ Pfg.height n := by
  have hxfg : Pfg.starting_point.1 = 0 := hf.starting_point_fst_mul hg hfg hxf hxg
  by_cases htop : Pf.minkowskiHeight Pg n = ⊤
  · -- past a `⊤` Minkowski height `f * g` has no coefficients left, so its polygon has ended
    refine le_of_eq (Eq.trans htop (hfg.height_eq_top_of_forall_eq_top hxfg fun k hk => ?_).symm)
    have h2 := minkowskiHeight_le_pointHeight_mul hf hg k
    rw [NewtonPolygon₀.minkowskiHeight_eq_top_mono hxf hxg htop hk] at h2
    exact pointHeight_eq_top_iff.1 (top_le_iff.1 h2)
  -- finite case: a supporting line of the Minkowski sum lies below every point of `f * g`
  obtain ⟨y, hy⟩ :=
    NewtonPolygon₀.exists_coe_of_ne (NewtonPolygon₀.minkowskiHeight_ne_bot hxf hxg n) htop
  obtain ⟨i₀, hi₀, hival⟩ := NewtonPolygon₀.exists_minkowskiHeight_eq (P := Pf) (Q := Pg) n
  rw [hy] at hival
  obtain ⟨σ, hP₁, hP₂, hQ₁, hQ₂⟩ :=
    NewtonPolygon₀.exists_subgradient hxf hxg hbf hbg hi₀ hy hival.symm
  have hcast : ((n : ℤ) - (i₀ : ℤ)) = ((n - i₀ : ℕ) : ℤ) := (Nat.cast_sub hi₀).symm
  rw [hcast] at hival
  have hsum : i₀ + (n - i₀) = n := by omega
  have hline : ∀ k : ℕ,
      (((y - σ * n) + σ * k : ℝ) : WithBotTop ℝ) ≤ pointHeight (coeffVal (f * g)) k := by
    intro k
    refine le_trans (le_of_eq ?_)
      (le_trans (NewtonPolygon₀.subgradient_line_le_minkowskiHeight hxf hxg hbf hbg hP₁ hP₂ hQ₁ hQ₂
        hival.symm k) (minkowskiHeight_le_pointHeight_mul hf hg k))
    congr 1
    rw [hsum]
    ring
  have hfin := hfg.line_le_height hxfg hline n
  rw [hy]
  refine le_trans (le_of_eq ?_) hfin
  congr 1
  ring

end IsNewtonPolygonOf

namespace IsEntireNewtonPolygonOf

variable {f g : PowerSeries K} {Pf Pg Pfg : NewtonPolygon₀ (Γ := ℝ)}

/-- **Exactness at the left endpoints** ([Ked07, proof of Prop. 1]): at
`faceLeft_f σ + faceLeft_g σ` the point of `fg` is the sum of the two left-endpoint points. -/
theorem pointHeight_mul_faceLeft [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (σ : ℝ) :
    pointHeight (coeffVal (f * g)) (Pf.faceLeft σ + Pg.faceLeft σ) =
      Pf.height (Pf.faceLeft σ) + Pg.height (Pg.faceLeft σ) := by
  have hPpt := hf.toIsNewtonPolygonOf.height_faceLeft_eq_pointHeight hf.starting_point_fst
    hf.unitSlope_ne_bot hf.slopesUnbounded σ
  have hQpt := hg.toIsNewtonPolygonOf.height_faceLeft_eq_pointHeight hg.starting_point_fst
    hg.unitSlope_ne_bot hg.slopesUnbounded σ
  rw [pointHeight_eq_coe] at hPpt hQpt
  have hidx : Pf.faceLeft σ + Pg.faceLeft σ - Pf.faceLeft σ = Pg.faceLeft σ := by omega
  have hstrict : ∀ i, i ≤ Pf.faceLeft σ + Pg.faceLeft σ → i ≠ Pf.faceLeft σ →
      coeffVal f (Pf.faceLeft σ) + coeffVal g (Pf.faceLeft σ + Pg.faceLeft σ - Pf.faceLeft σ) <
        coeffVal f i + coeffVal g (Pf.faceLeft σ + Pg.faceLeft σ - i) := by
    intro i hi hne
    rw [hidx]
    have hlt := NewtonPolygon₀.height_faceLeft_add_lt hf.starting_point_fst hg.starting_point_fst
      hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded hg.slopesUnbounded
      (i := i) (j := Pf.faceLeft σ + Pg.faceLeft σ - i) (by omega) hne
    rw [hPpt, hQpt, NewtonPolygon₀.coe_add_coe'] at hlt
    refine WithBot.coe_lt_coe.1 (lt_of_lt_of_le hlt ?_)
    rw [← NewtonPolygon₀.coe_add_coe', ← pointHeight_eq_coe, ← pointHeight_eq_coe]
    exact add_le_add (hf.height_le i) (hg.height_le _)
  rw [pointHeight_eq_coe, coeffVal_mul_eq_of_forall_lt f g (by omega) hstrict, hidx,
    hPpt, hQpt, NewtonPolygon₀.coe_add_coe']

/-- **Exactness at the right endpoints**: at `faceRight_f σ + faceRight_g σ` the point of `fg` is
the sum of the two right-endpoint points. -/
theorem pointHeight_mul_faceRight [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (σ : ℝ) :
    pointHeight (coeffVal (f * g)) (Pf.faceRight σ + Pg.faceRight σ) =
      Pf.height (Pf.faceRight σ) + Pg.height (Pg.faceRight σ) := by
  have hPpt := hf.toIsNewtonPolygonOf.height_faceRight_eq_pointHeight hf.starting_point_fst
    hf.unitSlope_ne_bot hf.slopesUnbounded σ
  have hQpt := hg.toIsNewtonPolygonOf.height_faceRight_eq_pointHeight hg.starting_point_fst
    hg.unitSlope_ne_bot hg.slopesUnbounded σ
  rw [pointHeight_eq_coe] at hPpt hQpt
  have hidx : Pf.faceRight σ + Pg.faceRight σ - Pf.faceRight σ = Pg.faceRight σ := by omega
  have hstrict : ∀ i, i ≤ Pf.faceRight σ + Pg.faceRight σ → i ≠ Pf.faceRight σ →
      coeffVal f (Pf.faceRight σ) + coeffVal g (Pf.faceRight σ + Pg.faceRight σ - Pf.faceRight σ) <
        coeffVal f i + coeffVal g (Pf.faceRight σ + Pg.faceRight σ - i) := by
    intro i hi hne
    rw [hidx]
    have hlt := NewtonPolygon₀.height_faceRight_add_lt hf.starting_point_fst hg.starting_point_fst
      hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded hg.slopesUnbounded
      (i := i) (j := Pf.faceRight σ + Pg.faceRight σ - i) (by omega) hne
    rw [hPpt, hQpt, NewtonPolygon₀.coe_add_coe'] at hlt
    refine WithBot.coe_lt_coe.1 (lt_of_lt_of_le hlt ?_)
    rw [← NewtonPolygon₀.coe_add_coe', ← pointHeight_eq_coe, ← pointHeight_eq_coe]
    exact add_le_add (hf.height_le i) (hg.height_le _)
  rw [pointHeight_eq_coe, coeffVal_mul_eq_of_forall_lt f g (by omega) hstrict, hidx,
    hPpt, hQpt, NewtonPolygon₀.coe_add_coe']

/-- **The Newton polygon of a product lies on/below the Minkowski sum.**  Every `n` with finite
Minkowski height lies on a face of the Minkowski sum (`exists_subgradient`), whose endpoints are
points of `fg` (`pointHeight_mul_faceLeft`, `pointHeight_mul_faceRight`); the chord inequality
`height_le_chord` between them is the Minkowski height (`minkowskiHeight_eq_of_mem_face`). -/
theorem height_mul_le_minkowskiHeight [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (n : ℕ) :
    Pfg.height n ≤ Pf.minkowskiHeight Pg n := by
  by_cases htop : Pf.minkowskiHeight Pg n = ⊤
  · rw [htop]; exact le_top
  have hxfg : Pfg.starting_point.1 = 0 := hf.toIsNewtonPolygonOf.starting_point_fst_mul
    hg.toIsNewtonPolygonOf hfg hf.starting_point_fst hg.starting_point_fst
  obtain ⟨y, hy⟩ := NewtonPolygon₀.exists_coe_of_ne
    (NewtonPolygon₀.minkowskiHeight_ne_bot hf.starting_point_fst hg.starting_point_fst n) htop
  obtain ⟨i₀, hi₀, hival⟩ := NewtonPolygon₀.exists_minkowskiHeight_eq (P := Pf) (Q := Pg) n
  rw [hy] at hival
  obtain ⟨σ, hP₁, hP₂, hQ₁, hQ₂⟩ := NewtonPolygon₀.exists_subgradient
    hf.starting_point_fst hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot
    hi₀ hy hival.symm
  -- `n` lies on the face of slope `σ` of the Minkowski sum
  have hL : Pf.faceLeft σ + Pg.faceLeft σ ≤ n := by
    have h1 : Pf.faceLeft σ ≤ i₀ := Pf.faceLeft_le_of_le_unitSlope (hP₂ i₀ le_rfl)
    have h2 : Pg.faceLeft σ ≤ n - i₀ := Pg.faceLeft_le_of_le_unitSlope (hQ₂ (n - i₀) le_rfl)
    omega
  have hR : n ≤ Pf.faceRight σ + Pg.faceRight σ := by
    have h1 : i₀ ≤ Pf.faceRight σ := Pf.le_faceRight_of_forall_le hf.slopesUnbounded hP₁
    have h2 : n - i₀ ≤ Pg.faceRight σ := Pg.le_faceRight_of_forall_le hg.slopesUnbounded hQ₁
    omega
  have hPle := Pf.faceLeft_le_faceRight hf.slopesUnbounded σ
  have hQle := Pg.faceLeft_le_faceRight hg.slopesUnbounded σ
  -- the sum is the line of slope `σ` on that face, its endpoints being points of `f * g`
  obtain ⟨yP, hyP⟩ := Pf.exists_height_faceLeft_eq hf.starting_point_fst σ
  obtain ⟨yQ, hyQ⟩ := Pg.exists_height_faceLeft_eq hg.starting_point_fst σ
  have hM1 : Pf.minkowskiHeight Pg (Pf.faceLeft σ + Pg.faceLeft σ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by
    rw [NewtonPolygon₀.minkowskiHeight_faceLeft hf.starting_point_fst hg.starting_point_fst
      hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded hg.slopesUnbounded σ,
      hyP, hyQ, NewtonPolygon₀.coe_add_coe]
  have hMval : ∀ m : ℕ, Pf.faceLeft σ + Pg.faceLeft σ ≤ m → m ≤ Pf.faceRight σ + Pg.faceRight σ →
      Pf.minkowskiHeight Pg m = ((yP + yQ +
        σ * ((m : ℝ) - ((Pf.faceLeft σ + Pg.faceLeft σ : ℕ) : ℝ)) : ℝ) : WithBotTop ℝ) :=
    fun m h1 h2 => NewtonPolygon₀.minkowskiHeight_eq_of_mem_face hf.starting_point_fst
      hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded
      hg.slopesUnbounded hM1 h1 h2
  have ha : Pfg.height ((Pf.faceLeft σ + Pg.faceLeft σ : ℕ) : ℤ)
      ≤ ((yP + yQ : ℝ) : WithBotTop ℝ) := by
    refine le_trans (hfg.height_le _) (le_of_eq ?_)
    rw [pointHeight_mul_faceLeft hf hg σ, hyP, hyQ, NewtonPolygon₀.coe_add_coe]
  have hc : Pfg.height ((Pf.faceRight σ + Pg.faceRight σ : ℕ) : ℤ) ≤ ((yP + yQ +
      σ * (((Pf.faceRight σ + Pg.faceRight σ : ℕ) : ℝ)
        - ((Pf.faceLeft σ + Pg.faceLeft σ : ℕ) : ℝ)) : ℝ) : WithBotTop ℝ) := by
    refine le_trans (hfg.height_le _) (le_of_eq ?_)
    rw [pointHeight_mul_faceRight hf hg σ,
      ← NewtonPolygon₀.minkowskiHeight_faceRight hf.starting_point_fst hg.starting_point_fst
        hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded hg.slopesUnbounded σ,
      hMval _ (by omega) le_rfl]
  -- the chord between the two endpoints is the line, and the polygon of `f * g` is below it
  have hchord := Pfg.height_le_chord (x := ((Pf.faceLeft σ + Pg.faceLeft σ : ℕ) : ℤ))
    (y := (n : ℤ)) (z := ((Pf.faceRight σ + Pg.faceRight σ : ℕ) : ℤ))
    (by rw [hxfg]; positivity) (by exact_mod_cast hL) (by exact_mod_cast hR) ha hc
  refine le_trans hchord (le_of_eq ?_)
  rw [hMval n hL hR]
  congr 1
  rcases eq_or_lt_of_le (show Pf.faceLeft σ + Pg.faceLeft σ ≤ Pf.faceRight σ + Pg.faceRight σ
    by omega) with heq | hlt
  · -- the face is a single point, so `n` is that point
    have hn : n = Pf.faceLeft σ + Pg.faceLeft σ := by omega
    rw [← heq, hn]
    norm_num
  · have hpos : (0 : ℝ) < ((Pf.faceRight σ + Pg.faceRight σ : ℕ) : ℝ)
        - ((Pf.faceLeft σ + Pg.faceLeft σ : ℕ) : ℝ) := by
      have : ((Pf.faceLeft σ + Pg.faceLeft σ : ℕ) : ℝ)
          < ((Pf.faceRight σ + Pg.faceRight σ : ℕ) : ℝ) := by exact_mod_cast hlt
      linarith
    push_cast
    push_cast at hpos
    field_simp
    ring

/-- **The Newton polygon of a product is the Minkowski sum of the Newton polygons of the
factors** ([Ked07, §2 and Cor. 2]: "the slope multiset of `PQ` is the union of the slope
multisets of `P` and `Q`"; [Kob84, §IV.4 Lemma 6] for a linear factor). -/
theorem height_mul [IsUltrametricDist K] (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (n : ℕ) :
    Pfg.height n = Pf.minkowskiHeight Pg n :=
  le_antisymm (hf.height_mul_le_minkowskiHeight hg hfg n)
    (hf.toIsNewtonPolygonOf.minkowskiHeight_le_height_mul hg.toIsNewtonPolygonOf hfg
      hf.starting_point_fst hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot n)

/-! ### Corollaries -/

/-- **The initial segment** ([LWX, §3.23 Step I]): if the first `n` slopes of `g` are at most
every slope of `f`, then up to `n` the polygon of `fg` is the polygon of `g` lifted by the
height of `f` at `0`. -/
theorem height_mul_of_forall_le [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) {n : ℕ}
    (hle : ∀ i, i < n → ∀ j, Pg.unitSlope i ≤ Pf.unitSlope j) :
    Pfg.height n = Pf.height 0 + Pg.height n := by
  rw [hf.height_mul hg hfg n]
  refine le_antisymm ?_ (NewtonPolygon₀.le_minkowskiHeight_iff.2 fun i hi => ?_)
  · refine le_trans (NewtonPolygon₀.minkowskiHeight_le (Nat.zero_le n)) (le_of_eq ?_)
    norm_num
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · norm_num
  -- an honest split moves `i` units of slope from `g`'s tail onto `f`'s head, which is at least
  -- as steep, so the split at `0` is the minimising one
  have hcast : ((n : ℤ) - (i : ℤ)) = ((n - i : ℕ) : ℤ) := (Nat.cast_sub hi).symm
  rw [hcast]
  by_cases hPtop : Pf.height ((i : ℕ) : ℤ) = ⊤
  · rw [hPtop, (NewtonPolygon₀.add_eq_top_iff (by simp)
      (Pg.height_natCast_ne_bot hg.starting_point_fst (n - i))).2 (Or.inl rfl)]
    exact le_top
  by_cases hQtop : Pg.height ((n - i : ℕ) : ℤ) = ⊤
  · rw [hQtop, (NewtonPolygon₀.add_eq_top_iff
      (Pf.height_natCast_ne_bot hf.starting_point_fst i) (by simp)).2 (Or.inr rfl)]
    exact le_top
  by_cases hgn : Pg.height ((n : ℕ) : ℤ) = ⊤
  · -- `g` already has a `⊤` slope below `n`, so by hypothesis every slope of `f` is `⊤` too
    exfalso
    obtain ⟨-, hn1, htop⟩ := Pg.unitSlope_eq_top_of_height_eq_top hgn
    rw [hg.starting_point_fst, sub_zero, Int.toNat_natCast] at hn1 htop
    have hPall : Pf.unitSlope 0 = ⊤ := top_le_iff.1 (htop ▸ hle (n - 1) (by omega) 0)
    have hP1 : Pf.height ((1 : ℕ) : ℤ) = ⊤ := by
      by_contra hcon
      exact Pf.unitSlope_ne_top_of_height_natCast hf.starting_point_fst hcon (by omega) hPall
    exact hPtop (Pf.height_eq_top_mono hP1 (by omega))
  -- all four heights are real: compare the two increments term by term
  obtain ⟨a, ha⟩ := NewtonPolygon₀.exists_coe_of_ne
    (Pf.height_natCast_ne_bot hf.starting_point_fst i) hPtop
  obtain ⟨b, hb⟩ := NewtonPolygon₀.exists_coe_of_ne
    (Pg.height_natCast_ne_bot hg.starting_point_fst (n - i)) hQtop
  obtain ⟨c, hc⟩ := NewtonPolygon₀.exists_coe_of_ne
    (Pg.height_natCast_ne_bot hg.starting_point_fst n) hgn
  obtain ⟨d, hd⟩ := NewtonPolygon₀.exists_coe_of_ne
    (Pf.height_ne_bot_of_nonneg hf.starting_point_fst (le_refl (0 : ℤ)))
    (Pf.height_natCast_zero_ne_top hf.starting_point_fst)
  rw [ha, hb, hc, hd, NewtonPolygon₀.coe_add_coe, NewtonPolygon₀.coe_add_coe,
    WithBotTop.coe_le_coe]
  -- `f`'s increment over `[0, i)` dominates `g`'s over `[n - i, n)` termwise
  have hfsum : a - d = ∑ t ∈ range i, NewtonPolygon.toReal (Pf.unitSlope t) := by
    have hs := Pf.heightFun_sub_eq_sum (Nat.zero_le i)
    rw [← Finset.range_eq_Ico] at hs
    have e1 : Pf.heightFun i = a := WithBotTop.coe_injective
      ((Pf.height_natCast_eq_heightFun hf.starting_point_fst hPtop).symm.trans ha)
    have e2 : Pf.heightFun 0 = d := WithBotTop.coe_injective
      ((Pf.height_natCast_eq_heightFun hf.starting_point_fst
        (by simpa using Pf.height_natCast_zero_ne_top hf.starting_point_fst)).symm.trans
        (by simpa using hd))
    rw [e1, e2] at hs
    linarith
  have hgsum : c - b = ∑ t ∈ range i, NewtonPolygon.toReal (Pg.unitSlope (n - i + t)) := by
    have hs := Pg.heightFun_sub_eq_sum (show n - i ≤ n by omega)
    rw [Finset.sum_Ico_eq_sum_range, show n - (n - i) = i by omega] at hs
    have e1 : Pg.heightFun n = c := WithBotTop.coe_injective
      ((Pg.height_natCast_eq_heightFun hg.starting_point_fst hgn).symm.trans hc)
    have e2 : Pg.heightFun (n - i) = b := WithBotTop.coe_injective
      ((Pg.height_natCast_eq_heightFun hg.starting_point_fst hQtop).symm.trans hb)
    rw [e1, e2] at hs
    linarith
  have hterm : ∀ t ∈ range i, NewtonPolygon.toReal (Pg.unitSlope (n - i + t))
      ≤ NewtonPolygon.toReal (Pf.unitSlope t) := by
    intro t ht
    rw [mem_range] at ht
    exact NewtonPolygon.toReal_le_toReal (hg.unitSlope_ne_bot _)
      (Pg.unitSlope_ne_top_of_height_natCast hg.starting_point_fst hgn (by omega))
      (hf.unitSlope_ne_bot _)
      (Pf.unitSlope_ne_top_of_height_natCast hf.starting_point_fst hPtop ht)
      (hle (n - i + t) (by omega) t)
  have := Finset.sum_le_sum hterm
  linarith

/-- **The initial segment, slope form**: under the hypotheses of `height_mul_of_forall_le` the
first `n` unit slopes of `fg` are those of `g`. -/
theorem unitSlope_mul_of_forall_le [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) {n : ℕ}
    (hle : ∀ i, i < n → ∀ j, Pg.unitSlope i ≤ Pf.unitSlope j) {j : ℕ}
    (hj : j < n) : Pfg.unitSlope j = Pg.unitSlope j := by
  have hxfg : Pfg.starting_point.1 = 0 := hf.toIsNewtonPolygonOf.starting_point_fst_mul
    hg.toIsNewtonPolygonOf hfg hf.starting_point_fst hg.starting_point_fst
  have h0 := hf.height_mul_of_forall_le hg hfg (n := j) fun i hi t => hle i (by omega) t
  have h1 := hf.height_mul_of_forall_le hg hfg (n := j + 1) fun i hi t => hle i (by omega) t
  obtain ⟨d, hd⟩ := NewtonPolygon₀.exists_coe_of_ne
    (Pf.height_ne_bot_of_nonneg hf.starting_point_fst (le_refl (0 : ℤ)))
    (Pf.height_natCast_zero_ne_top hf.starting_point_fst)
  by_cases hgt : Pg.height ((j + 1 : ℕ) : ℤ) = ⊤
  · -- past a `⊤` slope of `g` both polygons carry the junk slope
    have hfgt : Pfg.height ((j + 1 : ℕ) : ℤ) = ⊤ := by
      rw [h1, hgt, hd]
      exact (NewtonPolygon₀.add_eq_top_iff (by simp) (by simp)).2 (Or.inr rfl)
    obtain ⟨-, -, htP⟩ := Pfg.unitSlope_eq_top_of_height_eq_top hfgt
    obtain ⟨-, -, htQ⟩ := Pg.unitSlope_eq_top_of_height_eq_top hgt
    rw [hxfg, sub_zero, Int.toNat_natCast, Nat.add_sub_cancel] at htP
    rw [hg.starting_point_fst, sub_zero, Int.toNat_natCast, Nat.add_sub_cancel] at htQ
    rw [htP, htQ]
  have hgj : Pg.height ((j : ℕ) : ℤ) ≠ ⊤ := fun hc => hgt (Pg.height_eq_top_mono hc (by omega))
  obtain ⟨b0, hb0⟩ := NewtonPolygon₀.exists_coe_of_ne
    (Pg.height_natCast_ne_bot hg.starting_point_fst j) hgj
  obtain ⟨b1, hb1⟩ := NewtonPolygon₀.exists_coe_of_ne
    (Pg.height_natCast_ne_bot hg.starting_point_fst (j + 1)) hgt
  rw [Pg.unitSlope_eq_of_height_eq hg.starting_point_fst (hg.unitSlope_ne_bot j) hb0 hb1,
    Pfg.unitSlope_eq_of_height_eq hxfg (hbfg j)
      (h0.trans (by rw [hd, hb0, NewtonPolygon₀.coe_add_coe]))
      (h1.trans (by rw [hd, hb1, NewtonPolygon₀.coe_add_coe]))]
  congr 1
  ring

/-- **The product's slope at the right endpoint of a face exceeds `σ`.**  The Minkowski sum
rises by strictly more than `σ` across that step (`lt_minkowskiHeight_faceRight_succ`), and by
the product formula the polygon of `f * g` is that sum. -/
private theorem lt_unitSlope_mul_faceRight [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) (σ : ℝ) :
    (σ : WithBotTop ℝ) < Pfg.unitSlope (Pf.faceRight σ + Pg.faceRight σ) := by
  have hxfg : Pfg.starting_point.1 = 0 := hf.toIsNewtonPolygonOf.starting_point_fst_mul
    hg.toIsNewtonPolygonOf hfg hf.starting_point_fst hg.starting_point_fst
  obtain ⟨yP, hyP⟩ := Pf.exists_height_faceRight_eq hf.starting_point_fst σ
  obtain ⟨yQ, hyQ⟩ := Pg.exists_height_faceRight_eq hg.starting_point_fst σ
  have hM2 : Pf.minkowskiHeight Pg (Pf.faceRight σ + Pg.faceRight σ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by
    rw [NewtonPolygon₀.minkowskiHeight_faceRight hf.starting_point_fst hg.starting_point_fst
      hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded hg.slopesUnbounded σ,
      hyP, hyQ, NewtonPolygon₀.coe_add_coe]
  have hgrow := NewtonPolygon₀.lt_minkowskiHeight_faceRight_succ hf.starting_point_fst
    hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded
    hg.slopesUnbounded σ hM2
  rw [← hf.height_mul hg hfg] at hM2 hgrow
  by_cases htop : Pfg.height ((Pf.faceRight σ + Pg.faceRight σ + 1 : ℕ) : ℤ) = ⊤
  · obtain ⟨-, -, ht⟩ := Pfg.unitSlope_eq_top_of_height_eq_top htop
    rw [hxfg, sub_zero, Int.toNat_natCast, Nat.add_sub_cancel] at ht
    rw [ht]
    exact lt_top_iff_ne_top.2 (WithBotTop.coe_ne_top σ)
  obtain ⟨e, he⟩ := NewtonPolygon₀.exists_coe_of_ne
    (Pfg.height_natCast_ne_bot hxfg (Pf.faceRight σ + Pg.faceRight σ + 1)) htop
  rw [Pfg.unitSlope_eq_of_height_eq hxfg (hbfg _) hM2 he, WithBotTop.coe_lt_coe]
  rw [he, WithBotTop.coe_lt_coe] at hgrow
  linarith

/-- The slopes of a product of two polygons with unbounded slopes are unbounded: past the
right endpoints of the face of slope `σ` the Minkowski height grows faster than `σ`. -/
theorem slopesUnbounded_mul [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) : Pfg.SlopesUnbounded := by
  have hxfg : Pfg.starting_point.1 = 0 := hf.toIsNewtonPolygonOf.starting_point_fst_mul
    hg.toIsNewtonPolygonOf hfg hf.starting_point_fst hg.starting_point_fst
  by_cases hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥
  · exact fun σ => ⟨_, lt_unitSlope_mul_faceRight hf hg hfg hbfg σ⟩
  push Not at hbfg
  obtain ⟨j0, hj0⟩ := hbfg
  obtain ⟨hs0, hsupp⟩ := Pfg.slopes_zero_eq_bot_of_unitSlope_eq_bot hj0
  intro σ
  by_cases htopex : ∃ j, Pfg.unitSlope j = ⊤
  · obtain ⟨j, hj⟩ := htopex
    exact ⟨j, by rw [hj]; exact lt_top_iff_ne_top.2 (WithBotTop.coe_ne_top σ)⟩
  push Not at htopex
  exfalso
  -- with a `⊥` slope and no `⊤` slope the polygon of `f * g` is constant …
  have hall : ∀ j, Pfg.unitSlope j = ⊥ := by
    intro j
    rcases Pfg.unitSlope_cases j with ⟨n, h1, h2⟩ | ht | hb
    · have heq := Pfg.unitSlope_eq_slopes h1 h2
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [heq, hs0]
      · exact absurd (heq.trans (Pfg.slopes_junk n (by rw [hsupp]; exact_mod_cast hn))) (htopex j)
    · exact absurd ht (htopex j)
    · exact hb
  have hfin : ∀ m : ℕ, Pfg.height (m : ℤ) = ((Pfg.heightFun m : ℝ) : WithBotTop ℝ) := fun m =>
    Pfg.height_natCast_eq_heightFun hxfg
      (Pfg.height_natCast_ne_top_of_unitSlope hxfg fun j _ => htopex j)
  have hconst : ∀ m : ℕ, Pfg.heightFun m = Pfg.heightFun 0 := by
    intro m
    have hs := Pfg.heightFun_sub_eq_sum (Nat.zero_le m)
    rw [Finset.sum_congr rfl fun t _ => by rw [hall t, NewtonPolygon.toReal_bot],
      Finset.sum_const_zero] at hs
    linarith
  -- … but one step past the face of slope `1` the Minkowski sum must rise by more than `1`
  obtain ⟨yP, hyP⟩ := Pf.exists_height_faceRight_eq hf.starting_point_fst 1
  obtain ⟨yQ, hyQ⟩ := Pg.exists_height_faceRight_eq hg.starting_point_fst 1
  have hM2 : Pf.minkowskiHeight Pg (Pf.faceRight 1 + Pg.faceRight 1)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by
    rw [NewtonPolygon₀.minkowskiHeight_faceRight hf.starting_point_fst hg.starting_point_fst
      hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded hg.slopesUnbounded 1,
      hyP, hyQ, NewtonPolygon₀.coe_add_coe]
  have hgrow := NewtonPolygon₀.lt_minkowskiHeight_faceRight_succ hf.starting_point_fst
    hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded
    hg.slopesUnbounded 1 hM2
  have h1 : (yP + yQ : ℝ) = Pfg.heightFun 0 := by
    rw [← hf.height_mul hg hfg, hfin, hconst] at hM2
    exact (WithBotTop.coe_injective hM2).symm
  rw [← hf.height_mul hg hfg, hfin, hconst, WithBotTop.coe_lt_coe, h1] at hgrow
  linarith

/-- The standing hypotheses are closed under products (given a `⊥`-free polygon of the
product). -/
theorem mul [IsUltrametricDist K] (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) :
    IsEntireNewtonPolygonOf (coeffVal (f * g)) Pfg :=
  ⟨hfg, hf.toIsNewtonPolygonOf.starting_point_fst_mul hg.toIsNewtonPolygonOf hfg
    hf.starting_point_fst hg.starting_point_fst, hbfg, slopesUnbounded_mul hf hg hfg⟩

/-- **Multiplicities of slopes add** ([Ked07, Cor. 2]: "the multiplicity of `r` as a slope of
`PQ` is the sum of the multiplicities of `r` as a slope of `P` and `Q`"), in counting form: the
number of unit slopes `≤ σ` of `fg` is the sum of those of `f` and of `g`. -/
theorem faceRight_mul [IsUltrametricDist K] (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) (σ : ℝ) :
    Pfg.faceRight σ = Pf.faceRight σ + Pg.faceRight σ := by
  have hxfg : Pfg.starting_point.1 = 0 := hf.toIsNewtonPolygonOf.starting_point_fst_mul
    hg.toIsNewtonPolygonOf hfg hf.starting_point_fst hg.starting_point_fst
  refine le_antisymm (Nat.sInf_le (lt_unitSlope_mul_faceRight hf hg hfg hbfg σ))
    (Pfg.le_faceRight_of_forall_le (slopesUnbounded_mul hf hg hfg) fun t ht => ?_)
  refine le_trans (Pfg.unitSlope_mono (show t ≤ Pf.faceRight σ + Pg.faceRight σ - 1 by omega)) ?_
  obtain ⟨yP, hyP⟩ := Pf.exists_height_faceRight_eq hf.starting_point_fst σ
  obtain ⟨yQ, hyQ⟩ := Pg.exists_height_faceRight_eq hg.starting_point_fst σ
  have hy : Pf.height (Pf.faceRight σ) + Pg.height (Pg.faceRight σ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by rw [hyP, hyQ, NewtonPolygon₀.coe_add_coe]
  have hM2 : Pfg.height ((Pf.faceRight σ + Pg.faceRight σ : ℕ) : ℤ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by
    rw [hf.height_mul hg hfg, NewtonPolygon₀.minkowskiHeight_faceRight hf.starting_point_fst
      hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded
      hg.slopesUnbounded σ, hyP, hyQ, NewtonPolygon₀.coe_add_coe]
  have hprev : ((yP + yQ - σ : ℝ) : WithBotTop ℝ)
      ≤ Pfg.height ((Pf.faceRight σ + Pg.faceRight σ - 1 : ℕ) : ℤ) := by
    have hline := NewtonPolygon₀.subgradient_line_le_minkowskiHeight hf.starting_point_fst
      hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot
      (fun _ hu => Pf.unitSlope_le_of_lt_faceRight hu)
      (fun _ hu => (Pf.lt_unitSlope_of_faceRight_le hf.slopesUnbounded hu).le)
      (fun _ hu => Pg.unitSlope_le_of_lt_faceRight hu)
      (fun _ hu => (Pg.lt_unitSlope_of_faceRight_le hg.slopesUnbounded hu).le) hy
      (Pf.faceRight σ + Pg.faceRight σ - 1)
    rw [← hf.height_mul hg hfg] at hline
    refine le_trans (le_of_eq ?_) hline
    congr 1
    have hc : ((Pf.faceRight σ + Pg.faceRight σ - 1 : ℕ) : ℝ)
        = ((Pf.faceRight σ + Pg.faceRight σ : ℕ) : ℝ) - 1 := by
      have := Nat.cast_sub (R := ℝ) (show 1 ≤ Pf.faceRight σ + Pg.faceRight σ by omega)
      push_cast at this ⊢
      linarith
    rw [hc]
    ring
  have hnet : Pfg.height ((Pf.faceRight σ + Pg.faceRight σ - 1 : ℕ) : ℤ) ≠ ⊤ := fun hc =>
    WithBotTop.coe_ne_top _ (hM2.symm.trans (Pfg.height_eq_top_mono hc (by omega)))
  obtain ⟨e, he⟩ := NewtonPolygon₀.exists_coe_of_ne (Pfg.height_natCast_ne_bot hxfg _) hnet
  rw [Pfg.unitSlope_eq_of_height_eq hxfg (hbfg _) he
    (by rw [show Pf.faceRight σ + Pg.faceRight σ - 1 + 1 = Pf.faceRight σ + Pg.faceRight σ
      by omega]; exact hM2), WithBotTop.coe_le_coe]
  rw [he, WithBotTop.coe_le_coe] at hprev
  linarith

/-- The number of unit slopes `< σ` of `fg` is the sum of those of `f` and of `g`. -/
theorem faceLeft_mul [IsUltrametricDist K] (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) (σ : ℝ) :
    Pfg.faceLeft σ = Pf.faceLeft σ + Pg.faceLeft σ := by
  have hxfg : Pfg.starting_point.1 = 0 := hf.toIsNewtonPolygonOf.starting_point_fst_mul
    hg.toIsNewtonPolygonOf hfg hf.starting_point_fst hg.starting_point_fst
  have hSU := slopesUnbounded_mul hf hg hfg
  obtain ⟨yP, hyP⟩ := Pf.exists_height_faceLeft_eq hf.starting_point_fst σ
  obtain ⟨yQ, hyQ⟩ := Pg.exists_height_faceLeft_eq hg.starting_point_fst σ
  have hy : Pf.height (Pf.faceLeft σ) + Pg.height (Pg.faceLeft σ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by rw [hyP, hyQ, NewtonPolygon₀.coe_add_coe]
  have hM1' : Pf.minkowskiHeight Pg (Pf.faceLeft σ + Pg.faceLeft σ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by
    rw [NewtonPolygon₀.minkowskiHeight_faceLeft hf.starting_point_fst hg.starting_point_fst
      hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded hg.slopesUnbounded σ,
      hyP, hyQ, NewtonPolygon₀.coe_add_coe]
  have hM1 : Pfg.height ((Pf.faceLeft σ + Pg.faceLeft σ : ℕ) : ℤ)
      = ((yP + yQ : ℝ) : WithBotTop ℝ) := by rw [hf.height_mul hg hfg]; exact hM1'
  refine le_antisymm (Nat.sInf_le ?_) ?_
  · -- the step out of the left endpoint has slope at least `σ`
    show (σ : WithBotTop ℝ) ≤ Pfg.unitSlope (Pf.faceLeft σ + Pg.faceLeft σ)
    by_cases htop : Pfg.height ((Pf.faceLeft σ + Pg.faceLeft σ + 1 : ℕ) : ℤ) = ⊤
    · obtain ⟨-, -, ht⟩ := Pfg.unitSlope_eq_top_of_height_eq_top htop
      rw [hxfg, sub_zero, Int.toNat_natCast, Nat.add_sub_cancel] at ht
      rw [ht]
      exact le_top
    obtain ⟨e, he⟩ := NewtonPolygon₀.exists_coe_of_ne (Pfg.height_natCast_ne_bot hxfg _) htop
    have hline := NewtonPolygon₀.subgradient_line_le_minkowskiHeight hf.starting_point_fst
      hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot
      (fun _ hu => (Pf.unitSlope_lt_of_lt_faceLeft hu).le)
      (fun _ hu => Pf.le_unitSlope_of_faceLeft_le hf.slopesUnbounded hu)
      (fun _ hu => (Pg.unitSlope_lt_of_lt_faceLeft hu).le)
      (fun _ hu => Pg.le_unitSlope_of_faceLeft_le hg.slopesUnbounded hu) hy
      (Pf.faceLeft σ + Pg.faceLeft σ + 1)
    rw [← hf.height_mul hg hfg, he, WithBotTop.coe_le_coe] at hline
    rw [Pfg.unitSlope_eq_of_height_eq hxfg (hbfg _) hM1 he, WithBotTop.coe_le_coe]
    push_cast at hline
    linarith
  · -- and every earlier step has slope strictly below `σ`
    rcases Nat.eq_zero_or_pos (Pf.faceLeft σ + Pg.faceLeft σ) with h0 | h0
    · omega
    refine not_lt.1 fun hlt => ?_
    have hmem : (σ : WithBotTop ℝ) ≤ Pfg.unitSlope (Pfg.faceLeft σ) :=
      Nat.sInf_mem (hSU.exists_le σ)
    have hnet : Pfg.height ((Pf.faceLeft σ + Pg.faceLeft σ - 1 : ℕ) : ℤ) ≠ ⊤ := fun hc =>
      WithBotTop.coe_ne_top _ (hM1.symm.trans (Pfg.height_eq_top_mono hc (by omega)))
    obtain ⟨e, he⟩ := NewtonPolygon₀.exists_coe_of_ne (Pfg.height_natCast_ne_bot hxfg _) hnet
    have hmirror := NewtonPolygon₀.lt_minkowskiHeight_faceLeft_pred hf.starting_point_fst
      hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot hf.slopesUnbounded
      hg.slopesUnbounded σ h0 hM1'
    rw [← hf.height_mul hg hfg, he, WithBotTop.coe_lt_coe] at hmirror
    have hstep : Pfg.unitSlope (Pf.faceLeft σ + Pg.faceLeft σ - 1) < (σ : WithBotTop ℝ) := by
      rw [Pfg.unitSlope_eq_of_height_eq hxfg (hbfg _) he
        (by rw [show Pf.faceLeft σ + Pg.faceLeft σ - 1 + 1 = Pf.faceLeft σ + Pg.faceLeft σ
          by omega]; exact hM1), WithBotTop.coe_lt_coe]
      linarith
    exact absurd hmem (not_le.2 (lt_of_le_of_lt
      (Pfg.unitSlope_mono (show Pfg.faceLeft σ ≤ Pf.faceLeft σ + Pg.faceLeft σ - 1 by omega))
      hstep))

end IsEntireNewtonPolygonOf

/-! ### The constructed polygons

The statements above, for the polygons `newtonPolygon₀OfPowerSeries negLogNorm _` of series
restricted at every radius (polynomials, entire series), with nonzero constant coefficient. -/

/-- A series restricted at every radius has an affine floor of every slope, so its polygon has
unbounded slopes. -/
theorem slopesUnbounded_newtonPolygon₀OfPowerSeries {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f ≠ 0) :
    (newtonPolygon₀OfPowerSeries negLogNorm f).SlopesUnbounded := by
  have hne : f ≠ 0 := fun hc => hf0 (by rw [hc]; simp)
  have hspec := isNewtonPolygonOf_coeffVal_of_isRestricted one_pos (hf 1 one_pos) hne
  have hx := hspec.starting_point_fst_eq_zero (by rw [ne_eq, coeffVal_eq_top_iff]; exact hf0)
  refine hspec.slopesUnbounded_of_forall_line hx
    (newtonPolygon₀OfSeq_unitSlope_ne_bot _ (exists_coeffVal_ne_top hne)
      (isAdmissible_coeffVal_of_isRestricted one_pos (hf 1 one_pos))) fun σ => ?_
  -- the Gauss bound at radius `exp σ` is an affine floor of slope `σ`
  have hc0 : (0 : ℝ) < Real.exp σ := Real.exp_pos σ
  have hres := hf (Real.exp σ) hc0
  refine ⟨-Real.log (PowerSeries.gaussNorm norm (Real.exp σ) f), fun k => ?_⟩
  by_cases hk : PowerSeries.coeff k f = 0
  · rw [pointHeight_eq_top_iff.2 (coeffVal_eq_top_iff.2 hk)]
    exact le_top
  rw [pointHeight_coe (coeffVal_of_ne_zero hk), Algebra.algebraMap_self_apply,
    WithBotTop.coe_le_coe]
  have hnorm : 0 < ‖PowerSeries.coeff k f‖ := norm_pos_iff.mpr hk
  have hterm := PowerSeries.le_gaussNorm norm (Real.exp σ) f hres.hasGaussNorm k
  have hlog := Real.log_le_log (mul_pos hnorm (pow_pos hc0 k)) hterm
  rw [Real.log_mul hnorm.ne' (pow_pos hc0 k).ne', Real.log_pow, Real.log_exp] at hlog
  linarith

/-- The polygon of a series restricted at every radius, with nonzero constant coefficient,
satisfies the standing hypotheses of the product formula. -/
theorem isEntireNewtonPolygonOf_coeffVal {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f ≠ 0) :
    IsEntireNewtonPolygonOf (coeffVal f) (newtonPolygon₀OfPowerSeries negLogNorm f) := by
  have hne : f ≠ 0 := fun hc => hf0 (by rw [hc]; simp)
  have hspec := isNewtonPolygonOf_coeffVal_of_isRestricted one_pos (hf 1 one_pos) hne
  exact ⟨hspec, hspec.starting_point_fst_eq_zero (by rw [ne_eq, coeffVal_eq_top_iff]; exact hf0),
    newtonPolygon₀OfSeq_unitSlope_ne_bot _ (exists_coeffVal_ne_top hne)
      (isAdmissible_coeffVal_of_isRestricted one_pos (hf 1 one_pos)),
    slopesUnbounded_newtonPolygon₀OfPowerSeries hf hf0⟩

/-- The constructed polygon of a product of two series restricted at every radius satisfies the
specification. -/
theorem isNewtonPolygonOf_coeffVal_mul [IsUltrametricDist K] {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) :
    IsNewtonPolygonOf (coeffVal (f * g)) (newtonPolygon₀OfPowerSeries negLogNorm (f * g)) := by
  refine isNewtonPolygonOf_coeffVal_of_isRestricted one_pos
    (PowerSeries.isRestricted.mul 1 (hf 1 one_pos) (hg 1 one_pos)) fun hc => ?_
  have h0 : PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
  rw [hc, map_zero] at h0
  exact mul_ne_zero hf0 hg0 h0.symm

/-- Under the normalisation `a₀ = 1` the constructed polygon has height `0` at the origin. -/
theorem height_zero_newtonPolygon₀OfPowerSeries {f : PowerSeries K}
    (hf0 : PowerSeries.coeff 0 f = 1) :
    (newtonPolygon₀OfPowerSeries negLogNorm f).height 0 = 0 := by
  have hs := newtonPolygon₀_starting_point_of_coeff_zero_eq_one hf0
  rw [show (0 : ℤ) = (newtonPolygon₀OfPowerSeries negLogNorm f).starting_point.1 by rw [hs]]
  show (newtonPolygon₀OfPowerSeries negLogNorm f).toNewtonPolygon.height
    (newtonPolygon₀OfPowerSeries negLogNorm f).toNewtonPolygon.starting_point.1 = _
  rw [NewtonPolygon.height_startingPoint]
  show ((NewtonPolygon.startHeight
    (newtonPolygon₀OfPowerSeries negLogNorm f).toNewtonPolygon : ℝ) : WithBotTop ℝ) = 0
  rw [NewtonPolygon.startHeight]
  simp only [NewtonPolygon₀.toNewtonPolygon_startingPoint, hs, Algebra.algebraMap_self_apply]
  rfl

/-- **The Newton polygon of a product**, for the constructed polygons. -/
theorem height_newtonPolygon₀OfPowerSeries_mul [IsUltrametricDist K] {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).height n =
      (newtonPolygon₀OfPowerSeries negLogNorm f).minkowskiHeight
        (newtonPolygon₀OfPowerSeries negLogNorm g) n :=
  (isEntireNewtonPolygonOf_coeffVal hf hf0).height_mul (isEntireNewtonPolygonOf_coeffVal hg hg0)
    (isNewtonPolygonOf_coeffVal_mul hf hg hf0 hg0) n

/-- **The initial segment**, for the constructed polygons and the blueprint normalisation
`a₀ = b₀ = 1`: if the first `n` slopes of `g` are at most every slope of `f`, the polygon of
`fg` agrees with that of `g` at `n`. -/
theorem height_newtonPolygon₀OfPowerSeries_mul_of_forall_le [IsUltrametricDist K]
    {f g : PowerSeries K} (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f = 1)
    (hg0 : PowerSeries.coeff 0 g = 1) {n : ℕ}
    (hle : ∀ i, i < n → ∀ j, (newtonPolygon₀OfPowerSeries negLogNorm g).unitSlope i ≤
      (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).height n =
      (newtonPolygon₀OfPowerSeries negLogNorm g).height n := by
  have hf0' : PowerSeries.coeff 0 f ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hg0' : PowerSeries.coeff 0 g ≠ 0 := by rw [hg0]; exact one_ne_zero
  rw [(isEntireNewtonPolygonOf_coeffVal hf hf0').height_mul_of_forall_le
    (isEntireNewtonPolygonOf_coeffVal hg hg0') (isNewtonPolygonOf_coeffVal_mul hf hg hf0' hg0')
    hle, height_zero_newtonPolygon₀OfPowerSeries hf0, zero_add]

/-- **The initial segment, slope form**, for the constructed polygons. -/
theorem unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le [IsUltrametricDist K]
    {f g : PowerSeries K} (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) {n : ℕ}
    (hle : ∀ i, i < n → ∀ j, (newtonPolygon₀OfPowerSeries negLogNorm g).unitSlope i ≤
      (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j) {j : ℕ} (hj : j < n) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).unitSlope j =
      (newtonPolygon₀OfPowerSeries negLogNorm g).unitSlope j := by
  have hne : f * g ≠ 0 := fun hc => by
    have h0 : PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    rw [hc, map_zero] at h0
    exact mul_ne_zero hf0 hg0 h0.symm
  exact (isEntireNewtonPolygonOf_coeffVal hf hf0).unitSlope_mul_of_forall_le
    (isEntireNewtonPolygonOf_coeffVal hg hg0) (isNewtonPolygonOf_coeffVal_mul hf hg hf0 hg0)
    (newtonPolygon₀OfSeq_unitSlope_ne_bot _ (exists_coeffVal_ne_top hne)
      (isAdmissible_coeffVal_of_isRestricted one_pos
        (PowerSeries.isRestricted.mul 1 (hf 1 one_pos) (hg 1 one_pos)))) hle hj

/-- **Multiplicities of slopes add**, for the constructed polygons. -/
theorem faceRight_newtonPolygon₀OfPowerSeries_mul [IsUltrametricDist K] {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) (σ : ℝ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).faceRight σ =
      (newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ +
        (newtonPolygon₀OfPowerSeries negLogNorm g).faceRight σ := by
  have hne : f * g ≠ 0 := fun hc => by
    have h0 : PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    rw [hc, map_zero] at h0
    exact mul_ne_zero hf0 hg0 h0.symm
  exact (isEntireNewtonPolygonOf_coeffVal hf hf0).faceRight_mul
    (isEntireNewtonPolygonOf_coeffVal hg hg0) (isNewtonPolygonOf_coeffVal_mul hf hg hf0 hg0)
    (newtonPolygon₀OfSeq_unitSlope_ne_bot _ (exists_coeffVal_ne_top hne)
      (isAdmissible_coeffVal_of_isRestricted one_pos
        (PowerSeries.isRestricted.mul 1 (hf 1 one_pos) (hg 1 one_pos)))) σ

/-- **The strict multiplicities add**, for the constructed polygons. -/
theorem faceLeft_newtonPolygon₀OfPowerSeries_mul [IsUltrametricDist K] {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) (σ : ℝ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).faceLeft σ =
      (newtonPolygon₀OfPowerSeries negLogNorm f).faceLeft σ +
        (newtonPolygon₀OfPowerSeries negLogNorm g).faceLeft σ := by
  have hne : f * g ≠ 0 := fun hc => by
    have h0 : PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    rw [hc, map_zero] at h0
    exact mul_ne_zero hf0 hg0 h0.symm
  exact (isEntireNewtonPolygonOf_coeffVal hf hf0).faceLeft_mul
    (isEntireNewtonPolygonOf_coeffVal hg hg0) (isNewtonPolygonOf_coeffVal_mul hf hg hf0 hg0)
    (newtonPolygon₀OfSeq_unitSlope_ne_bot _ (exists_coeffVal_ne_top hne)
      (isAdmissible_coeffVal_of_isRestricted one_pos
        (PowerSeries.isRestricted.mul 1 (hf 1 one_pos) (hg 1 one_pos)))) σ

/-- The polygon of a nonzero polynomial is finite at its degree. -/
theorem height_newtonPolygon₀OfPowerSeries_coe_natDegree_ne_top (G : Polynomial K)
    (hG : G ≠ 0) :
    (newtonPolygon₀OfPowerSeries negLogNorm (G : PowerSeries K)).height G.natDegree ≠ ⊤ :=
  (isNewtonPolygonOf_coeffVal_coe G hG).height_ne_top_of_ne_top (by
    rw [ne_eq, coeffVal_eq_top_iff, Polynomial.coeff_coe]
    exact Polynomial.leadingCoeff_ne_zero.2 hG)

/-- **The finite factor supplies the initial segment** ([LWX, §3.23 Step I], the form the
Fredholm-determinant application needs): for `f` restricted at every radius and a polynomial
`G`, both with constant coefficient `1`, if every slope of `G` is at most every slope of `f`
then the polygon of `f · G` agrees with that of `G` at `deg G`. -/
theorem height_newtonPolygon₀OfPowerSeries_mul_coe [IsUltrametricDist K] {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f = 1)
    (G : Polynomial K) (hG0 : G.coeff 0 = 1)
    (hle : ∀ i, i < G.natDegree → ∀ j,
      (newtonPolygon₀OfPowerSeries negLogNorm (G : PowerSeries K)).unitSlope i ≤
        (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * (G : PowerSeries K))).height G.natDegree =
      (newtonPolygon₀OfPowerSeries negLogNorm (G : PowerSeries K)).height G.natDegree :=
  height_newtonPolygon₀OfPowerSeries_mul_of_forall_le hf
    (fun c _ => Polynomial.isRestricted_toPowerSeries (c := c) G) hf0
    (by rwa [Polynomial.coeff_coe]) hle

end
