/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.NewtonPolygons.Support

/-!
# Faces of a one-sided Newton polygon

For a real slope `σ`, the *face of slope `σ`* of a convex polygon is the (possibly degenerate)
segment on which the supporting line of slope `σ` touches it.  [Ked07, proof of Corollary 2]:
"the left and right endpoints of the segment of slope `r` in the Newton polygon are the points
where the support lines of slightly smaller and slightly larger slope, respectively, touch the
polygon."  In the unit-slope language of `Height.lean` the two endpoints are

* `NewtonPolygon₀.faceLeft P σ` — the first unit interval whose slope is `≥ σ`, equivalently the
  number of unit slopes `< σ`;
* `NewtonPolygon₀.faceRight P σ` — the first unit interval whose slope is `> σ`, equivalently the
  number of unit slopes `≤ σ`.

Both are finite when the slopes are *unbounded* (`NewtonPolygon₀.SlopesUnbounded`): the
polygon is finite (junk tail `⊤`), or its slopes tend to `+∞`.  This holds for the polygon of a
polynomial and of an entire series, and it is exactly what excludes the final rays on which the
product formula of `Product.lean` fails (`(1 − X)·∑ Xⁱ = 1`).  The standing hypotheses of the
product formula are bundled as `IsEntireNewtonPolygonOf`.

Two kinds of results:

* **convexity only** (`namespace NewtonPolygon₀`): the line of slope `σ` through the polygon at
  an index separating the unit slopes lies on/below the polygon, strictly so on the far side of
  a face endpoint; the polygon is linear on the face;
* **consequences of the specification** (`namespace IsNewtonPolygonOf`), all through the
  supporting-line lemma `IsNewtonPolygonOf.line_le_height`: a vertex of the Newton polygon is a
  point of the sequence (so the face endpoints are points), the polygon is `⊤` beyond the last
  point, and a sequence lying above a line of every slope has unbounded slopes.

## Sources

[Ked07] K. S. Kedlaya, *p-adic differential equations*, 18.787 (MIT, fall 2007), unit "Newton
polygons", §§1–2 (`kskedlaya.org/18.787/newton-poly.pdf`).
[Kob84] N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Ch. IV §3
(p. 97, vertices) and §4 (pp. 99–102, the three types of polygon; Lemma 6).
-/

open Finset

noncomputable section

namespace NewtonPolygon

/-- A `WithBotTop ℝ` value that is neither junk value is the coercion of its `toReal`. -/
theorem coe_toReal_eq_self {x : WithBotTop ℝ} (h1 : x ≠ ⊥) (h2 : x ≠ ⊤) :
    ((toReal x : ℝ) : WithBotTop ℝ) = x := by
  induction x using WithBotTop.rec with
  | bot => exact absurd rfl h1
  | coe a => rw [toReal_coe]
  | top => exact absurd rfl h2

/-- On non-junk values `toReal` is order-preserving. -/
theorem toReal_le_toReal {x y : WithBotTop ℝ} (hxb : x ≠ ⊥) (hxt : x ≠ ⊤) (hyb : y ≠ ⊥)
    (hyt : y ≠ ⊤) (h : x ≤ y) : toReal x ≤ toReal y := by
  rwa [← coe_toReal_eq_self hxb hxt, ← coe_toReal_eq_self hyb hyt, WithBotTop.coe_le_coe] at h

end NewtonPolygon

namespace NewtonPolygon₀

variable (P : NewtonPolygon₀ (Γ := ℝ))

/-- A one-sided polygon has *unbounded slopes* when every real number is exceeded by some unit
slope (the junk value `⊤` counts): the polygon is finite, or its slopes tend to `+∞`.
[Kob84, §IV.4] type (2), together with the polygons of polynomials. -/
def SlopesUnbounded : Prop := ∀ σ : ℝ, ∃ j : ℕ, (σ : WithBotTop ℝ) < P.unitSlope j

/-- The left endpoint of the face of slope `σ`: the first unit interval whose slope is `≥ σ`,
equivalently the number of unit slopes `< σ` ([Ked07, proof of Cor. 2]: "the points where the
support lines of slightly smaller ... slope ... touch the polygon").  Junk `0` if no unit slope
is `≥ σ`. -/
def faceLeft (σ : ℝ) : ℕ := sInf {j : ℕ | (σ : WithBotTop ℝ) ≤ P.unitSlope j}

/-- The right endpoint of the face of slope `σ`: the first unit interval whose slope is `> σ`,
equivalently the number of unit slopes `≤ σ` ([Ked07, proof of Cor. 2]: "... slightly larger
slope").  Junk `0` if no unit slope is `> σ`. -/
def faceRight (σ : ℝ) : ℕ := sInf {j : ℕ | (σ : WithBotTop ℝ) < P.unitSlope j}

variable {P}

/-! ### Supporting lines from convexity

The polygon is convex (`unitSlope_mono`), so the line of slope `σ` through the polygon at an
index `i₀` at which the unit slopes cross from `≤ σ` to `≥ σ` lies on/below the polygon; it is
strictly below wherever the crossing is strict. -/

/-- The increment of `heightFun` over `[m, n)` is the sum of the unit slopes crossed. -/
theorem heightFun_sub_eq_sum {m n : ℕ} (hmn : m ≤ n) :
    P.heightFun n - P.heightFun m = ∑ i ∈ Ico m n, NewtonPolygon.toReal (P.unitSlope i) := by
  rw [NewtonPolygon₀.heightFun, NewtonPolygon₀.heightFun, Finset.sum_Ico_eq_sub _ hmn]
  ring

/-- A real bound on a non-junk unit slope, read off the `WithBotTop` comparison. -/
private lemma toReal_unitSlope_le_of_le {t : ℕ} {σ : ℝ} (hb : P.unitSlope t ≠ ⊥)
    (ht : P.unitSlope t ≠ ⊤) (h : P.unitSlope t ≤ (σ : WithBotTop ℝ)) :
    NewtonPolygon.toReal (P.unitSlope t) ≤ σ :=
  WithBotTop.coe_le_coe.1 ((NewtonPolygon.coe_toReal_eq_self hb ht).symm ▸ h)

/-- A real lower bound on a non-junk unit slope. -/
private lemma le_toReal_unitSlope_of_le {t : ℕ} {σ : ℝ} (hb : P.unitSlope t ≠ ⊥)
    (ht : P.unitSlope t ≠ ⊤) (h : (σ : WithBotTop ℝ) ≤ P.unitSlope t) :
    σ ≤ NewtonPolygon.toReal (P.unitSlope t) :=
  WithBotTop.coe_le_coe.1 ((NewtonPolygon.coe_toReal_eq_self hb ht).symm ▸ h)

/-- A strict real bound on a non-junk unit slope. -/
private lemma toReal_unitSlope_lt_of_lt {t : ℕ} {σ : ℝ} (hb : P.unitSlope t ≠ ⊥)
    (ht : P.unitSlope t ≠ ⊤) (h : P.unitSlope t < (σ : WithBotTop ℝ)) :
    NewtonPolygon.toReal (P.unitSlope t) < σ :=
  WithBotTop.coe_lt_coe.1 ((NewtonPolygon.coe_toReal_eq_self hb ht).symm ▸ h)

/-- A strict real lower bound on a non-junk unit slope. -/
private lemma lt_toReal_unitSlope_of_lt {t : ℕ} {σ : ℝ} (hb : P.unitSlope t ≠ ⊥)
    (ht : P.unitSlope t ≠ ⊤) (h : (σ : WithBotTop ℝ) < P.unitSlope t) :
    σ < NewtonPolygon.toReal (P.unitSlope t) :=
  WithBotTop.coe_lt_coe.1 ((NewtonPolygon.coe_toReal_eq_self hb ht).symm ▸ h)

/-- At a natural index the height is the walked value, when finite. -/
theorem height_natCast_eq_heightFun (hx : P.starting_point.1 = 0) {k : ℕ}
    (h : P.height (k : ℤ) ≠ ⊤) : P.height (k : ℤ) = ((P.heightFun k : ℝ) : WithBotTop ℝ) := by
  have hk : ((k : ℕ) : ℤ) = P.starting_point.1 + (k : ℤ) := by rw [hx]; ring
  rw [hk] at h ⊢
  exact P.height_eq_heightFun k h

/-- Right of the anchor the height is never the junk value `⊥`: `⊥` occurs only strictly left
of the starting vertex. -/
theorem height_ne_bot_of_nonneg (hx : P.starting_point.1 = 0) {x : ℤ} (hx0 : 0 ≤ x) :
    P.height x ≠ ⊥ := by
  rw [ne_eq, P.height_eq_bot_iff, hx]
  exact not_lt.2 hx0

/-- At a natural index the height is never `⊥`. -/
theorem height_natCast_ne_bot (hx : P.starting_point.1 = 0) (n : ℕ) : P.height (n : ℤ) ≠ ⊥ :=
  P.height_ne_bot_of_nonneg hx (Int.natCast_nonneg n)

/-- At the anchor the height is the (real) starting height, in particular not `⊤`. -/
theorem height_natCast_zero_ne_top (hx : P.starting_point.1 = 0) : P.height (0 : ℤ) ≠ ⊤ := by
  rw [show (0 : ℤ) = P.starting_point.1 from hx.symm]
  show P.toNewtonPolygon.height P.toNewtonPolygon.starting_point.1 ≠ ⊤
  rw [NewtonPolygon.height_startingPoint]
  exact WithBotTop.coe_ne_top _

/-- Below a finite height at a natural index, the unit slopes are not `⊤`. -/
theorem unitSlope_ne_top_of_height_natCast (hx : P.starting_point.1 = 0) {k : ℕ}
    (h : P.height (k : ℤ) ≠ ⊤) {i : ℕ} (hik : i < k) : P.unitSlope i ≠ ⊤ := by
  refine P.unitSlope_ne_top_of_height_ne_top (c := k) ?_ hik
  rwa [hx, zero_add]

/-- The height increment over `[i₀, k)` is at least `σ` per step when every slope there is. -/
private lemma le_heightFun_sub {i₀ k : ℕ} (hik : i₀ ≤ k) {σ : ℝ}
    (h : ∀ t, i₀ ≤ t → t < k → σ ≤ NewtonPolygon.toReal (P.unitSlope t)) :
    σ * ((k : ℝ) - i₀) ≤ P.heightFun k - P.heightFun i₀ := by
  rw [P.heightFun_sub_eq_sum hik]
  have hsum := Finset.card_nsmul_le_sum (Ico i₀ k)
    (fun t => NewtonPolygon.toReal (P.unitSlope t)) σ
    (fun t ht => h t (mem_Ico.1 ht).1 (mem_Ico.1 ht).2)
  rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hik] at hsum
  linarith

/-- The height increment over `[k, i₀)` is at most `σ` per step when every slope there is. -/
private lemma heightFun_sub_le {k i₀ : ℕ} (hki : k ≤ i₀) {σ : ℝ}
    (h : ∀ t, k ≤ t → t < i₀ → NewtonPolygon.toReal (P.unitSlope t) ≤ σ) :
    P.heightFun i₀ - P.heightFun k ≤ σ * ((i₀ : ℝ) - k) := by
  rw [P.heightFun_sub_eq_sum hki]
  have hsum := Finset.sum_le_card_nsmul (Ico k i₀)
    (fun t => NewtonPolygon.toReal (P.unitSlope t)) σ
    (fun t ht => h t (mem_Ico.1 ht).1 (mem_Ico.1 ht).2)
  rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hki] at hsum
  linarith

/-- Strict form of `le_heightFun_sub`. -/
private lemma lt_heightFun_sub {i₀ k : ℕ} (hik : i₀ < k) {σ : ℝ}
    (h : ∀ t, i₀ ≤ t → t < k → σ < NewtonPolygon.toReal (P.unitSlope t)) :
    σ * ((k : ℝ) - i₀) < P.heightFun k - P.heightFun i₀ := by
  rw [P.heightFun_sub_eq_sum hik.le]
  have hne : (Ico i₀ k).Nonempty := nonempty_Ico.2 hik
  have hsum : ∑ _t ∈ Ico i₀ k, σ < ∑ t ∈ Ico i₀ k, NewtonPolygon.toReal (P.unitSlope t) :=
    Finset.sum_lt_sum_of_nonempty hne fun t ht => h t (mem_Ico.1 ht).1 (mem_Ico.1 ht).2
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hik.le] at hsum
  linarith

/-- Strict form of `heightFun_sub_le`. -/
private lemma heightFun_sub_lt {k i₀ : ℕ} (hki : k < i₀) {σ : ℝ}
    (h : ∀ t, k ≤ t → t < i₀ → NewtonPolygon.toReal (P.unitSlope t) < σ) :
    P.heightFun i₀ - P.heightFun k < σ * ((i₀ : ℝ) - k) := by
  rw [P.heightFun_sub_eq_sum hki.le]
  have hne : (Ico k i₀).Nonempty := nonempty_Ico.2 hki
  have hsum : ∑ t ∈ Ico k i₀, NewtonPolygon.toReal (P.unitSlope t) < ∑ _t ∈ Ico k i₀, σ :=
    Finset.sum_lt_sum_of_nonempty hne fun t ht => h t (mem_Ico.1 ht).1 (mem_Ico.1 ht).2
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hki.le] at hsum
  linarith

/-- **The supporting line at an index.**  If the unit slopes before `i₀` are `≤ σ` and those from
`i₀` on are `≥ σ`, the line of slope `σ` through `(i₀, height i₀)` lies on/below the polygon.
[Ked07, §2]: "`v_r` is the `y`-intercept of the supporting line of the Newton polygon of slope
`r`". -/
theorem line_le_height_of_unitSlope (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    {i₀ : ℕ} {σ : ℝ} (h₁ : ∀ t, t < i₀ → P.unitSlope t ≤ (σ : WithBotTop ℝ))
    (h₂ : ∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) ≤ P.unitSlope t) {y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) (k : ℕ) :
    ((y + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) ≤ P.height k := by
  by_cases hk : P.height (k : ℤ) = ⊤
  · rw [hk]; exact le_top
  have hi₀ : P.height (i₀ : ℤ) ≠ ⊤ := by rw [hy]; exact WithBotTop.coe_ne_top _
  have hyeq : y = P.heightFun i₀ :=
    WithBotTop.coe_injective (hy.symm.trans (P.height_natCast_eq_heightFun hx hi₀))
  rw [P.height_natCast_eq_heightFun hx hk, WithBotTop.coe_le_coe, hyeq]
  rcases le_or_gt i₀ k with hik | hki
  · have := P.le_heightFun_sub hik fun t ht ht' =>
      P.le_toReal_unitSlope_of_le (hb t) (P.unitSlope_ne_top_of_height_natCast hx hk ht') (h₂ t ht)
    linarith
  · have := P.heightFun_sub_le hki.le fun t _ ht' =>
      P.toReal_unitSlope_le_of_le (hb t)
        (P.unitSlope_ne_top_of_height_natCast hx hi₀ ht') (h₁ t ht')
    linarith

/-- Strict form of `line_le_height_of_unitSlope` to the left: if the unit slopes before `i₀` are
`< σ`, the supporting line is strictly below the polygon left of `i₀`.  (Only the left-hand
hypothesis is needed: to the left of `i₀` the right-hand slopes never enter the sum.) -/
theorem line_lt_height_of_unitSlope_lt (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥) {i₀ : ℕ} {σ : ℝ}
    (h₁ : ∀ t, t < i₀ → P.unitSlope t < (σ : WithBotTop ℝ)) {y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) {k : ℕ} (hk : k < i₀) :
    ((y + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) < P.height k := by
  have hi₀ : P.height (i₀ : ℤ) ≠ ⊤ := by rw [hy]; exact WithBotTop.coe_ne_top _
  have hkne : P.height (k : ℤ) ≠ ⊤ := fun hc =>
    hi₀ (P.height_eq_top_mono hc (by exact_mod_cast hk.le))
  have hyeq : y = P.heightFun i₀ :=
    WithBotTop.coe_injective (hy.symm.trans (P.height_natCast_eq_heightFun hx hi₀))
  rw [P.height_natCast_eq_heightFun hx hkne, WithBotTop.coe_lt_coe, hyeq]
  have := P.heightFun_sub_lt hk fun t _ ht' =>
    P.toReal_unitSlope_lt_of_lt (hb t) (P.unitSlope_ne_top_of_height_natCast hx hi₀ ht') (h₁ t ht')
  linarith

/-- Strict form of `line_le_height_of_unitSlope` to the right: if the unit slopes from `i₀` on
are `> σ`, the supporting line is strictly below the polygon right of `i₀`.  (Only the right-hand
hypothesis is needed.) -/
theorem line_lt_height_of_lt_unitSlope (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥) {i₀ : ℕ} {σ : ℝ}
    (h₂ : ∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) < P.unitSlope t) {y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) {k : ℕ} (hk : i₀ < k) :
    ((y + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) < P.height k := by
  by_cases hkt : P.height (k : ℤ) = ⊤
  · rw [hkt]; exact lt_top_iff_ne_top.2 (WithBotTop.coe_ne_top _)
  have hi₀ : P.height (i₀ : ℤ) ≠ ⊤ := by rw [hy]; exact WithBotTop.coe_ne_top _
  have hyeq : y = P.heightFun i₀ :=
    WithBotTop.coe_injective (hy.symm.trans (P.height_natCast_eq_heightFun hx hi₀))
  rw [P.height_natCast_eq_heightFun hx hkt, WithBotTop.coe_lt_coe, hyeq]
  have := P.lt_heightFun_sub hk fun t ht ht' =>
    P.lt_toReal_unitSlope_of_lt (hb t) (P.unitSlope_ne_top_of_height_natCast hx hkt ht') (h₂ t ht)
  linarith

/-- On a stretch of unit slopes all equal to `σ` the polygon is the line of slope `σ`. -/
theorem height_eq_of_forall_unitSlope_eq (hx : P.starting_point.1 = 0) {i₀ : ℕ} {σ y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) {k : ℕ} (hik : i₀ ≤ k)
    (h : ∀ t, i₀ ≤ t → t < k → P.unitSlope t = (σ : WithBotTop ℝ)) :
    P.height k = ((y + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) := by
  rcases eq_or_lt_of_le hik with rfl | hlt
  · rw [hy]; norm_num
  -- the last slope crossed is the real `σ`, so the height at `k` is not the junk value `⊤`
  have hk : P.height (k : ℤ) ≠ ⊤ := by
    intro hcon
    obtain ⟨-, -, htop⟩ := P.unitSlope_eq_top_of_height_eq_top hcon
    rw [hx, sub_zero, Int.toNat_natCast] at htop
    rw [h (k - 1) (by omega) (by omega)] at htop
    exact WithBotTop.coe_ne_top σ htop
  have hi₀ : P.height (i₀ : ℤ) ≠ ⊤ := by rw [hy]; exact WithBotTop.coe_ne_top _
  have hyeq : y = P.heightFun i₀ :=
    WithBotTop.coe_injective (hy.symm.trans (P.height_natCast_eq_heightFun hx hi₀))
  rw [P.height_natCast_eq_heightFun hx hk, hyeq]
  congr 1
  have hsum := P.heightFun_sub_eq_sum hik
  rw [Finset.sum_congr rfl fun t ht => by
      rw [h t (mem_Ico.1 ht).1 (mem_Ico.1 ht).2, NewtonPolygon.toReal_coe],
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hik] at hsum
  linarith

/-! ### The face of slope `σ` -/

/-- With unbounded slopes, every real `σ` is reached by some unit slope. -/
theorem SlopesUnbounded.exists_le (hP : P.SlopesUnbounded) (σ : ℝ) :
    ∃ j : ℕ, (σ : WithBotTop ℝ) ≤ P.unitSlope j :=
  (hP σ).imp fun _ hj => hj.le

/-- Left of `faceLeft σ` the unit slopes are `< σ`. -/
theorem unitSlope_lt_of_lt_faceLeft {σ : ℝ} {j : ℕ} (hj : j < P.faceLeft σ) :
    P.unitSlope j < (σ : WithBotTop ℝ) :=
  not_le.1 (Nat.notMem_of_lt_sInf hj)

/-- From `faceLeft σ` on the unit slopes are `≥ σ`. -/
theorem le_unitSlope_of_faceLeft_le (hP : P.SlopesUnbounded) {σ : ℝ} {j : ℕ}
    (hj : P.faceLeft σ ≤ j) : (σ : WithBotTop ℝ) ≤ P.unitSlope j :=
  have h : (σ : WithBotTop ℝ) ≤ P.unitSlope (P.faceLeft σ) := Nat.sInf_mem (hP.exists_le σ)
  h.trans (P.unitSlope_mono hj)

/-- `faceLeft σ` is at most any index whose unit slope is `≥ σ`. -/
theorem faceLeft_le_of_le_unitSlope {σ : ℝ} {j : ℕ} (hj : (σ : WithBotTop ℝ) ≤ P.unitSlope j) :
    P.faceLeft σ ≤ j :=
  Nat.sInf_le hj

/-- Left of `faceRight σ` the unit slopes are `≤ σ`. -/
theorem unitSlope_le_of_lt_faceRight {σ : ℝ} {j : ℕ} (hj : j < P.faceRight σ) :
    P.unitSlope j ≤ (σ : WithBotTop ℝ) :=
  not_lt.1 (Nat.notMem_of_lt_sInf hj)

/-- From `faceRight σ` on the unit slopes are `> σ`. -/
theorem lt_unitSlope_of_faceRight_le (hP : P.SlopesUnbounded) {σ : ℝ} {j : ℕ}
    (hj : P.faceRight σ ≤ j) : (σ : WithBotTop ℝ) < P.unitSlope j :=
  have h : (σ : WithBotTop ℝ) < P.unitSlope (P.faceRight σ) := Nat.sInf_mem (hP σ)
  h.trans_le (P.unitSlope_mono hj)

/-- `faceRight σ` is at least any index below which the unit slopes are `≤ σ`. -/
theorem le_faceRight_of_forall_le (hP : P.SlopesUnbounded) {σ : ℝ} {j : ℕ}
    (hj : ∀ t, t < j → P.unitSlope t ≤ (σ : WithBotTop ℝ)) : j ≤ P.faceRight σ :=
  have h : (σ : WithBotTop ℝ) < P.unitSlope (P.faceRight σ) := Nat.sInf_mem (hP σ)
  not_lt.1 fun hlt => absurd (hj _ hlt) (not_le.2 h)

/-- The face of slope `σ` is the interval `[faceLeft σ, faceRight σ]`. -/
theorem faceLeft_le_faceRight (hP : P.SlopesUnbounded) (σ : ℝ) : P.faceLeft σ ≤ P.faceRight σ :=
  have h : (σ : WithBotTop ℝ) < P.unitSlope (P.faceRight σ) := Nat.sInf_mem (hP σ)
  P.faceLeft_le_of_le_unitSlope h.le

/-- Faces of increasing slopes are ordered: the face of slope `σ` ends before the face of any
larger slope `τ` begins. -/
theorem faceRight_le_faceLeft_of_lt (hP : P.SlopesUnbounded) {σ τ : ℝ} (h : σ < τ) :
    P.faceRight σ ≤ P.faceLeft τ :=
  have hτ : (τ : WithBotTop ℝ) ≤ P.unitSlope (P.faceLeft τ) := Nat.sInf_mem (hP.exists_le τ)
  Nat.sInf_le ((WithBotTop.coe_lt_coe.2 h).trans_le hτ)

/-- A height at a natural index below which no unit slope is `⊤` is not `⊤`. -/
theorem height_natCast_ne_top_of_unitSlope (hx : P.starting_point.1 = 0) {n : ℕ}
    (h : ∀ j, j < n → P.unitSlope j ≠ ⊤) : P.height (n : ℤ) ≠ ⊤ := by
  intro hcon
  obtain ⟨-, hn1, htop⟩ := P.unitSlope_eq_top_of_height_eq_top hcon
  rw [hx, sub_zero, Int.toNat_natCast] at hn1 htop
  exact h (n - 1) (by omega) htop

/-- Such a height is therefore a real number. -/
theorem exists_height_natCast_eq (hx : P.starting_point.1 = 0) {n : ℕ}
    (h : ∀ j, j < n → P.unitSlope j ≠ ⊤) : ∃ y : ℝ, P.height (n : ℤ) = (y : WithBotTop ℝ) :=
  ⟨P.heightFun n, P.height_natCast_eq_heightFun hx (P.height_natCast_ne_top_of_unitSlope hx h)⟩

/-- The height at the left endpoint of a face is a real number: every earlier unit slope is
`< σ`, hence not `⊤`. -/
theorem exists_height_faceLeft_eq (hx : P.starting_point.1 = 0) (σ : ℝ) :
    ∃ y : ℝ, P.height (P.faceLeft σ) = (y : WithBotTop ℝ) :=
  P.exists_height_natCast_eq hx fun _ hj => (P.unitSlope_lt_of_lt_faceLeft hj).ne_top

/-- The height at the right endpoint of a face is a real number. -/
theorem exists_height_faceRight_eq (hx : P.starting_point.1 = 0) (σ : ℝ) :
    ∃ y : ℝ, P.height (P.faceRight σ) = (y : WithBotTop ℝ) :=
  P.exists_height_natCast_eq hx fun _ hj =>
    ne_top_of_le_ne_top (WithBotTop.coe_ne_top σ) (P.unitSlope_le_of_lt_faceRight hj)

/-- On the face of slope `σ` the polygon is the line of slope `σ` through the left endpoint. -/
theorem height_eq_of_mem_face (hx : P.starting_point.1 = 0) (hP : P.SlopesUnbounded) {σ y : ℝ}
    (hy : P.height (P.faceLeft σ) = (y : WithBotTop ℝ)) {k : ℕ} (h1 : P.faceLeft σ ≤ k)
    (h2 : k ≤ P.faceRight σ) :
    P.height k = ((y + σ * ((k : ℝ) - P.faceLeft σ) : ℝ) : WithBotTop ℝ) :=
  P.height_eq_of_forall_unitSlope_eq hx hy h1 fun _ ht ht' =>
    le_antisymm (P.unitSlope_le_of_lt_faceRight (lt_of_lt_of_le ht' h2))
      (P.le_unitSlope_of_faceLeft_le hP ht)

/-- The supporting line of slope `σ` through the left endpoint of the face lies on/below the
polygon. -/
theorem faceLeft_line_le_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) {σ y : ℝ} (hy : P.height (P.faceLeft σ) = (y : WithBotTop ℝ))
    (k : ℕ) : ((y + σ * ((k : ℝ) - P.faceLeft σ) : ℝ) : WithBotTop ℝ) ≤ P.height k :=
  P.line_le_height_of_unitSlope hx hb (fun _ ht => (P.unitSlope_lt_of_lt_faceLeft ht).le)
    (fun _ ht => P.le_unitSlope_of_faceLeft_le hP ht) hy k

/-- Left of the face, the supporting line through its left endpoint is strictly below the
polygon. -/
theorem faceLeft_line_lt_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    {σ y : ℝ} (hy : P.height (P.faceLeft σ) = (y : WithBotTop ℝ))
    {k : ℕ} (hk : k < P.faceLeft σ) :
    ((y + σ * ((k : ℝ) - P.faceLeft σ) : ℝ) : WithBotTop ℝ) < P.height k :=
  P.line_lt_height_of_unitSlope_lt hx hb (fun _ ht => P.unitSlope_lt_of_lt_faceLeft ht) hy hk

/-- The supporting line of slope `σ` through the right endpoint of the face lies on/below the
polygon. -/
theorem faceRight_line_le_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) {σ y : ℝ} (hy : P.height (P.faceRight σ) = (y : WithBotTop ℝ))
    (k : ℕ) : ((y + σ * ((k : ℝ) - P.faceRight σ) : ℝ) : WithBotTop ℝ) ≤ P.height k :=
  P.line_le_height_of_unitSlope hx hb (fun _ ht => P.unitSlope_le_of_lt_faceRight ht)
    (fun _ ht => (P.lt_unitSlope_of_faceRight_le hP ht).le) hy k

/-- Right of the face, the supporting line through its right endpoint is strictly below the
polygon. -/
theorem faceRight_line_lt_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) {σ y : ℝ} (hy : P.height (P.faceRight σ) = (y : WithBotTop ℝ))
    {k : ℕ} (hk : P.faceRight σ < k) :
    ((y + σ * ((k : ℝ) - P.faceRight σ) : ℝ) : WithBotTop ℝ) < P.height k :=
  P.line_lt_height_of_lt_unitSlope hx hb (fun _ ht => P.lt_unitSlope_of_faceRight_le hP ht) hy hk

/-- **The supporting line with a margin.**  If every unit slope before `i₀` is at most `σ - δ`
and every one from `i₀` on is at least `σ + δ`, then the line of slope `σ` through `(i₀, y)`
clears the polygon by `δ` at every index other than `i₀` (a step away from `i₀` costs at least
`δ`).  This is the quantitative form of `line_lt_height_of_unitSlope_lt` /
`line_lt_height_of_lt_unitSlope` that the vertex characterisation needs. -/
theorem line_add_margin_le_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    {i₀ : ℕ} {σ δ : ℝ} (hδ : 0 ≤ δ)
    (h₁ : ∀ t, t < i₀ → P.unitSlope t ≤ ((σ - δ : ℝ) : WithBotTop ℝ))
    (h₂ : ∀ t, i₀ ≤ t → ((σ + δ : ℝ) : WithBotTop ℝ) ≤ P.unitSlope t) {y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) {k : ℕ} (hk : k ≠ i₀) :
    ((y + δ + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) ≤ P.height k := by
  have hle : ((σ - δ : ℝ) : WithBotTop ℝ) ≤ ((σ + δ : ℝ) : WithBotTop ℝ) :=
    WithBotTop.coe_le_coe.2 (by linarith)
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · -- left of `i₀`: use the shallower slope `σ - δ`; each of the `≥ 1` steps back gains `δ`
    have key := P.line_le_height_of_unitSlope hx hb h₁ (fun t ht => hle.trans (h₂ t ht)) hy k
    refine le_trans (WithBotTop.coe_le_coe.2 ?_) key
    have : (k : ℝ) + 1 ≤ (i₀ : ℝ) := by exact_mod_cast hlt
    nlinarith
  · -- right of `i₀`: use the steeper slope `σ + δ`
    have key := P.line_le_height_of_unitSlope hx hb (fun t ht => (h₁ t ht).trans hle) h₂ hy k
    refine le_trans (WithBotTop.coe_le_coe.2 ?_) key
    have : (i₀ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hgt
    nlinarith

end NewtonPolygon₀

/-- **The standing hypotheses of the product formula**: `P` is the Newton polygon of `v`
(`IsNewtonPolygonOf`), anchored at the origin (`v 0 ≠ ⊤`: a nonzero constant coefficient),
with no `⊥` unit slope (excluded for constructed polygons by admissibility,
`newtonPolygon₀OfSeq_unitSlope_ne_bot`) and with unbounded slopes (a polynomial, or an entire
series — whence the name). -/
structure IsEntireNewtonPolygonOf (v : ℕ → WithTop ℝ) (P : NewtonPolygon₀ (Γ := ℝ)) : Prop
    extends IsNewtonPolygonOf v P where
  /-- The polygon is anchored at `x = 0`. -/
  starting_point_fst : P.starting_point.1 = 0
  /-- No unit slope is the junk value `⊥`. -/
  unitSlope_ne_bot : ∀ j, P.unitSlope j ≠ ⊥
  /-- The slopes are unbounded: the polygon is finite or its slopes tend to `+∞`. -/
  slopesUnbounded : P.SlopesUnbounded

/-- A point height is never the junk value `⊥`: it is `⊤` at a vanishing value and a real
number otherwise. -/
theorem pointHeight_ne_bot (v : ℕ → WithTop ℝ) (k : ℕ) : pointHeight v k ≠ ⊥ := by
  cases hv : v k <;> simp [pointHeight, hv]

namespace IsNewtonPolygonOf

variable {v : ℕ → WithTop ℝ} {P : NewtonPolygon₀ (Γ := ℝ)}

/-- A Newton polygon of a sequence with a finite `0`-th value is anchored at `x = 0`. -/
theorem starting_point_fst_eq_zero (h : IsNewtonPolygonOf v P) (h0 : v 0 ≠ ⊤) :
    P.starting_point.1 = 0 := by
  obtain ⟨k, hk, -⟩ := h.start_mem
  have hle : P.starting_point.1 ≤ ((0 : ℕ) : ℤ) := h.starting_point_fst_le h0
  omega

/-- At the anchor the polygon passes through the point (`start_mem`). -/
theorem height_zero_eq (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0) :
    P.height 0 = pointHeight v 0 := by
  obtain ⟨k, hk, hv⟩ := h.start_mem
  rw [hx] at hk
  obtain rfl : k = 0 := by exact_mod_cast hk
  rw [pointHeight_coe hv, show (0 : ℤ) = P.starting_point.1 from hx.symm]
  show P.toNewtonPolygon.height P.toNewtonPolygon.starting_point.1 = _
  rw [NewtonPolygon.height_startingPoint]
  rfl

/-- Below a finite point the height is finite (`height_le`). -/
theorem height_ne_top_of_ne_top (h : IsNewtonPolygonOf v P) {k : ℕ} (hk : v k ≠ ⊤) :
    P.height k ≠ ⊤ :=
  ne_top_of_le_ne_top (fun hc => hk (pointHeight_eq_top_iff.1 hc)) (h.height_le k)

/-- **A vertex of the Newton polygon is a point of the sequence** ([Kob84, §IV.3 p. 97]: "By
the vertices of the Newton polygon we mean the points `(i_j, ord_p a_{i_j})` where the slopes
change").  Spec-level: where the unit slope strictly increases, the polygon's height is the
point's height — otherwise a slightly raised supporting line would still lie below every point,
contradicting `line_le_height`. -/
theorem height_eq_pointHeight_of_unitSlope_lt (h : IsNewtonPolygonOf v P)
    (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥) {i : ℕ}
    (hi : P.unitSlope i < P.unitSlope (i + 1)) :
    P.height ((i + 1 : ℕ) : ℤ) = pointHeight v (i + 1) := by
  classical
  -- every slope up to `i` is bounded by `unitSlope i`, which is not `⊤`
  have hitop : P.unitSlope i ≠ ⊤ := by
    intro hc
    exact not_top_lt (show (⊤ : WithBotTop ℝ) < P.unitSlope (i + 1) from hc ▸ hi)
  have hne : ∀ j, j < i + 1 → P.unitSlope j ≠ ⊤ := fun j hj hc =>
    hitop (top_le_iff.1 (hc ▸ P.unitSlope_mono (show j ≤ i by omega)))
  obtain ⟨hval, hhval⟩ := P.exists_height_natCast_eq hx hne
  refine le_antisymm (h.height_le _) ?_
  by_contra hcon
  rw [not_le, hhval] at hcon
  -- a slope `σ` strictly between the two, with a margin `δ` on both sides
  obtain ⟨σ, δ, hδ, hσ₁, hσ₂⟩ : ∃ σ δ : ℝ, 0 < δ ∧
      P.unitSlope i ≤ ((σ - δ : ℝ) : WithBotTop ℝ) ∧
      ((σ + δ : ℝ) : WithBotTop ℝ) ≤ P.unitSlope (i + 1) := by
    obtain ⟨a, ha⟩ : ∃ a : ℝ, P.unitSlope i = (a : WithBotTop ℝ) := by
      generalize hv : P.unitSlope i = w at hitop
      induction w using WithBotTop.rec with
      | bot => exact absurd (hv ▸ rfl) (hb i)
      | coe r => exact ⟨r, rfl⟩
      | top => exact absurd rfl hitop
    by_cases htop : P.unitSlope (i + 1) = ⊤
    · exact ⟨a + 2, 1, one_pos, by rw [ha]; exact WithBotTop.coe_le_coe.2 (by linarith),
        by rw [htop]; exact le_top⟩
    obtain ⟨b, hbb⟩ : ∃ b : ℝ, P.unitSlope (i + 1) = (b : WithBotTop ℝ) := by
      generalize hv : P.unitSlope (i + 1) = w at htop
      induction w using WithBotTop.rec with
      | bot => exact absurd (hv ▸ rfl) (hb (i + 1))
      | coe r => exact ⟨r, rfl⟩
      | top => exact absurd rfl htop
    have hab : a < b := by rw [ha, hbb] at hi; exact WithBotTop.coe_lt_coe.1 hi
    exact ⟨(a + b) / 2, (b - a) / 4, by linarith,
      by rw [ha]; exact WithBotTop.coe_le_coe.2 (by linarith),
      by rw [hbb]; exact WithBotTop.coe_le_coe.2 (by linarith)⟩
  -- the margin hypotheses, propagated by convexity
  have hm₁ : ∀ t, t < i + 1 → P.unitSlope t ≤ ((σ - δ : ℝ) : WithBotTop ℝ) := fun t ht =>
    (P.unitSlope_mono (show t ≤ i by omega)).trans hσ₁
  have hm₂ : ∀ t, i + 1 ≤ t → ((σ + δ : ℝ) : WithBotTop ℝ) ≤ P.unitSlope t := fun t ht =>
    hσ₂.trans (P.unitSlope_mono ht)
  -- an `ε ≤ δ` that also fits under the point at `i + 1`
  obtain ⟨ε, hε0, hεδ, hεpt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧
      ((hval + ε : ℝ) : WithBotTop ℝ) ≤ pointHeight v (i + 1) := by
    by_cases hp : v (i + 1) = ⊤
    · exact ⟨δ, hδ, le_rfl, by rw [pointHeight_eq_top_iff.2 hp]; exact le_top⟩
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hp
    rw [pointHeight_coe hc.symm, Algebra.algebraMap_self_apply, WithBotTop.coe_lt_coe] at hcon
    refine ⟨min δ (c - hval), lt_min hδ (by linarith), min_le_left _ _, ?_⟩
    rw [pointHeight_coe hc.symm, Algebra.algebraMap_self_apply]
    exact WithBotTop.coe_le_coe.2 (by have := min_le_right δ (c - hval); linarith)
  -- the raised line lies on/below every point, so `line_le_height` puts it below the polygon
  have hline : ∀ n : ℕ,
      (((hval + ε - σ * (i + 1)) + σ * n : ℝ) : WithBotTop ℝ) ≤ pointHeight v n := by
    intro n
    rcases eq_or_ne n (i + 1) with rfl | hn
    · refine le_trans (le_of_eq ?_) hεpt
      norm_num
    · refine le_trans (WithBotTop.coe_le_coe.2 ?_)
        ((P.line_add_margin_le_height hx hb hδ.le hm₁ hm₂ hhval hn).trans (h.height_le n))
      push_cast
      linarith
  have := h.line_le_height hx hline (i + 1)
  rw [hhval] at this
  have hfin : hval + ε - σ * ((i : ℝ) + 1) + σ * ((i + 1 : ℕ) : ℝ) ≤ hval :=
    WithBotTop.coe_le_coe.1 this
  push_cast at hfin
  linarith

/-- **The polygon is `⊤` beyond the last point** ([Kob84, §IV.3 p. 97]: the polygon of a
polynomial ends at `(n, ord_p a_n)`).  Spec-level: a steep line through a finite height at `n`,
raised by `1`, would lie below every point.  (No `0 < n` hypothesis: at `n = 0` the sequence has
no points at all and `IsNewtonPolygonOf` is already unsatisfiable.) -/
theorem height_eq_top_of_forall_eq_top (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    {n : ℕ} (hv : ∀ k, n ≤ k → v k = ⊤) : P.height n = ⊤ := by
  classical
  by_contra hcon
  -- the height at `n` would be a genuine real number
  obtain ⟨hval, hhval⟩ : ∃ y : ℝ, P.height (n : ℤ) = (y : WithBotTop ℝ) := by
    have hbot := P.height_natCast_ne_bot hx n
    generalize hw : P.height (n : ℤ) = w at hbot hcon
    induction w using WithBotTop.rec with
    | bot => exact absurd rfl hbot
    | coe r => exact ⟨r, rfl⟩
    | top => exact absurd rfl hcon
  -- a slope steep enough that the line through `(n, hval + 1)` stays below the finitely many
  -- points left of `n`; beyond `n` there are no points at all
  set g : ℕ → ℝ := fun k => |hval + 1 - NewtonPolygon.toReal (pointHeight v k)| with hg
  set σ : ℝ := ∑ k ∈ range n, g k with hσ
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hσk : ∀ k, k < n → hval + 1 - NewtonPolygon.toReal (pointHeight v k) ≤ σ := fun k hk =>
    le_trans (le_abs_self _) (Finset.single_le_sum (f := g) (fun j _ => abs_nonneg _)
      (mem_range.2 hk))
  have hline : ∀ k : ℕ,
      (((hval + 1 - σ * n) + σ * k : ℝ) : WithBotTop ℝ) ≤ pointHeight v k := by
    intro k
    rcases le_or_gt n k with hk | hk
    · rw [pointHeight_eq_top_iff.2 (hv k hk)]; exact le_top
    by_cases hp : pointHeight v k = ⊤
    · rw [hp]; exact le_top
    obtain ⟨c, hc⟩ : ∃ c : ℝ, pointHeight v k = (c : WithBotTop ℝ) := by
      generalize hw : pointHeight v k = w at hp
      induction w using WithBotTop.rec with
      | bot => exact absurd hw (pointHeight_ne_bot v k)
      | coe r => exact ⟨r, rfl⟩
      | top => exact absurd rfl hp
    rw [hc]
    refine WithBotTop.coe_le_coe.2 ?_
    have hgk := hσk k hk
    rw [hc, NewtonPolygon.toReal_coe] at hgk
    have hnk : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
    nlinarith
  have hfin := h.line_le_height hx hline n
  rw [hhval] at hfin
  have : hval + 1 - σ * (n : ℝ) + σ * (n : ℝ) ≤ hval := WithBotTop.coe_le_coe.1 hfin
  linarith

/-- **Unbounded slopes from affine floors of every slope**: if for every real `σ` the points lie
on/above some line of slope `σ`, the slopes of the Newton polygon are unbounded.  (If all unit
slopes were `≤ σ`, the polygon would grow at most linearly with slope `σ`, but
`line_le_height` at slope `σ + 1` forces faster growth.) -/
theorem slopesUnbounded_of_forall_line (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hl : ∀ σ : ℝ, ∃ b : ℝ, ∀ k : ℕ, ((b + σ * k : ℝ) : WithBotTop ℝ) ≤ pointHeight v k) :
    P.SlopesUnbounded := by
  intro σ
  by_contra hcon
  push Not at hcon
  -- with every slope `≤ σ` no slope is `⊤`, so every height is the walked real value
  have hne : ∀ j : ℕ, P.unitSlope j ≠ ⊤ := fun j hj =>
    absurd (hj ▸ hcon j) (by simp)
  have hfin : ∀ k : ℕ, P.height (k : ℤ) = ((P.heightFun k : ℝ) : WithBotTop ℝ) := fun k =>
    P.height_natCast_eq_heightFun hx (P.height_natCast_ne_top_of_unitSlope hx fun j _ => hne j)
  -- the polygon then grows at rate at most `σ`
  have hgrow : ∀ k : ℕ, P.heightFun k ≤ P.heightFun 0 + σ * k := fun k => by
    have := P.heightFun_sub_le (Nat.zero_le k)
      (fun t _ _ => P.toReal_unitSlope_le_of_le (hb t) (hne t) (hcon t))
    simp only [Nat.cast_zero, sub_zero] at this
    linarith
  -- but the affine floor at slope `σ + 1` forces faster growth
  obtain ⟨b, hb'⟩ := hl (σ + 1)
  have hlow : ∀ k : ℕ, b + (σ + 1) * k ≤ P.heightFun k := fun k => by
    have := h.line_le_height hx hb' k
    rw [hfin k] at this
    exact WithBotTop.coe_le_coe.1 this
  set c : ℝ := P.heightFun 0 - b with hc
  have hall : ∀ k : ℕ, (k : ℝ) ≤ c := fun k => by
    have h1 := hlow k
    have h2 := hgrow k
    rw [hc]
    linarith
  have := hall (⌈c⌉₊ + 1)
  have hceil : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
  push_cast at this
  linarith

/-- The left endpoint of a face is a point of the sequence ([Ked07, proof of Cor. 2]). -/
theorem height_faceLeft_eq_pointHeight (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded) (σ : ℝ) :
    P.height (P.faceLeft σ) = pointHeight v (P.faceLeft σ) := by
  rcases Nat.eq_zero_or_pos (P.faceLeft σ) with hf | hf
  · rw [hf]; exact h.height_zero_eq hx
  obtain ⟨m, hm⟩ : ∃ m, P.faceLeft σ = m + 1 := ⟨P.faceLeft σ - 1, by omega⟩
  have hlt : P.unitSlope m < P.unitSlope (m + 1) :=
    lt_of_lt_of_le (P.unitSlope_lt_of_lt_faceLeft (by omega))
      (hm ▸ P.le_unitSlope_of_faceLeft_le hP le_rfl)
  rw [hm]
  exact h.height_eq_pointHeight_of_unitSlope_lt hx hb hlt

/-- The right endpoint of a face is a point of the sequence ([Ked07, proof of Cor. 2]). -/
theorem height_faceRight_eq_pointHeight (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded) (σ : ℝ) :
    P.height (P.faceRight σ) = pointHeight v (P.faceRight σ) := by
  rcases Nat.eq_zero_or_pos (P.faceRight σ) with hf | hf
  · rw [hf]; exact h.height_zero_eq hx
  obtain ⟨m, hm⟩ : ∃ m, P.faceRight σ = m + 1 := ⟨P.faceRight σ - 1, by omega⟩
  have hlt : P.unitSlope m < P.unitSlope (m + 1) :=
    lt_of_le_of_lt (P.unitSlope_le_of_lt_faceRight (by omega))
      (hm ▸ P.lt_unitSlope_of_faceRight_le hP le_rfl)
  rw [hm]
  exact h.height_eq_pointHeight_of_unitSlope_lt hx hb hlt

end IsNewtonPolygonOf

end
