/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.NewtonPolygons.OfSlopes
import PhD.NewtonPolygons.SpecConstruction

/-!
# Supporting lines for one-sided Newton polygons

Spec-level consequences of `IsNewtonPolygonOf` (the "greatest convex minorant" specification)
that the LWX slope analysis consumes:

* `IsNewtonPolygonOf.twoSlope_le_height` — the **competitor lemma**: a two-slope broken line
  lying on/below every point lies on/below the Newton polygon (instance of `isGreatest` with
  the competitor `ofSlopes`).  With equal slopes this is the supporting-line lemma
  `line_le_height`.
* the two facts the slope reading needs on top of `Height.lean`'s dictionary
  (`height_eq_heightFun`, `heightFun_succ`, `unitSlope_ne_top_of_height_ne_top`,
  `toReal_unitSlope_le`, `unitSlope_eq_top_of_height_eq_top`): the unit slope as a height
  increment (`unitSlope_eq_of_height_eq`) and the `⊥`-exclusion for constructed polygons
  (`newtonPolygon₀OfSeq_unitSlope_ne_bot`, from `OfSlopes.lean`'s `slopes_zero_ne_bot`), plus
  the `Monotone` packaging `monotone_toReal_unitSlope` that `ofSlopes` consumes.

Everything here is over `Γ = ℝ`; nothing depends on the LWX development.  Note the library
quirk that forces the `⊥` hypotheses: the degenerate one-point polygon (`support = 1`,
`lengths 0 = 0`, `slopes 0 = ⊥`) has *finite* height `y₀` at `x = 1` (the junk guard of
`rightHeight` only checks `⊤`), so a finite height does not exclude a `⊥` unit slope — only
the construction does.
-/

open Finset

noncomputable section

namespace NewtonPolygon₀

variable (P : NewtonPolygon₀ (Γ := ℝ))

/-- The unit slope is the height increment, for a unit slope that is not the `⊥` junk value
(`height_eq_heightFun` twice and `heightFun_succ`; `⊤` is excluded by the finite height at
`j + 1`). -/
theorem unitSlope_eq_of_height_eq (hx : P.starting_point.1 = 0) {j : ℕ}
    (hb : P.unitSlope j ≠ ⊥) {a c : ℝ} (hj : P.height (j : ℤ) = (a : WithBotTop ℝ))
    (hj1 : P.height ((j + 1 : ℕ) : ℤ) = (c : WithBotTop ℝ)) :
    P.unitSlope j = ((c - a : ℝ) : WithBotTop ℝ) := by
  have hj' : P.height (P.starting_point.1 + (j : ℤ)) ≠ ⊤ := by
    rw [hx, zero_add, hj]
    exact WithBotTop.coe_ne_top _
  have hj1' : P.height (P.starting_point.1 + ((j + 1 : ℕ) : ℤ)) ≠ ⊤ := by
    rw [hx, zero_add, hj1]
    exact WithBotTop.coe_ne_top _
  have e1 := P.height_eq_heightFun j hj'
  have e2 := P.height_eq_heightFun (j + 1) hj1'
  rw [hx, zero_add, hj] at e1
  rw [hx, zero_add, hj1] at e2
  have ha : a = P.heightFun j :=
    le_antisymm (WithBotTop.coe_le_coe.1 e1.le) (WithBotTop.coe_le_coe.1 e1.ge)
  have hc : c = P.heightFun (j + 1) :=
    le_antisymm (WithBotTop.coe_le_coe.1 e2.le) (WithBotTop.coe_le_coe.1 e2.ge)
  have ht : P.unitSlope j ≠ ⊤ := P.unitSlope_ne_top_of_height_ne_top hj1' (Nat.lt_succ_self j)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, P.unitSlope j = (r : WithBotTop ℝ) := by
    generalize hv : P.unitSlope j = w at hb ht
    induction w using WithBotTop.rec with
    | bot => exact absurd rfl hb
    | coe r => exact ⟨r, rfl⟩
    | top => exact absurd rfl ht
  rw [hr]
  congr 1
  rw [hc, ha, P.heightFun_succ, hr, NewtonPolygon.toReal_coe]
  ring

/-- With all heights finite (and no `⊥` slope), the real unit-slope sequence is monotone
(`toReal_unitSlope_le`). -/
theorem monotone_toReal_unitSlope (hx : P.starting_point.1 = 0)
    (hfin : ∀ k : ℕ, P.height k ≠ ⊤) :
    Monotone fun j ↦ NewtonPolygon.toReal (P.unitSlope j) := by
  intro i j hij
  refine P.toReal_unitSlope_le hij ?_
  refine P.unitSlope_ne_top_of_height_ne_top (c := j + 1) ?_ (Nat.lt_succ_self j)
  rw [hx, zero_add]
  exact hfin (j + 1)

end NewtonPolygon₀

/-- **The `⊥`-exclusion for constructed polygons**: the Newton polygon of an admissible sequence
has no `⊥` unit slope (`slopes_zero_ne_bot` for the first slope,
`slopes_zero_eq_bot_of_unitSlope_eq_bot` for the rest). -/
theorem newtonPolygon₀OfSeq_unitSlope_ne_bot (v : ℕ → WithTop ℝ) (h1 : ∃ i, v i ≠ ⊤)
    (h2 : IsAdmissible v) (j : ℕ) : (newtonPolygon₀OfSeq v).unitSlope j ≠ ⊥ := fun hbot ↦
  slopes_zero_ne_bot v h1 h2
    ((newtonPolygon₀OfSeq v).slopes_zero_eq_bot_of_unitSlope_eq_bot hbot).1

namespace IsNewtonPolygonOf

variable {v : ℕ → WithTop ℝ} {P : NewtonPolygon₀ (Γ := ℝ)}

private theorem monotone_twoSlope {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) (N : ℕ) :
    Monotone fun i : ℕ ↦ if i < N then s₁ else s₂ := by
  intro a b hab
  simp only
  split_ifs with ha hb hb
  · exact le_rfl
  · exact hs
  · omega
  · exact le_rfl

private theorem sum_twoSlope (s₁ s₂ : ℝ) (N k : ℕ) :
    ∑ i ∈ range k, (if i < N then s₁ else s₂) =
      s₁ * min (k : ℝ) N + s₂ * max ((k : ℝ) - N) 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    by_cases hk : k < N
    · have h1 : ((k : ℝ) + 1) ≤ N := by exact_mod_cast hk
      rw [if_pos hk, min_eq_left h1, min_eq_left (by linarith), max_eq_right (by linarith),
        max_eq_right (by linarith)]
      ring
    · have h1 : (N : ℝ) ≤ k := by exact_mod_cast not_lt.1 hk
      rw [if_neg hk, min_eq_right h1, min_eq_right (by linarith), max_eq_left (by linarith),
        max_eq_left (by linarith)]
      ring

/-- **The competitor lemma.** If the two-slope broken line
`y₀ + s₁·min(n, N) + s₂·max(n − N, 0)` (slopes `s₁ ≤ s₂`, break at `N`) lies on/below every
point of `v`, it lies on/below the Newton polygon of `v`. -/
theorem twoSlope_le_height (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    {y₀ s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) {N : ℕ}
    (hpts : ∀ n : ℕ,
      ((y₀ + s₁ * min (n : ℝ) N + s₂ * max ((n : ℝ) - N) 0 : ℝ) : WithBotTop ℝ) ≤
        pointHeight v n)
    (k : ℕ) :
    ((y₀ + s₁ * min (k : ℝ) N + s₂ * max ((k : ℝ) - N) 0 : ℝ) : WithBotTop ℝ) ≤
      P.height k := by
  set Q := NewtonPolygon₀.ofSlopes (fun i : ℕ ↦ if i < N then s₁ else s₂)
    (monotone_twoSlope hs N) y₀ with hQ
  have hQh : ∀ n : ℕ, Q.height n =
      ((y₀ + s₁ * min (n : ℝ) N + s₂ * max ((n : ℝ) - N) 0 : ℝ) : WithBotTop ℝ) := by
    intro n
    rw [hQ, NewtonPolygon₀.height_ofSlopes, sum_twoSlope, add_assoc]
  have hbelow : Q.IsBelow P :=
    h.isGreatest Q (by rw [hQ, NewtonPolygon₀.ofSlopes_starting_point, hx])
      (fun n ↦ by rw [hQh n]; exact hpts n)
  rw [← hQh k]
  exact NewtonPolygon₀.isBelow_iff_height.1 hbelow k

/-- **Supporting lines.** A line on/below every point lies on/below the Newton polygon. -/
theorem line_le_height (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0) {a b : ℝ}
    (hpts : ∀ n : ℕ, ((a + b * n : ℝ) : WithBotTop ℝ) ≤ pointHeight v n) (k : ℕ) :
    ((a + b * k : ℝ) : WithBotTop ℝ) ≤ P.height k := by
  have hsimp : ∀ n : ℕ,
      (a + b * min (n : ℝ) ((0 : ℕ) : ℝ) + b * max ((n : ℝ) - ((0 : ℕ) : ℝ)) 0 : ℝ) =
        a + b * n := by
    intro n
    rw [Nat.cast_zero, min_eq_right (Nat.cast_nonneg n), sub_zero,
      max_eq_left (Nat.cast_nonneg n)]
    ring
  have key := h.twoSlope_le_height hx (le_refl b) (N := 0) (y₀ := a)
    (fun n ↦ by rw [hsimp n]; exact hpts n) k
  rwa [hsimp k] at key

end IsNewtonPolygonOf

end
