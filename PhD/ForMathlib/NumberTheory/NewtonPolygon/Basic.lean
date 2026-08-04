/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Order.WithBotTop

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ]

/-- Embed the right-hand support bound (`WithTop ℕ`) into `WithBotTop ℤ`, for comparison with the
`ℤ`-valued segment indices (`⊤ ↦ ⊤`, `k ↦ k`). -/
def ofRight : WithTop ℕ → WithBotTop ℤ
  | ⊤ => ⊤
  | (k : ℕ) => ((k : ℤ) : WithBotTop ℤ)

/-- An integer `n` to the right of `ofRight s` is nonnegative (as `s` only embeds naturals) and
satisfies the corresponding `WithTop ℕ` bound `s ≤ n.toNat`. -/
lemma ofRight_le_coe {s : WithTop ℕ} {n : ℤ} (h : ofRight s ≤ (n : WithBotTop ℤ)) :
    0 ≤ n ∧ s ≤ (n.toNat : WithTop ℕ) := by
  rcases s with _ | k
  · exact absurd (top_le_iff.mp h) (WithBotTop.coe_ne_top n)
  · have hk : (k : ℤ) ≤ n := WithBotTop.coe_le_coe.mp h
    exact ⟨by omega, WithTop.coe_le_coe.mpr (show k ≤ n.toNat by omega)⟩

/-- If the vertex one step right of an integer `n ≥ 0` is still strictly left of `ofRight s`,
then the corresponding `WithTop ℕ` bound `n.toNat + 1 < s` holds. -/
lemma coe_add_one_lt_ofRight {s : WithTop ℕ} {n : ℤ} (h0 : 0 ≤ n)
    (h : (n : WithBotTop ℤ) + 1 < ofRight s) : (n.toNat : WithTop ℕ) + 1 < s := by
  rcases s with _ | k
  · exact WithTop.coe_lt_top (n.toNat + 1)
  · have hk : n + 1 < (k : ℤ) := WithBotTop.coe_lt_coe.mp h
    exact WithTop.coe_lt_coe.mpr (show n.toNat + 1 < k by omega)

/-- Converse to `ofRight_le_coe` at natural indices: a `WithTop ℕ` bound `s ≤ m` pushes forward
to `ofRight s ≤ m` in `WithBotTop ℤ`. -/
lemma ofRight_le_natCast {s : WithTop ℕ} {m : ℕ} (h : s ≤ (m : WithTop ℕ)) :
    ofRight s ≤ ((m : ℤ) : WithBotTop ℤ) := by
  rcases s with _ | k
  · exact absurd (top_le_iff.mp h) WithTop.coe_ne_top
  · have hk : k ≤ m := WithTop.coe_le_coe.mp h
    exact WithBotTop.coe_le_coe.mpr (show (k : ℤ) ≤ (m : ℤ) by omega)

/-- Converse to `coe_add_one_lt_ofRight` at natural indices: a strict `WithTop ℕ` bound
`m + 1 < s` pushes forward to `m + 1 < ofRight s` in `WithBotTop ℤ`. -/
lemma natCast_add_one_lt_ofRight {s : WithTop ℕ} {m : ℕ} (h : (m : WithTop ℕ) + 1 < s) :
    ((m : ℤ) : WithBotTop ℤ) + 1 < ofRight s := by
  rcases s with _ | k
  · exact (WithBotTop.coe_ne_top ((m : ℤ) + 1)).lt_top
  · have hk : m + 1 < k := WithTop.coe_lt_coe.mp h
    exact WithBotTop.coe_lt_coe.mpr (show (m : ℤ) + 1 < (k : ℤ) by omega)

/-- A doubly-infinite Newton polygon. Where we either have infinite segments on the left or none. -/
structure NewtonPolygon where
  /-- Support indexing how many segments we have; `support.1` gives number of segments to the right
    and `support.2` indicates if there are 0 or infinitely many segments to the left. -/
  support : WithTop ℕ × ({0, ⊥} : Set (WithBotTop ℤ))
  /-- A function indexing the slopes of the segments; we care about the indices inside the support. -/
  slopes : ℤ → WithBotTop ℝ
  /-- Past the right end the slopes are junk, fixed to `⊤`. -/
  slopes_junkRight : ∀ n : ℤ, ofRight support.1 ≤ n → slopes n = ⊤
  /-- Past the left end the slopes are junk, fixed to `⊥`. -/
  slopes_junkLeft : ∀ n : ℤ, n < (support.2 : WithBotTop ℤ) → slopes n = ⊥
  /-- Any non final slope is finite -/
  slopes_nonFinal : ∀ n : ℤ, (support.2 : WithBotTop ℤ) ≤ n ∧ n + 1 < ofRight support.1 →
    ∃ a : ℝ, slopes n = some (some a)
  /-- Final slopes are only ⊤/⊥ if the support is (1,0). -/
  slopes_final : ∀ n : ℕ, n + 1 = support.1 ∧ (slopes n = ⊤ ∨ slopes n = ⊥) → support.1 = 1 ∧
    (support.2 : WithBotTop ℤ) = 0
  /-- Slopes are increasing. -/
  slopes_increasing : ∀ n, slopes n ≤ slopes (n + 1)
  /-- A function indexing the lengths of the segments. -/
  lengths : ℤ → WithTop ℕ
  /-- Past the right end the lengths are junk; fixed to be 0. -/
  lengths_junkRight : ∀ n : ℤ, ofRight support.1 ≤ n → lengths n = 0
  /-- Past the left end the lengths are junk; fixed to be 0. -/
  lengths_junkLeft : ∀ n : ℤ, n < (support.2 : WithBotTop ℤ) → lengths n = 0
  /-- Any non final length is finite and non-zero. -/
  lengths_nonFinal : ∀ n : ℤ, (support.2 : WithBotTop ℤ) ≤ n ∧ n + 1 < ofRight support.1 →
    ∃ a : ℕ, a ≠ 0 ∧ lengths n = some a
  /-- Final lengths are only 0 if the support is (1,0), and then the slope is junk (`⊤`/`⊥`):
  a zero-width segment never carries an honest real slope. -/
  lengths_final : ∀ n : ℕ, n + 1 = support.1 ∧ lengths n = 0 → support.1 = 1 ∧
    (support.2 : WithBotTop ℤ) = 0 ∧ (slopes n = ⊤ ∨ slopes n = ⊥)
  /-- Starting point of the Newton polygon. -/
  starting_point : ℤ × Γ

namespace NewtonPolygon

/-- The real number carried by a `WithBotTop ℝ`, with both `⊤` and `⊥` sent to the junk value
`0`. This is only ever applied on the honest, real-valued part of a polygon. -/
def toReal (x : WithBotTop ℝ) : ℝ := WithBotTop.rec (motive := fun _ => ℝ) 0 (fun a => a) 0 x

@[simp] lemma toReal_coe (r : ℝ) : toReal (r : WithBotTop ℝ) = r := rfl
@[simp] lemma toReal_top : toReal (⊤ : WithBotTop ℝ) = 0 := rfl
@[simp] lemma toReal_bot : toReal (⊥ : WithBotTop ℝ) = 0 := rfl

variable (NP : NewtonPolygon (Γ := Γ))

/-- Worker for `rightSlope`, marching one unit interval at a time to the right of the starting
vertex `x₀`.

Picture a token sitting on the polygon and stepping right in unit intervals. At every moment it is
inside some segment, and the arguments record its state:
* `n` — the index of the segment the token is currently in;
* `r` — how many further unit intervals of segment `n` still lie to the *right* of the token, so
  `r = 0` means the token is on the last unit of segment `n`, about to cross a vertex;
* the final argument `j` — how many unit steps the token must still take to reach its target.

`rightSlopeAux NP n r j` is then the slope of whichever segment the token lands in after those `j`
steps. It is started by `rightSlope` at `n = 0` and `r = (length of segment 0) - 1` (the token
begins on the first of that segment's units, so all but that one lie ahead).

The design choice is to carry `r` explicitly rather than recompute vertex positions from cumulative
sums of `lengths`. That turns the walk into a plain structural recursion on `j` — every branch
below recurses with `j` strictly smaller — so termination is automatic, and it avoids doing any
arithmetic on the `WithTop ℕ` lengths (which can be `⊤`).

Worked example: segment `0` of width `2` (slope `s₀`) followed by segment `1` of width `1`
(slope `s₁`). `rightSlope` starts the token at `(n, r) = (0, 1)`, and the offsets unfold as
```
  rightSlope 0 = rightSlopeAux 0 1 0                        = s₀   -- base case, in segment 0
  rightSlope 1 = rightSlopeAux 0 1 1 → rightSlopeAux 0 0 0  = s₀   -- one step, still in segment 0
  rightSlope 2 = rightSlopeAux 0 1 2 → 0 0 1 → 1 0 0        = s₁   -- r hits 0, cross into segment 1
```
so the two units of segment `0` (offsets `0, 1`) report `s₀` and the first unit of segment `1`
(offset `2`) reports `s₁`, exactly as the polygon is drawn. -/
def rightSlopeAux (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) (r : ℕ) : ℕ → WithBotTop ℝ
  -- No steps left: the token has arrived, and it is sitting in segment `n`.
  | 0 => NP.slopes n
  | j + 1 =>
    match r with
    -- At least one more unit of segment `n` lies ahead: step right, stay in `n`, one fewer ahead.
    | r + 1 => rightSlopeAux NP n r j
    -- On the last unit of segment `n`: the next step crosses the vertex into segment `n + 1`,
    -- and its length decides what happens.
    | 0 =>
      match NP.lengths (n + 1) with
      -- Infinite length: `n + 1` is a final ray covering this offset and everything to its right,
      -- so its slope is the answer no matter how many steps remain — short-circuit here.
      | ⊤ => NP.slopes (n + 1)
      -- Finite width `w + 1`: enter `n + 1` on its first unit, leaving `w` units ahead of us.
      | (w + 1 : ℕ) => rightSlopeAux NP (n + 1) w j
      -- Width `0`. This only arises in the junk region past a terminating polygon, where every
      -- length is `0` and every slope is `⊤`. We deliberately do *not* guard against it: the token
      -- keeps sliding through these empty segments (still decrementing `j`), and the base case
      -- returns their `⊤` slope. Simpler than a special case, and yields exactly the intended `⊤`.
      | (0 : ℕ) => rightSlopeAux NP (n + 1) 0 j

/-- The slope of the polygon on the unit interval `[x₀ + j, x₀ + j + 1]`, `j` steps to the right
of the starting vertex `x₀`. In the junk region to the right of the support this is `⊤`.

Segment `0` is where the token starts, and its length fixes the initial `r` passed to
`rightSlopeAux`: a finite length `w + 1` leaves `w` units ahead of the starting unit; an infinite
length (`⊤`, a ray leaving `x₀` directly) means segment `0`'s slope already governs every offset;
a `0` length is the degenerate "nothing to the right of `x₀`" case, caught by the same junk
fall-through described in `rightSlopeAux`. -/
def rightSlope (j : ℕ) : WithBotTop ℝ :=
  match NP.lengths 0 with
  | ⊤ => NP.slopes 0
  | (w + 1 : ℕ) => NP.rightSlopeAux 0 w j
  | (0 : ℕ) => NP.rightSlopeAux 0 0 j

/-- Worker for `leftSlope`: the exact mirror image of `rightSlopeAux` (see there for the token
picture and the meaning of `n`, `r`, `j`). The only differences are that the token walks *left*, so
crossing a vertex moves to segment `n - 1` rather than `n + 1`, and the junk value on this side is
`⊥` (unbounded below) rather than `⊤`. -/
def leftSlopeAux (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) (r : ℕ) : ℕ → WithBotTop ℝ
  -- No steps left: the token has arrived, sitting in segment `n`.
  | 0 => NP.slopes n
  | j + 1 =>
    match r with
    -- At least one more unit of segment `n` lies ahead (to the left): step, stay in `n`.
    | r + 1 => leftSlopeAux NP n r j
    -- On the last unit of segment `n`: the next step crosses into segment `n - 1`.
    | 0 =>
      match NP.lengths (n - 1) with
      | ⊤ => NP.slopes (n - 1)                     -- `n - 1` is a leftward ray: its slope wins.
      | (w + 1 : ℕ) => leftSlopeAux NP (n - 1) w j  -- finite width `w + 1`: enter it, `w` ahead.
      | (0 : ℕ) => leftSlopeAux NP (n - 1) 0 j      -- width `0`: slide through the left junk (`⊥`).

/-- The slope of the polygon on the unit interval `[x₀ - j - 1, x₀ - j]`, `j` steps to the left of
the starting vertex `x₀` (so `leftSlope 0` is the slope of segment `-1`). In the junk region to
the left of the support this is `⊥`. -/
def leftSlope (j : ℕ) : WithBotTop ℝ :=
  match NP.lengths (-1) with
  | ⊤ => NP.slopes (-1)
  | (w + 1 : ℕ) => NP.leftSlopeAux (-1) w j
  | (0 : ℕ) => NP.leftSlopeAux (-1) 0 j

/-- The height of the starting vertex, its `Γ`-valued `y`-coordinate pushed into `ℝ`. -/
def startHeight : ℝ := algebraMap Γ ℝ NP.starting_point.2

/-- The `y`-value `k` integer steps to the right of the starting vertex: the starting height plus
the accumulated unit slopes. It is `⊤` once we cross into the right-hand junk region (detected by
the incoming unit slope `rightSlope (k - 1)` being `⊤`). -/
noncomputable def rightHeight (k : ℕ) : WithBotTop ℝ :=
  if 1 ≤ k ∧ NP.rightSlope (k - 1) = ⊤ then ⊤
  else ((NP.startHeight + ∑ i ∈ Finset.range k, toReal (NP.rightSlope i) : ℝ) : WithBotTop ℝ)

/-- The `y`-value `k` integer steps to the left of the starting vertex: the starting height minus
the accumulated unit slopes. It is `⊥` once we cross into the left-hand junk region (unbounded
below), detected by the incoming unit slope `leftSlope (k - 1)` being `⊥`. -/
noncomputable def leftHeight (k : ℕ) : WithBotTop ℝ :=
  if 1 ≤ k ∧ NP.leftSlope (k - 1) = ⊥ then ⊥
  else ((NP.startHeight - ∑ i ∈ Finset.range k, toReal (NP.leftSlope i) : ℝ) : WithBotTop ℝ)

/-- The `y`-value of the Newton polygon at the integer `x`-coordinate `x`.

Starting from the vertex `x₀ = NP.starting_point.1` we progress along the unit slopes: to the
right we accumulate them, to the left we subtract them. On the honest support this is the real
height (viewed in `WithBotTop ℝ`); to the right of a terminating polygon it is `⊤`, and to the
left of an unbounded-below polygon it is `⊥`. Final rays (segments of infinite length) are
extended indefinitely. -/
noncomputable def height (x : ℤ) : WithBotTop ℝ :=
  if 0 ≤ x - NP.starting_point.1 then NP.rightHeight (x - NP.starting_point.1).toNat
  else NP.leftHeight (NP.starting_point.1 - x).toNat

/-- The `y`-value at the starting vertex `x₀` is exactly the starting height: the right-hand
accumulation is empty and the junk guard is off. -/
@[simp] lemma height_startingPoint :
    NP.height NP.starting_point.1 = (NP.startHeight : WithBotTop ℝ) := by
  simp [height, rightHeight]

/-- `IsBelow NP₁ NP₂` says the polygon `NP₁` lies (weakly) below `NP₂`: at every integer
`x`-coordinate its height is `≤` that of `NP₂`, measured in `WithBotTop ℝ` (so `⊥`/`⊤` junk
regions compare in the expected way). Since the vertices of both polygons sit at integer
`x`-coordinates, each polygon is affine on every unit interval `[n, n + 1]`, and hence comparing
the heights at the integers is equivalent to comparing them at all real `x`. -/
def IsBelow (NP₁ NP₂ : NewtonPolygon (Γ := Γ)) : Prop := ∀ x : ℤ, NP₁.height x ≤ NP₂.height x

@[refl]
lemma IsBelow.refl (NP : NewtonPolygon (Γ := Γ)) : IsBelow NP NP := fun _ => le_refl _

lemma IsBelow.rfl {NP : NewtonPolygon (Γ := Γ)} : IsBelow NP NP := IsBelow.refl NP

lemma IsBelow.trans {NP₁ NP₂ NP₃ : NewtonPolygon (Γ := Γ)}
    (h₁ : IsBelow NP₁ NP₂) (h₂ : IsBelow NP₂ NP₃) : IsBelow NP₁ NP₃ :=
  fun x => (h₁ x).trans (h₂ x)

/-- A Newton polygon is *one-sided* (left-finite) when it starts at its leftmost vertex, i.e.
the left indicator `support.2` is `0` rather than `⊥`: no segments lie to the left of the
starting vertex. These are the polygons of power series, and they admit the simpler
`NewtonPolygon₀` description below. -/
def IsOneSided (NP : NewtonPolygon (Γ := Γ)) : Prop := (NP.support.2 : WithBotTop ℤ) = 0

end NewtonPolygon

/-- A one-sided `NewtonPolygon`. -/
structure NewtonPolygon₀ where
  /-- Number of segments we have. -/
  support : WithTop ℕ
  /-- A function indexing the slopes of the segments, we care about the indexes < support. -/
  slopes : ℕ → WithBotTop ℝ
  /-- Outside the support the slopes are fixed to be ⊤ -/
  slopes_junk : ∀ n : ℕ, support ≤ n → slopes n = ⊤
  /-- Any non final slope is finite -/
  slopes_nonFinal : ∀ n : ℕ, n + 1 < support → ∃ a : ℝ, slopes n = some (some a)
  /-- Final slopes are only ⊤/⊥ if the support is 1 -/
  slopes_final : ∀ n : ℕ, n + 1 = support ∧ (slopes n = ⊤ ∨ slopes n = ⊥) → support = 1
  /-- Slopes are increasing. -/
  slopes_increasing : ∀ n : ℕ, slopes n ≤ slopes (n + 1)
  /-- A function indexing the lengths of the segments. -/
  lengths : ℕ → WithTop ℕ
  /-- Outside the support the slopes are fixed to be 0. -/
  lengths_junk : ∀ n : ℕ, support ≤ n → lengths n = 0
  /-- Any non final length is finite and non-zero. -/
  lengths_nonFinal : ∀ n : ℕ, n + 1 < support → ∃ a : ℕ, a ≠ 0 ∧ lengths n = some a
  /-- Final lengths are only 0 if the support is 1, and then the slope is junk (`⊤`/`⊥`):
  a zero-width segment never carries an honest real slope. -/
  lengths_final : ∀ n : ℕ, n + 1 = support ∧ lengths n = 0 →
    support = 1 ∧ (slopes n = ⊤ ∨ slopes n = ⊥)
  /-- Starting point of the Newton polygon. -/
  starting_point : ℤ × Γ

namespace NewtonPolygon₀

variable (P : NewtonPolygon₀ (Γ := Γ))

/-- Realise a one-sided polygon `P` as a genuine `NewtonPolygon`, embedding its `ℕ`-indexed data
into the bi-infinite `ℤ`-indexed structure: everything at `n < 0` is junk (`⊥` slopes, `0`
lengths), the right-hand support is the segment count `P.support`, and the left indicator is `0`
(no segments to the left). -/
def toNewtonPolygon : NewtonPolygon (Γ := Γ) where
  support := (P.support, ⟨0, Set.mem_insert 0 {⊥}⟩)
  slopes := fun n => if n < 0 then ⊥ else P.slopes n.toNat
  slopes_junkRight := by
    intro n hn
    obtain ⟨h0, hs⟩ := ofRight_le_coe hn
    rw [if_neg (not_lt.2 h0)]
    exact P.slopes_junk _ hs
  slopes_junkLeft := fun n hn => if_pos (WithBotTop.coe_lt_coe.mp hn)
  slopes_nonFinal := by
    rintro n ⟨h1, h2⟩
    have h0 : (0 : ℤ) ≤ n := WithBotTop.coe_le_coe.mp h1
    rw [if_neg (not_lt.2 h0)]
    exact P.slopes_nonFinal _ (coe_add_one_lt_ofRight h0 h2)
  slopes_final := by
    rintro n ⟨h1, h2⟩
    rw [if_neg (not_lt.2 (Int.natCast_nonneg n)), Int.toNat_natCast] at h2
    exact ⟨P.slopes_final n ⟨h1, h2⟩, rfl⟩
  slopes_increasing := by
    intro n
    by_cases hn : n < 0
    · rw [if_pos hn]
      exact bot_le
    · rw [if_neg hn, if_neg (show ¬ n + 1 < 0 by omega),
        show (n + 1).toNat = n.toNat + 1 by omega]
      exact P.slopes_increasing n.toNat
  lengths := fun n => if n < 0 then 0 else P.lengths n.toNat
  lengths_junkRight := by
    intro n hn
    obtain ⟨h0, hs⟩ := ofRight_le_coe hn
    rw [if_neg (not_lt.2 h0)]
    exact P.lengths_junk _ hs
  lengths_junkLeft := fun n hn => if_pos (WithBotTop.coe_lt_coe.mp hn)
  lengths_nonFinal := by
    rintro n ⟨h1, h2⟩
    have h0 : (0 : ℤ) ≤ n := WithBotTop.coe_le_coe.mp h1
    rw [if_neg (not_lt.2 h0)]
    exact P.lengths_nonFinal _ (coe_add_one_lt_ofRight h0 h2)
  lengths_final := by
    rintro n ⟨h1, h2⟩
    rw [if_neg (not_lt.2 (Int.natCast_nonneg n)), Int.toNat_natCast] at h2
    obtain ⟨hs, hj⟩ := P.lengths_final n ⟨h1, h2⟩
    refine ⟨hs, rfl, ?_⟩
    rwa [if_neg (not_lt.2 (Int.natCast_nonneg n)), Int.toNat_natCast]
  starting_point := P.starting_point

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- The `NewtonPolygon` underlying a one-sided polygon is indeed one-sided. -/
lemma toNewtonPolygon_isOneSided : NewtonPolygon.IsOneSided P.toNewtonPolygon := rfl

/-! The embedding `toNewtonPolygon` is transparent over the natural indices: the following simp
lemmas strip it away, so the doubly-infinite `height`/`IsBelow` theory can be used for one-sided
polygons directly, with nothing lost. -/

section
omit [CommSemiring Γ] [Algebra Γ ℝ]

@[simp] lemma toNewtonPolygon_support_fst : P.toNewtonPolygon.support.1 = P.support := rfl

@[simp] lemma toNewtonPolygon_startingPoint :
    P.toNewtonPolygon.starting_point = P.starting_point := rfl

@[simp] lemma toNewtonPolygon_slopes_natCast (n : ℕ) :
    P.toNewtonPolygon.slopes (n : ℤ) = P.slopes n := by
  show (if (n : ℤ) < 0 then ⊥ else P.slopes (n : ℤ).toNat) = P.slopes n
  rw [if_neg (not_lt.2 (Int.natCast_nonneg n)), Int.toNat_natCast]

@[simp] lemma toNewtonPolygon_slopes_of_neg {x : ℤ} (hx : x < 0) :
    P.toNewtonPolygon.slopes x = ⊥ := if_pos hx

@[simp] lemma toNewtonPolygon_lengths_natCast (n : ℕ) :
    P.toNewtonPolygon.lengths (n : ℤ) = P.lengths n := by
  show (if (n : ℤ) < 0 then 0 else P.lengths (n : ℤ).toNat) = P.lengths n
  rw [if_neg (not_lt.2 (Int.natCast_nonneg n)), Int.toNat_natCast]

@[simp] lemma toNewtonPolygon_lengths_of_neg {x : ℤ} (hx : x < 0) :
    P.toNewtonPolygon.lengths x = 0 := if_pos hx

end

/-- The height of a one-sided polygon at an integer `x`, through the embedding into
doubly-infinite polygons. Right of the starting vertex this is the walked value; strictly left of
it the polygon is junk and the height is `⊥` (so `IsBelow` constrains nothing there). -/
noncomputable def height (x : ℤ) : WithBotTop ℝ := P.toNewtonPolygon.height x

@[simp] lemma height_toNewtonPolygon (x : ℤ) : P.toNewtonPolygon.height x = P.height x := rfl

/-- `IsBelow P₁ P₂` says the one-sided polygon `P₁` lies (weakly) below `P₂` at every integer
`x`-coordinate, defined by pulling `NewtonPolygon.IsBelow` back along `toNewtonPolygon` — so
agreement with the doubly-infinite notion is definitional (`isBelow_iff`). -/
def IsBelow (P₁ P₂ : NewtonPolygon₀ (Γ := Γ)) : Prop :=
  NewtonPolygon.IsBelow P₁.toNewtonPolygon P₂.toNewtonPolygon

/-- The one-sided `IsBelow` agrees, definitionally, with the doubly-infinite one under the
embedding. -/
lemma isBelow_iff {P₁ P₂ : NewtonPolygon₀ (Γ := Γ)} :
    IsBelow P₁ P₂ ↔ NewtonPolygon.IsBelow P₁.toNewtonPolygon P₂.toNewtonPolygon := Iff.rfl

lemma isBelow_iff_height {P₁ P₂ : NewtonPolygon₀ (Γ := Γ)} :
    IsBelow P₁ P₂ ↔ ∀ x : ℤ, P₁.height x ≤ P₂.height x := Iff.rfl

@[refl]
lemma IsBelow.refl (P : NewtonPolygon₀ (Γ := Γ)) : IsBelow P P := NewtonPolygon.IsBelow.refl _

lemma IsBelow.rfl {P : NewtonPolygon₀ (Γ := Γ)} : IsBelow P P := IsBelow.refl P

lemma IsBelow.trans {P₁ P₂ P₃ : NewtonPolygon₀ (Γ := Γ)} (h₁ : IsBelow P₁ P₂)
    (h₂ : IsBelow P₂ P₃) : IsBelow P₁ P₃ :=
  NewtonPolygon.IsBelow.trans h₁ h₂

end NewtonPolygon₀

namespace NewtonPolygon.IsOneSided

/-- Strip a one-sided `NewtonPolygon` back down to a `NewtonPolygon₀`: restrict the `ℤ`-indexed
data to the natural indices, with `support` the right-hand segment count `support.1`. Everything
discarded was junk (`support.2 = 0` pins the junk region to the negative indices). Converse to
`NewtonPolygon₀.toNewtonPolygon`. -/
def toNewtonPolygon₀ {NP : NewtonPolygon (Γ := Γ)} (h : NP.IsOneSided) :
    NewtonPolygon₀ (Γ := Γ) where
  support := NP.support.1
  slopes := fun n => NP.slopes n
  slopes_junk := fun n hn => NP.slopes_junkRight n (ofRight_le_natCast hn)
  slopes_nonFinal := by
    intro n hn
    have h0 : (NP.support.2 : WithBotTop ℤ) = 0 := h
    refine NP.slopes_nonFinal n ⟨?_, natCast_add_one_lt_ofRight hn⟩
    rw [h0]
    exact WithBotTop.coe_le_coe.mpr (Int.natCast_nonneg n)
  slopes_final := fun n hn => (NP.slopes_final n hn).1
  slopes_increasing := fun n => NP.slopes_increasing n
  lengths := fun n => NP.lengths n
  lengths_junk := fun n hn => NP.lengths_junkRight n (ofRight_le_natCast hn)
  lengths_nonFinal := by
    intro n hn
    have h0 : (NP.support.2 : WithBotTop ℤ) = 0 := h
    refine NP.lengths_nonFinal n ⟨?_, natCast_add_one_lt_ofRight hn⟩
    rw [h0]
    exact WithBotTop.coe_le_coe.mpr (Int.natCast_nonneg n)
  lengths_final := fun n hn => ⟨(NP.lengths_final n hn).1, (NP.lengths_final n hn).2.2⟩
  starting_point := NP.starting_point

end NewtonPolygon.IsOneSided

/-! ### Finite Newton polygons

A polygon is *finite* when it has finitely many segments (their lengths may still be infinite: a
final ray counts as one segment). Finite polygons are in particular one-sided, and the one-sided
polygons are exactly the image of `NewtonPolygon₀.toNewtonPolygon` — re-embedding the extracted
one-sided data recovers the original polygon on the nose. -/

section IsFinite

omit [CommSemiring Γ] [Algebra Γ ℝ]

/-- Two doubly-infinite Newton polygons agree once their data fields agree (the `Prop` fields
carry no information). -/
@[ext] lemma NewtonPolygon.ext {NP₁ NP₂ : NewtonPolygon (Γ := Γ)}
    (hsupport : NP₁.support = NP₂.support) (hslopes : NP₁.slopes = NP₂.slopes)
    (hlengths : NP₁.lengths = NP₂.lengths)
    (hstart : NP₁.starting_point = NP₂.starting_point) : NP₁ = NP₂ := by
  obtain ⟨s₁, sl₁, _, _, _, _, _, l₁, _, _, _, _, sp₁⟩ := NP₁
  obtain ⟨s₂, sl₂, _, _, _, _, _, l₂, _, _, _, _, sp₂⟩ := NP₂
  have e1 : s₁ = s₂ := hsupport
  have e2 : sl₁ = sl₂ := hslopes
  have e3 : l₁ = l₂ := hlengths
  have e4 : sp₁ = sp₂ := hstart
  subst e1; subst e2; subst e3; subst e4
  rfl

/-- Two one-sided Newton polygons agree once their data fields agree. -/
@[ext] lemma NewtonPolygon₀.ext {P₁ P₂ : NewtonPolygon₀ (Γ := Γ)}
    (hsupport : P₁.support = P₂.support) (hslopes : P₁.slopes = P₂.slopes)
    (hlengths : P₁.lengths = P₂.lengths)
    (hstart : P₁.starting_point = P₂.starting_point) : P₁ = P₂ := by
  obtain ⟨s₁, sl₁, _, _, _, _, l₁, _, _, _, sp₁⟩ := P₁
  obtain ⟨s₂, sl₂, _, _, _, _, l₂, _, _, _, sp₂⟩ := P₂
  have e1 : s₁ = s₂ := hsupport
  have e2 : sl₁ = sl₂ := hslopes
  have e3 : l₁ = l₂ := hlengths
  have e4 : sp₁ = sp₂ := hstart
  subst e1; subst e2; subst e3; subst e4
  rfl

/-- A doubly-infinite Newton polygon is *finite* when it has finitely many segments: none to the
left (it is one-sided) and finitely many to the right (`support.1 ≠ ⊤`). -/
def NewtonPolygon.IsFinite (NP : NewtonPolygon (Γ := Γ)) : Prop :=
  NP.IsOneSided ∧ NP.support.1 ≠ ⊤

/-- A one-sided Newton polygon is *finite* when its segment count is finite. -/
def NewtonPolygon₀.IsFinite (P : NewtonPolygon₀ (Γ := Γ)) : Prop :=
  P.support ≠ ⊤

/-- Re-embedding the one-sided data extracted from a one-sided polygon recovers the polygon:
the one-sided polygons are exactly the image of `NewtonPolygon₀.toNewtonPolygon`. -/
lemma NewtonPolygon.IsOneSided.toNewtonPolygon₀_toNewtonPolygon {NP : NewtonPolygon (Γ := Γ)}
    (h : NP.IsOneSided) : h.toNewtonPolygon₀.toNewtonPolygon = NP := by
  have h' : (NP.support.2 : WithBotTop ℤ) = 0 := h
  refine NewtonPolygon.ext (Prod.ext rfl (Subtype.ext h'.symm)) ?_ ?_ rfl
  · funext x
    show (if x < 0 then (⊥ : WithBotTop ℝ) else NP.slopes (x.toNat : ℤ)) = NP.slopes x
    by_cases hx : x < 0
    · rw [if_pos hx]
      exact (NP.slopes_junkLeft x (by rw [h']; exact WithBotTop.coe_lt_coe.mpr hx)).symm
    · rw [if_neg hx, Int.toNat_of_nonneg (not_lt.1 hx)]
  · funext x
    show (if x < 0 then (0 : WithTop ℕ) else NP.lengths (x.toNat : ℤ)) = NP.lengths x
    by_cases hx : x < 0
    · rw [if_pos hx]
      exact (NP.lengths_junkLeft x (by rw [h']; exact WithBotTop.coe_lt_coe.mpr hx)).symm
    · rw [if_neg hx, Int.toNat_of_nonneg (not_lt.1 hx)]

/-- Extracting the one-sided data back out of the embedding recovers the original polygon. -/
lemma NewtonPolygon₀.toNewtonPolygon_toNewtonPolygon₀ (P : NewtonPolygon₀ (Γ := Γ))
    (h : P.toNewtonPolygon.IsOneSided) : h.toNewtonPolygon₀ = P := by
  refine NewtonPolygon₀.ext rfl ?_ ?_ rfl
  · funext n
    exact P.toNewtonPolygon_slopes_natCast n
  · funext n
    exact P.toNewtonPolygon_lengths_natCast n

/-- The embedding of a one-sided polygon is finite iff the polygon is. -/
@[simp] lemma NewtonPolygon₀.toNewtonPolygon_isFinite {P : NewtonPolygon₀ (Γ := Γ)} :
    P.toNewtonPolygon.IsFinite ↔ P.IsFinite :=
  ⟨fun h => h.2, fun h => ⟨P.toNewtonPolygon_isOneSided, h⟩⟩

/-- Every one-sided Newton polygon is represented by a `NewtonPolygon₀`. -/
lemma NewtonPolygon.IsOneSided.exists_newtonPolygon₀ {NP : NewtonPolygon (Γ := Γ)}
    (h : NP.IsOneSided) : ∃ P : NewtonPolygon₀ (Γ := Γ), P.toNewtonPolygon = NP :=
  ⟨h.toNewtonPolygon₀, h.toNewtonPolygon₀_toNewtonPolygon⟩

/-- Every finite Newton polygon is represented by a `NewtonPolygon₀`, necessarily with finitely
many segments. -/
lemma NewtonPolygon.IsFinite.exists_newtonPolygon₀ {NP : NewtonPolygon (Γ := Γ)}
    (h : NP.IsFinite) :
    ∃ P : NewtonPolygon₀ (Γ := Γ), P.IsFinite ∧ P.toNewtonPolygon = NP :=
  ⟨h.1.toNewtonPolygon₀, h.2, h.1.toNewtonPolygon₀_toNewtonPolygon⟩

end IsFinite
