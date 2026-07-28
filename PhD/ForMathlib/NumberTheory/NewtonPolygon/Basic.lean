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

/-- A (doubly-infinite) Newton polygon.

The segments are indexed by `ℤ`. The support records which indices carry a genuine segment: the
left end `support.1` is pinned to `0` (the polygon starts at the leftmost vertex, indexed `0`) or
`⊥` (the polygon is infinite to the left, where there is no canonical leftmost vertex); the right
end `support.2 : WithTop ℕ` is the index of the rightmost segment, or `⊤` if the polygon extends
right forever. Outside the support the data is junk: slopes are `⊤` past the right end and `⊥` past
the left end, and lengths are `0`. Fixing `support.1 = 0` cuts out the one-sided polygons (e.g. those
coming from power series), for which a simpler API can be developed. -/
structure NewtonPolygon where
  support : WithBotTop ℤ × WithTop ℕ
  support_left : support.1 = 0 ∨ support.1 = ⊥
  slopes : ℤ → WithBotTop ℝ
  slopes_junk_top : ∀ n : ℤ, ofRight support.2 < (n : WithBotTop ℤ) → slopes n = ⊤
  slopes_junk_bot : ∀ n : ℤ, (n : WithBotTop ℤ) < support.1 → slopes n = ⊥
  slopes_junk_interior : ∀ n : ℤ,
    ((n : WithBotTop ℤ) < ofRight support.2 → slopes n ≠ ⊤) ∧ (support.1 < (n : WithBotTop ℤ) → slopes n ≠ ⊥)
  lengths : ℤ → WithTop ℕ
  lengths_junk_top : ∀ n : ℤ, ofRight support.2 < (n : WithBotTop ℤ) → lengths n = 0
  lengths_junk_bot : ∀ n : ℤ, (n : WithBotTop ℤ) < support.1 → lengths n = 0
  lengths_junk_interior : ∀ n : ℤ,
    support.1 < (n : WithBotTop ℤ) ∧ (n : WithBotTop ℤ) < ofRight support.2 →
      0 < lengths n ∧ lengths n ≠ ⊤
  increasing : ∀ n, slopes n ≤ slopes (n + 1)
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
`support.1 = 0`: no segments lie to the left of the starting vertex. These are the polygons of
power series, and they admit the simpler `NewtonPolygon₀` description below. -/
def IsOneSided (NP : NewtonPolygon (Γ := Γ)) : Prop := NP.support.1 = 0

end NewtonPolygon

/-- A **one-sided** Newton polygon, given by a simpler `ℕ`-indexed structure. Segments are indexed
by `ℕ` starting at the leftmost vertex, so there is *no* left-hand junk to record and no `⊥`-vs-`0`
left endpoint to track: `support : WithTop ℕ` is just the number of segments (`⊤` if the polygon
extends to the right forever), and everything at index `≥ support` is junk. -/
structure NewtonPolygon₀ where
  support : WithTop ℕ
  slopes : ℕ → WithBotTop ℝ
  slopes_junk : ∀ n : ℕ, support ≤ (n : WithTop ℕ) → slopes n = ⊤
  slopes_ne_top : ∀ n : ℕ, (n + 1 : WithTop ℕ) < support → slopes n ≠ ⊤
  lengths : ℕ → WithTop ℕ
  lengths_junk : ∀ n : ℕ, support ≤ (n : WithTop ℕ) → lengths n = 0
  lengths_pos : ∀ n : ℕ, (n + 1 : WithTop ℕ) < support → 0 < lengths n ∧ lengths n ≠ ⊤
  -- The last length may be `⊤` (a ray) but not `0` — *unless* it is the only segment, since a
  -- single segment may have length `0` (e.g. constants). `n + 1 = support` picks out the last
  -- segment, `2 ≤ support` excludes the single-segment case. Disjoint from `lengths_pos` (`=` vs `<`).
  lengths_final : ∀ n : ℕ, (2 : WithTop ℕ) ≤ support → (n + 1 : WithTop ℕ) = support → lengths n ≠ 0
  increasing : ∀ n : ℕ, slopes n ≤ slopes (n + 1)
  starting_point : ℤ × Γ

namespace NewtonPolygon₀

variable (P : NewtonPolygon₀ (Γ := Γ))

/-- The index of the rightmost segment of `P` (`length - 1`, with `⊤ ↦ ⊤` and `0 ↦ 0`); this is the
right-hand support bound `support.2` of the associated `NewtonPolygon`. -/
def rightIndex : WithTop ℕ :=
  match P.support with
  | ⊤ => ⊤
  | (m : ℕ) => ((m - 1 : ℕ) : WithTop ℕ)

/-- Realise a one-sided polygon `P` as a genuine `NewtonPolygon`, embedding its `ℕ`-indexed data
into the bi-infinite `ℤ`-indexed structure: everything at `n < 0` is junk (`⊥` slopes, `0`
lengths), and `support = (0, P.rightIndex)`. The non-trivial obligations are left as `sorry` for
now; only `support_left` is discharged (it holds definitionally). -/
noncomputable def toNewtonPolygon : NewtonPolygon (Γ := Γ) where
  support := (0, P.rightIndex)
  support_left := Or.inl rfl
  slopes := fun n => if n < 0 then ⊥ else P.slopes n.toNat
  slopes_junk_top := by sorry
  slopes_junk_bot := by sorry
  slopes_junk_interior := by sorry
  lengths := fun n => if n < 0 then 0 else P.lengths n.toNat
  lengths_junk_top := by sorry
  lengths_junk_bot := by sorry
  lengths_junk_interior := by sorry
  increasing := by sorry
  starting_point := P.starting_point

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- The `NewtonPolygon` underlying a one-sided polygon is indeed one-sided. -/
lemma toNewtonPolygon_isOneSided : NewtonPolygon.IsOneSided P.toNewtonPolygon := rfl

end NewtonPolygon₀
