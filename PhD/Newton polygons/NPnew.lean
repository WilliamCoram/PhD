import Mathlib

structure LowerConvexHull (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The number of points -/
  n : ℕ -- we will want to add a withTop ℕ to resolve for powerseries in the future
  /-- `x j` is the x-coordinate of the `j`th point when `0 ≤ j < n`. -/
  x : ℕ → K
  /-- `y j` is the y-coordinate of the `j`th point when `0 ≤ j < n`. -/
  y : ℕ → K
  /-- The x-coordinates are strictly increasing -/
  increasing : StrictMonoOn x (Set.Ico 0 n)
  /-- The Newton polygon is lower convex.
  This considers three successive points with indices `j`, `j+1` and `j+2`. -/
  -- We have a ≤ as we are allowing the slops to be the same for now.
  convex : ∀ j : ℕ, j + 2 ≤ n →
      x j * y (j + 2) + x (j + 1) * y j  + x (j + 2) * y (j + 1) <
        x j * y (j + 1) + x (j + 1) * y (j + 2) + x (j + 2) * y j

namespace LowerConvexHull

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The slopes of a lower convex hull. -/
def slope (U : LowerConvexHull K) (j : ℕ) : K :=
  (U.y (j + 1) - U.y j) / (U.x (j + 1) - U.x j)

/-- The segments have positive (projected) length. -/
lemma length_pos (U : LowerConvexHull K) {j : ℕ} (hj : j ∈ Set.Ico 0 (U.n - 1)) :
    0 < U.x (j + 1) - U.x j := by
  rw [sub_pos]
  simp only [Set.mem_Ico, zero_le, true_and] at hj
  refine U.increasing ?_ ?_ (lt_add_one j) <;> simp <;> omega

/-- The slopes are increasing. -/
lemma slope_MonotoneOn (U : LowerConvexHull K) : StrictMonoOn U.slope (Set.Ico 0 (U.n - 1)) := by
  refine strictMonoOn_of_lt_succ Set.ordConnected_Ico ?_
  intro j hj₁ hj₂ hj₃
  simp only [slope]
  have h₁ : 0 < U.x (j + 1) - U.x j := U.length_pos hj₂
  have h₂ : 0 < U.x (j + 2) - U.x (j + 1) := U.length_pos hj₃
  simp +arith only [Nat.succ_eq_succ, Nat.succ_eq_add_one]
  rw [div_lt_div_iff₀ h₁ h₂, ← sub_pos]
  have := U.convex j (by simp at hj₃; omega)
  rw [← sub_pos] at this
  convert this using 1
  ring
------------------------------------------------------------------------------------------------
/-
The goal is to give a function that sends a Polynomial R to a lower convexhull.
To do this I want to write this as a composition of two functions.
Function 1. Sends a Polynomial to a finite set of points
         2. Sends a finite set of points to its lower convex hull

Function 1 should be straight forward... just do i ↦ (i, v(a_i))
  -- can probably leave it as a general function v for now
-/

section fun1

variable  (M F : Type*) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FunLike F K M] (v : F)
-- Given a polynomial we want a 3-tuple of a natural number and two functions indexing the wanted points

structure finset_Prod where -- maybe theres a nicer way to be doing this
  n : ℕ -- number of points
  x : ℕ → ℕ -- x values
  y : ℕ → M -- y values

-- Note the below will not work for powerseries, so maybe need to think of a better approach

noncomputable
def Poly_set (f : Polynomial K) : finset_Prod M where
  n := Finset.card {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0}
  x := fun i => ((Finset.sort (· ≤ ·)
    {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0}).getD i 0).val
    -- copilot found this; need to work out if this seems fine practically to use
    -- note will not work for infinite set cases
    -- is 0 an okay junk value
  y := fun i => if i < (Finset.card {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0})
                  then v (Polynomial.coeff f i)
                else 0 -- maybe want a better junk value for this

end fun1


section fun2
/-
If we denote a finite set S in Prod K K by f_x : ℕ → K and f_y : ℕ → K indexing their
x and y points, with x values ordered, we want to compute its LowerConvexHull
-/
variable (N : ℕ) -- Size of our finite set, i.e. only care for i < N in f_x and f_y
variable (f_x : ℕ → K) (f_y : ℕ → K) [hx : Fact (StrictMonoOn (f_x) (Set.Ico 0 N))]


noncomputable
def NextPoint (i : ℕ) : ℕ :=

  sorry

end fun2

variable  (M F : Type*) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FunLike F K M] (v : F)

/-
The goal is to give a function that sends a Polynomial R to a lower convexhull.
To do this I want to write this as a composition of two functions.
Function 1. Sends a Polynomial to a finite set of points
         2. Sends a finite set of points to its lower convex hull

Function 1 should be straight forward... just do i ↦ (i, v(a_i))
  -- can probably leave it as a general function v for now
-/

-- will need to add more requirements on the R; i.e. normed ring

noncomputable
def setOfPoly : Polynomial K → finset_Prod M :=
  fun f => (Poly_set M F v f)

def setToLCH : (finset_Prod M) → (LowerConvexHull K) := by

  sorry

def NewtonPolygon : Polynomial K → LowerConvexHull K :=
  setToLCH K ∘ (setOfPoly M F v) -- why :(
