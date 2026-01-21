import Mathlib

structure LowerConvexHull (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The number of points -/
  n : ℕ
  /-- `x j` is the x-coordinate of the `j`th point when `0 ≤ j < n`. -/
  x : ℕ → K --may need to add Top for slope of infinite length
  /-- `y j` is the y-coordinate of the `j`th point when `0 ≤ j < n`. -/
  y : ℕ → K
  -- also may want to switch the y function to a set of slopes; will still need a first y value
  /-- The x-coordinates are strictly increasing -/
  increasing : StrictMonoOn x (Set.Ico 0 n)
  /-- The Newton polygon is lower convex.
  This considers three successive points with indices `j`, `j+1` and `j+2`. -/
  -- We have a ≤ as we are allowing the slops to be the same for now.

  -- need to change this to <
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

/-- The slopes are strictly increasing. -/
lemma slope_MonotoneOn (U : LowerConvexHull K) : StrictMonoOn U.slope (Set.Ico 0 (U.n - 1)) := by
  refine strictMono_of_le_succ Set.ordConnected_Ico ?_ -- find name
  intro j hj₁ hj₂ hj₃
  simp only [slope]
  have h₁ : 0 < U.x (j + 1) - U.x j := U.length_pos hj₂
  have h₂ : 0 < U.x (j + 2) - U.x (j + 1) := U.length_pos hj₃
  simp +arith only [Nat.succ_eq_succ, Nat.succ_eq_add_one]
  rw [div_le_div_iff₀ h₁ h₂, ← sub_nonneg]
  have := U.convex j (by simp at hj₃; omega)
  rw [← sub_nonneg] at this
  convert this using 1
  ring
------------------------------------------------------------------------------------------------


/-
If we denote a finite set S in Prod K K by f_x : ℕ → K and f_y : ℕ → K indexing their
x and y points, with x values ordered, we want to compute its LowerConvexHull
-/
variable (N : ℕ) -- Size of our finite set, i.e. only care for i < N in f_x and f_y
variable (f_x : ℕ → K) (f_y : ℕ → K) [hx : Fact (StrictMonoOn (f_x) (Set.Ico 0 N))]

/- The set of slopes out of the point indexed by i -/
def Set_of_Slopes (i : ℕ) : Set K :=
  Set.image (fun j => (f_y j - f_y i) / (f_x j - f_x i)) {j | j < N ∧ i < j}

def Set_of_Slopes_isFinite (i : ℕ): Set.Finite (Set_of_Slopes N f_y f_x i) := by
  apply Set.Finite.image
  exact Set.Finite.sep (Set.finite_lt_nat N) (LT.lt i)

noncomputable
def Set_of_Slopes_isFinset (i : ℕ) : Finset K :=
  Set.Finite.toFinset (Set_of_Slopes_isFinite N f_y f_x i)

noncomputable
def MinSlope (i : ℕ) (Nonempty : Nonempty (Set_of_Slopes_isFinset N f_y f_x i)) : K := by
  refine Finset.min' (Set_of_Slopes_isFinset N f_y f_x i ) ?_
  exact Finset.nonempty_coe_sort.mp Nonempty

noncomputable
def NextPoint (i : ℕ) : ℕ :=
  letI := Classical.propDecidable (Nonempty (Set_of_Slopes_isFinset N f_y f_x i))
  if Nonempty : Nonempty (Set_of_Slopes_isFinset N f_y f_x i) then
    letI := Classical.propDecidable
      (∃ j : ℕ, i < j ∧ j < N ∧ (f_y j - f_y i) / (f_x j - f_x i) = MinSlope N f_x f_y i Nonempty)
    if h : ∃ j : ℕ, i < j ∧ j < N ∧ (f_y j - f_y i) / (f_x j - f_x i) = MinSlope N f_x f_y i Nonempty
      then Nat.find h -- need to find the maximum
    else N - 1 -- only non-empty when we are at the final point (i.e. N - 1)
  else N - 1 -- we remain at the final point we are interested in

noncomputable
def Index_x : ℕ → ℕ
  | 0 => 0
  | i + 1 => NextPoint N f_x f_y (Index_x i)

--the final point will always be at the largest x value in the original set
noncomputable
def LowerConvexHull_n (h : (∃ i,  Index_x N f_x f_y i = N - 1)) : ℕ :=
  Nat.find h

noncomputable
def LowerConvexHull_set : LowerConvexHull K where
  n := have h : (∃ i,  Index_x N f_x f_y i = N - 1) := by

        -- by our construction, as the index set is only finite
        sorry
    LowerConvexHull_n N f_x f_y h
  x := fun i => f_x (Index_x N f_x f_y i)
  y := fun i => f_y (Index_x N f_x f_y i)
  increasing := by
    refine StrictMono.strictMonoOn ?_ (Set.Ico 0 (LowerConvexHull_n N f_x f_y sorry))
    refine strictMono_nat_of_lt_succ ?_
    intro r
    cases r
    · unfold Index_x NextPoint
      simp only [nonempty_subtype]
      split
      · split
        · -- need to check constructions
          sorry
        · -- same as below
          sorry
      · -- what happens when N = 0... so need to do cases
        sorry
    ·
      -- this is only true for n < N, so we have lost information somewhere!
      sorry
  convex := by
    simp only
    intro i hi
    have h :
        (f_y (Index_x N f_x f_y (i+1)) - f_y (Index_x N f_x f_y i)) /
        (f_x (Index_x N f_x f_y (i+1)) - f_x (Index_x N f_x f_y i)) ≤
        (f_y (Index_x N f_x f_y (i+2)) - f_y (Index_x N f_x f_y i)) /
        (f_x (Index_x N f_x f_y (i+1)) - f_x (Index_x N f_x f_y i)) := by
      -- this is just showing the slope to a later point is greater; which worKs as both slopes are in
      -- the set of slopes and the first one is the min
      -- how to do this in lean?
      ring_nf
      obtain ⟨hx⟩ := hx
      simp only [le_neg_add_iff_add_le, add_sub_cancel]
      have : 0 < (f_x (Index_x N f_x f_y (i+1)) - f_x (Index_x N f_x f_y i)):= by
        sorry
      rw [mul_comm]
      simp_rw [← div_eq_inv_mul]
      simp only [div_le_div_iff_of_pos_right this]  -- why does this not worK?
      -- now we just need to show f_y is strictly mono; this is true by construction

      sorry
    have h1 :
        (f_y (Index_x N f_x f_y (i+1)) - f_y (Index_x N f_x f_y i)) *
        (f_x (Index_x N f_x f_y (i+2)) - f_x (Index_x N f_x f_y i)) ≤
        (f_y (Index_x N f_x f_y (i+2)) - f_y (Index_x N f_x f_y i)) *
        (f_x (Index_x N f_x f_y (i+1)) - f_x (Index_x N f_x f_y i)) := by
      -- multiply out at h

      sorry
    field_simp



    -- rearrange h1
    sorry

end LowerConvexHull

----------------------------------------------------------------------------------------------------
namespace NewtonPolygons

open Polynomial LowerConvexHull

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : Polynomial K)

/-
It thus remains to find `N`, `f_x`, `f_y` for polynomials, and show `f_x` is strictly mono
-/

def coeff_set : Set ℕ :=
  Set.image (fun i => i) {i | i ≤ degree f ∧ coeff f i ≠ 0 }

def coeff_set_is_finite : Set.Finite (coeff_set f) := by
  apply Set.Finite.image
  have : {i : ℕ | i ≤ degree f}.Finite := by
    cases degree f
    · simp only [le_bot_iff, WithBot.natCast_ne_bot, Set.setOf_false, Set.finite_empty]
    · -- exact Set.finite_lt_nat ?_ -- i am unsure how to not grey out the a†
      sorry
  exact Set.Finite.sep this (fun i => coeff f i ≠ 0)

/-- The number of coefficients that have non-zero coefficients-/
noncomputable
def Polynomial_N : ℕ :=
  (coeff_set_is_finite f).toFinset.card

noncomputable
def fun_x : ℕ → ℕ
  | 0 => letI := Classical.propDecidable (∃ n : ℕ, coeff f n ≠ 0)
         if h : ∃ n : ℕ, coeff f n ≠ 0 then (Nat.find h)
         else 0
  | i + 1 => letI := Classical.propDecidable (∃ n : ℕ, coeff f n ≠ 0 ∧ n > fun_x i)
             if h : ∃ n : ℕ, coeff f n ≠ 0 ∧ n > fun_x i then (Nat.find h)
             else 0

/- There may be a better way to show that this is the inclusion of the function fun_x into K -/
/-- The function indexing the first coord of the points in the relevant set to consider -/
noncomputable
def fun_x' : ℕ → K :=
  fun i => fun_x f i

/-- fun_x is strictly increasing -/
def fun_x.isMono : (StrictMonoOn (fun_x' f) (Set.Ico 0 (Polynomial_N f))) := by
  -- certainly true by construction; have coeff f fun_x (Polynomial_N f) ≠ 0 as fun_x (Polynomial_N f) = degree f
  rw [StrictMonoOn]
  simp only [Set.mem_Ico, zero_le, true_and]
  intro a ha b hb hab
  cases a
  ·
    sorry
  ·
    sorry


/-- The function indexing the second coord of the points in the relevant set to consider-/
noncomputable
def fun_y : ℕ → K :=
  fun i => coeff f (fun_x f i)

noncomputable
def NewtonPolygon : LowerConvexHull K :=
  LowerConvexHull_set (Polynomial_N f) (fun_x' f) (fun_y f) -- I thinK this is missing the requirement of strictly increasing



-- I think I want to change this section... I need Newton polygon to be a function from
-- polynomials (powerseries) to lower convex hull!



end NewtonPolygons
