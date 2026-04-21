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

variable  (M F : Type*) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FunLike F M K] (v : F)
-- Given a polynomial we want a 3-tuple of a natural number and two functions indexing the wanted points

structure finset_Prod where
  n : ℕ -- number of points
  x : ℕ → M -- x values
  y : ℕ → M -- y values
  increasing : StrictMonoOn x (Set.Ico 0 n) -- We need to have the set be ordered in the x-axis with
    -- points having the same x value (maybe there is a nicer way to define this structure?)
    -- but this certainly is what the set arising from a polynomial/powerseries will look like

-- Note the below will not work for powerseries, so maybe need to think of a better approach

noncomputable
def Poly_set (f : Polynomial M) : finset_Prod K where
  n := Finset.card {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0}
  x := fun i => ((Finset.sort (· ≤ ·)
    {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0}).getD i 0).val
  y := fun i => if i < (Finset.card {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0})
                  then v (Polynomial.coeff f i)
                else v (Polynomial.coeff f 0)
  increasing := by
    -- should be immediate from definition
    sorry
  -- the junk value is to return to the first value (seems reasonable?)

end fun1

section fun2
/-
If we denote a finite set S in Prod K K by f_x : ℕ → K and f_y : ℕ → K indexing their
x and y points, with x values ordered, we want to compute its LowerConvexHull
-/
variable [Infinite K]
variable (N : ℕ) -- Size of our finite set, i.e. only care for i < N in f_x and f_y
variable (f_x : ℕ → K) (f_y : ℕ → K) [hx : Fact (StrictMonoOn (f_x) (Set.Ico 0 N))]
-- assuming the f_x is strictly mono; that is we have ordered our set

/- The set of slopes out of the point indexed by i -/
def Set_of_Slopes (i : ℕ) : Set K :=
  Set.image (fun j => (f_y j - f_y i) / (f_x j - f_x i)) {j | j < N ∧ i < j}

lemma Set_of_Slopes_nonempty (i : ℕ) (hi : i < N - 1) : Nonempty (Set_of_Slopes N f_x f_y i) := by
  simp_rw [Set_of_Slopes]
  refine Set.nonempty_iff_ne_empty'.mpr ?_
  have : {j | j < N ∧ i < j} ≠ ∅ := by
    contrapose hi
    simp only [ne_eq, not_not, not_lt, tsub_le_iff_right] at *
    by_contra h
    simp only [not_le] at h
    have : (i + 1) ∈ {j | j < N ∧ i < j} := by
      simpa
    aesop
  aesop

def Set_of_Slopes_isFinite (i : ℕ): Set.Finite (Set_of_Slopes N f_x f_y i) := by
  apply Set.Finite.image
  exact Set.Finite.sep (Set.finite_lt_nat N) (LT.lt i)

noncomputable
def Set_of_Slopes_isFinset (i : ℕ) : Finset K :=
  Set.Finite.toFinset (Set_of_Slopes_isFinite N f_x f_y i)

lemma Set_of_Slopes_ne (i : ℕ) : ∃ b : K, b ∉ Set_of_Slopes N f_x f_y i := by
  have := Set.Infinite.diff (by (expose_names; exact Set.infinite_univ_iff.mpr inst_3))
    (Set_of_Slopes_isFinite N f_x f_y i)
  contrapose this
  have : Set_of_Slopes N f_x f_y i = Set.univ := by
    aesop
  simp_all only [Set.mem_univ, not_true_eq_false, exists_const, not_false_eq_true, sdiff_self,
    Set.bot_eq_empty, Set.finite_empty, Set.Finite.not_infinite]

noncomputable
def MinSlope (i : ℕ) : K :=
  ((Finset.sort (· ≤ ·) (Set_of_Slopes_isFinset N f_x f_y i)).getD 0
    (Set_of_Slopes_ne N f_x f_y i).choose)
/- the junk value happens when 0 is outside the domain of the finset i.e. the set of slopes is empty
  this happens when there are no later points... so want a junk value to represent top?
  Later I find points which have
  ... for now choosing it from choice using Set_of_Slopes_ne, but this seems wrong and stupid

  -- Note alternatively I could choose the final point by choosing the cardinality of the set!
-/

lemma Set_of_Slopes_list_length (i : ℕ) (hi : i < N - 1) :
    0 < ((Finset.sort (· ≤ ·) (Set_of_Slopes_isFinset N f_x f_y i))).length := by
  simp only [Finset.length_sort, Finset.card_pos, Set_of_Slopes_isFinset]
  convert Set_of_Slopes_nonempty N f_x f_y i hi
  aesop

section Finset.sort

lemma Finset.sort.getElem_mem {α : Type*} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] [IsAntisymm α r] [IsTotal α r] (s : Finset α) (fallback : α)
    (n : ℕ) (hn : n < (Finset.sort r s).length) : (Finset.sort r s).getD n fallback ∈ s := by
  simp_all only [List.getD_eq_getElem?_getD, getElem?_pos, Option.getD_some]
  convert List.getElem_mem hn
  · aesop

lemma Finset.sort.range {α : Type*} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] [IsAntisymm α r] [IsTotal α r] (s : Finset α) (fallback : α) (n : ℕ) :
    (Finset.sort r s).getD n fallback = fallback ∨ (Finset.sort r s).getD n fallback ∈ s := by
  by_cases h : n < (Finset.sort r s).length
  · right; exact getElem_mem r s fallback n h
  · left; aesop

end Finset.sort

lemma MinSlope_exists (i : ℕ) (hi : i < N - 1) : ∃ a, a ∈ {j | j < N ∧ i < j} ∧
    (f_y a - f_y i) / (f_x a - f_x i) = MinSlope N f_x f_y i := by
  have : (Finset.sort (· ≤ ·) (Set_of_Slopes_isFinset N f_x f_y i)).getD 0
    (Set_of_Slopes_ne N f_x f_y i).choose ∈ Set_of_Slopes N f_x f_y i := by
    have := Finset.sort.getElem_mem (· ≤ ·) (Set_of_Slopes_isFinset N f_x f_y i)
      (Set_of_Slopes_ne N f_x f_y i).choose 0 (Set_of_Slopes_list_length N f_x f_y i hi)
    simp_rw [Set_of_Slopes_isFinset] at this
    aesop
  aesop

def NextPoint_potential (i : ℕ) : Set ℕ :=
  {j |  (f_y j - f_y i) / (f_x j - f_x i) = MinSlope N f_x f_y i} ∩ {j | j < N ∧ i < j}

lemma NextPoint_potential_nonempty (i : ℕ) (hi : i < N - 1) :
    Nonempty (NextPoint_potential N f_x f_y i) := by
  simp only [nonempty_subtype]
  simp_rw [NextPoint_potential]
  convert MinSlope_exists N f_x f_y i hi
  aesop

-- can show NextPoint_potential is non empty if i ≠ N - 1
-- since MinSlope returns Set_of_Slopes_ne... only if Set_of_slopes is empty
-- and Set_of_slopes is empty precisely when i = N - 1 (at least in the region we care about)

-- proof was initially done by aristotle... but I later found the lemmas myself and golfed to oblivion
def NextPoint_potential_isFinite (i : ℕ) : Set.Finite (NextPoint_potential N f_x f_y i) :=
  Set.Finite.inter_of_right (Set.finite_iff_bddAbove.mpr (bddAbove_def.mpr (by use N; grind))) _

noncomputable
def NextPoint_potential_isFinset (i : ℕ) : Finset ℕ :=
  Set.Finite.toFinset (NextPoint_potential_isFinite N f_x f_y i)

-- note this gives the index of the point!
noncomputable
def NextPoint (i : ℕ) : ℕ :=
  ((Finset.sort (· ≤ ·) (NextPoint_potential_isFinset N f_x f_y i)).getD 0 (N - 1))
  -- this gives the minimum x value which gives arise to the MinSlope
  -- if there are no j this corresponds to there being no slope... so we want to remain at our
  -- final point; that is N - 1

lemma NextPoint_final : NextPoint N f_x f_y (N - 1) = N - 1 := by
  have : (NextPoint_potential N f_x f_y (N - 1)) = ∅ := by
    simp_rw [NextPoint_potential]
    have : {j | j < N ∧ N - 1 < j} = ∅ := by
      grind
    aesop
  simp_rw [NextPoint, NextPoint_potential_isFinset, this]
  aesop

lemma NextPoint_terminal : ∃ b : ℕ, NextPoint N f_x f_y b = (N - 1) :=
  ⟨N - 1, NextPoint_final N f_x f_y⟩

lemma NextPoint_potential_list_length (i : ℕ) (hi : i < N - 1) :
    0 < ((Finset.sort (· ≤ ·) (NextPoint_potential_isFinset N f_x f_y i))).length := by
  simp only [Finset.length_sort, Finset.card_pos, NextPoint_potential_isFinset]
  convert NextPoint_potential_nonempty N f_x f_y i hi
  aesop

lemma NextPoint_subset (i : ℕ) (hi : i ∈ (Set.Ico 0 (Nat.find (NextPoint_terminal N f_x f_y))))
    : NextPoint N f_x f_y i ∈ {j | j < N ∧ i < j} := by
  simp_rw [NextPoint]
  have hi : i < N - 1 := by
    have : Nat.find (NextPoint_terminal N f_x f_y) ≤ N - 1 := by
      have := NextPoint_final N f_x f_y
      aesop
    calc
    _ <  Nat.find (NextPoint_terminal N f_x f_y) := by
      aesop
    _ ≤ _ := this
  have h := Finset.sort.getElem_mem (· ≤ ·) (NextPoint_potential_isFinset N f_x f_y i)
    i 0 (NextPoint_potential_list_length N f_x f_y i hi)
  have : NextPoint_potential N f_x f_y i ⊆ {j | j < N ∧ i < j} := by
    simp_rw [NextPoint_potential]
    aesop
  simp_rw [NextPoint_potential_isFinset, Set.Finite.mem_toFinset] at h ⊢
  grind

lemma NextPoint_max (i : ℕ) : NextPoint N f_x f_y i ≤ N - 1 := by
  simp_rw [NextPoint]
  rcases (Finset.sort.range (· ≤ ·) (NextPoint_potential_isFinset N f_x f_y i) (N - 1) 0) with h | h
  · aesop
  · have : NextPoint_potential N f_x f_y i ⊆ {j | j < N ∧ i < j} := by
      simp_rw [NextPoint_potential]
      aesop
    simp_rw [NextPoint_potential_isFinset, Set.Finite.mem_toFinset] at h ⊢
    grind --- note this is the samemethod as what was used in NextPoint_subset, extract?

noncomputable
def LCH_x : ℕ → K :=
  fun i => f_x (Nat.iterate (NextPoint N f_x f_y) i 0)

noncomputable
def LCH_y : ℕ → K :=
  fun i => f_y (Nat.iterate (NextPoint N f_x f_y) i 0)

lemma LCH_increasing : StrictMonoOn (LCH_x N f_x f_y)
    (Set.Ico 0 (Nat.find (NextPoint_terminal N f_x f_y) + 1)) := by
  by_cases t : N = 0
  · have : (Nat.find (NextPoint_terminal N f_x f_y)) = 0 := by
      have := NextPoint_final N f_x f_y
      aesop
    simp_rw [this]
    have : (Set.Ico 0 1) = {0} := by
      aesop
    simp only [this, Set.strictMonoOn_singleton]
  by_cases h : (Nat.find (NextPoint_terminal N f_x f_y)) = 0
  · simp_rw [h]
    have : (Set.Ico 0 1) = {0} := by
      aesop
    simp only [this, Set.strictMonoOn_singleton]
  unfold LCH_x
  suffices h : ∀ i : (Set.Ico 0 (Nat.find (NextPoint_terminal N f_x f_y))),
      (NextPoint N f_x f_y)^[i] 0 < (NextPoint N f_x f_y)^[i + 1] 0 by
    have max := NextPoint_max N f_x f_y
    simp_rw [StrictMonoOn] at ⊢
    intro a ha b hb hab
    have : (NextPoint N f_x f_y)^[a] 0 < (NextPoint N f_x f_y)^[b] 0 := by
      -- follows from h
      sorry
    have := hx.out
    simp_rw [StrictMonoOn] at this
    have (i : ℕ): ((NextPoint N f_x f_y)^[i] 0) ∈ Set.Ico 0 N := by
      induction' i with n hn
      · simp only [Function.iterate_zero, id_eq, Set.mem_Ico, le_refl, true_and]
        exact Nat.zero_lt_of_ne_zero t
      · simp_rw [Function.iterate_succ_apply']
        simp only [Set.mem_Ico, zero_le, true_and]
        specialize max ((NextPoint N f_x f_y)^[n] 0)
        refine (Nat.le_sub_one_iff_lt ?_).mp max
        exact Nat.zero_lt_of_ne_zero t
    have h1 := this ((NextPoint N f_x f_y)^[a] 0)
    have h2 := this ((NextPoint N f_x f_y)^[b] 0)
    aesop
  intro i
  simp_rw [Function.iterate_succ_apply']
  -- definitely true by construction of NextPoint



  /-
  have : (NextPoint N f_x f_y)^[↑i] 0 ∈ Set.Ico 0 (Nat.find (NextPoint_terminal N f_x f_y)) := by
    -- this is not actually true
    -- comparing different indices completely
    -- NextPoint is values in ℕ
    sorry
  have := NextPoint_subset N f_x f_y ((NextPoint N f_x f_y)^[↑i] 0) this
  aesop
  -/
  sorry

noncomputable
def LowerConvexHull_ofSet : LowerConvexHull K where
  n := Nat.find (NextPoint_terminal N f_x f_y) + 1
    -- note the + 1 as we want to allow the final point to be included
  x := LCH_x N f_x f_y
  y := LCH_y N f_x f_y
  increasing := LCH_increasing N f_x f_y
  convex := by

    sorry

end fun2

variable  (M F : Type*) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FunLike F M K] (v : F)

/-
The goal is to give a function that sends a Polynomial R to a lower convexhull.
To do this I want to write this as a composition of two functions.
Function 1. Sends a Polynomial to a finite set of points
         2. Sends a finite set of points to its lower convex hull

Function 1 should be straight forward... just do i ↦ (i, v(a_i))
  -- can probably leave it as a general function v for now
-/

noncomputable
def setOfPoly (f : Polynomial M) : finset_Prod K := Poly_set M F v f

noncomputable
def setToLCH (S : finset_Prod K) : LowerConvexHull K :=
  LowerConvexHull_ofSet S.n S.x S.y (hx := ⟨S.increasing⟩)

noncomputable
def NewtonPolygon (f : Polynomial M) : LowerConvexHull K :=
  setToLCH ((setOfPoly M F v) f)



/--
Huge problem. My whole set up of using Next Point is wrong!

The function
  noncomputable
  def LCH_x : ℕ → K :=
    fun i => f_x (Nat.iterate (NextPoint N f_x f_y) i 0)
is correct to use, but how I have implemented NextPoint_final is wrong

e.g.
  n := Nat.find (NextPoint_terminal N f_x f_y) + 1
is completely incorrect. Just because this is the final one does not mean that this is how many
iternations it will take to get to this point!!

Thus need to rework everything


-/
