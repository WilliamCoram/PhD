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
  convex : ∀ j : ℕ, j + 2 < n →
      -- note this was originally ≤ n... but surely it has to be <
      -- (as this allows x (j+2)) to make sense
      x j * y (j + 2) + x (j + 1) * y j  + x (j + 2) * y (j + 1) ≤
        x j * y (j + 1) + x (j + 1) * y (j + 2) + x (j + 2) * y j
    -- note this convex condition is just saying that from the point j, the slope to j+1 is ≤
    -- the slope to j+2.

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

/-- The slopes are increasing. -/ -- again not strict for now!
lemma slope_MonotoneOn (U : LowerConvexHull K) : MonotoneOn U.slope (Set.Ico 0 (U.n - 1)) := by
  refine monotoneOn_of_le_succ Set.ordConnected_Ico ?_
  intro j hj₁ hj₂ hj₃
  simp only [slope]
  have h₁ : 0 < U.x (j + 1) - U.x j := U.length_pos hj₂
  have h₂ : 0 < U.x (j + 2) - U.x (j + 1) := U.length_pos hj₃
  simp +arith only [Nat.succ_eq_succ, Nat.succ_eq_add_one]
  rw [div_le_div_iff₀ h₁ h₂, ← sub_nonpos]
  have := U.convex j (by simp at hj₃; omega)
  rw [← sub_nonpos] at this
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

-- Note the below will not work for powerseries, so maybe need to think of a better approach later

-- fixed from an aristotle proof that did not work
noncomputable
def Poly_set (f : Polynomial M) : finset_Prod K where
  n := Finset.card {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0}
  x := fun i => ((Finset.sort (· ≤ ·)
    {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0}).getD i 0)
  y := fun i => if i < (Finset.card {b : Fin (f.natDegree + 1) | Polynomial.coeff f b ≠ 0})
                  then v (Polynomial.coeff f i)
                else v (Polynomial.coeff f 0)
                -- the junk value is to return to the first value (seems reasonable?)
  increasing i hi j hj hij := by
    -- this was adjusted from an aristotle proof which didnt work
    have h_sorted : List.Pairwise (fun x y => x < y) (Finset.sort (· ≤ ·)
        (Finset.filter (fun b : Fin (f.natDegree + 1) ↦ f.coeff b.val ≠ 0) Finset.univ)) :=
      Finset.sort_sorted_lt _
    have hi' : i < (Finset.sort (· ≤ ·) {b : Fin (f.natDegree + 1) | f.coeff ↑b ≠ 0}).length := by
      aesop
    have hj' : j < (Finset.sort (· ≤ ·) {b : Fin (f.natDegree + 1) | f.coeff ↑b ≠ 0}).length := by
      aesop
    convert  List.pairwise_iff_get.mp h_sorted ⟨i, hi'⟩ ⟨j, hj'⟩ hij
    all_goals aesop
    -- would like to extract but could not get the set up to work outside of the structure
    -- i.e. lean would complain about things not begin infered

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

omit [LinearOrder K] [IsStrictOrderedRing K] [Infinite K] hx in
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

-- this was initially proven by Aristotle
omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Set_of_Slopes_ne (i : ℕ) : ∃ b : K, b ∉ Set_of_Slopes N f_x f_y i := by
  have := Set.Infinite.diff (by (expose_names; exact Set.infinite_univ_iff.mpr inst_1))
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

omit [IsStrictOrderedRing K] [Infinite K] hx in
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

omit [IsStrictOrderedRing K] hx in
lemma MinSlope_exists (i : ℕ) (hi : i < N - 1) : ∃ a, a ∈ {j | j < N ∧ i < j} ∧
    (f_y a - f_y i) / (f_x a - f_x i) = MinSlope N f_x f_y i := by
  have : (Finset.sort (· ≤ ·) (Set_of_Slopes_isFinset N f_x f_y i)).getD 0
    (Set_of_Slopes_ne N f_x f_y i).choose ∈ Set_of_Slopes N f_x f_y i := by
    have := Finset.sort.getElem_mem (· ≤ ·) (Set_of_Slopes_isFinset N f_x f_y i)
      (Set_of_Slopes_ne N f_x f_y i).choose 0 (Set_of_Slopes_list_length N f_x f_y i hi)
    simp_rw [Set_of_Slopes_isFinset] at this
    aesop
  aesop

omit [IsStrictOrderedRing K] hx in
-- proof by aristotle then tidied up
lemma MinSlope_min (i : ℕ) (m : K) (hm : m ∈ Set_of_Slopes N f_x f_y i) :
    MinSlope N f_x f_y i ≤ m := by
  have h_sorted : ∀ {l : List K}, List.Sorted (· ≤ ·) l → ∀ m ∈ l, l.getD 0
      (Classical.choose (Set_of_Slopes_ne N f_x f_y i)) ≤ m := by
    intro l hl m hm
    induction l <;> aesop
  convert h_sorted _ m _
  · exact Finset.sort_sorted _ _
  · exact Finset.mem_sort ( · ≤ · ) |>.2
      (Set.Finite.mem_toFinset (Set_of_Slopes_isFinite N f_x f_y i ) |>.2 hm )

def NextPoint_potential (i : ℕ) : Set ℕ :=
  {j |  (f_y j - f_y i) / (f_x j - f_x i) = MinSlope N f_x f_y i} ∩ {j | j < N ∧ i < j}

omit [IsStrictOrderedRing K] hx in
lemma NextPoint_potential_nonempty (i : ℕ) (hi : i < N - 1) :
    Nonempty (NextPoint_potential N f_x f_y i) := by
  simp only [nonempty_subtype]
  simp_rw [NextPoint_potential]
  convert MinSlope_exists N f_x f_y i hi
  aesop

omit [IsStrictOrderedRing K] hx in
lemma NextPoint_empty (i : ℕ) (hi : N - 1 ≤ i) : (NextPoint_potential N f_x f_y i) = ∅ := by
  simp_rw [NextPoint_potential]
  have : {j | j < N ∧ N - 1 < j} = ∅ := by
    grind
  grind

def NextPoint_potential_isFinite (i : ℕ) : Set.Finite (NextPoint_potential N f_x f_y i) :=
  Set.Finite.inter_of_right (Set.finite_iff_bddAbove.mpr (bddAbove_def.mpr (by use N; grind))) _

noncomputable
def NextPoint_potential_isFinset (i : ℕ) : Finset ℕ :=
  Set.Finite.toFinset (NextPoint_potential_isFinite N f_x f_y i)

omit [IsStrictOrderedRing K] hx in
lemma NextPoint_potential_list_length (i : ℕ) (hi : i < N - 1) :
    0 < ((Finset.sort (· ≤ ·) (NextPoint_potential_isFinset N f_x f_y i))).length := by
  simp only [Finset.length_sort, Finset.card_pos, NextPoint_potential_isFinset]
  convert NextPoint_potential_nonempty N f_x f_y i hi
  aesop

noncomputable
def NextPoint (i : ℕ) : ℕ :=
  ((Finset.sort (· ≤ ·) (NextPoint_potential_isFinset N f_x f_y i)).getD 0 (N - 1))
  -- this gives the minimum x value which gives arise to the MinSlope
  -- if there are no j this corresponds to there being no slope... so we want to remain at our
  -- final point; that is N - 1

lemma NextPoint_element (i : ℕ) (hi : i < N - 1) :
    NextPoint N f_x f_y i ∈ NextPoint_potential N f_x f_y i := by
  simp_rw [NextPoint]
  have := NextPoint_potential_nonempty N f_x f_y i hi
  convert Finset.sort.getElem_mem (fun x1 x2 ↦ x1 ≤ x2) (NextPoint_potential_isFinset N f_x f_y i)
      (N - 1) 0 (NextPoint_potential_list_length N f_x f_y i hi)
  simp_rw [NextPoint_potential_isFinset]
  aesop

omit [IsStrictOrderedRing K] hx in
lemma NextPoint_subset (i : ℕ) (hi : i < N - 1) : NextPoint N f_x f_y i ∈ {j | j < N ∧ i < j} := by
  simp_rw [NextPoint]
  have h := Finset.sort.getElem_mem (· ≤ ·) (NextPoint_potential_isFinset N f_x f_y i)
    i 0 (NextPoint_potential_list_length N f_x f_y i hi)
  have : NextPoint_potential N f_x f_y i ⊆ {j | j < N ∧ i < j} := by
    simp_rw [NextPoint_potential]
    aesop
  simp_rw [NextPoint_potential_isFinset, Set.Finite.mem_toFinset] at h ⊢
  grind

omit [IsStrictOrderedRing K] hx in
lemma NextPoint_increasing (i : ℕ) (hi : i < N - 1) : i < NextPoint N f_x f_y i := by
  have := NextPoint_subset N f_x f_y i hi
  aesop

omit [IsStrictOrderedRing K] hx in
lemma NextPoint_max (i : ℕ) : NextPoint N f_x f_y i ≤ N - 1 := by
  simp_rw [NextPoint]
  rcases (Finset.sort.range (· ≤ ·) (NextPoint_potential_isFinset N f_x f_y i) (N - 1) 0) with h | h
  · aesop
  · have : NextPoint_potential N f_x f_y i ⊆ {j | j < N ∧ i < j} := by
      simp_rw [NextPoint_potential]
      aesop
    simp_rw [NextPoint_potential_isFinset, Set.Finite.mem_toFinset] at h ⊢
    grind --- note this is the same method as what was used in NextPoint_subset, extract?

omit [IsStrictOrderedRing K] hx in
lemma NextPoint_max' (i : ℕ) : Nat.iterate (NextPoint N f_x f_y) i 0 ≤ N -1 := by
  induction' i with n hn
  · aesop
  · simp only [Function.iterate_succ', Function.comp_apply]
    exact NextPoint_max N f_x f_y ((NextPoint N f_x f_y)^[n] 0)

noncomputable
def LCH_x : ℕ → K :=
  fun i => f_x (Nat.iterate (NextPoint N f_x f_y) i 0)

omit [IsStrictOrderedRing K] hx in
-- we are eventually at our final point.
lemma FinalIndex : ∃ a : ℕ, Nat.iterate (NextPoint N f_x f_y) a 0 = N - 1 := by
  /- This is true by construction. If we are not at our final point we have to choose a later point
    which gives the minimum slope, this is further along the x-axis.
    The size of the set of potenial next points is strictly decreasing (until empty), so eventually
    we will be left with the empty set (note in reality one will eventually choose the final point
    as the next point - but we can argue this with Nat.find instead).
    -/
  by_cases triv1 : N = 0
  · use 0; aesop
  by_cases triv2 : N = 1
  · use 0; aesop
  by_contra h
  simp only [not_exists, ← ne_eq] at h
  have h : ∀ x, (NextPoint N f_x f_y)^[x] 0 < N - 1 := by -- why we need 2 ≤ N
    intro a
    specialize h a
    have := NextPoint_max' N f_x f_y a
    grind
  have inc (i : ℕ) : (NextPoint N f_x f_y)^[i] 0 < (NextPoint N f_x f_y)^[i+1] 0 := by
    simp only [Function.iterate_succ', Function.comp_apply]
    exact NextPoint_increasing N f_x f_y ((NextPoint N f_x f_y)^[i] 0) (h i)
  apply strictMono_nat_of_lt_succ at inc
  have := StrictMono.not_bddAbove_range_of_wellFoundedLT inc
  have : BddAbove (Set.range fun n ↦ (NextPoint N f_x f_y)^[n] 0) := by
    refine bddAbove_def.mpr ?_
    use N-1
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact fun a ↦ NextPoint_max' N f_x f_y a
  aesop

lemma test (i : ℕ) (hi : i < (Nat.find (FinalIndex N f_x f_y))) :
    (NextPoint N f_x f_y)^[i] 0 < N - 1 := by
  contrapose hi
  simp only [Nat.lt_find_iff, not_forall, Decidable.not_not, exists_prop]
  simp only [not_lt] at hi
  use i
  simp only [le_refl, true_and]
  exact Nat.le_antisymm (NextPoint_max' N f_x f_y i) hi

lemma NextPoint_increasing' (i : ℕ) (hi : i < (Nat.find (FinalIndex N f_x f_y))) :
    (NextPoint N f_x f_y)^[i] 0 < (NextPoint N f_x f_y)^[i+1] 0 := by
  simp only [Function.iterate_succ', Function.comp_apply]
  refine NextPoint_increasing N f_x f_y ((NextPoint N f_x f_y)^[i] 0) ?_
  exact test N f_x f_y i (by grind)

lemma LCH_increasing : StrictMonoOn (LCH_x N f_x f_y)
    (Set.Ico 0 (Nat.find (FinalIndex N f_x f_y) + 1)) := by
  by_cases t : N = 0
  · have : Nat.find (FinalIndex N f_x f_y) = 0 := by
      aesop
    simp_rw [this]
    have : (Set.Ico 0 1) = {0} := by
      aesop
    simp only [this, Set.strictMonoOn_singleton]
  by_cases h : Nat.find (FinalIndex N f_x f_y) = 0
  · simp_rw [h]
    have : (Set.Ico 0 1) = {0} := by
      grind
    simp only [this, Set.strictMonoOn_singleton]
  unfold LCH_x
  suffices h : ∀ i : (Set.Ico 0 (Nat.find (FinalIndex N f_x f_y))),
      (NextPoint N f_x f_y)^[i] 0 < (NextPoint N f_x f_y)^[i + 1] 0 by
    have max := NextPoint_max N f_x f_y
    refine strictMonoOn_of_lt_succ (Set.ordConnected_Ico) ?_
    intro a ha ha' ha''
    have : a ∈ Set.Ico 0 (Nat.find (FinalIndex N f_x f_y)) := by
      simp only [Nat.succ_eq_succ, Nat.succ_eq_add_one] at ha''
      aesop
    specialize h ⟨a, this⟩
    simp only [Nat.succ_eq_succ, Nat.succ_eq_add_one]
    have Final := hx.out
    simp_rw [StrictMonoOn] at Final
    have (i : ℕ) : ((NextPoint N f_x f_y)^[i] 0) ∈ Set.Ico 0 N := by
      have := NextPoint_max' N f_x f_y i
      grind
    have h1 := this a
    have h2 := this (a+1)
    aesop
  intro i
  exact NextPoint_increasing' N f_x f_y i (by grind)

noncomputable
def LCH_y : ℕ → K :=
  fun i => f_y (Nat.iterate (NextPoint N f_x f_y) i 0)

lemma test1 (j : ℕ) (hj : j < (Nat.find (FinalIndex N f_x f_y))) :
    (f_y ((NextPoint N f_x f_y)^[j + 1] 0) - f_y ((NextPoint N f_x f_y)^[j] 0)) /
    (f_x ((NextPoint N f_x f_y)^[j + 1] 0) - f_x ((NextPoint N f_x f_y)^[j] 0)) =
    MinSlope N f_x f_y ((NextPoint N f_x f_y)^[j] 0) := by
  have := NextPoint_element N f_x f_y (((NextPoint N f_x f_y)^[j] 0)) (test N f_x f_y j hj)
  simp_rw [NextPoint_potential] at this
  have := Set.mem_of_mem_inter_left this
  simp only [Set.mem_setOf_eq] at this
  simp only [Function.iterate_succ', Function.comp_apply, this]

lemma hmm : 0 / 0 = 0 := by
  exact rfl
  -- note this means that in test1 I can actually remove the hj assumption!
  -- as NextPoint is set to remain at N-1 after this region!!
  -- Perhaps want to decide if it is worth proving this or not
  -- there is probably a lot of extra (pointless?) API I could make if wanted.
  -- e.g. Lemma saying that NextPoint is constant outside of region

lemma bar : ∀ (j : ℕ), j + 2 < Nat.find (FinalIndex N f_x f_y) + 1 →
    LCH_x N f_x f_y j * LCH_y N f_x f_y (j + 2) + LCH_x N f_x f_y (j + 1) * LCH_y N f_x f_y j +
      LCH_x N f_x f_y (j + 2) * LCH_y N f_x f_y (j + 1) ≤
    LCH_x N f_x f_y j * LCH_y N f_x f_y (j + 1) + LCH_x N f_x f_y (j + 1) * LCH_y N f_x f_y (j + 2) +
      LCH_x N f_x f_y (j + 2) * LCH_y N f_x f_y j := by
  by_cases H : N = 0
  · have : Nat.find (FinalIndex N f_x f_y) = 0 := by
      aesop
    grind
  by_cases H' : N = 1
  · have : Nat.find (FinalIndex N f_x f_y) = 0 := by
      aesop
    grind
  -- Want to break apart into N at least 2 so that we can have prove hj1 and hj2
  -- perhaps a better/different way to do this
  intro j hj
  simp_rw [LCH_x, LCH_y]
  suffices ((f_y ((NextPoint N f_x f_y)^[j+1] 0)) - (f_y ((NextPoint N f_x f_y)^[j] 0))) /
      ((f_x ((NextPoint N f_x f_y)^[j+1] 0)) - (f_x ((NextPoint N f_x f_y)^[j] 0))) ≤
      ((f_y ((NextPoint N f_x f_y)^[j+2] 0)) - (f_y ((NextPoint N f_x f_y)^[j] 0))) /
      ((f_x ((NextPoint N f_x f_y)^[j+2] 0)) - (f_x ((NextPoint N f_x f_y)^[j] 0))) by
    have t1 : 0 < (f_x ((NextPoint N f_x f_y)^[j + 1] 0) - f_x ((NextPoint N f_x f_y)^[j] 0)) := by
      simp only [sub_pos]
      have hj1 : ((NextPoint N f_x f_y)^[j] 0) ∈ Set.Ico 0 N := by
        have := NextPoint_max' N f_x f_y j
        grind
      have hj2 : ((NextPoint N f_x f_y)^[j+1] 0) ∈ Set.Ico 0 N := by
        have := NextPoint_max' N f_x f_y (j+1)
        grind
      exact hx.out hj1 hj2 (NextPoint_increasing' N f_x f_y j (by grind))
    have t2 : 0 < (f_x ((NextPoint N f_x f_y)^[j + 2] 0) - f_x ((NextPoint N f_x f_y)^[j] 0)) := by
      simp only [sub_pos]
      have hj1 : ((NextPoint N f_x f_y)^[j] 0) ∈ Set.Ico 0 N := by
        have := NextPoint_max' N f_x f_y j
        grind
      have hj3 : ((NextPoint N f_x f_y)^[j+2] 0) ∈ Set.Ico 0 N := by
        have := NextPoint_max' N f_x f_y (j+2)
        grind
        -- can almost certainly extract this as I have used it 5 times!!
        -- Need a decision on whether it replaces NextPoint_max etc?
      refine hx.out hj1 hj3 ?_
      trans (NextPoint N f_x f_y)^[j+1] 0
      · exact NextPoint_increasing' N f_x f_y j (by grind)
      · exact NextPoint_increasing' N f_x f_y (j+1) (by grind)
    field_simp at this -- clears denominators
    linarith -- :D very happy this just works
  have minslope : ((f_y ((NextPoint N f_x f_y)^[j+1] 0)) - (f_y ((NextPoint N f_x f_y)^[j] 0))) /
      ((f_x ((NextPoint N f_x f_y)^[j+1] 0)) - (f_x ((NextPoint N f_x f_y)^[j] 0))) =
      MinSlope N f_x f_y ((NextPoint N f_x f_y)^[j] 0) := by
    exact test1 N f_x f_y j (by grind)
  rw [minslope]
  refine MinSlope_min N f_x f_y ((NextPoint N f_x f_y)^[j] 0)
    ((f_y ((NextPoint N f_x f_y)^[j + 2] 0) - f_y ((NextPoint N f_x f_y)^[j] 0)) /
    (f_x ((NextPoint N f_x f_y)^[j + 2] 0) - f_x ((NextPoint N f_x f_y)^[j] 0))) ?_
  simp_rw [Set_of_Slopes]
  simp only [Set.mem_image, Set.mem_setOf_eq]
  use (NextPoint N f_x f_y)^[j+2] 0
  constructor
  · constructor
    · have := NextPoint_max' N f_x f_y (j+2)
      grind
    · have h1 := NextPoint_increasing N f_x f_y ((NextPoint N f_x f_y)^[j+1] 0)
      have : (NextPoint N f_x f_y)^[j+1] 0 < N - 1 := by
        exact test N f_x f_y (j+1) (by grind)
      specialize h1 this
      have h2 := NextPoint_increasing N f_x f_y ((NextPoint N f_x f_y)^[j] 0)
      have : (NextPoint N f_x f_y)^[j] 0 < N - 1 := by
        exact test N f_x f_y j (by grind)
      specialize h2 this
      simp_rw [Function.iterate_succ', Function.comp_apply] at *
      grind
  · rfl

noncomputable
def LowerConvexHull_ofSet : LowerConvexHull K where
  n := Nat.find (FinalIndex N f_x f_y) + 1 -- note the + 1 so that we include the last point
  x := LCH_x N f_x f_y
  y := LCH_y N f_x f_y
  increasing := LCH_increasing N f_x f_y
  convex := bar N f_x f_y

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
