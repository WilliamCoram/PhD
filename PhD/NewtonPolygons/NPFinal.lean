import Mathlib

structure LowerConvexHull (K : Type*) [Semiring K] [Preorder K] where
  /-- The number of points -/
  n : ℕ -- we will want to add a withTop ℕ to resolve for powerseries in the future
  /-- `x j` is the x-coordinate of the `j`th point when `0 ≤ j < S.n`. -/
  x : ℕ → K
  /-- `y j` is the y-coordinate of the `j`th point when `0 ≤ j < S.n`. -/
  y : ℕ → K
  /-- The x-coordinates are strictly increasing. -/
  increasing : StrictMonoOn x (Set.Ico 0 n)
  /-- The Newton polygon is lower convex.
  This considers three successive points with indices `j`, `j+1` and `j+2`. -/
  -- We have a ≤ as we are allowing the slops to be the same for now.
  convex : ∀ j : ℕ, j + 2 < n →
    x j * y (j + 2) + x (j + 1) * y j  + x (j + 2) * y (j + 1) ≤
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
The goal is to give a function that sends a Polynomial to a lower convexhull.
To do this I want to write this as a composition of two functions.
  1. Sends a Polynomial to a finite set of points
  2. Sends a finite set of points to its lower convex hull
-/

section PolyToFinset

variable  (M F : Type*) [Semiring M] (v : M → K)
-- I am not entirely sure if this is the correct generality for M (the coeff space of the polynomial)

/-- A way to define a set in M×M such that the `x` coordinates are strictly increasing. -/
structure newtonSet where -- Newton set?
  /-- Number of points. -/
  n : ℕ
  /-- `x j` is the x-coordinate of the `j`th point when `0 ≤ j < S.n` -/
  x : ℕ → K
  /-- `y j` is the y-coordinate of the `j`th point when `0 ≤ j < S.n` -/
  y : ℕ → K
  /-- The x-coordinates are strictly increasing. -/
  increasing : StrictMonoOn x (Set.Ico 0 n)

-- The below will not work for powerseries, so maybe need to think of a better approach later

noncomputable
local instance (f : Polynomial M) : DecidablePred fun m ↦ f.coeff ↑m ≠ 0 := by
  exact Classical.decPred fun m ↦ f.coeff m ≠ 0

noncomputable
def Poly_set (f : Polynomial M) : newtonSet (K := K) where
  n := Finset.card f.support
  x := fun i => (Finset.sort f.support).getD i 0
  y := fun i => if i < Finset.card f.support
                  then v (Polynomial.coeff f i)
                else 0
  -- outside of S.n all our points are (0,0). This choice should not matter though.
  increasing i hi j hj hij := by
    -- this proof was adjusted from an aristotle proof which didnt work
    have hi' : i < (Finset.sort f.support).length := by
      aesop
    have hj' : j < (Finset.sort f.support).length := by
      aesop
    simp_all only [Set.mem_Ico, zero_le, true_and, Finset.length_sort, List.getD_eq_getElem?_getD,
      getElem?_pos, Option.getD_some, Nat.cast_lt, gt_iff_lt]
    exact List.SortedLT.getElem_lt_getElem_of_lt (Finset.sortedLT_sort f.support) hij

end PolyToFinset

section FinsetToLCH

variable (S : newtonSet (K := K))

/-- The set of slopes out of the point indexed by i -/
def Set_of_Slopes (i : ℕ) : Set K :=
  Set.image (fun j => (S.y j - S.y i) / (S.x j - S.x i)) {j | j < S.n ∧ i < j}

omit [IsStrictOrderedRing K] in
lemma Set_of_Slopes_nonempty (i : ℕ) (hi : i < S.n - 1) : Nonempty (Set_of_Slopes S i) := by
  refine Set.nonempty_iff_ne_empty'.mpr ?_
  have : {j | j < S.n ∧ i < j} ≠ ∅ := by
    contrapose hi
    simp only [not_lt, tsub_le_iff_right] at *
    by_contra h
    simp only [not_le] at h
    have : (i + 1) ∈ {j | j < S.n ∧ i < j} := by
      simpa
    aesop
  simpa [Set_of_Slopes]

omit [IsStrictOrderedRing K] in
lemma Set_of_Slopes_empty (i : ℕ) (hi : S.n - 1 ≤ i) : Set_of_Slopes S i = ∅ := by
  simp_rw [Set_of_Slopes, Set.image_eq_empty]
  grind

omit [IsStrictOrderedRing K] in
lemma Set_of_Slopes_isFinite (i : ℕ) : Set.Finite (Set_of_Slopes S i) :=
  Set.Finite.image _ (Set.Finite.sep (Set.finite_lt_nat S.n) (LT.lt i))

/-- The set of slopes as a finset. -/
noncomputable
def Set_of_Slopes_isFinset (i : ℕ) : Finset K := Set.Finite.toFinset (Set_of_Slopes_isFinite S i)

omit [IsStrictOrderedRing K] in
lemma Set_of_Slopes_list_length (i : ℕ) (hi : i < S.n - 1) :
    0 < ((Finset.sort (Set_of_Slopes_isFinset S i))).length := by
  simp only [Finset.length_sort, Finset.card_pos, Set_of_Slopes_isFinset]
  convert Set_of_Slopes_nonempty S i hi
  aesop

/-- The minimum slope from the point indexed by `i`. -/
noncomputable
def MinSlope (i : ℕ) : K := (Finset.sort (Set_of_Slopes_isFinset S i)).getD 0 0

omit [IsStrictOrderedRing K] in
-- proof by aristotle then tidied up
lemma MinSlope_isMin (i : ℕ) (m : K) (hm : m ∈ Set_of_Slopes S i) :
    MinSlope S i ≤ m := by
  have h_sorted : ∀ {l : List K}, List.Pairwise (· ≤ ·) l → ∀ m ∈ l, l.getD 0 0 ≤ m := by
    intro l hl m hm
    induction l <;> aesop
  convert h_sorted _ m _
  · exact Finset.pairwise_sort _ _
  · exact Finset.mem_sort ( · ≤ · ) |>.2
      (Set.Finite.mem_toFinset (Set_of_Slopes_isFinite S i ) |>.2 hm)

section Finset.sort

/- Some general statements that can be added to Finset.sort -/

lemma Finset.sort.getElem_mem {α : Type*} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] [Std.Antisymm r] [Std.Total r] (s : Finset α) (fallback : α)
    (n : ℕ) (hn : n < (Finset.sort s r).length) : (Finset.sort s r).getD n fallback ∈ s := by
  simp_all only [List.getD_eq_getElem?_getD, getElem?_pos, Option.getD_some]
  convert List.getElem_mem hn
  aesop

lemma Finset.sort.range {α : Type*} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] [Std.Antisymm r] [Std.Total r] (s : Finset α) (fallback : α) (n : ℕ) :
    (Finset.sort s r).getD n fallback = fallback ∨ (Finset.sort s r).getD n fallback ∈ s := by
  by_cases h : n < (Finset.sort s r).length
  · right; exact getElem_mem r s fallback n h
  · left; aesop

end Finset.sort

omit [IsStrictOrderedRing K] in
lemma MinSlope_exists (i : ℕ) (hi : i < S.n - 1) : ∃ a, a ∈ {j | j < S.n ∧ i < j} ∧
    (S.y a - S.y i) / (S.x a - S.x i) = MinSlope S i := by
  have : (Finset.sort (Set_of_Slopes_isFinset S i)).getD 0 0 ∈ Set_of_Slopes S i := by
    have := Finset.sort.getElem_mem (· ≤ ·) (Set_of_Slopes_isFinset S i)
      0 0 (Set_of_Slopes_list_length S i hi)
    simp_rw [Set_of_Slopes_isFinset] at this
    aesop
  aesop

/-- The points `j` with `i < j < S.n` such that they give rise to `MinSlope S i`. -/
def NextPoint_potential (i : ℕ) : Set ℕ :=
  {j |  (S.y j - S.y i) / (S.x j - S.x i) = MinSlope S i} ∩ {j | j < S.n ∧ i < j}

omit [IsStrictOrderedRing K] in
lemma NextPoint_potential_nonempty (i : ℕ) (hi : i < S.n - 1) :
    Nonempty (NextPoint_potential S i) := by
  simp only [nonempty_subtype]
  simp_rw [NextPoint_potential]
  convert MinSlope_exists S i hi
  aesop

omit [IsStrictOrderedRing K] in
lemma NextPoint_empty (i : ℕ) (hi : S.n - 1 ≤ i) : (NextPoint_potential S i) = ∅ := by
  simp_rw [NextPoint_potential]
  have : {j | j < S.n ∧ S.n - 1 < j} = ∅ := by
    grind
  grind

omit [IsStrictOrderedRing K] in
lemma NextPoint_potential_isFinite (i : ℕ) : Set.Finite (NextPoint_potential S i) :=
  Set.Finite.inter_of_right (Set.finite_iff_bddAbove.mpr (bddAbove_def.mpr (by use S.n; grind))) _

/-- NextPoint_potential as a finset. -/
noncomputable
def NextPoint_potential_isFinset (i : ℕ) : Finset ℕ :=
  Set.Finite.toFinset (NextPoint_potential_isFinite S i)

omit [IsStrictOrderedRing K] in
lemma NextPoint_potential_list_length (i : ℕ) (hi : i < S.n - 1) :
    0 < (Finset.sort (NextPoint_potential_isFinset S i)).length := by
  simp only [Finset.length_sort, Finset.card_pos, NextPoint_potential_isFinset]
  convert NextPoint_potential_nonempty S i hi
  aesop

-- Note I could be using .head or .tail instead to get the first or last point

/-- Given an index `i` this gives the smallest index which gives rise to `MinSlope S i`. -/
noncomputable
def NextPoint (i : ℕ) : ℕ :=
  (Finset.sort (NextPoint_potential_isFinset S i)).getD 0 (S.n - 1)

omit [IsStrictOrderedRing K] in
lemma NextPoint_isPotential (i : ℕ) (hi : i < S.n - 1) :
    NextPoint S i ∈ NextPoint_potential S i := by
  simp_rw [NextPoint]
  have := NextPoint_potential_nonempty S i hi
  convert Finset.sort.getElem_mem _ (NextPoint_potential_isFinset S i)
      (S.n - 1) 0 (NextPoint_potential_list_length S i hi)
  simp_rw [NextPoint_potential_isFinset]
  aesop

omit [IsStrictOrderedRing K] in
lemma NextPoint_max (i : ℕ) : NextPoint S i ≤ S.n - 1 := by
  simp_rw [NextPoint]
  rcases (Finset.sort.range (· ≤ ·) (NextPoint_potential_isFinset S i) (S.n - 1) 0) with h | h
  · aesop
  · have : NextPoint_potential S i ⊆ {j | j < S.n ∧ i < j} := by
      simp_rw [NextPoint_potential]
      aesop
    simp_rw [NextPoint_potential_isFinset, Set.Finite.mem_toFinset] at h ⊢
    grind

omit [IsStrictOrderedRing K] in
lemma NextPoint_increasing (i : ℕ) (hi : i < S.n - 1) : i < NextPoint S i := by
  have := NextPoint_isPotential S i hi
  simp_rw [NextPoint_potential] at this
  aesop

/-- The function iterating `NextPoint S` on 0. -/
noncomputable
abbrev NextPoint_iterate := fun i ↦ Nat.iterate (NextPoint S) i 0

omit [IsStrictOrderedRing K] in
lemma NextPoint_iterate_max (i : ℕ) : NextPoint_iterate S i ≤ S.n - 1 := by
  simp_rw [NextPoint_iterate]
  induction' i with n hn
  · aesop
  · simp only [Function.iterate_succ', Function.comp_apply]
    exact NextPoint_max S ((NextPoint S)^[n] 0)

omit [IsStrictOrderedRing K] in
lemma NextPoint_iterate_max' (i : ℕ) (h : S.n ≠ 0) : NextPoint_iterate S i ∈ Set.Ico 0 S.n := by
  have := NextPoint_iterate_max S i
  grind

omit [IsStrictOrderedRing K] in
lemma FinalIndex : ∃ a : ℕ, NextPoint_iterate S a = S.n - 1 := by
  by_cases triv1 : S.n = 0
  · use 0; aesop
  by_cases triv2 : S.n = 1
  · use 0; aesop
  by_contra h
  simp only [not_exists, ← ne_eq] at h
  have h : ∀ x, (NextPoint S)^[x] 0 < S.n - 1 := by -- why we need 2 ≤ S.n
    intro a
    specialize h a
    have := NextPoint_iterate_max S a
    grind
  have inc (i : ℕ) : (NextPoint S)^[i] 0 < (NextPoint S)^[i+1] 0 := by
    simp only [Function.iterate_succ', Function.comp_apply]
    exact NextPoint_increasing S ((NextPoint S)^[i] 0) (h i)
  apply strictMono_nat_of_lt_succ at inc
  have := StrictMono.not_bddAbove_range_of_wellFoundedLT inc
  have : BddAbove (Set.range fun n ↦ (NextPoint S)^[n] 0) := by
    refine bddAbove_def.mpr ?_
    use S.n - 1
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact fun a ↦ NextPoint_iterate_max S a
  aesop

omit [IsStrictOrderedRing K] in
lemma NextPoint_iterate_le_max (i : ℕ) (hi : i < Nat.find (FinalIndex S)) :
    NextPoint_iterate S i < S.n - 1 := by
  contrapose hi
  simp only [Nat.lt_find_iff, not_forall, Decidable.not_not, exists_prop]
  simp only [not_lt] at hi
  use i
  simp only [le_refl, true_and]
  exact Nat.le_antisymm (NextPoint_iterate_max S i) hi

omit [IsStrictOrderedRing K] in
lemma NextPoint_iterate_increasing (i : ℕ) (hi : i < Nat.find (FinalIndex S)) :
    NextPoint_iterate S i < NextPoint_iterate S (i + 1) := by
  simp only [NextPoint_iterate, Function.iterate_succ', Function.comp_apply]
  refine NextPoint_increasing S ((NextPoint S)^[i] 0) ?_
  exact NextPoint_iterate_le_max S i (by grind)

omit [IsStrictOrderedRing K] in
lemma MinSlope_eq (j : ℕ) (hj : j < Nat.find (FinalIndex S)) :
    (S.y (NextPoint_iterate S (j + 1)) - S.y (NextPoint_iterate S j)) /
    (S.x (NextPoint_iterate S (j + 1)) - S.x (NextPoint_iterate S j)) =
    MinSlope S (NextPoint_iterate S j) := by
  have := NextPoint_isPotential S (NextPoint_iterate S j) (NextPoint_iterate_le_max S j hj)
  have := Set.mem_of_mem_inter_left this
  rw [Set.mem_setOf_eq] at this
  simp only [NextPoint_iterate, Function.iterate_succ', Function.comp_apply, this]

omit [IsStrictOrderedRing K] in
lemma Sx_comp_NextPoint_iterate_StrictMonoOn : StrictMonoOn (S.x ∘ (NextPoint_iterate S))
    (Set.Ico 0 (Nat.find (FinalIndex S) + 1)) := by
  by_cases t : S.n = 0
  · have : Nat.find (FinalIndex S) = 0 := by
      aesop
    simp_rw [this]
    have : (Set.Ico 0 1) = {0} := by
      aesop
    simp only [this, Set.strictMonoOn_singleton]
  by_cases h : Nat.find (FinalIndex S) = 0
  · simp_rw [h]
    have : (Set.Ico 0 1) = {0} := by
      grind
    simp only [this, Set.strictMonoOn_singleton]
  suffices h : ∀ i : (Set.Ico 0 (Nat.find (FinalIndex S))),
      NextPoint_iterate S i < NextPoint_iterate S (i + 1) by
    refine strictMonoOn_of_lt_succ (Set.ordConnected_Ico) ?_
    intro a ha ha' ha''
    have Final := S.increasing
    have (i : ℕ) : NextPoint_iterate S i ∈ Set.Ico 0 S.n := by
      have := NextPoint_iterate_max S i
      grind
    aesop
  intro i
  exact NextPoint_iterate_increasing S i (by grind)

lemma S_NextPoint_iterate_convex : ∀ (j : ℕ), j + 2 < Nat.find (FinalIndex S) + 1 →
    (S.x ∘ NextPoint_iterate S) j * (S.y ∘ NextPoint_iterate S) (j + 2) +
    (S.x ∘ NextPoint_iterate S) (j + 1) * (S.y ∘ NextPoint_iterate S) j +
    (S.x ∘ NextPoint_iterate S) (j + 2) * (S.y ∘ NextPoint_iterate S) (j + 1) ≤
    (S.x ∘ NextPoint_iterate S) j * (S.y ∘ NextPoint_iterate S) (j + 1) +
    (S.x ∘ NextPoint_iterate S) (j + 1) * (S.y ∘ NextPoint_iterate S) (j + 2) +
    (S.x ∘ NextPoint_iterate S) (j + 2) * (S.y ∘ NextPoint_iterate S) j:= by
  by_cases H : S.n = 0
  · have : Nat.find (FinalIndex S) = 0 := by
      aesop
    grind
  by_cases H' : S.n = 1
  · have : Nat.find (FinalIndex S) = 0 := by
      aesop
    grind
  intro j hj
  suffices ((S.y ∘ NextPoint_iterate S) (j + 1) - (S.y ∘ NextPoint_iterate S) j) /
      ((S.x ∘ NextPoint_iterate S) (j + 1) - (S.x ∘ NextPoint_iterate S) j) ≤
      ((S.y ∘ NextPoint_iterate S) (j + 2) - (S.y ∘ NextPoint_iterate S) j) /
      ((S.x ∘ NextPoint_iterate S) (j + 2) - (S.x ∘ NextPoint_iterate S) j) by
    have t1 : 0 < (S.x ∘ NextPoint_iterate S) (j + 1) - (S.x ∘ NextPoint_iterate S) j := by
      simp only [sub_pos]
      exact S.increasing (NextPoint_iterate_max' S j H) (NextPoint_iterate_max' S (j + 1) H)
        (NextPoint_iterate_increasing S j (by grind))
    have t2 : 0 < (S.x ∘ NextPoint_iterate S) (j + 2) - (S.x ∘ NextPoint_iterate S) j := by
      simp only [sub_pos]
      refine S.increasing (NextPoint_iterate_max' S j H) (NextPoint_iterate_max' S (j + 2) H) ?_
      trans NextPoint_iterate S (j + 1)
      · exact NextPoint_iterate_increasing S j (by grind)
      · exact NextPoint_iterate_increasing S (j+1) (by grind)
    field_simp at this
    linarith
  simp_rw [Function.comp_apply, MinSlope_eq S j (by grind)]
  refine MinSlope_isMin S (NextPoint_iterate S j)
    (((S.y ∘ NextPoint_iterate S) (j + 2) - (S.y ∘ NextPoint_iterate S) j) /
    ((S.x ∘ NextPoint_iterate S) (j + 2) - (S.x ∘ NextPoint_iterate S) j)) ?_
  use NextPoint_iterate S (j + 2)
  constructor
  · constructor
    · have := NextPoint_iterate_max S (j + 2)
      grind
    · have h1 := NextPoint_increasing S (NextPoint_iterate S (j + 1))
        (NextPoint_iterate_le_max S (j + 1) (by grind))
      have h2 := NextPoint_increasing S (NextPoint_iterate S j)
        (NextPoint_iterate_le_max S j (by grind))
      simp_rw [NextPoint_iterate, Function.iterate_succ', Function.comp_apply] at *
      grind
  · rfl

noncomputable
def LowerConvexHull_ofSet : LowerConvexHull K where
  n := Nat.find (FinalIndex S) + 1
  x := S.x ∘ NextPoint_iterate S
  y := S.y ∘ NextPoint_iterate S
  increasing := Sx_comp_NextPoint_iterate_StrictMonoOn S
  convex := S_NextPoint_iterate_convex S

end FinsetToLCH

variable  (M F : Type*) [Field M] [LinearOrder M] [IsStrictOrderedRing M] (v : M → K)

noncomputable
def newtonSet_of_Poly (f : Polynomial M) : newtonSet (K := K) := Poly_set M v f

noncomputable
def LCH_of_newtonSet (S : newtonSet (K := K)) : LowerConvexHull K :=
  LowerConvexHull_ofSet S

noncomputable
def NewtonPolygon (f : Polynomial M) : LowerConvexHull K :=
  LCH_of_newtonSet (newtonSet_of_Poly M v f)
