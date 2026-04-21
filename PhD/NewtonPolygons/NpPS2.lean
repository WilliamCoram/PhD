import Mathlib

namespace NewtonPolygon

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ]

variable (Γ) in
/-- The y-values of our points, for powerseries this will be the valuations of the coefficients.
-/
abbrev ValSeq := ℕ → WithTop Γ

variable (v : ValSeq Γ)

/-- Predicate: the i-th coefficient is nonzero (has finite valuation). -/
def finite (i : ℕ) : Prop := v i ≠ ⊤

/-- The set of indices with nonzero coefficients. -/
def support : Set ℕ := {i | finite v i}

section Slopes

-- Ideally I would like this slope to be an element of Γ - for this I need to be able to subtract
-- in Γ, and divide by ℕ
-- What is the minimum assumption for this?

-- a ring Γ that is a ℚ-module, and such that ℝ is a Γ-algebra?

-- compute the slope as a real number (since ℝ is complete we can use sInf)
noncomputable
def slopeReal (x₀ x₁ : ℕ) (y₀ y₁ : Γ) : ℝ :=
  (algebraMap Γ ℝ y₁ - algebraMap Γ ℝ y₀) / (x₁ - x₀)

def slopeSet (i₀ : ℕ) (i₁ : Γ) : Set ℝ :=
  {m | ∃ j₀ : ℕ, j₀ > i₀ ∧ finite v j₀ ∧ ∃ j₁ : Γ, v j₀ = j₁ ∧ m = slopeReal i₀ j₀ i₁ j₁}

def achievingSet (i₀ : ℕ) (i₁ : Γ) (m : ℝ) : Set ℕ :=
  {j : ℕ | j > i₀ ∧ finite v j ∧ ∃ j₁ : Γ, v j = j₁ ∧ m = slopeReal i₀ j i₁ j₁}

end Slopes

section AlgorithmStep

variable (Γ) in
/-- The result of one step of the Newton polygon algorithm. -/
inductive StepResult where
  /-- No more finite values. -/
  | Tail
  /-- The set of minimum slopes is unbounded below. -/
  | unboundedBelow
  /-- Infinitely many points achieve the minimum slope m: final ray with infinitely many points. -/
  | infiniteRay (m : ℝ)
  /-- The minimum slope is achieved by finitely many points;
      move to the rightmost point (j₀, j₁). -/
  | nextVertex (j₀ : ℕ) (j₁ : Γ) (m : ℝ)
  /-- The infimum is not attained (all later points are strictly above the limiting line):
      final ray with no further lattice points. -/
  | limitingRay (m : ℝ)

/-- Compute the next step of the Newton polygon algorithm.
    Given current index i, determines what happens next.
    This is noncomputable because it uses sInf on Γ and classical choice. -/
noncomputable def nextStep (i₀ : ℕ) (i₁ : Γ) : StepResult Γ :=
  open Classical in
  if slopeSet v i₀ i₁ = ∅ then
    -- No more finite values: tail
    StepResult.Tail
  else
    -- slopeSetR is nonempty, compute the infimum in Γ and check if it is achieved by some
    -- rational slope
    if ¬ (BddBelow (slopeSet v i₀ i₁)) then
       -- if slopeSet is unbounded below we are left a vertical half-line down from i
      StepResult.unboundedBelow
    else
      if hm : ∃ m ∈ slopeSet v i₀ i₁, m = sInf (slopeSet v i₀ i₁) then
        if hInf : (achievingSet v i₀ i₁ (Classical.choose hm)).Infinite then
          -- infinitely many points achieve the minimum slope
          StepResult.infiniteRay (Classical.choose hm)
        else
          -- Finitely many points achieve the minimum: take the maximum
          have hNonempty : (achievingSet v i₀ i₁ (Classical.choose hm)).Nonempty := by
            simp only [↓existsAndEq, and_true] at hm
            use Classical.choose hm
            simp_rw [achievingSet]
            grind
          let j := (Set.not_infinite.mp hInf).toFinset.max'
            ((Set.not_infinite.mp hInf).toFinset_nonempty.mpr hNonempty)
          match v j with
            | ⊤ => StepResult.Tail -- should not happen by construction
            | (j₁ : Γ) => StepResult.nextVertex j j₁ (Classical.choose hm)
      else
        -- infimum not obtained (happens when the limit is in the completion)
        StepResult.limitingRay (sInf (slopeSet v i₀ i₁))

end AlgorithmStep

section Segments

variable (Γ) in
/-- A segment of the Newton polygon from vertex (i₀, i₁) to (j₀, j₁).
    All coordinates are concrete values (indices as ℕ, valuations as ℤ). -/
structure Segment where
  /-- Starting x-coordinate (index) -/
  x : ℕ
  /-- Starting y-coordinate -/
  y : Γ
  /-- Length (projected) -/
  l : WithTop ℕ
  /-- Slope -/
  m : WithTop ℝ
  -- we potentially want an infinite slope for polynomials; but maybe there is a way to avoid this
  --
  /-- Option whether it hits a point -/
  hitsPoint : Bool

  --- the idea is as follows
  --- finite length => hitsPoint true & nextVertex
  --- infinite length => hits point true = infiniteRay
  ---                    hits point false = limitingRay
  --- slope = ⊤ => length = 0 & stepResult.tail

-- note I really want ends_at_y to be in Γ

end Segments

section NPStructure

variable (Γ) in
/-- The empty Newton polygon (for the zero series or constant series). -/
def emptyPolygon : List (Segment Γ) := []

end NPStructure

section ComputingNP

variable {R : Type*} [Semiring R]

noncomputable
def toValSeq (f : PowerSeries R) (v : R → WithTop Γ) : ValSeq Γ :=
  fun i => v (PowerSeries.coeff i f)

/-- Create a single segment given valid data. -/
def mkSegment (x : ℕ) (y : Γ) (l : WithTop ℕ) (m : ℝ) (bool : Bool) : Segment Γ :=
  {x := x, y := y, l := l, m := m, hitsPoint := bool}

/-- Find the first index with finite valuation, starting from a given position. -/
noncomputable
def findFirstFinite (startIdx : ℕ) : Option (ℕ × Γ) := open Classical in
  if h : ∃ i ≥ startIdx, finite v i then
    let i := Nat.find h
    match v i with
    | ⊤ => none  -- contradicts finiteness
    | (val : Γ) => some (i, val)
  else
    none

variable (Γ) in
/-- Result of iteratively building the Newton polygon. -/
inductive BuildResult where
  /-- Successfully built the polygon. -/
  | complete (npd : List (Segment Γ))
  /-- Hit the segment limit before completing. -/
  | incomplete (npd : List (Segment Γ)) (reason : String)

/-- Build the Newton polygon by iterating the nextStep algorithm.
    This is the main computational function.

    The algorithm follows Gouvêa Section 7.4:
    1. Start at the first nonzero coefficient (i₀, v₀)
    2. Rotate the line counterclockwise to find minimum slope
    3. Move to the rightmost point achieving minimum slope
    4. Repeat until termination (polynomial tail, infinite ray, or limiting ray)
-/
noncomputable def buildNewtonPolygon (n : ℕ) : BuildResult Γ :=
  open Classical in
  -- Find the starting point (first finite valuation)
  match findFirstFinite v 0 with
  | none => BuildResult.complete (emptyPolygon Γ)
  | some (i, v_i) =>
    -- Iteratively build segments
    let rec build (currentIdx : ℕ) (currentVal : Γ) (npd : List (Segment Γ)) (fuel : ℕ) :
        BuildResult Γ :=
      if fuel = 0 then
        BuildResult.incomplete npd "reached segment limit"
      else
        match nextStep v currentIdx currentVal with
        | StepResult.Tail =>
            -- No more nonzero coefficients: series is essentially a polynomial
            BuildResult.complete npd
        | StepResult.unboundedBelow =>
            -- No more segments: valuation is unbounded below
            BuildResult.complete npd
        | StepResult.infiniteRay m =>
            -- Infinitely many points on a line of slope m
            let ray := mkSegment currentIdx currentVal ⊤ m true
            BuildResult.complete (npd ++ [ray])
        | StepResult.limitingRay m =>
            -- Limiting slope not achieved by any point
            let ray := mkSegment currentIdx currentVal ⊤ m false
            BuildResult.complete (npd ++ [ray])
        | StepResult.nextVertex j v_j m =>
            if h : currentIdx < j then
              let seg := mkSegment currentIdx currentVal (j - currentIdx) m true
              build j v_j (npd ++ [seg]) (fuel - 1)
            else
              -- Shouldn't happen
              BuildResult.incomplete npd "invalid vertex ordering"
    build i v_i [] n

/-- Extract the Newton polygon data, of the first n segments. -/
noncomputable
def newtonPolygon (n : ℕ)  : List (Segment Γ) :=
  match buildNewtonPolygon v n with
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd
  -- maybe I want to carry around the string so that I can tell when it is complete?

end ComputingNP

section API

/-- Get all slopes of the Newton polygon (the "Newton slopes"). -/
noncomputable
def NewtonPolygonData.slopes (npd : List (Segment Γ)) : List (WithTop ℝ) :=
  npd.map fun seg => seg.m

/-- Get the length of each segment (projection onto x-axis). -/
def NewtonPolygonData.lengths (npd : List (Segment Γ)) : List (WithTop ℕ) :=
  npd.map fun seg => seg.l

end API

section WellFormed

def Segment.isRay (seg : Segment Γ) : Prop :=
  seg.l = ⊤

def Segment.isFinite (seg : Segment Γ) : Prop :=
  ∃ n : ℕ, seg.l = n

def NewtonPolygonData.connected (npd : List (Segment Γ)) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.length,
    ∃ l : ℕ, npd[k].l = l → npd[k].x + l = npd[k+1].x ∧ v (npd[k].x + l) = npd[k+1].y
  -- could try and change this to Segment.isFinite?

def NewtonPolygonData.slopes_strictlyIncreasing (npd : List (Segment Γ)) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.length,
    Segment.isFinite npd[k+1] → npd[k].m < npd[k+1].m

def NewtonPolygonData.ray_slope_valid (npd : List (Segment Γ)) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.length,
    Segment.isRay npd[k+1] → if npd[k+1].hitsPoint = true then npd[k].m < npd[k+1].m
                      else npd[k].m ≤ npd[k+1].m

structure NewtonPolygonData.WellFormed (npd : List (Segment Γ)) : Prop where
  connected : NewtonPolygonData.connected (v := v) npd
  slopes_strictlyIncreasing : NewtonPolygonData.slopes_strictlyIncreasing npd
  ray_slope_valid : NewtonPolygonData.ray_slope_valid npd

set_option linter.unusedSectionVars false in
theorem emptyPolygon_wellFormed (v : ValSeq Γ) :
    NewtonPolygonData.WellFormed (v := v) (emptyPolygon Γ) where
  connected := by simp [emptyPolygon, NewtonPolygonData.connected]
  slopes_strictlyIncreasing := by simp [emptyPolygon, NewtonPolygonData.slopes_strictlyIncreasing]
  ray_slope_valid := by simp [emptyPolygon, NewtonPolygonData.ray_slope_valid]

def getSegments : BuildResult Γ → List (Segment Γ)
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

lemma getSegments_eq (n : ℕ) {i₀ : ℕ} {i₁ : Γ} (h : findFirstFinite v 0 = some (i₀, i₁)) :
    getSegments (buildNewtonPolygon.build v i₀ i₁ [] n) = newtonPolygon v n := by
  unfold getSegments newtonPolygon buildNewtonPolygon
  aesop

def ends_at (segs : List (Segment Γ)) (j₀ : ℕ) (j₁ : Γ) : Prop :=
  match segs.getLast? with
  | some s => ∃ l : ℕ, s.l = l ∧ s.x + l = j₀ ∧ v (s.x + l) = j₁
  | none => True

section nextVertexAPI

lemma nextVertex_bddBelow (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma nextVertex_finite (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) :
    (achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁))).Finite := by
  rw [nextStep] at h
  split_ifs at h with _ _ h1 h2
  grind

lemma nextVertex_nonEmpty (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) :
    (achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁))).Nonempty := by
  rw [nextStep] at h
  split_ifs at h with _ _ hm
  simp only [↓existsAndEq, and_true] at hm
  use Classical.choose hm
  simp_rw [achievingSet]
  grind

lemma nextVertex_j₀_eq_max (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) : j₀ =
    (nextVertex_finite v h).toFinset.max' ((nextVertex_finite v  h).toFinset_nonempty.mpr
    (nextVertex_nonEmpty v h)) := by
  simp_rw [nextStep] at h
  split_ifs at h with _ _ H
  split at h
  · trivial
  · simp_all only [StepResult.nextVertex.injEq]
    grind

lemma nextVertex_j₀Mem (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) :
    j₀ ∈ achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁)) := by
  have : j₀ ∈ (nextVertex_finite v h).toFinset := by
    simp_rw [nextVertex_j₀_eq_max v h]
    exact Finset.max'_mem _ _
  simp only [Set.Finite.mem_toFinset] at this
  exact this

lemma nextVertex_j₁_eq (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) : v j₀ = j₁ := by
  simp_rw [nextStep] at h
  aesop

lemma nextVertex_j₀Finite (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) : finite v j₀ := by
  have := nextVertex_j₁_eq v h
  simp_all [finite]

lemma nextVertex_slope_eq_sInf (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) :
    slopeReal i₀ j₀ i₁ j₁ = sInf (slopeSet v i₀ i₁) := by
  obtain ⟨hij, finj, j', hj', fin⟩ := nextVertex_j₀Mem v h
  simp_all [nextVertex_j₁_eq v h]

end nextVertexAPI

lemma connected_append_singleton {segs : List (Segment Γ)} (seg : Segment Γ)
    (h_conn : NewtonPolygonData.connected (v := v) segs) (h_end : ends_at v segs seg.x seg.y) :
    NewtonPolygonData.connected (v := v) (segs ++ [seg]) := by
  simp_rw [NewtonPolygonData.connected] at ⊢ h_conn
  intro k hk
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Order.lt_add_one_iff,
    Order.add_one_le_iff] at hk
  have : k + 1 < segs.length ∨ k + 1 = segs.length := by
    grind
  rcases this with h | h
  · grind
  · simp_rw [ends_at] at h_end
    have : segs.getLast? = segs[k] := by grind
    simp_all only [List.getElem_append_left, le_refl, List.getElem_append_right, tsub_self,
      List.getElem_cons_zero]
    obtain ⟨l, hl, H⟩ := h_end
    exact ⟨l, fun _ ↦ H⟩

theorem build_connected (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} (segs : List (Segment Γ)) (fuel : ℕ)
    (h_conn : NewtonPolygonData.connected (v := v) segs) (h_end : ends_at v segs i₀ i₁) :
    NewtonPolygonData.connected (v := v) (getSegments (buildNewtonPolygon.build v i₀ i₁ segs fuel)) := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs
  · simp [getSegments, buildNewtonPolygon.build, h_conn]
  · unfold buildNewtonPolygon.build
    rcases h : nextStep v i₀ i₁ with (_ | _ | m | ⟨j₀, j₁, m⟩ | m)
    · simpa [getSegments] using h_conn
    · simpa [getSegments] using h_conn
    · exact connected_append_singleton (v := v) (mkSegment i₀ i₁ ⊤ m true) h_conn h_end
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
      split_ifs with hij
      · refine ih (segs := segs ++ [mkSegment i₀ i₁ (j₀ - i₀) m true])
          (connected_append_singleton (v := v) (mkSegment i₀ i₁ (j₀ - i₀) m true) h_conn h_end) ?_
        simp [ends_at, mkSegment]
        refine ⟨j₀ - i₀, rfl, Nat.add_sub_of_le hij.le, ?_⟩
        convert nextVertex_j₁_eq v h
        grind
      · simpa [getSegments] using h_conn
    · exact connected_append_singleton (v := v) (mkSegment i₀ i₁ ⊤ m false) h_conn h_end

lemma newtonPolygon_connected (v : ValSeq Γ) (n : ℕ) :
    NewtonPolygonData.connected (v := v) (newtonPolygon v n) := by
  rcases h : findFirstFinite v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using (emptyPolygon_wellFormed (Γ := Γ) v).connected
  · convert build_connected v [] n (emptyPolygon_wellFormed (Γ := Γ) v).connected (by trivial)
    rw [getSegments_eq (Γ := Γ) v n h]

section SlopeConvexity

/-- Slope inequality for three ordered points: if successive slopes are decreasing,
    the overall slope is between them. -/
lemma succSlope_le_Slope {a₀ a₁ a₂ : ℝ} {b₀ b₁ b₂ : ℝ} (ha1 : a₀ < a₁) (ha2 : a₁ < a₂)
    (hab : (b₂ - b₁) / (a₂ - a₁) ≤ (b₁ - b₀) / (a₁ - a₀)) :
    (b₂ - b₀) / (a₂ - a₀) ≤ (b₁ - b₀) / (a₁ - a₀) := by
  have : b₂ ≤ b₀ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₀) := by
    have h : b₂ = b₁ + (b₂ - b₁) / (a₂ - a₁) * (a₂ - a₁) := by grind
    have : b₀ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₀) = b₁ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₁) := by
      grind
    rw [this, h]
    simp only [add_le_add_iff_left, ge_iff_le]
    exact mul_le_mul_of_nonneg_right hab (by grind)
  rw [add_comm, ← tsub_le_iff_right] at this
  rw [div_le_iff₀' (by grind), mul_comm]
  grind

/-- Strict version of slope convexity inequality. -/
lemma succSlope_lt_Slope {a₀ a₁ a₂ : ℝ} {b₀ b₁ b₂ : ℝ} (ha1 : a₀ < a₁) (hb2 : a₁ < a₂)
    (hab : (b₂ - b₁) / (a₂ - a₁) < (b₁ - b₀) / (a₁ - a₀)) :
    (b₂ - b₀) / (a₂ - a₀) < (b₁ - b₀) / (a₁ - a₀) := by
  have : b₂ < b₀ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₀) := by
    have h : b₂ = b₁ + (b₂ - b₁) / (a₂ - a₁) * (a₂ - a₁) := by grind
    have : b₀ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₀) = b₁ + (b₁ - b₀) / (a₁ - a₀) * (a₂ - a₁) := by
      grind
    rw [this, h]
    simp only [add_lt_add_iff_left, gt_iff_lt]
    exact mul_lt_mul_of_pos_right hab (by grind)
  rw [div_lt_iff₀' (by grind), mul_comm]
  grind

end SlopeConvexity

section infiniteRayAPI

/-- If nextStep returns infiniteRay m, the slopeSet is bounded below. -/
lemma infiniteRay_bddBelow (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = StepResult.infiniteRay m) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

/-- If nextStep returns infiniteRay m, there exist infinitely many points achieving slope m. -/
lemma infiniteRay_nonempty (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = StepResult.infiniteRay m) :
    (achievingSet v i₀ i₁ m).Nonempty := by
  simp_rw [nextStep] at h
  split_ifs at h
  · simp_all only [StepResult.infiniteRay.injEq]
    rename_i _ _ _ fin
    exact Set.Infinite.nonempty fin
  · aesop

end infiniteRayAPI

section limitingRayAPI

/-- If nextStep returns limitingRay m, the slopeSet is bounded below. -/
lemma limitingRay_bddBelow (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = StepResult.limitingRay m) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

/-- If nextStep returns limitingRay m, the slopeSet is nonempty. -/
lemma limitingRay_nonempty (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = StepResult.limitingRay m) :
    (slopeSet v i₀ i₁).Nonempty := by
  simp_rw [nextStep] at h
  split at h
  · trivial
  · rename_i fin
    exact Set.nonempty_iff_ne_empty.mpr fin

end limitingRayAPI

section SlopesMonotonicityProof

lemma segment_append_singleton_slopes_strictlyIncreasing (segs : List (Segment Γ)) (seg : Segment Γ)
    (h : NewtonPolygonData.slopes_strictlyIncreasing segs) (h' : ∀ s ∈ segs.getLast?, s.m < seg.m)
    : NewtonPolygonData.slopes_strictlyIncreasing (segs ++ [seg]) := by
  intro k hk
  by_cases hk' : k < segs.length
  · by_cases hk'' : k + 1 < segs.length
    · aesop
    · grind
  · grind

/-- Building maintains slopes_strictlyIncreasing via induction on fuel. -/
theorem build_slopes_strictlyIncreasing (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ}
    (segs : List (Segment Γ)) (fuel : ℕ)
    (h_slopes : NewtonPolygonData.slopes_strictlyIncreasing segs)
    (h_end : ends_at v segs i₀ i₁)
    (h_fin : ∀ s ∈ segs.getLast?, Segment.isFinite s)
    (h_m : ∀ s (hs : s ∈ segs.getLast?), ∃ m : ℝ, s.m = m)
    (h_bdd :  ∀ s ∈ segs.getLast?, BddBelow (slopeSet v s.x s.y))
    (h_final1 : ∀ s ∈ segs.getLast?, s.m = sInf (slopeSet v s.x s.y))
    (h_final2 : ∀ s (hs : s ∈ segs.getLast?),
      Set.Finite (achievingSet v s.x s.y (Classical.choose (h_m s hs))))
    (h_final3 :  ∀ s (hs : s ∈ segs.getLast?),
      Set.Nonempty (achievingSet v s.x s.y (Classical.choose (h_m s hs))))
    (h_final4 : ∀ s (hs : s ∈ segs.getLast?), s.x + s.l = (Set.Finite.toFinset (h_final2 s hs)).max'
      ((h_final2 s hs).toFinset_nonempty.mpr (h_final3 s hs))) :
    NewtonPolygonData.slopes_strictlyIncreasing (getSegments (buildNewtonPolygon.build v i₀ i₁ segs fuel)) := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs h_slopes h_end
  · simpa [buildNewtonPolygon.build] using h_slopes
  · unfold buildNewtonPolygon.build
    rcases h : nextStep v i₀ i₁ with ( _ | _ | m | ⟨j₀, j₁, m⟩ | m )
    all_goals try trivial
    · -- since we are adding something that has length ⊤ we can ignore the final comparison
      sorry
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
        dite_eq_ite]
      split_ifs with hij
      · convert ih (segs ++ [mkSegment i₀ i₁ (j₀ - i₀) m true]) _ _ _ _ _ _ _ _ _
        · refine segment_append_singleton_slopes_strictlyIncreasing segs (mkSegment i₀ i₁ (j₀ - i₀) m true)
            h_slopes ?_
          intro s hs
          simp_rw [ends_at] at h_end
          by_contra
          suffices (slopeReal s.x j₀ s.y j₁) ≤ sInf (slopeSet v s.x s.y) by

            sorry
          specialize h_final1 s hs
          obtain ⟨m, hm⟩ := h_m s hs
          simp_rw [hm] at h_final1
          simp only [WithTop.coe_inj] at h_final1
          simp_rw [← h_final1, slopeReal, mkSegment, not_lt] at ⊢ this

          -- this is so fucking stupid ... I need to make API that says what the slope is...

          -- this method is just horrible
          sorry
        · simp [ends_at, mkSegment]
          use (j₀ - i₀)

          sorry
        all_goals sorry
      · trivial
    ·
      sorry

/-- The final polygon has strictly increasing slopes. -/
lemma newtonPolygon.slopes_strictlyIncreasing (v : ValSeq Γ) (n : ℕ) :
    NewtonPolygonData.slopes_strictlyIncreasing (newtonPolygon v n) := by

  sorry

end SlopesMonotonicityProof

section RayValidProof

/-- The final polygon has valid ray slopes. -/
lemma newtonPolygon.ray_slope_valid (v : ValSeq Γ) (n : ℕ) :
    NewtonPolygonData.ray_slope_valid (newtonPolygon v n) := by
  rcases h : findFirstFinite v 0 with _ | ⟨i₀, i₁⟩
  · simp [newtonPolygon, buildNewtonPolygon, h, emptyPolygon, NewtonPolygonData.ray_slope_valid]
  · -- For the non-empty case, the algorithm ends with either a finite segment or a ray
    -- If it ends with a ray, the properties infiniteRay_bddBelow/nonempty or limitingRay_bddBelow/nonempty
    -- ensure the slope constraints are satisfied by the infimum properties
    sorry

end RayValidProof

section wellFormed

theorem newtonPolygon.WellFormed (v : ValSeq Γ) (n : ℕ) :
    NewtonPolygonData.WellFormed (v := v) (newtonPolygon v n) where
  connected := newtonPolygon_connected v n
  slopes_strictlyIncreasing := newtonPolygon.slopes_strictlyIncreasing v n
  ray_slope_valid := newtonPolygon.ray_slope_valid v n

end wellFormed
