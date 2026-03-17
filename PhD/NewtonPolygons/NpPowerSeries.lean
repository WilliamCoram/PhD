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
  | nextVertex (j₀ : ℕ) (j₁ : Γ)
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
            | (j₁ : Γ) => StepResult.nextVertex j j₁
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
  i₀ : ℕ
  /-- Starting y-coordinate (valuation as integer) -/
  i₁ : Γ
  /-- Ending x-coordinate (index) -/
  j₀ : ℕ
  /-- Ending y-coordinate (valuation as integer) -/
  j₁ : Γ
  /-- i₀ < i₁ -/
  lt : i₀ < j₀
  deriving Repr

/-- The horizontal length of a segment. -/
def Segment.length (seg : Segment Γ) : ℕ := seg.j₀ - seg.i₀

/-- The slope of a segment as a rational number. -/
noncomputable
def Segment.slope (seg : Segment Γ) : ℝ :=
  slopeReal seg.i₀ seg.j₀ seg.i₁ seg.j₁

/-- A segment is valid if its endpoints correspond to actual nonzero coefficients
    with the claimed valuations. -/
def Segment.valid (seg : Segment Γ) : Prop :=
  finite v seg.i₀ ∧ finite v seg.j₀ ∧ v seg.i₀ = seg.i₁ ∧ v seg.j₀ = seg.j₁

/-- The y-coordinate of a point on the line from (i₀, i₁) with slope m. -/
noncomputable def lineAt (i₀ : ℕ) (i₁: Γ) (m : ℝ) (j₀ : ℕ) : ℝ :=
  algebraMap Γ ℝ i₁ + m * (j₀ - i₀)

/-- A segment is supporting if all points with j₀ > i₀ lie on or above the line. -/
def Segment.supporting (seg : Segment Γ) : Prop :=
  ∀ j₀ > seg.i₀, finite v j₀ → ∀ (j₁ : Γ), j₁ = v j₀ →
  algebraMap Γ ℝ j₁ ≥ lineAt seg.i₀ seg.i₁ seg.slope j₀

/-- A segment is tight if its endpoint (j₀, j₁) lies exactly on the line. -/
def Segment.tight (seg : Segment Γ) : Prop :=
  algebraMap Γ ℝ seg.j₁ = lineAt seg.i₀ seg.i₁ seg.slope seg.j₀

/-- Every segment is tight by construction. -/
theorem Segment.tight_of_slope (seg : Segment Γ) : seg.tight := by
  have : (seg.j₀ : ℝ) - seg.i₀ ≠ 0 := by
     exact ne_of_gt (by simpa using seg.lt)
  simp only [tight, lineAt, Segment.slope, slopeReal]
  grind

variable (Γ) in
/-- A final ray of the Newton polygon starting from (i₀, v₀) with slope m. -/
structure FinalRay where
  /-- Starting x-coordinate (index) -/
  i₀ : ℕ
  /-- Starting y-coordinate (valuation as integer) -/
  i₁ : Γ
  /-- The slope of the ray -/
  slope : ℝ
  /-- Whether the ray contains infinitely many lattice points -/
  hitsInfinitelyMany : Bool
  -- deriving Repr -- this breaks, so I really do want to have this slope as an element of Γ!

/-- A final ray is supporting if all later points lie on or above the ray. -/
def FinalRay.supporting (ray : FinalRay Γ) : Prop :=
  ∀ j > ray.i₀, finite v j → ∀ (j₁ : Γ), v j = j₁ →
  algebraMap Γ ℝ j₁ ≥ lineAt ray.i₀ ray.i₁ ray.slope j

end Segments

section NPStructure

variable (Γ) in
/-- The Newton polygon of a power series, consisting of:
    - A (possibly empty) list of segments with strictly increasing slopes
    - An optional final ray -/
structure NewtonPolygonData where
  /-- The list of segments. -/
  segments : List (Segment Γ)
  /-- The final ray, if the polygon terminates with a ray. -/
  finalRay : Option (FinalRay Γ)
  --deriving Repr

/-- Predicate to show if segments are properly connected. -/
def NewtonPolygonData.connected (npd : NewtonPolygonData Γ) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.segments.length,
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).j₀ = (npd.segments[k + 1]'hk).i₀ ∧
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).j₁ = (npd.segments[k + 1]'hk).i₁

/-- Predicate to show if slopes are strictly increasing. -/
def NewtonPolygonData.slopes_strictlyIncreasing (npd : NewtonPolygonData Γ) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.segments.length,
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).slope < (npd.segments[k + 1]'hk).slope

/-- Predicate to show the final ray is properly connected to the last segment. -/
def NewtonPolygonData.ray_connected (npd : NewtonPolygonData Γ) : Prop :=
  match npd.finalRay, npd.segments.getLast? with
  | some r, some s => r.i₀ = s.j₀ ∧ r.i₁ = s.j₁
  | _, _ => True

/-- Predicate to show the final ray's slope is at least the last segment's slope. -/
def  NewtonPolygonData.ray_slope_valid (npd : NewtonPolygonData Γ) : Prop :=
  match npd.finalRay, npd.segments.getLast? with
  | some r, some s => if r.hitsInfinitelyMany = true then s.slope < r.slope
                        else s.slope ≤ r.slope
  | _, _ => True

/-- A well-formed Newton polygon satisfies all connectivity and monotonicity conditions. -/
structure NewtonPolygonData.WellFormed (npd : NewtonPolygonData Γ) : Prop where
  connected : npd.connected
  slopes_strictlyIncreasing : npd.slopes_strictlyIncreasing
  ray_connected : npd.ray_connected
  ray_slope_valid : npd.ray_slope_valid

variable (Γ) in
/-- The empty Newton polygon (for the zero series or constant series). -/
def emptyPolygon : NewtonPolygonData Γ where
  segments := []
  finalRay := none

/-- The empty polygon is well-formed. -/
theorem emptyPolygon_wellFormed : (emptyPolygon Γ).WellFormed where
  connected _ hk := by simp [emptyPolygon] at hk
  slopes_strictlyIncreasing _ hk := by simp [emptyPolygon] at hk
  ray_connected := by simp [emptyPolygon, NewtonPolygonData.ray_connected]
  ray_slope_valid := by simp [emptyPolygon, NewtonPolygonData.ray_slope_valid]

end NPStructure

section ComputingNP

variable {R : Type*} [Semiring R]

noncomputable
def toValSeq (f : PowerSeries R) (v : R → WithTop Γ) : ValSeq Γ :=
  fun i => v (PowerSeries.coeff i f)

/-- Create a single segment given valid data. -/
def mkSegment (i₀ j₀ : ℕ) (i₁ j₁ : Γ) (hlt : i₀ < j₀) : Segment Γ :=
  {i₀ := i₀, i₁ := i₁, j₀ := j₀, j₁ := j₁, lt := hlt}

lemma mem_segmentSlope_slopeSet (s : Segment Γ) (a₀ : ℕ) (a₁ : Γ) (h : s.i₀ < a₀)
    (h_fin : finite v a₀) (ha₁ : v a₀ = a₁) : Segment.slope (mkSegment s.i₀ a₀ s.i₁ a₁ h) ∈
    slopeSet v s.i₀ s.i₁ := by
  simp_rw [slopeSet, Segment.slope]
  simp only [gt_iff_lt, Set.mem_setOf_eq]
  use a₀
  refine ⟨h, h_fin, ?_⟩
  use a₁
  exact ⟨ha₁, rfl⟩

/-- Create a final ray. -/
def mkFinalRay (i₀ : ℕ) (i₁ : Γ) (slope : ℝ) (infinite : Bool) : FinalRay Γ :=
  {i₀ := i₀, i₁ := i₁, slope := slope, hitsInfinitelyMany := infinite}

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
  | complete (npd : NewtonPolygonData Γ)
  /-- Hit the segment limit before completing. -/
  | incomplete (npd : NewtonPolygonData Γ) (reason : String)

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
    let rec build (currentIdx : ℕ) (currentVal : Γ) (segments : List (Segment Γ)) (fuel : ℕ) :
        BuildResult Γ :=
      if fuel = 0 then
        BuildResult.incomplete ⟨segments, none⟩ "reached segment limit"
      else
        match nextStep v currentIdx currentVal with
        | StepResult.Tail =>
            -- No more nonzero coefficients: series is essentially a polynomial
            BuildResult.complete ⟨segments, none⟩
        | StepResult.unboundedBelow =>
            -- No more segments: valuation is unbounded below
            BuildResult.complete ⟨segments, none⟩
        | StepResult.infiniteRay m =>
            -- Infinitely many points on a line of slope m
            let ray := mkFinalRay currentIdx currentVal m true
            BuildResult.complete ⟨segments, some ray⟩
        | StepResult.limitingRay m =>
            -- Limiting slope not achieved by any point
            let ray := mkFinalRay currentIdx currentVal m false
            BuildResult.complete ⟨segments, some ray⟩
        | StepResult.nextVertex j v_j =>
            if h : currentIdx < j then
              let seg := mkSegment currentIdx j currentVal v_j h
              build j v_j (segments ++ [seg]) (fuel - 1)
            else
              -- Shouldn't happen
              BuildResult.incomplete ⟨segments, none⟩ "invalid vertex ordering"
    build i v_i [] n

/-- Extract the Newton polygon data, of the first n segments. -/
noncomputable
def newtonPolygon (n : ℕ)  : NewtonPolygonData Γ :=
  match buildNewtonPolygon v n with
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

end ComputingNP

section API

/-- Get all slopes of the Newton polygon (the "Newton slopes"). -/
noncomputable
def NewtonPolygonData.slopes (npd : NewtonPolygonData Γ) : List ℝ :=
  npd.segments.map Segment.slope

/-- Get the length of each segment (projection onto x-axis). -/
def NewtonPolygonData.lengths (npd : NewtonPolygonData Γ) : List ℕ :=
  npd.segments.map Segment.length

/-- Get the vertices (break points) of the polygon as (index, valuation) pairs. -/
def NewtonPolygonData.vertices (npd : NewtonPolygonData Γ) : List (ℕ × Γ) :=
  match npd.segments with
  | [] => []
  | seg :: rest =>
    (seg.i₀, seg.i₁) :: rest.foldl (fun acc s => acc ++ [(s.j₀, s.j₁)]) [(seg.j₀, seg.j₁)]

/-- Get slopes paired with their lengths (useful for root counting). -/
noncomputable
def NewtonPolygonData.slopesWithLengths (npd : NewtonPolygonData Γ) : List (ℝ × ℕ) :=
  npd.segments.map fun seg => (seg.slope, seg.length)

/-- Total horizontal extent of the polygon. -/
def NewtonPolygonData.totalLength (npd : NewtonPolygonData Γ) : ℕ :=
  npd.lengths.foldl (· + ·) 0

/-- Check if the polygon is pure (has only one slope). -/
def NewtonPolygonData.isPure (npd : NewtonPolygonData Γ) : Bool :=
  npd.segments.length ≤ 1 && npd.finalRay.isNone

/-- Get the unique slope if the polygon is pure, otherwise none. -/
noncomputable
def NewtonPolygonData.pureSlope (npd : NewtonPolygonData Γ) : Option ℝ :=
  if npd.isPure then npd.slopes.head? else none

end API

section isWellFormed

def getSegments : BuildResult Γ → List (Segment Γ)
  | BuildResult.complete npd => npd.segments
  | BuildResult.incomplete npd _ => npd.segments

lemma getSegments_eq (n : ℕ) {i₀ : ℕ} {i₁ : Γ} (h : findFirstFinite v 0 = some (i₀, i₁)) :
    getSegments (buildNewtonPolygon.build v i₀ i₁ [] n) = (newtonPolygon v n).segments := by
  unfold getSegments newtonPolygon buildNewtonPolygon
  aesop

def segments_connected (segs : List (Segment Γ)) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < segs.length, (segs[k]'(Nat.lt_of_succ_lt hk)).j₀ = (segs[k + 1]'hk).i₀ ∧
    (segs[k]'(Nat.lt_of_succ_lt hk)).j₁ = (segs[k + 1]'hk).i₁

def ends_at (segs : List (Segment Γ)) (j₀ : ℕ) (j₁ : Γ) : Prop :=
  match segs.getLast? with
  | some s => s.j₀ = j₀ ∧ s.j₁ = j₁
  | none => True

theorem build_connected (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} (segs : List (Segment Γ)) (fuel : ℕ)
    (h_conn : segments_connected segs) (h_end : ends_at segs i₀ i₁) :
    segments_connected (getSegments (buildNewtonPolygon.build v i₀ i₁ segs fuel)) := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs
  · simp [getSegments, buildNewtonPolygon.build, h_conn]
  · unfold buildNewtonPolygon.build
    rcases h : nextStep v i₀ i₁ with ( _ | _ | _ | ⟨j₀, j₁⟩ | _ )
    all_goals try exact h_conn
    simp_all only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      segments_connected, ends_at]
    split_ifs with hij
    · simp_rw [mkSegment]
      grind
    · exact h_conn

lemma newtonPolygon.connected (n : ℕ) : NewtonPolygonData.connected (newtonPolygon v n) := by
  rcases h : findFirstFinite v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using emptyPolygon_wellFormed.connected
  · convert build_connected v [] n emptyPolygon_wellFormed.connected
      (by simp only [ends_at, List.getLast?_nil])
    rw [getSegments_eq v n h]
    rfl

def getResult : BuildResult Γ → NewtonPolygonData Γ
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

lemma getResult_eq (n : ℕ) {i₀ : ℕ} {i₁ : Γ}
    (h : findFirstFinite v 0 = some (i₀, i₁)) : newtonPolygon v n =
    getResult (buildNewtonPolygon.build v i₀ i₁ [] n) := by
  unfold getResult newtonPolygon buildNewtonPolygon
  aesop

theorem build_ray_connected (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} (segs : List (Segment Γ)) (fuel : ℕ)
    (h_end : ends_at segs i₀ i₁) :
    (getResult (buildNewtonPolygon.build v i₀ i₁ segs fuel)).ray_connected := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs
  all_goals unfold buildNewtonPolygon.build
  · trivial
  · simp_rw [ends_at] at h_end ih
    simp only [getResult, NewtonPolygonData.ray_connected, mkFinalRay]
    rcases h : nextStep v i₀ i₁ with ( _ | _ | _ | ⟨j₀, j₁⟩ | _ )
    all_goals try grind
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
    split_ifs with hij
    · refine ih _ ?_
      aesop
    · trivial

lemma newtonPolygon.ray_connected (n : ℕ)  :
    NewtonPolygonData.ray_connected (newtonPolygon v n) := by
  rcases h : findFirstFinite v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using emptyPolygon_wellFormed.ray_connected
  · convert build_ray_connected v [] n ?_
    · exact getResult_eq v n h
    · trivial

def slopes_strictlyIncreasing (segs : List (Segment Γ)) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < segs.length,
    (segs[k]'(Nat.lt_of_succ_lt hk)).slope < (segs[k + 1]'hk).slope

section nextVertexAPI

lemma nextVertex_bddBelow (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma nextVertex_finite (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    (achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁))).Finite := by
  rw [nextStep] at h
  split_ifs at h with _ _ h1 h2
  grind

lemma nextVertex_nonEmpty (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    (achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁))).Nonempty := by
  rw [nextStep] at h
  split_ifs at h with _ _ hm
  simp only [↓existsAndEq, and_true] at hm
  use Classical.choose hm
  simp_rw [achievingSet]
  grind

lemma nextVertex_j₀_eq_max (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁) : j₀ =
    (nextVertex_finite v h).toFinset.max' ((nextVertex_finite v  h).toFinset_nonempty.mpr
    (nextVertex_nonEmpty v h)) := by
  simp_rw [nextStep] at h
  split_ifs at h with _ _ H
  split at h
  · trivial
  · simp_all only [StepResult.nextVertex.injEq]
    grind

lemma nextVertex_j₀Mem (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    j₀ ∈ achievingSet v i₀ i₁ (sInf (slopeSet v i₀ i₁)) := by
  have : j₀ ∈ (nextVertex_finite v h).toFinset := by
    simp_rw [nextVertex_j₀_eq_max v h]
    exact Finset.max'_mem _ _
  simp only [Set.Finite.mem_toFinset] at this
  exact this

lemma nextVertex_j₁_eq (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁) : v j₀ = j₁ := by
  simp_rw [nextStep] at h
  aesop

lemma nextVertex_j₀Finite (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ}
    (h :  nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁) : finite v j₀ := by
  have := nextVertex_j₁_eq v h
  simp_all [finite]

lemma nextVertex_slope_eq_sInf (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ}
    (h : nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    slopeReal i₀ j₀ i₁ j₁ = sInf (slopeSet v i₀ i₁) := by
  obtain ⟨hij, finj, j', hj', fin⟩ := nextVertex_j₀Mem v h
  simp_all [nextVertex_j₁_eq v h]

end nextVertexAPI

lemma segment_append_singleton_slopes_strictlyIncreasing (segs : List (Segment Γ)) (seg : Segment Γ)
    (h : slopes_strictlyIncreasing segs) (h' : ∀ s ∈ segs.getLast?, s.slope < seg.slope)
    : slopes_strictlyIncreasing (segs ++ [seg]) := by
  intro k hk
  by_cases hk' : k < segs.length
  · by_cases hk'' : k + 1 < segs.length
    · aesop
    · grind
  · grind

section convexity

-- definitely need a better name...
/-
  We do this by extending the 2nd slope, and considering the point with (a₂, b')... we show
  b' is greater than b₂.
-/
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

end convexity

theorem build_slopes_strictlyIncreasing (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} (segs : List (Segment Γ))
    (fuel : ℕ) (h_sorted : slopes_strictlyIncreasing segs) (h_conn : ends_at segs i₀ i₁)
    (h_bdd :  ∀ s ∈ segs.getLast?, BddBelow (slopeSet v s.i₀ s.i₁))
    (h_final1 : ∀ s ∈ segs.getLast?, s.slope = sInf (slopeSet v s.i₀ s.i₁))
    (h_final2 : ∀ s ∈ segs.getLast?, Set.Finite (achievingSet v s.i₀ s.i₁ s.slope))
    (h_final3 : ∀ s ∈ segs.getLast?, Set.Nonempty (achievingSet v s.i₀ s.i₁ s.slope))
    (h_final4 : ∀ s (hs : s ∈ segs.getLast?), s.j₀ = (Set.Finite.toFinset (h_final2 s hs)).max'
      ((h_final2 s hs).toFinset_nonempty.mpr (h_final3 s hs))) :
    slopes_strictlyIncreasing (getSegments (buildNewtonPolygon.build v i₀ i₁ segs fuel)) := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs h_sorted h_conn
  · simpa [buildNewtonPolygon.build] using h_sorted
  · unfold buildNewtonPolygon.build
    rcases h : nextStep v i₀ i₁ with ( _ | _ | _ | ⟨j₀, j₁⟩ | _ )
    all_goals try trivial
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
    split_ifs with hij
    · convert ih (segs ++ [mkSegment i₀ j₀ i₁ j₁ hij]) _ _ _ _ _ _ _
      · refine segment_append_singleton_slopes_strictlyIncreasing segs (mkSegment i₀ j₀ i₁ j₁ hij)
          h_sorted ?_
        intro s hs
        simp_rw [ends_at] at h_conn
        have help : s.i₀ < j₀ := by
          grind [s.lt]
        by_contra
        suffices Segment.slope (mkSegment s.i₀ j₀ s.i₁ j₁ help) ≤
            sInf (slopeSet v s.i₀ s.i₁) by
          have : sInf (slopeSet v s.i₀ s.i₁) = Segment.slope (mkSegment s.i₀ j₀ s.i₁ j₁ help) := by
            have : Segment.slope (mkSegment s.i₀ j₀ s.i₁ j₁ help) ∈ (slopeSet v s.i₀ s.i₁) := by
              exact ⟨j₀, help, nextVertex_j₀Finite v h, j₁, nextVertex_j₁_eq v h, rfl⟩
            grind [csInf_le (h_bdd s hs) this]
          have : j₀ ∈ (achievingSet v s.i₀ s.i₁ (Segment.slope s)) := by
            exact ⟨help, nextVertex_j₀Finite v h, j₁, nextVertex_j₁_eq v h,
              by simpa [h_final1 s hs] using this⟩
          grind [Finset.le_max' (h_final2 s hs).toFinset j₀ (by simpa using this)]
        specialize h_final1 s hs
        have e' : s.j₀ = i₀ := by grind
        have e : s.j₁ = i₁ := by grind
        simp_rw [← h_final1, Segment.slope, slopeReal, mkSegment, gt_iff_lt, not_lt, e, e'] at ⊢ this
        exact succSlope_le_Slope (by simpa [← e'] using Nat.cast_lt.mpr s.lt)
          (Nat.cast_lt.mpr hij) this
      · simp [ends_at, mkSegment]
      · simpa [mkSegment] using nextVertex_bddBelow v h
      · simpa using nextVertex_slope_eq_sInf v h
      all_goals simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.mem_def, Option.some.injEq, forall_eq']
      · convert nextVertex_finite v h
        simpa using nextVertex_slope_eq_sInf v h
        -- something about mkSegment.slope is not working nicely...
        -- I think I really do need to have the better version of not using slopes in ℝ
      · convert nextVertex_nonEmpty v h
        simpa using nextVertex_slope_eq_sInf v h
      · intro s hs -- once again mkSegment is causing a problem
        convert nextVertex_j₀_eq_max v h
        all_goals rw [← hs]
        all_goals try rfl -- Ideally I should be able to remove the intro s hs and get this to work cleanly
        simpa using nextVertex_slope_eq_sInf v h
    · trivial

lemma newtonPolygon.slopes_strictlyIncreasing (n : ℕ) :
    (newtonPolygon v n).slopes_strictlyIncreasing := by
  rcases h : findFirstFinite v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using
      emptyPolygon_wellFormed.slopes_strictlyIncreasing
  · convert build_slopes_strictlyIncreasing v [] n
      emptyPolygon_wellFormed.slopes_strictlyIncreasing (by trivial) (by aesop) (by aesop)
        (by aesop) (by aesop) (by grind)
    rw [getSegments_eq v n h]
    rfl

section infiniteRayAPI

lemma infiniteRay_bddBelow (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.infiniteRay m) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma infiniteRay_nonempty (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.infiniteRay m) :
    (achievingSet v i₀ i₁ m).Nonempty := by
  simp_rw [nextStep] at h
  split_ifs at h
  · simp_all only [StepResult.infiniteRay.injEq]
    rename_i _ _ _ fin
    exact Set.Infinite.nonempty fin
  · aesop

lemma infiniteRay_slope_eq_sInf (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.infiniteRay m) :
    m = sInf (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  split_ifs at h
  · simp only [StepResult.infiniteRay.injEq] at h
    rename_i _ _ t _
    convert Classical.choose_spec t
    aesop
  · aesop

lemma infiniteRay_ex (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.infiniteRay m) :
    ∃ j₀ : ℕ, j₀ > i₀ ∧ finite v j₀ ∧ ∃ j₁ : Γ, v j₀ = j₁ ∧  m = slopeReal i₀ j₀ i₁ j₁ := by
  obtain ⟨_, b⟩ := infiniteRay_nonempty v h
  simp_rw [achievingSet] at b
  aesop

end infiniteRayAPI

section limitingRayAPI

lemma limitingRay_bddBelow (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.limitingRay m) :
    BddBelow (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma limitingRay_nonempty (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.limitingRay m) : (slopeSet v i₀ i₁).Nonempty := by
  simp_rw [nextStep] at h
  split at h
  · trivial
  · rename_i fin
    exact Set.nonempty_iff_ne_empty.mpr fin

lemma limitingRay_slope_eq_sInf (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h :  nextStep v i₀ i₁ = StepResult.limitingRay m) : m = sInf (slopeSet v i₀ i₁) := by
  simp_rw [nextStep] at h
  split_ifs at h
  all_goals aesop

end limitingRayAPI

theorem build_ray_slope_valid (v : ValSeq Γ) (i₀ : ℕ) (i₁ : Γ) (segs : List (Segment Γ)) (fuel : ℕ)
    (h_end : ends_at segs i₀ i₁)
    (h_bdd :  ∀ s ∈ segs.getLast?, BddBelow (slopeSet v s.i₀ s.i₁))
    (h_final1 : ∀ s ∈ segs.getLast?, s.slope = sInf (slopeSet v s.i₀ s.i₁))
    (h_final2 : ∀ s ∈ segs.getLast?, Set.Finite (achievingSet v s.i₀ s.i₁ s.slope))
    (h_final3 : ∀ s ∈ segs.getLast?, Set.Nonempty (achievingSet v s.i₀ s.i₁ s.slope))
    (h_final4 : ∀ s (hs : s ∈ segs.getLast?), s.j₀ = (Set.Finite.toFinset (h_final2 s hs)).max'
      ((h_final2 s hs).toFinset_nonempty.mpr (h_final3 s hs))) :
    (getResult (buildNewtonPolygon.build v i₀ i₁ segs fuel)).ray_slope_valid := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs
  all_goals unfold buildNewtonPolygon.build
  · trivial
  · rw [ends_at] at h_end
    simp only [getResult]
    rcases h : nextStep v i₀ i₁ with ( _ | _ | _ | ⟨j₀, j₁⟩ | _ )
    all_goals try trivial
    all_goals simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    · unfold NewtonPolygonData.ray_slope_valid
      simp only
      split
      · simp_all only [Option.mem_def, Option.some.injEq, forall_eq']
        rename_i _  _ m _ _ r s hs hr t
        simp_rw [← hr]
        split_ifs
        · obtain ⟨k₀, hk₀1, hk₀2, k₁, hk₁, hkeq⟩ := infiniteRay_ex _ h
          by_contra
          have help : s.i₀ < k₀ := by grind [s.lt]
          suffices Segment.slope (mkSegment s.i₀ k₀ s.i₁ k₁ help) ≤
              sInf (slopeSet v s.i₀ s.i₁) by
            have : sInf (slopeSet v s.i₀ s.i₁) = Segment.slope (mkSegment s.i₀ k₀ s.i₁ k₁ help) := by
              have : Segment.slope (mkSegment s.i₀ k₀ s.i₁ k₁ help) ∈ (slopeSet v s.i₀ s.i₁) := by
                exact ⟨k₀, help, hk₀2, k₁, hk₁, rfl⟩
              grind [csInf_le h_bdd this]
            have : k₀ ∈ (achievingSet v s.i₀ s.i₁ (Segment.slope s)) := by
              exact ⟨help, hk₀2, k₁, hk₁, by simpa [h_final1] using this⟩
            grind [Finset.le_max' (h_final2 s hs).toFinset k₀ (by simpa using this)]
          simp only [not_lt] at this
          have foo : s.j₀ = i₀ := by
            grind
          simp_rw [← h_final1, Segment.slope, slopeReal, h_end, foo, hkeq] at ⊢ this
          exact succSlope_le_Slope (by rw [← foo]; exact Nat.cast_lt.mpr s.lt)
            (Nat.cast_lt.mpr hk₀1) this
        · trivial
      · trivial
    · split_ifs with hij
      · convert ih j₀ j₁ (segs ++ [mkSegment i₀ j₀ i₁ j₁ hij]) (by simp [ends_at, mkSegment])
           _ _ _ _ _
        all_goals intro s hs
        all_goals simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.mem_def, Option.some.injEq] at hs
        all_goals simp_rw [← hs]
        · exact nextVertex_bddBelow _ h
        · exact nextVertex_slope_eq_sInf _ h
        · convert nextVertex_finite _ h
          exact nextVertex_slope_eq_sInf _ h
        · convert nextVertex_nonEmpty _ h
          exact nextVertex_slope_eq_sInf _ h
        · simp_rw [mkSegment]
          convert nextVertex_j₀_eq_max _ h
          exact nextVertex_slope_eq_sInf _ h
      · trivial
    · unfold NewtonPolygonData.ray_slope_valid
      split
      · simp_all only [Option.mem_def, Option.some.injEq, forall_eq']
        rename_i m _ _ r s hs hr heq
        simp_rw [← hr]
        split_ifs with t
        · trivial
        · have : (mkFinalRay i₀ i₁ m false).slope = m := by rfl
          rw [this]
          simp_rw [limitingRay_slope_eq_sInf v h]
          refine le_csInf (limitingRay_nonempty _ h) ?_
          by_contra
          simp only [not_forall, not_le] at this
          obtain ⟨m', hm', m'_lt⟩ := this
          obtain ⟨a₀, ha₀, a₀_fin, a₁, ha₁, hm'⟩ := hm'
          have help : s.i₀ < a₀ := by grind [s.lt]
          suffices Segment.slope (mkSegment s.i₀ a₀ s.i₁ a₁ help) <
              sInf (slopeSet v s.i₀ s.i₁) by
            have contra := csInf_le h_bdd (mem_segmentSlope_slopeSet v s a₀ a₁ help a₀_fin ha₁)
            grind
          have foo : s.j₀ = i₀ := by
            grind
          simp_rw [← h_final1, Segment.slope, slopeReal, h_end, foo, hm'] at m'_lt ⊢
          exact succSlope_lt_Slope (by rw [← foo]; exact Nat.cast_lt.mpr s.lt) (Nat.cast_lt.mpr ha₀)
            m'_lt
      · trivial

lemma newtonPolygon.ray_slope_valid (n : ℕ) : (newtonPolygon v n).ray_slope_valid := by
  rcases h : findFirstFinite v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using emptyPolygon_wellFormed.ray_slope_valid
  · convert build_ray_slope_valid v i₀ i₁ [] n
      (emptyPolygon_wellFormed (Γ := Γ)).ray_slope_valid (by grind)
      (by aesop) (by aesop) (by aesop) (by grind)
    rw [getResult_eq v n h]

lemma newtonPolygon.wellFormed (n : ℕ) : (newtonPolygon v n).WellFormed where
  connected := newtonPolygon.connected v n
  slopes_strictlyIncreasing := newtonPolygon.slopes_strictlyIncreasing v n
  ray_connected := newtonPolygon.ray_connected v n
  ray_slope_valid := newtonPolygon.ray_slope_valid v n
