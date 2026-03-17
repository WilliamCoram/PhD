import Mathlib

namespace NewtonPolygon

variable (K : Type*) [CommSemiring K] [LinearOrder K] [Algebra K ℝ]

/-- The y-values of our points, for powerseries this will be the valuations of the coefficients.
-/
abbrev ValSeq := ℕ → WithTop K

variable (v : ValSeq K)

/-- Predicate: the i-th coefficient is nonzero (has finite valuation). -/
def finite (i : ℕ) : Prop := v i ≠ ⊤

/-- The set of indices with nonzero coefficients. -/
def support : Set ℕ := {i | finite K v i}

section Slopes

-- Ideally I would like this slope to be an element of K - for this I need to be able to subtract
-- in K, and divide by ℕ
-- What is the minimum assumption for this?

-- a ring K that is a ℚ-module, and such that ℝ is a K-algebra?

-- compute the slope as a real number (since ℝ is complete we can use sInf)
noncomputable
def slopeReal (x₀ x₁ : ℕ) (y₀ y₁ : K) : ℝ :=
  (algebraMap K ℝ y₁ - algebraMap K ℝ y₀) / (x₁ - x₀)

def slopeSet (i₀ : ℕ) (i₁ : K) : Set ℝ :=
  {m | ∃ j₀ : ℕ, j₀ > i₀ ∧ finite K v j₀ ∧ ∃ j₁ : K, v j₀ = j₁ ∧ m = slopeReal K i₀ j₀ i₁ j₁}

def achievingSet (i₀ : ℕ) (i₁ : K) (m : ℝ) : Set ℕ :=
  {j : ℕ | j > i₀ ∧ finite K v j ∧ ∃ j₁ : K, v j = j₁ ∧ m = slopeReal K i₀ j i₁ j₁}

end Slopes

section AlgorithmStep

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
  | nextVertex (j₀ : ℕ) (j₁ : K)
  /-- The infimum is not attained (all later points are strictly above the limiting line):
      final ray with no further lattice points. -/
  | limitingRay (m : ℝ)

/-- Compute the next step of the Newton polygon algorithm.
    Given current index i, determines what happens next.
    This is noncomputable because it uses sInf on K and classical choice. -/
noncomputable def nextStep (i₀ : ℕ) (i₁ : K) : StepResult K :=
  open Classical in
  if slopeSet K v i₀ i₁ = ∅ then
    -- No more finite values: tail
    StepResult.Tail
  else
    -- slopeSetR is nonempty, compute the infimum in K and check if it is achieved by some
    -- rational slope
    if ¬ (BddBelow (slopeSet K v i₀ i₁)) then
       -- if slopeSet is unbounded below we are left a vertical half-line down from i
      StepResult.unboundedBelow
    else
      if hm : ∃ m ∈ slopeSet K v i₀ i₁, m = sInf (slopeSet K v i₀ i₁) then
        if hInf : (achievingSet K v i₀ i₁ (Classical.choose hm)).Infinite then
          -- infinitely many points achieve the minimum slope
          StepResult.infiniteRay (Classical.choose hm)
        else
          -- Finitely many points achieve the minimum: take the maximum
          have hNonempty : (achievingSet K v i₀ i₁ (Classical.choose hm)).Nonempty := by
            simp only [↓existsAndEq, and_true] at hm
            use Classical.choose hm
            simp_rw [achievingSet]
            grind
          /-
          let j := (Set.not_infinite.mp hInf).toFinset.max'
            ((Set.not_infinite.mp hInf).toFinset_nonempty.mpr hNonempty)
            -- should probably change over to this?
          -/
          let j := (Set.not_infinite.mp hInf).toFinset.sup'
            ((Set.not_infinite.mp hInf).toFinset_nonempty.mpr hNonempty) id
            -- question: why is this sup' not max...
          match v j with
            | ⊤ => StepResult.Tail -- should not happen by construction
            | (j₁ : K) => StepResult.nextVertex j j₁
      else
        -- infimum not obtained (happens when the limit is in the completion)
        StepResult.limitingRay (sInf (slopeSet K v i₀ i₁))

end AlgorithmStep

section Segments

/-- A segment of the Newton polygon from vertex (i₀, i₁) to (j₀, j₁).
    All coordinates are concrete values (indices as ℕ, valuations as ℤ). -/
structure Segment where
  /-- Starting x-coordinate (index) -/
  i₀ : ℕ
  /-- Starting y-coordinate (valuation as integer) -/
  i₁ : K
  /-- Ending x-coordinate (index) -/
  j₀ : ℕ
  /-- Ending y-coordinate (valuation as integer) -/
  j₁ : K
  /-- i₀ < i₁ -/
  lt : i₀ < j₀
  deriving Repr

-- The horizontal length of a segment. -/
def Segment.length (seg : Segment K) : ℕ := seg.j₀ - seg.i₀

/-- The slope of a segment as a rational number. -/
noncomputable
def Segment.slope (seg : Segment K) : ℝ :=
  slopeReal K seg.i₀ seg.j₀ seg.i₁ seg.j₁

/-- A segment is valid if its endpoints correspond to actual nonzero coefficients
    with the claimed valuations. -/
def Segment.valid (seg : Segment K) : Prop :=
  finite K v seg.i₀ ∧ finite K v seg.j₀ ∧ v seg.i₀ = seg.i₁ ∧ v seg.j₀ = seg.j₁

/-- The y-coordinate of a point on the line from (i₀, i₁) with slope m. -/
noncomputable def lineAt (i₀ : ℕ) (i₁: K) (m : ℝ) (j₀ : ℕ) : ℝ :=
  algebraMap K ℝ i₁ + m * (j₀ - i₀)

/-- A segment is supporting if all points with j₀ > i₀ lie on or above the line. -/
def Segment.supporting (seg : Segment K) : Prop :=
  ∀ j₀ > seg.i₀, finite K v j₀ → ∀ (j₁ : K), j₁ = v j₀ →
  algebraMap K ℝ j₁ ≥ lineAt K seg.i₀ seg.i₁ seg.slope j₀

/-- A segment is tight if its endpoint (j₀, j₁) lies exactly on the line. -/
def Segment.tight (seg : Segment K) : Prop :=
  algebraMap K ℝ seg.j₁ = lineAt K seg.i₀ seg.i₁ seg.slope seg.j₀

/-- Every segment is tight by construction. -/
theorem Segment.tight_of_slope (seg : Segment K) : seg.tight := by
  have : (seg.j₀ : ℝ) - seg.i₀ ≠ 0 := by
     exact ne_of_gt (by simpa using seg.lt)
  simp only [tight, lineAt, Segment.slope, slopeReal]
  grind

/-- A final ray of the Newton polygon starting from (i₀, v₀) with slope m. -/
structure FinalRay where
  /-- Starting x-coordinate (index) -/
  i₀ : ℕ
  /-- Starting y-coordinate (valuation as integer) -/
  i₁ : K
  /-- The slope of the ray -/
  slope : ℝ
  /-- Whether the ray contains infinitely many lattice points -/
  hitsInfinitelyMany : Bool
  -- deriving Repr -- this breaks, so I really do want to have this slope as an element of K!

/-- A final ray is supporting if all later points lie on or above the ray. -/
def FinalRay.supporting (ray : FinalRay K) : Prop :=
  ∀ j > ray.i₀, finite K v j → ∀ (j₁ : K), v j = j₁ →
  algebraMap K ℝ j₁ ≥ lineAt K ray.i₀ ray.i₁ ray.slope j

end Segments

section NPStructure

/-- The Newton polygon of a power series, consisting of:
    - A (possibly empty) list of segments with strictly increasing slopes
    - An optional final ray -/
structure NewtonPolygonData where
  /-- The list of segments. -/
  segments : List (Segment K)
  /-- The final ray, if the polygon terminates with a ray. -/
  finalRay : Option (FinalRay K)
  --deriving Repr

/-- Predicate to show if segments are properly connected. -/
def NewtonPolygonData.connected (npd : NewtonPolygonData K) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.segments.length,
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).j₀ = (npd.segments[k + 1]'hk).i₀ ∧
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).j₁ = (npd.segments[k + 1]'hk).i₁

/-- Predicate to show if slopes are strictly increasing. -/
def NewtonPolygonData.slopes_strictlyIncreasing (npd : NewtonPolygonData K) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.segments.length,
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).slope < (npd.segments[k + 1]'hk).slope

/-- Predicate to show the final ray is properly connected to the last segment. -/
def NewtonPolygonData.ray_connected (npd : NewtonPolygonData K) : Prop :=
  match npd.finalRay, npd.segments.getLast? with
  | some r, some s => r.i₀ = s.j₀ ∧ r.i₁ = s.j₁
  | _, _ => True

/-- Predicate to show the final ray's slope is at least the last segment's slope. -/
def  NewtonPolygonData.ray_slope_valid (npd : NewtonPolygonData K) : Prop :=
  match npd.finalRay, npd.segments.getLast? with
  | some r, some s => if r.hitsInfinitelyMany = true then s.slope < r.slope
                        else s.slope ≤ r.slope
  | _, _ => True
  -- this has to be ≤ as we can consider the example of 1 + x + p ∑ x^n

/-- A well-formed Newton polygon satisfies all connectivity and monotonicity conditions. -/
structure NewtonPolygonData.WellFormed (npd : NewtonPolygonData K) : Prop where
  connected : npd.connected
  slopes_strictlyIncreasing : npd.slopes_strictlyIncreasing
  ray_connected : npd.ray_connected
  ray_slope_valid : npd.ray_slope_valid

/-- The empty Newton polygon (for the zero series or constant series). -/
def emptyPolygon : NewtonPolygonData K where
  segments := []
  finalRay := none

/-- The empty polygon is well-formed. -/
theorem emptyPolygon_wellFormed : (emptyPolygon K).WellFormed where
  connected _ hk := by simp [emptyPolygon] at hk
  slopes_strictlyIncreasing _ hk := by simp [emptyPolygon] at hk
  ray_connected := by simp [emptyPolygon, NewtonPolygonData.ray_connected]
  ray_slope_valid := by simp [emptyPolygon, NewtonPolygonData.ray_slope_valid]

end NPStructure

section ComputingNP

variable {R : Type*} [Semiring R]

noncomputable
def toValSeq (f : PowerSeries R) (v : R → WithTop K) : ValSeq K :=
  fun i => v (PowerSeries.coeff i f)

/-- Create a single segment given valid data. -/
def mkSegment (i₀ j₀ : ℕ) (i₁ j₁ : K) (hlt : i₀ < j₀) : Segment K :=
  {i₀ := i₀, i₁ := i₁, j₀ := j₀, j₁ := j₁, lt := hlt}

lemma mem_segmentSlope_slopeSet (s : Segment K) (a₀ : ℕ) (a₁ : K) (h : s.i₀ < a₀)
    (h_fin : finite K v a₀) (ha₁ : v a₀ = a₁) : Segment.slope K (mkSegment K s.i₀ a₀ s.i₁ a₁ h) ∈
    slopeSet K v s.i₀ s.i₁ := by
  simp_rw [slopeSet, Segment.slope]
  simp only [gt_iff_lt, Set.mem_setOf_eq]
  use a₀
  refine ⟨h, h_fin, ?_⟩
  use a₁
  exact ⟨ha₁, rfl⟩

/-- Create a final ray. -/
def mkFinalRay (i₀ : ℕ) (i₁ : K) (slope : ℝ) (infinite : Bool) : FinalRay K :=
  {i₀ := i₀, i₁ := i₁, slope := slope, hitsInfinitelyMany := infinite}

/-- Configuration for polygon computation to handle termination. -/
structure ComputeConfig (n : ℕ) where
  /-- Maximum number of segments to compute (for termination). -/
  maxSegments : ℕ := n

/-- Find the first index with finite valuation, starting from a given position. -/
noncomputable
def findFirstFinite (startIdx : ℕ) : Option (ℕ × K) := open Classical in
  if h : ∃ i ≥ startIdx, finite K v i then
    let i := Nat.find h
    match v i with
    | ⊤ => none  -- contradicts finiteness
    | (val : K) => some (i, val)
  else
    none

/-- Result of iteratively building the Newton polygon. -/
inductive BuildResult where
  /-- Successfully built the polygon. -/
  | complete (npd : NewtonPolygonData K)
  /-- Hit the segment limit before completing. -/
  | incomplete (npd : NewtonPolygonData K) (reason : String)

/-- Build the Newton polygon by iterating the nextStep algorithm.
    This is the main computational function.

    The algorithm follows Gouvêa Section 7.4:
    1. Start at the first nonzero coefficient (i₀, v₀)
    2. Rotate the line counterclockwise to find minimum slope
    3. Move to the rightmost point achieving minimum slope
    4. Repeat until termination (polynomial tail, infinite ray, or limiting ray)
-/
noncomputable def buildNewtonPolygon {n : ℕ} (cfg : ComputeConfig n := {}) : BuildResult K :=
  open Classical in
  -- Find the starting point (first finite valuation)
  match findFirstFinite K v 0 with
  | none => BuildResult.complete (emptyPolygon K)
  | some (i, v_i) =>
    -- Iteratively build segments
    let rec build (currentIdx : ℕ) (currentVal : K) (segments : List (Segment K)) (fuel : ℕ) :
        BuildResult K :=
      if fuel = 0 then
        BuildResult.incomplete ⟨segments, none⟩ "reached segment limit"
      else
        match nextStep K v currentIdx currentVal with
        | StepResult.Tail =>
            -- No more nonzero coefficients: series is essentially a polynomial
            BuildResult.complete ⟨segments, none⟩
        | StepResult.unboundedBelow =>
            -- No more segments: valuation is unbounded below
            BuildResult.complete ⟨segments, none⟩
        | StepResult.infiniteRay m =>
            -- Infinitely many points on a line of slope m
            let ray := mkFinalRay K currentIdx currentVal m true
            BuildResult.complete ⟨segments, some ray⟩
        | StepResult.limitingRay m =>
            -- Limiting slope not achieved by any point
            let ray := mkFinalRay K currentIdx currentVal m false
            BuildResult.complete ⟨segments, some ray⟩
        | StepResult.nextVertex j v_j =>
            if h : currentIdx < j then
              let seg := mkSegment K currentIdx j currentVal v_j h
              build j v_j (segments ++ [seg]) (fuel - 1)
            else
              -- Shouldn't happen
              BuildResult.incomplete ⟨segments, none⟩ "invalid vertex ordering"
    build i v_i [] cfg.maxSegments

/-- Extract the Newton polygon data, of the first n segments. -/
noncomputable
def newtonPolygon {n : ℕ} (cfg : ComputeConfig n := {}) : NewtonPolygonData K :=
  match buildNewtonPolygon K v cfg with
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

end ComputingNP

section API

/-- Get all slopes of the Newton polygon (the "Newton slopes"). -/
noncomputable
def NewtonPolygonData.slopes (npd : NewtonPolygonData K) : List ℝ :=
  npd.segments.map (Segment.slope K)

/-- Get the length of each segment (projection onto x-axis). -/
def NewtonPolygonData.lengths (npd : NewtonPolygonData K) : List ℕ :=
  npd.segments.map (Segment.length K)

/-- Get the vertices (break points) of the polygon as (index, valuation) pairs. -/
def NewtonPolygonData.vertices (npd : NewtonPolygonData K) : List (ℕ × K) :=
  match npd.segments with
  | [] => []
  | seg :: rest =>
    (seg.i₀, seg.i₁) :: rest.foldl (fun acc s => acc ++ [(s.j₀, s.j₁)]) [(seg.j₀, seg.j₁)]

/-- Get slopes paired with their lengths (useful for root counting). -/
noncomputable
def NewtonPolygonData.slopesWithLengths (npd : NewtonPolygonData K) : List (ℝ × ℕ) :=
  npd.segments.map fun seg => (seg.slope, seg.length)

/-- Total horizontal extent of the polygon. -/
def NewtonPolygonData.totalLength (npd : NewtonPolygonData K) : ℕ :=
  npd.lengths.foldl (· + ·) 0

/-- Check if the polygon is pure (has only one slope).
    Following Gouvêa Definition 7.4.1: A polynomial is pure if its Newton
    polygon has only one slope. -/
def NewtonPolygonData.isPure (npd : NewtonPolygonData K) : Bool :=
  npd.segments.length ≤ 1 && npd.finalRay.isNone

/-- Get the unique slope if the polygon is pure, otherwise none. -/
noncomputable
def NewtonPolygonData.pureSlope (npd : NewtonPolygonData K) : Option ℝ :=
  if npd.isPure then npd.slopes.head? else none

end API

section isWellFormed

def getSegments : BuildResult K → List (Segment K)
  | BuildResult.complete npd => npd.segments
  | BuildResult.incomplete npd _ => npd.segments

lemma getSegments_eq (n : ℕ) (cfg : ComputeConfig n := {}) (i₀ : ℕ) (i₁ : K)
    (h : findFirstFinite K v 0 = some (i₀, i₁)) :
    getSegments K (buildNewtonPolygon.build K v i₀ i₁ [] cfg.maxSegments) =
    (newtonPolygon K v cfg).segments := by
  unfold getSegments newtonPolygon buildNewtonPolygon
  aesop

def segments_connected (segs : List (Segment K)) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < segs.length,
    (segs[k]'(Nat.lt_of_succ_lt hk)).j₀ = (segs[k + 1]'hk).i₀ ∧
    (segs[k]'(Nat.lt_of_succ_lt hk)).j₁ = (segs[k + 1]'hk).i₁

def ends_at (segs : List (Segment K)) (j₀ : ℕ) (j₁ : K) : Prop :=
  match segs.getLast? with
  | some s => s.j₀ = j₀ ∧ s.j₁ = j₁
  | none => True

theorem build_connected (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (segs : List (Segment K)) (fuel : ℕ)
    (h_conn : segments_connected K segs) (h_end : ends_at K segs i₀ i₁) :
    segments_connected K (getSegments K (buildNewtonPolygon.build K v i₀ i₁ segs fuel)) := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs h_conn h_end
  · simp [getSegments, buildNewtonPolygon.build, h_conn]
  · unfold buildNewtonPolygon.build
    rcases h : nextStep K v i₀ i₁ with ( _ | _ | _ | ⟨j₀, j₁⟩ | _ )
    all_goals try exact h_conn
    simp_all only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      segments_connected, ends_at]
    split_ifs with hij
    · convert ih _ _ _ _ _ using 1
      · intro k hk
        rcases lt_trichotomy k (segs.length - 1) with hk' | rfl | hk'
        all_goals try grind
        simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
          Order.lt_add_one_iff, Order.add_one_le_iff, tsub_lt_self_iff] at hk
        have : ¬ (segs.length - 1 + 1 < segs.length) := by
          grind
        simp only [List.getElem_append, List.getElem_singleton, tsub_lt_self_iff, hk, this]
        simp only [List.getLast?_eq_getElem?, tsub_lt_self_iff, hk, and_self, getElem?_pos] at h_end
        exact h_end
      · simp [mkSegment]
    · exact h_conn

lemma newtonPolygon.connected (n : ℕ) (cfg : ComputeConfig n := {}) :
    NewtonPolygonData.connected K (newtonPolygon K v cfg) := by
  rcases h : findFirstFinite K v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using (emptyPolygon_wellFormed K).connected
  · convert build_connected K v i₀ i₁ [] cfg.maxSegments (emptyPolygon_wellFormed K).connected
      (by simp only [ends_at, List.getLast?_nil])
    rw [getSegments_eq K v n cfg i₀ i₁ h]
    rfl

def getResult : BuildResult K → NewtonPolygonData K
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

lemma getResult_eq (n : ℕ) (cfg : ComputeConfig n := {}) (i₀ : ℕ) (i₁ : K)
    (h : findFirstFinite K v 0 = some (i₀, i₁)) : newtonPolygon K v cfg =
    getResult K (buildNewtonPolygon.build K v i₀ i₁ [] cfg.maxSegments) := by
  unfold getResult newtonPolygon buildNewtonPolygon
  aesop

theorem build_ray_connected (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (segs : List (Segment K)) (fuel : ℕ)
    (h_end : ends_at K segs i₀ i₁) :
    (getResult K (buildNewtonPolygon.build K v i₀ i₁ segs fuel)).ray_connected := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs
  all_goals unfold buildNewtonPolygon.build
  · trivial
  · rw [ends_at] at h_end
    simp only [getResult, NewtonPolygonData.ray_connected, mkFinalRay]
    rcases h : nextStep K v i₀ i₁ with ( _ | _ | _ | ⟨j₀, j₁⟩ | _ )
    all_goals try grind
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
    split_ifs with hij
    · refine ih _ _ _ ?_
      simp_rw [ends_at]
      aesop
    · trivial

lemma newtonPolygon.ray_connected (n : ℕ) (cfg : ComputeConfig n := {}) :
    NewtonPolygonData.ray_connected K (newtonPolygon K v cfg) := by
  rcases h : findFirstFinite K v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using (emptyPolygon_wellFormed K).ray_connected
  · convert build_ray_connected K v i₀ i₁ [] cfg.maxSegments
      (emptyPolygon_wellFormed K).ray_connected
    exact getResult_eq K v n cfg i₀ i₁ h

def slopes_strictlyIncreasing (segs : List (Segment K)) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < segs.length,
    (segs[k]'(Nat.lt_of_succ_lt hk)).slope < (segs[k + 1]'hk).slope

lemma nextStep_inf_eq_slope (v : ValSeq K) (i₀ j₀ : ℕ) (i₁ j₁ : K)
    (h_step : nextStep K v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    slopeReal K i₀ j₀ i₁ j₁ = sInf (slopeSet K v i₀ i₁) := by
  unfold nextStep at h_step
  split_ifs at h_step with h_nonempty h_bdd hm h
  convert (Classical.choose_spec hm).2
  cases h_step' : v (Finset.sup' (Set.Finite.toFinset (Classical.not_not.mp h)) (by grind) id)
  · aesop
  · simp_all only [id_eq, StepResult.nextVertex.injEq]
    have h_sup : j₀ ∈ achievingSet K v i₀ i₁ (Classical.choose hm) := by
      simp_rw [← h_step.1]
      apply (Set.Finite.mem_toFinset (Classical.not_not.mp h)).mp
      exact Finset.max'_mem _ _
    obtain ⟨_, _, _, _, final⟩ := h_sup
    aesop

lemma segment_append_singleton_slopes_strictlyIncreasing (segs : List (Segment K)) (seg : Segment K)
    (h_sorted : slopes_strictlyIncreasing K segs) (h_le : ∀ s ∈ segs.getLast?, s.slope < seg.slope)
    : slopes_strictlyIncreasing K (segs ++ [seg]) := by
  intro k hk
  by_cases hk' : k < segs.length
  · by_cases hk'' : k + 1 < segs.length
    · aesop
    · grind
  · grind

section nextVertexAPI

lemma aaa (v : ValSeq K) (i₀ j₀ : ℕ) (i₁ j₁ : K)
    (h :  nextStep K v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    BddBelow (slopeSet K v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma foo (v : ValSeq K) (i₀ j₀ : ℕ) (i₁ j₁ : K)
    (h :  nextStep K v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    (achievingSet K v i₀ i₁ (slopeReal K i₀ j₀ i₁ j₁)).Nonempty := by
  have := nextStep_inf_eq_slope K v i₀ j₀ i₁ j₁ h
  simp_rw [nextStep] at h
  split_ifs at h
  aesop

lemma bar (v : ValSeq K) (i₀ j₀ : ℕ) (i₁ j₁ : K)
    (h :  nextStep K v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    (achievingSet K v i₀ i₁ (slopeReal K i₀ j₀ i₁ j₁)).Finite := by
  have := nextStep_inf_eq_slope K v i₀ j₀ i₁ j₁ h
  simp_rw [nextStep] at h
  split_ifs at h
  rename_i _ _ c d
  simp_rw [(Classical.choose_spec c).2] at d
  aesop

lemma err (v : ValSeq K) (i₀ j₀ : ℕ) (i₁ j₁ : K)
    (h :  nextStep K v i₀ i₁ = StepResult.nextVertex j₀ j₁) :
    (bar K v _ _ _ _ h).toFinset.sup'
    ((bar K v _ _ _ _ h).toFinset_nonempty.mpr (foo K v _ _ _ _ h)) id = j₀ := by
  have := nextStep_inf_eq_slope K v i₀ j₀ i₁ j₁ h
  simp_rw [nextStep] at h
  split_ifs at h with a b c d
  split at h
  · trivial
  · simp_all only [StepResult.nextVertex.injEq]
    convert h.1
    exact (Classical.choose_spec c).2.symm

lemma umm (v : ValSeq K) (i₀ j₀ : ℕ) (i₁ j₁ : K)
    (h :  nextStep K v i₀ i₁ = StepResult.nextVertex j₀ j₁) : finite K v j₀ := by
  simp_rw [nextStep] at h
  have h' := h
  split_ifs at h with _ _ c _
  split at h
  · trivial
  · rename_i _ _ final
    simp_rw [(Classical.choose_spec c).2, ← nextStep_inf_eq_slope K v _ _ _ _ h',
      err K v _ _ _ _ h'] at final
    simp_all [finite]

lemma ahh (v : ValSeq K) (i₀ j₀ : ℕ) (i₁ j₁ : K)
    (h :  nextStep K v i₀ i₁ = StepResult.nextVertex j₀ j₁) : v j₀ = j₁ := by
  simp_rw [nextStep] at h
  have := err K v i₀ j₀ i₁ j₁ h
  split_ifs at h
  split at h
  · trivial
  · aesop

end nextVertexAPI


lemma test (a₀ a₁ a₂ : ℝ) (b₀ b₁ b₂ : ℝ) (ha1 : a₀ < a₁) (hb2 : a₁ < a₂)
    (hab : (b₂ - b₁) / (a₂ - a₁) ≤ (b₁ - b₀) / (a₁ - a₀)) :
    (b₂ - b₀) / (a₂ - a₀) ≤ (b₁ - b₀) / (a₁ - a₀) := by
  let m := (b₂ - b₁) / (a₂ - a₁)
  let l := (b₁ - b₀) / (a₁ - a₀)
  let n := (b₂ - b₀) / (a₂ - a₀)
  let x := b₀ + l * (a₂ - a₀)
  have x' : x = b₁ + l * (a₂ - a₁) := by grind
  have leq' : m ≤ l := by grind
  have fin : b₂ ≤ x := by
    have : b₂ = b₁ + m * (a₂ - a₁) := by grind
    simp_rw [this]
    simp_rw [x']
    simp only [add_le_add_iff_left, ge_iff_le]
    exact mul_le_mul_of_nonneg_right (a := a₂ - a₁) leq' (by grind)
  simp_rw [x, l] at fin
  rw [add_comm, ← tsub_le_iff_right] at fin
  have : a₂ - a₀ > 0 := by grind
  rw [div_le_iff₀' this, mul_comm]
  exact fin

theorem build_slopes_strictlyIncreasing (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (segs : List (Segment K))
    (fuel : ℕ) (h_sorted : slopes_strictlyIncreasing K segs) (h_conn : ends_at K segs i₀ i₁)
    (h_bdd :  ∀ s ∈ segs.getLast?, BddBelow (slopeSet K v s.i₀ s.i₁))
    (h_final1 : ∀ s ∈ segs.getLast?, s.slope = sInf (slopeSet K v s.i₀ s.i₁))
    (h_final2 : ∀ s ∈ segs.getLast?, Set.Finite (achievingSet K v s.i₀ s.i₁ s.slope))
    (h_final3 : ∀ s ∈ segs.getLast?, Set.Nonempty (achievingSet K v s.i₀ s.i₁ s.slope))
    (h_final4 : ∀ s (hs : s ∈ segs.getLast?), s.j₀ = (Set.Finite.toFinset (h_final2 s hs)).sup'
      ((h_final2 s hs).toFinset_nonempty.mpr (h_final3 s hs)) id) :
    slopes_strictlyIncreasing K (getSegments K (buildNewtonPolygon.build K v i₀ i₁ segs fuel)) := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs h_sorted h_conn
  · simpa [buildNewtonPolygon.build] using h_sorted
  · unfold buildNewtonPolygon.build
    split_ifs
    all_goals try trivial
    rcases h : nextStep K v i₀ i₁ with ( _ | _ | _ | ⟨j₀, j₁⟩ | _ )
    all_goals try trivial
    simp only [add_tsub_cancel_right]
    split_ifs with hij
    · unfold getSegments
      convert ih j₀ j₁ (segs ++ [mkSegment K i₀ j₀ i₁ j₁ hij]) _ _ _ _ _ _ _
      · refine segment_append_singleton_slopes_strictlyIncreasing K segs ?_ h_sorted ?_
        intro s hs
        simp_rw [h_final1 s hs]
        by_contra
        simp only [not_lt] at this
        have help : s.i₀ < j₀ := by
          have t : s.i₀ < s.j₀ := s.lt
          have tt : s.j₀ = i₀ := by
            simp_rw [ends_at] at h_conn
            split at h_conn
            · grind
            · grind
          grind
        suffices Segment.slope K (mkSegment K s.i₀ j₀ s.i₁ j₁ help) ≤ sInf (slopeSet K v s.i₀ s.i₁) by
          specialize h_final4 s hs
          have tt : s.j₀ = i₀ := by
            simp_rw [ends_at] at h_conn
            split at h_conn
            · grind
            · grind
          simp_rw [tt] at h_final4
          have leq : Segment.slope K (mkSegment K s.i₀ j₀ s.i₁ j₁ help) = sInf (slopeSet K v s.i₀ s.i₁) := by
            have int : Segment.slope K (mkSegment K s.i₀ j₀ s.i₁ j₁ help) ∈ (slopeSet K v s.i₀ s.i₁) := by
              simp_rw [slopeSet]
              simp only [gt_iff_lt, Set.mem_setOf_eq]
              use j₀
              refine ⟨help, umm K v i₀ j₀ i₁ j₁ h, ?_⟩
              use j₁
              exact ⟨ahh K v i₀ j₀ i₁ j₁ h, rfl⟩
            have : Segment.slope K (mkSegment K s.i₀ j₀ s.i₁ j₁ help) ≥
                sInf (slopeSet K v s.i₀ s.i₁) := by
              exact csInf_le (h_bdd s hs) int
            grind
          have : j₀ ∈ (achievingSet K v s.i₀ s.i₁ (Segment.slope K s)) := by
            simp_rw [achievingSet]
            simp only [gt_iff_lt, Set.mem_setOf_eq]
            refine ⟨help, umm K v i₀ j₀ i₁ j₁ h, ?_⟩
            use j₁
            refine ⟨ahh K v i₀ j₀ i₁ j₁ h, ?_⟩
            rw [h_final1 s hs]
            exact leq.symm
          simp_rw [h_final4] at hij
          have : j₀ ∈ (h_final2 s hs).toFinset := by
            simpa using this
          have : j₀ ≤ (h_final2 s hs).toFinset.sup'
              ((Set.Finite.toFinset_nonempty (h_final2 s hs)).mpr (h_final3 s hs)) id := by
            exact Finset.le_sup' (s := (h_final2 s hs).toFinset) id this
            --exact Finset.le_max (s := (h_final2 s hs).toFinset) this -- when move to Finset.max'
          grind
        specialize h_final1 s hs
        simp_rw [← h_final1] at *
        simp_rw [Segment.slope, slopeReal, mkSegment] at *
        have e : s.j₁ = i₁ := by
          simp_rw [ends_at] at h_conn
          split at h_conn
          · grind
          · grind
        have e' : s.j₀ = i₀ := by
          simp_rw [ends_at] at h_conn
          split at h_conn
          · grind
          · grind
        rw [e, e'] at this ⊢
        exact test s.i₀ i₀ j₀ ((algebraMap K ℝ) s.i₁) ((algebraMap K ℝ) i₁) ((algebraMap K ℝ) j₁)
          (by rw [← e']; exact Nat.cast_lt.mpr s.lt) (Nat.cast_lt.mpr hij) this
      · simp_rw [ends_at, List.getLast?_append, List.getLast?_singleton, Option.some_or]
        exact ⟨rfl, rfl⟩
      · simpa [mkSegment] using (aaa K v i₀ j₀ i₁ j₁ h)
      · simpa using nextStep_inf_eq_slope K v i₀ j₀ i₁ j₁ h
      all_goals intro s hs
      all_goals simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.mem_def, Option.some.injEq] at hs
      · simp [← hs]
        exact bar K v _ _ _ _ h
      · simp_rw [← hs]
        exact foo K v _ _ _ _ h
      · simp_rw [← hs, err K v _ _ _ _ h]
        rfl
    · trivial

lemma newtonPolygon.slopes_strictlyIncreasing (n : ℕ) (cfg : ComputeConfig n := {}) :
    (newtonPolygon K v cfg).slopes_strictlyIncreasing := by
  rcases h : findFirstFinite K v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using
      (emptyPolygon_wellFormed K).slopes_strictlyIncreasing
  · convert build_slopes_strictlyIncreasing K v i₀ i₁ [] cfg.maxSegments
      (emptyPolygon_wellFormed K).slopes_strictlyIncreasing (by trivial)
    rw [getSegments_eq K v n cfg i₀ i₁]
    all_goals aesop


---- ray slope:

section infiniteRayAPI

lemma aaa' (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (m : ℝ)
    (h :  nextStep K v i₀ i₁ = StepResult.infiniteRay m) :
    BddBelow (slopeSet K v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma foo' (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (m : ℝ)
    (h :  nextStep K v i₀ i₁ = StepResult.infiniteRay m) :
    (achievingSet K v i₀ i₁ m).Nonempty := by
  simp_rw [nextStep] at h
  split_ifs at h
  · simp_all only [StepResult.infiniteRay.injEq]
    rename_i _ _ _ fin
    exact Set.Infinite.nonempty fin
  · aesop

lemma wee (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (m : ℝ)
    (h :  nextStep K v i₀ i₁ = StepResult.infiniteRay m) :
    m = sInf (slopeSet K v i₀ i₁) := by
  simp_rw [nextStep] at h
  split_ifs at h
  · simp only [StepResult.infiniteRay.injEq] at h
    rename_i _ _ t _
    convert Classical.choose_spec t
    aesop
  · aesop

lemma ex (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (m : ℝ)
    (h :  nextStep K v i₀ i₁ = StepResult.infiniteRay m) :
    ∃ j₀ : ℕ, j₀ > i₀ ∧ finite K v j₀ ∧ ∃ j₁ : K, v j₀ = j₁ ∧  m = slopeReal K i₀ j₀ i₁ j₁ := by
  obtain ⟨a, b⟩ := foo' K v i₀ i₁ m h
  simp_rw [achievingSet] at b
  aesop

end infiniteRayAPI

section limitingRayAPI

lemma aaa'' (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (m : ℝ)
    (h :  nextStep K v i₀ i₁ = StepResult.limitingRay m) :
    BddBelow (slopeSet K v i₀ i₁) := by
  simp_rw [nextStep] at h
  grind

lemma grr (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (m : ℝ)
    (h :  nextStep K v i₀ i₁ = StepResult.limitingRay m) : (slopeSet K v i₀ i₁).Nonempty := by
  simp_rw [nextStep] at h
  split at h
  · trivial
  · rename_i fin
    exact Set.nonempty_iff_ne_empty.mpr fin

lemma wee' (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (m : ℝ)
    (h :  nextStep K v i₀ i₁ = StepResult.limitingRay m) : m = sInf (slopeSet K v i₀ i₁) := by
  simp_rw [nextStep] at h
  split_ifs at h
  all_goals aesop

end limitingRayAPI

lemma test' (a₀ a₁ a₂ : ℝ) (b₀ b₁ b₂ : ℝ) (ha1 : a₀ < a₁) (hb2 : a₁ < a₂)
    (hab : (b₂ - b₁) / (a₂ - a₁) < (b₁ - b₀) / (a₁ - a₀)) :
    (b₂ - b₀) / (a₂ - a₀) < (b₁ - b₀) / (a₁ - a₀) := by
  let m := (b₂ - b₁) / (a₂ - a₁)
  let l := (b₁ - b₀) / (a₁ - a₀)
  let n := (b₂ - b₀) / (a₂ - a₀)
  let x := b₀ + l * (a₂ - a₀)
  have x' : x = b₁ + l * (a₂ - a₁) := by grind
  have leq' : m < l := by grind
  have fin : b₂ < x := by
    have : b₂ = b₁ + m * (a₂ - a₁) := by grind
    simp_rw [this]
    simp_rw [x']
    simp only [add_lt_add_iff_left, gt_iff_lt]
    exact mul_lt_mul_of_pos_right (a := a₂ - a₁) leq' (by grind)
  simp_rw [x, l] at fin
  rw [add_comm] at fin
  have : a₂ - a₀ > 0 := by grind
  rw [div_lt_iff₀' this, mul_comm]
  exact sub_right_lt_of_lt_add fin

theorem build_ray_slope_valid (v : ValSeq K) (i₀ : ℕ) (i₁ : K) (segs : List (Segment K)) (fuel : ℕ)
    (h_end : ends_at K segs i₀ i₁)
    (h_bdd :  ∀ s ∈ segs.getLast?, BddBelow (slopeSet K v s.i₀ s.i₁))
    (h_final1 : ∀ s ∈ segs.getLast?, s.slope = sInf (slopeSet K v s.i₀ s.i₁))
    (h_final2 : ∀ s ∈ segs.getLast?, Set.Finite (achievingSet K v s.i₀ s.i₁ s.slope))
    (h_final3 : ∀ s ∈ segs.getLast?, Set.Nonempty (achievingSet K v s.i₀ s.i₁ s.slope))
    (h_final4 : ∀ s (hs : s ∈ segs.getLast?), s.j₀ = (Set.Finite.toFinset (h_final2 s hs)).sup'
      ((h_final2 s hs).toFinset_nonempty.mpr (h_final3 s hs)) id) :
    (getResult K (buildNewtonPolygon.build K v i₀ i₁ segs fuel)).ray_slope_valid := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs
  all_goals unfold buildNewtonPolygon.build
  · trivial
  · rw [ends_at] at h_end
    simp only [getResult]
    rcases h : nextStep K v i₀ i₁ with ( _ | _ | _ | ⟨j₀, j₁⟩ | _ )
    all_goals try trivial
    all_goals simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    · unfold NewtonPolygonData.ray_slope_valid
      simp only
      split
      · simp_all only [Option.mem_def, id_eq, Option.some.injEq, forall_eq']
        rename_i _ _ _ _ m _ _ r s hs hr t
        simp_rw [← hr]
        split_ifs
        · have : (mkFinalRay K i₀ i₁ m true).slope = m := by rfl
          simp_rw [this]
          obtain ⟨k₀, hk₀1, hk₀2, k₁, hk₁, hkeq⟩ := ex K v i₀ i₁ m h
          simp_rw [hkeq]
          by_contra
          have help : s.i₀ < k₀ := by
            calc
              _ ≤ s.j₀ := s.lt
              _ = i₀ := by grind
              _ ≤ k₀ := by grind
          suffices Segment.slope K (mkSegment K s.i₀ k₀ s.i₁ k₁ help) ≤
              sInf (slopeSet K v s.i₀ s.i₁) by
            -- literally the same proof as in slopesIncreasing ... but with different notation
            -- do this after I decide how I can clean the above up!
            sorry
          simp only [gt_iff_lt, not_lt] at this
          have foo : s.j₀ = i₀ := by
            grind
          simp_rw [← h_final1, Segment.slope, slopeReal, h_end, foo] at *
          have foo : s.j₀ = i₀ := by
            grind
          exact test s.i₀ i₀ k₀ (algebraMap K ℝ s.i₁) (algebraMap K ℝ i₁) (algebraMap K ℝ k₁)
            (by rw [← foo]; exact Nat.cast_lt.mpr s.lt) (Nat.cast_lt.mpr hk₀1) this
        · trivial
      · trivial
    · split_ifs with hij
      · convert ih j₀ j₁ (segs ++ [mkSegment K i₀ j₀ i₁ j₁ hij]) (by simp [ends_at, mkSegment])
           _ _ _ _ _
        all_goals intro s hs
        all_goals simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.mem_def, Option.some.injEq] at hs
        all_goals simp_rw [← hs]
        · exact aaa _ _ _ _ _ _ h
        · exact nextStep_inf_eq_slope _ _ _ _ _ _ h
          -- note as Chris mentioned this means I can supress a lot of the informatio in the API!
        · exact bar K v _ _ _ _ h
        · exact foo _ _ _ _ _ _ h
        · simpa [mkSegment] using (err _ _ _ _ _ _ h).symm
      · trivial
    · unfold NewtonPolygonData.ray_slope_valid
      simp only
      split
      · simp_all only [Option.mem_def, id_eq, Option.some.injEq, forall_eq']
        rename_i m _ _ r s hs hr heq
        simp_rw [← hr]
        split_ifs with t
        · trivial
        · have : (mkFinalRay K i₀ i₁ m false).slope = m := by rfl
          simp_rw [this]
          simp_rw [wee' _ _ _ _ _ h]
          refine le_csInf (grr _ _ _ _ _ h) ?_
          by_contra
          simp only [not_forall, not_le] at this
          obtain ⟨m', hm', m'_lt⟩ := this
          simp_rw [slopeSet] at hm'
          obtain ⟨a₀, ha₀, a₀_fin, a₁, ha₁, hm'⟩ := hm'
          have help : s.i₀ < a₀ := by
            calc
              _ ≤ s.j₀ := s.lt
              _ = i₀ := by grind
              _ ≤ _ := by grind
          suffices Segment.slope K (mkSegment K s.i₀ a₀ s.i₁ a₁ help) <
              sInf (slopeSet K v s.i₀ s.i₁) by
            have contra := csInf_le h_bdd (mem_segmentSlope_slopeSet K v s a₀ a₁ help a₀_fin ha₁)
            grind
          have foo : s.j₀ = i₀ := by
            grind
          simp_rw [← h_final1, Segment.slope, slopeReal, h_end, foo] at *
          simp_rw [hm'] at m'_lt
          have foo : s.j₀ = i₀ := by
            grind
          exact test' s.i₀ i₀ a₀ (algebraMap K ℝ s.i₁) (algebraMap K ℝ i₁) (algebraMap K ℝ a₁)
            (by rw [← foo]; exact Nat.cast_lt.mpr s.lt) (Nat.cast_lt.mpr ha₀) m'_lt
      · trivial
      -- how to work with the limits?
      -- do I want to say that the limit from s.i₀ would also be smaller??

lemma newtonPolygon.ray_slope_valid (n : ℕ) (cfg : ComputeConfig n := {}) :
    (newtonPolygon K v cfg).ray_slope_valid := by
  rcases h : findFirstFinite K v 0 with _ | ⟨i₀, i₁⟩
  · simpa [newtonPolygon, buildNewtonPolygon, h] using
      (emptyPolygon_wellFormed K).ray_slope_valid
  · convert build_ray_slope_valid K v i₀ i₁ [] cfg.maxSegments
      (emptyPolygon_wellFormed K).ray_slope_valid
    simp_rw [getResult_eq K v _ _ _ _ h]
    all_goals aesop


--- and finally:

lemma newtonPolygon.wellFormed (n : ℕ) (cfg : ComputeConfig n := {}) :
    (newtonPolygon K v cfg).WellFormed where
  connected := newtonPolygon.connected K v n cfg
  slopes_strictlyIncreasing := newtonPolygon.slopes_strictlyIncreasing K v n cfg
  ray_connected := newtonPolygon.ray_connected K v n cfg
  ray_slope_valid := newtonPolygon.ray_slope_valid K v n cfg

--- Idea: Create a function giving a list of segments
--- the segment i is the ith-segment of newtonPolygonData after running build with maxSlopes = i
--- include option of final slope or not...



def newtonPolygon_fullSegments : ℕ → (Segment K) :=
  fun n => List.getD (newtonPolygon K v _).segments n (sorry)
  -- so I really do need to rework this cfg problem
  --


  -- the idea is that at each step `n` we build the newtonPolygon with config `n` and take the
  -- `n`-th segment
  -- this returns a sequence of segments
  -- Note if we pair this with a final slope ... we can tell when to stop caring about the list
  -- if there is a final slope we know the segments after this point will not be relevant

  -- Question is how to do this?
  -- Do I want this as a structure?




-- Other API I want...
/-
  For polynomials we can use cfg (degree) to get build_result complete
  Every step is also a next vertex (until tail)
-/
