import Mathlib


-- Wanted to try and convert this into a method similar to previous work... the problem is there
-- is no equivalent way to define a newtonSet for a powerseries... we would need to
-- consider whether the valuation is finite or not and this would change the set
-- and we cannot order the set of ones with finite as it is (potentially) infinite

-- we could try and use Nat.find etc but this seems to overcomplicate and makes a meal of it

/-!
This file deines the Newton polygon of a power series, following the aligorthim from Gouveas
"p-adic numbers."
-/

namespace NewtonPolygon

/-- The type of valuation sequences: maps each index to either a finite valuation
    (for nonzero coefficients) or ⊤ (for zero coefficients). -/
abbrev ValSeq := ℕ → WithTop ℤ

variable (v : ValSeq)

/-- Predicate: the i-th coefficient is nonzero (has finite valuation). -/
def finite (i : ℕ) : Prop := v i ≠ ⊤

/-- The set of indices with nonzero coefficients. -/
def support : Set ℕ := {i | finite v i}

section Slopes

/-! We define the slope between two points.
  Then considering the infinite set {(i, v i) | v i finite}, we define the set of slopes
  from a point (i, v_i) which will be used in the construction of the Newton polgon.  -/

/-- Slope from (a, b) to (a', b') where both are finite valuations and i > a.
    Returns a rational number. -/
def slopeRat (a a' : ℕ) (b b' : ℤ) : ℚ :=
  (b' - b : ℚ) / (a' - a : ℚ)

/-- Slope from (a, b) to (i, vi) as a real number (for infimum computation). -/
noncomputable
def slopeReal (a a' : ℕ) (b b' : ℤ) : ℝ :=
  (b' - b : ℝ) / (a' - a : ℝ)

/-- The set of all slopes from vertex (i, v_i) to later nonzero coefficients (as rationals). -/
def slopeSetQ (i : ℕ) (v_i : ℤ) : Set ℚ :=
  {m : ℚ | ∃ j : ℕ, j > i ∧ finite v j ∧ ∃ v_j : ℤ, v j = v_j ∧ m = slopeRat i j v_i v_j}

/-- The set of all slopes from vertex (i₀, v₀) to later nonzero coefficients (as reals).
    This version is used for computing infima since ℝ is conditionally complete. -/
noncomputable
def slopeSetR (i : ℕ) (v_i : ℤ) : Set ℝ :=
  {m : ℝ | ∃ j : ℕ, j > i ∧ finite v j ∧ ∃ v_j : ℤ, v j = v_j ∧ m = slopeReal i j v_i v_j}

/-- The set of indices achieving a given slope m from (i, v_i). -/
def achievingSet (i : ℕ) (v_i : ℤ) (m : ℚ) : Set ℕ :=
  {j : ℕ | j > i ∧ finite v i ∧ ∃ v_j : ℤ, v j = v_j ∧ m = slopeRat i j v_i v_j}

end Slopes

section AlgorithmStep

/-- The result of one step of the Newton polygon algorithm. -/
inductive StepResult where
  /-- No more nonzero coefficients after i: the series is a polynomial ending here. -/
  | polynomialTail
  /-- Infinitely many points achieve the minimum slope m: final ray with infinitely many points. -/
  | infiniteRay (m : ℚ)
  /-- The minimum slope is achieved by finitely many points;
      move to the rightmost one (j, v_j). -/
  | nextVertex (j : ℕ) (v_j : ℤ)
  /-- The infimum is not attained (all later points are strictly above the limiting line):
      final ray with no further lattice points. Uses ℚ approximation. -/
  | limitingRay (m : ℚ)

/-- Compute the next step of the Newton polygon algorithm.
    Given current vertex (i, v_i), determines what happens next.
    This is noncomputable because it uses sInf on ℝ and classical choice. -/
noncomputable
def nextStep (i : ℕ) (v_i: ℤ) : StepResult :=
  open Classical in
  if slopeSetR v i v_i = ∅ then
    -- No more nonzero coefficients: polynomial tail
    StepResult.polynomialTail
  else
    -- slopeSetR is nonempty, compute the infimum in ℝ and check if it is achieved by some
    -- rational slope
    if hm : ∃ m ∈ slopeSetQ v i v_i, (m : ℝ) = sInf (slopeSetR v i v_i) then
      if hInfinite : (achievingSet v i v_i (Classical.choose hm)).Infinite then
        -- Infinitely many points achieve the minimum: infinite ray
        StepResult.infiniteRay (Classical.choose hm)
      else if hNonempty : (achievingSet v i v_i (Classical.choose hm)).Nonempty then
        -- Finitely many points achieve the minimum: take the rightmost
        have hfin : (achievingSet v i v_i (Classical.choose hm)).Finite :=
          Set.not_infinite.mp hInfinite
        let j := hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hNonempty) id
        match v j with
        | ⊤ => StepResult.polynomialTail  -- Shouldn't happen, but need to handle
        | (v_j : ℤ) => StepResult.nextVertex j v_j
      else
        -- This case shouldn't happen if m ∈ slopeSetQ, but handle it
        StepResult.limitingRay (Classical.choose hm)
    else
      -- Infimum not attained by a rational: use 0 as placeholder
      -- (In practice, for power series with integer valuations, this won't happen)
      StepResult.limitingRay 0

end AlgorithmStep

section Segments

/-- A segment of the Newton polygon from vertex (i, v_i) to (j, v_j).
    All coordinates are concrete values (indices as ℕ, valuations as ℤ). -/
structure Segment where
  /-- Starting x-coordinate (index) -/
  i : ℕ
  /-- Starting y-coordinate (valuation as integer) -/
  v_i : ℤ
  /-- Ending x-coordinate (index) -/
  j : ℕ
  /-- Ending y-coordinate (valuation as integer) -/
  v_j : ℤ
  /-- i₀ < i₁ -/
  lt : i < j
  deriving Repr

/-- The horizontal length of a segment. -/
def Segment.length (seg : Segment) : ℕ := seg.j - seg.i

/-- The slope of a segment as a rational number. -/
def Segment.slope (seg : Segment) : ℚ :=
  slopeRat seg.i seg.j seg.v_i seg.v_j

/-- A segment is valid if its endpoints correspond to actual nonzero coefficients
    with the claimed valuations. -/
def Segment.valid (seg : Segment) : Prop :=
  finite v seg.i ∧ finite v seg.j ∧
  v seg.i = seg.v_i ∧ v seg.j = seg.v_j

/-- The y-coordinate of a point on the line from (i₀, v₀) with slope m. -/
noncomputable def lineAt (i : ℕ) (v_i : ℤ) (m : ℝ) (j : ℕ) : ℝ := v_i + m * ((j : ℝ) - (i : ℝ))

/-- A segment is supporting if all points with i > i₀ lie on or above the line. -/
def Segment.supporting (seg : Segment) : Prop :=
  ∀ j > seg.i, finite v j → ∀ (v_j : ℤ), v_j = v j → (v_j : ℝ) ≥ lineAt seg.i seg.v_i seg.slope j

/-- A segment is tight if its endpoint (i₁, v₁) lies exactly on the line
    (which it should by construction). -/
def Segment.tight (seg : Segment) : Prop :=
  (seg.v_j : ℝ) = lineAt seg.i seg.v_i seg.slope seg.j

/-- Every segment is tight by construction. -/
theorem Segment.tight_of_slope (seg : Segment) : seg.tight := by
  have h : (seg.j : ℝ) - (seg.i : ℝ) ≠ 0 :=
    ne_of_gt (by simpa [sub_pos] using Nat.cast_lt.mpr seg.lt)
  simp only [tight, lineAt, Segment.slope, slopeRat]
  aesop

/-- A final ray of the Newton polygon starting from (i₀, v₀) with slope m. -/
structure FinalRay where
  /-- Starting x-coordinate (index) -/
  i : ℕ
  /-- Starting y-coordinate (valuation as integer) -/
  v_i : ℤ
  /-- The slope of the ray -/
  slope : ℚ
  /-- Whether the ray contains infinitely many lattice points -/
  hitsInfinitelyMany : Bool
  deriving Repr

/-- A final ray is supporting if all later points lie on or above the ray. -/
def FinalRay.supporting (ray : FinalRay) : Prop :=
  ∀ j > ray.i, finite v j → ∀ (v_j : ℤ), v j = v_j → (v_j : ℝ) ≥ lineAt ray.i ray.v_i ray.slope j

end Segments

section NPStructure

/-- The Newton polygon of a power series, consisting of:
    - A (possibly empty) list of segments with strictly increasing slopes
    - An optional final ray

    The polygon starts at (0, v(a₀)) and traces the lower convex hull
    of the points (i, v(aᵢ)) for nonzero aᵢ. -/
structure NewtonPolygonData where
  /-- The list of segments. -/
  segments : List Segment
  /-- The final ray, if the polygon terminates with a ray. -/
  finalRay : Option FinalRay
  deriving Repr

/-- Predicate to show if segments are properly connected. -/
def NewtonPolygonData.connected (npd : NewtonPolygonData) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.segments.length,
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).j = (npd.segments[k + 1]'hk).i ∧
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).v_j = (npd.segments[k + 1]'hk).v_i

/-- Predicate to show if slopes are strictly increasing. -/
def NewtonPolygonData.slopes_strictlyIncreasing (npd : NewtonPolygonData) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.segments.length,
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).slope < (npd.segments[k + 1]'hk).slope

/-- Predicate to show the final ray is properly connected to the last segment. -/
def NewtonPolygonData.ray_connected (npd : NewtonPolygonData) : Prop :=
  match npd.finalRay, npd.segments.getLast? with
  | some r, some s => r.i = s.j ∧ r.v_i = s.v_j
  | _, _ => True

/-- Predicate to show the final ray's slope is at least the last segment's slope. -/
def NewtonPolygonData.ray_slope_valid (npd : NewtonPolygonData) : Prop :=
  match npd.finalRay, npd.segments.getLast? with
  | some r, some s => s.slope < r.slope
  | _, _ => True

/-- A well-formed Newton polygon satisfies all connectivity and monotonicity conditions. -/
structure NewtonPolygonData.WellFormed (npd : NewtonPolygonData) : Prop where
  connected : npd.connected
  slopes_strictlyIncreasing : npd.slopes_strictlyIncreasing
  ray_connected : npd.ray_connected
  ray_slope_valid : npd.ray_slope_valid

/-- The empty Newton polygon (for the zero series or constant series). -/
def emptyPolygon : NewtonPolygonData where
  segments := []
  finalRay := none

/-- The empty polygon is well-formed. -/
theorem emptyPolygon_wellFormed : emptyPolygon.WellFormed where
  connected _ hk := by simp [emptyPolygon] at hk
  slopes_strictlyIncreasing _ hk := by simp [emptyPolygon] at hk
  ray_connected := by simp [emptyPolygon, NewtonPolygonData.ray_connected]
  ray_slope_valid := by simp [emptyPolygon, NewtonPolygonData.ray_slope_valid]

end NPStructure

section ComputingNP

variable {R : Type*} [Semiring R]

noncomputable
def toValSeq (f : PowerSeries R) (v : R → WithTop ℤ) : ValSeq :=
  fun i => v (PowerSeries.coeff i f)

/-- Create a single segment given valid data. -/
def mkSegment (i j : ℕ) (v_i v_j : ℤ) (hlt : i < j) : Segment :=
  {i := i, v_i := v_i, j := j, v_j := v_j, lt := hlt}

/-- Create a final ray. -/
def mkFinalRay (i : ℕ) (v_i : ℤ) (slope : ℚ) (infinite : Bool) : FinalRay :=
  {i := i, v_i := v_i, slope := slope, hitsInfinitelyMany := infinite }

/-- Configuration for polygon computation to handle termination. -/
structure ComputeConfig where
  /-- Maximum number of segments to compute (for termination). -/
  maxSegments : ℕ := 1000
  /-- Maximum index to search for finite valuations. -/
  maxIndex : ℕ := 10000

/-- Find the first index with finite valuation, starting from a given position. -/
noncomputable
def findFirstFinite (startIdx : ℕ) : Option (ℕ × ℤ) := open Classical in
  if h : ∃ i ≥ startIdx, finite v i then
    let i := Nat.find h
    match v i with
    | ⊤ => none  -- contradicts finiteness, shouldn't happen
    | (val : ℤ) => some (i, val)
  else
    none

/-- Result of iteratively building the Newton polygon. -/
inductive BuildResult where
  /-- Successfully built the polygon. -/
  | complete (npd : NewtonPolygonData)
  /-- Hit the segment limit before completing. -/
  | incomplete (npd : NewtonPolygonData) (reason : String)
  deriving Repr

/-- Build the Newton polygon by iterating the nextStep algorithm.
    This is the main computational function.

    The algorithm follows Gouvêa Section 7.4:
    1. Start at the first nonzero coefficient (i₀, v₀)
    2. Rotate the line counterclockwise to find minimum slope
    3. Move to the rightmost point achieving minimum slope
    4. Repeat until termination (polynomial tail, infinite ray, or limiting ray)
-/
noncomputable def buildNewtonPolygon (cfg : ComputeConfig := {}) : BuildResult := open Classical in
  -- Find the starting point (first finite valuation)
  match findFirstFinite v 0 with
  | none => BuildResult.complete emptyPolygon
  | some (i, v_i) =>
    -- Iteratively build segments
    let rec build (currentIdx : ℕ) (currentVal : ℤ) (segments : List Segment) (fuel : ℕ) :
        BuildResult :=
      if fuel = 0 then
        BuildResult.incomplete ⟨segments, none⟩ "reached segment limit"
      else
        match nextStep v currentIdx currentVal with
        | StepResult.polynomialTail =>
            -- No more nonzero coefficients: series is essentially a polynomial
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
    build i v_i [] cfg.maxSegments

/-- Extract the Newton polygon data, returning the empty polygon if computation
    was incomplete. -/
noncomputable
def newtonPolygon (cfg : ComputeConfig := {}) : NewtonPolygonData :=
  match buildNewtonPolygon v cfg with
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

end ComputingNP

section API

/-- Get all slopes of the Newton polygon (the "Newton slopes"). -/
def NewtonPolygonData.slopes (npd : NewtonPolygonData) : List ℚ :=
  npd.segments.map Segment.slope

/-- Get the length of each segment (projection onto x-axis). -/
def NewtonPolygonData.lengths (npd : NewtonPolygonData) : List ℕ :=
  npd.segments.map Segment.length

/-- Get the vertices (break points) of the polygon as (index, valuation) pairs. -/
def NewtonPolygonData.vertices (npd : NewtonPolygonData) : List (ℕ × ℤ) :=
  match npd.segments with
  | [] => []
  | seg :: rest =>
    (seg.i, seg.v_i) :: rest.foldl (fun acc s => acc ++ [(s.j, s.v_j)])
      [(seg.j, seg.v_j)]

/-- Get slopes paired with their lengths (useful for root counting). -/
def NewtonPolygonData.slopesWithLengths (npd : NewtonPolygonData) : List (ℚ × ℕ) :=
  npd.segments.map fun seg => (seg.slope, seg.length)

/-- Total horizontal extent of the polygon. -/
def NewtonPolygonData.totalLength (npd : NewtonPolygonData) : ℕ :=
  npd.lengths.foldl (· + ·) 0

/-- Check if the polygon is pure (has only one slope).
    Following Gouvêa Definition 7.4.1: A polynomial is pure if its Newton
    polygon has only one slope. -/
def NewtonPolygonData.isPure (npd : NewtonPolygonData) : Bool :=
  npd.segments.length ≤ 1 && npd.finalRay.isNone

/-- Get the unique slope if the polygon is pure, otherwise none. -/
def NewtonPolygonData.pureSlope (npd : NewtonPolygonData) : Option ℚ :=
  if npd.isPure then npd.slopes.head? else none

end API

section work

-- following is based off of work from aristotle

def getSegments : BuildResult → List Segment
  | BuildResult.complete npd => npd.segments
  | BuildResult.incomplete npd _ => npd.segments

-- may not even be needed but perhaps nice API to have
theorem build_valid (v : ValSeq) (i : ℕ) (v_i : ℤ) (segs : List Segment) (fuel : ℕ)
    (hi : finite v i) (hvi : v i = v_i) (hsegs : ∀ s ∈ segs, s.valid v) :
    ∀ s ∈ getSegments (buildNewtonPolygon.build v i v_i segs fuel), s.valid v := by
  induction' fuel with fuel ih generalizing i v_i segs;
  · unfold buildNewtonPolygon.build
    aesop
  · unfold buildNewtonPolygon.build
    rcases h : nextStep v i v_i with ( _ | _ | _ | _ ) <;> simp_all +decide;
    · unfold getSegments
      aesop
    · exact hsegs;
    · rename_i j v_j
      split_ifs with hj
      · apply ih j v_j (segs ++ [mkSegment i j v_i v_j hj])
        · unfold nextStep at h
          split_ifs at h
          simp_all +decide only [slopeSetR, gt_iff_lt, slopeSetQ, Set.mem_setOf_eq, id_eq]
          cases h' : v (Finset.sup' (Set.Finite.toFinset (Set.not_infinite.mp ‹_›)) (by aesop)
            fun x => x)
          <;> simp_all +decide [finite]
        · -- this will be got from rw'ing nextStep at h
          -- then unfolding the mess it gives
          sorry
        · -- can reduce to checking the ++ seg ... and this is done in the above sorry
          sorry
      · aesop
    · unfold getSegments; aesop

lemma newtonPolygon.segmentsValid (cfg : ComputeConfig := {}) (n : ℕ)
    (hn : n < (newtonPolygon v cfg).segments.length) :
    ((newtonPolygon v cfg).segments[n]).valid v := by
  cases h : findFirstFinite v 0
  · -- get hn is false
    sorry
  · have h' := h
    unfold findFirstFinite at h
    simp only [ge_iff_le, zero_le, true_and, Option.dite_none_right_eq_some] at h
    obtain ⟨⟨i, hi⟩, H⟩ := h
    rename_i val
    obtain ⟨a,b⟩ := val
    have : getSegments (buildNewtonPolygon.build v a b [] cfg.maxSegments) =
        (newtonPolygon v cfg).segments := by
      unfold getSegments newtonPolygon buildNewtonPolygon
      aesop
    convert build_valid v a b [] cfg.maxSegments (by grind) (by aesop) (by aesop) _ _
    aesop

def segments_connected (segs : List Segment) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < segs.length,
    (segs[k]'(Nat.lt_of_succ_lt hk)).j = (segs[k + 1]'hk).i ∧
    (segs[k]'(Nat.lt_of_succ_lt hk)).v_j = (segs[k + 1]'hk).v_i

def ends_at (segs : List Segment) (j : ℕ) (v_j : ℤ) : Prop :=
  match segs.getLast? with
  | some s => s.j = j ∧ s.v_j = v_j
  | none => True

theorem build_connected (v : ValSeq) (i : ℕ) (v_i : ℤ) (segs : List Segment) (fuel : ℕ)
    (h_conn : segments_connected segs) (h_end : ends_at segs i v_i) :
    segments_connected (getSegments (buildNewtonPolygon.build v i v_i segs fuel)) := by
  induction' fuel with fuel ih generalizing i v_i segs h_conn h_end
  · unfold getSegments buildNewtonPolygon.build
    aesop
  · unfold buildNewtonPolygon.build
    rcases h : nextStep v i v_i with ( _ | _ | _ | _ )
    <;> simp_all +decide only [Nat.add_eq_zero_iff, and_false, ↓reduceIte, add_tsub_cancel_right]
    · exact h_conn
    · exact ((fun a ↦ h_conn) ∘ v) fuel
    · split_ifs <;> simp_all +decide only [segments_connected, ends_at, not_lt]
      · convert ih _ _ _ _ _ using 1
        · intro k hk
          rcases lt_trichotomy k (segs.length - 1) with hk' | rfl | hk'
          <;> simp_all +decide only [List.getElem_append, List.getElem_singleton]
          · grind
          · cases segs
            <;> simp_all +decide only [List.length_nil, not_lt_zero, IsEmpty.forall_iff,
              implies_true, List.getLast?_nil, zero_tsub, zero_add, List.nil_append,
              List.length_cons, lt_self_iff_false]
            cases ‹List Segment› <;> simp_all +decide only [List.getLast?, List.length_nil,
              zero_add, add_lt_iff_neg_right, not_lt_zero, List.getElem_singleton,
              List.getElem_cons_succ, IsEmpty.forall_iff, implies_true, List.getLast_singleton,
              tsub_self, List.cons_append, List.nil_append, List.length_cons, Nat.reduceAdd,
              Nat.one_lt_ofNat, ↓reduceDIte, List.getElem_cons_zero]
            · exact ⟨rfl, rfl⟩
            · convert h_end using 1
              · simp +decide only [add_tsub_cancel_right, lt_add_iff_pos_right, ↓reduceDIte,
                  List.getElem_cons_succ, lt_self_iff_false, List.getLast_eq_getElem,
                  List.length_cons]
                rfl
              · simp +decide only [add_tsub_cancel_right, lt_add_iff_pos_right, ↓reduceDIte,
                  List.getElem_cons_succ, lt_self_iff_false, List.getLast_eq_getElem,
                  List.length_cons]
                rfl
          · grind
        · simp +decide only [mkSegment, List.getLast?_append, List.getLast?_singleton,
            Option.some_or, and_self]
      · exact fun k hk ↦ And.symm ((fun {a b} ↦ And.comm.mp) (h_conn k hk))
    · exact h_conn

lemma newtonPolygon.connected (cfg : ComputeConfig := {}) :
    NewtonPolygonData.connected (newtonPolygon v cfg) := by
  cases h : findFirstFinite v 0
  · simpa [newtonPolygon, buildNewtonPolygon, h] using emptyPolygon_wellFormed.connected
  · have h' := h
    unfold findFirstFinite at h
    simp only [ge_iff_le, zero_le, true_and, Option.dite_none_right_eq_some] at h
    obtain ⟨⟨i, hi⟩, H⟩ := h
    rename_i val
    obtain ⟨a,b⟩ := val
    have : getSegments (buildNewtonPolygon.build v a b [] cfg.maxSegments) =
        (newtonPolygon v cfg).segments := by
      unfold getSegments newtonPolygon buildNewtonPolygon
      aesop
    convert build_connected v a b [] cfg.maxSegments (emptyPolygon_wellFormed.connected)
      (by simp only [ends_at, List.getLast?_nil])
    aesop

def getResult : BuildResult → NewtonPolygonData -- maybe do not need this and getSegments?
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

theorem build_ray_connected (v : ValSeq) (i : ℕ) (v_i : ℤ) (segs : List Segment) (fuel : ℕ)
    (h_end : ends_at segs i v_i) :
    (getResult (buildNewtonPolygon.build v i v_i segs fuel)).ray_connected := by
  induction' fuel with fuel ih generalizing i v_i segs
  · unfold buildNewtonPolygon.build
    simp only [↓reduceIte]
    exact ((fun a ↦ a) ∘ fun a ↦ a) trivial
  · unfold buildNewtonPolygon.build
    split_ifs
    <;> simp_all +decide only [Nat.add_eq_zero_iff, and_false]
    rcases h : nextStep v i v_i with ( _ | _ | _ | _ )
    <;> simp_all +decide only [mkFinalRay]
    · exact ((fun a ↦ a) ∘ fun a ↦ a) trivial
    · simp [getResult, NewtonPolygonData.ray_connected]
      cases segs
      <;> simp_all +decide only [ends_at, List.getLast?_nil]
      grind
    · split_ifs <;> simp_all +decide only [ends_at, not_lt]
      · convert ih _ _ _ _ using 1
        simp +decide only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
        exact ⟨rfl, rfl⟩
      · exact ((fun a ↦ a) ∘ fun a ↦ a) trivial
    · cases segs <;> simp_all +decide only [ends_at]
      · exact ((fun a ↦ a) ∘ fun a ↦ a) trivial
      · cases ‹List Segment› <;> simp_all +decide only [List.getLast?, List.getLast_singleton];
        · unfold getResult NewtonPolygonData.ray_connected
          simp +decide only
          aesop
        · cases ‹List Segment›
          <;> tauto

lemma newtonPolygon.ray_connected (cfg : ComputeConfig := {}) :
    NewtonPolygonData.ray_connected (newtonPolygon v cfg) := by
  cases h : findFirstFinite v 0
  · simpa [newtonPolygon, buildNewtonPolygon, h] using emptyPolygon_wellFormed.ray_connected
  · have h' := h
    unfold findFirstFinite at h
    simp only [ge_iff_le, zero_le, true_and, Option.dite_none_right_eq_some] at h
    obtain ⟨⟨i, hi⟩, H⟩ := h
    rename_i val
    obtain ⟨a,b⟩ := val
    have : newtonPolygon v cfg =
        (getResult (buildNewtonPolygon.build v a b [] cfg.maxSegments)) := by
      unfold getResult newtonPolygon buildNewtonPolygon
      aesop
    convert build_ray_connected v a b [] cfg.maxSegments (((fun a ↦ a) ∘ fun a ↦ a) trivial)


def slopes_strictlyIncreasing (segs : List Segment) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < segs.length,
    (segs[k]'(Nat.lt_of_succ_lt hk)).slope < (segs[k + 1]'hk).slope

-- maybe not needed? But still nice API to have
lemma nextStep_inf_eq_slope (v : ValSeq) (i : ℕ) (v_i : ℤ) (j : ℕ) (v_j : ℤ)
    (h_step : nextStep v i v_i = StepResult.nextVertex j v_j) :
    (slopeRat i j v_i v_j : ℝ) = sInf (slopeSetR v i v_i) := by
  rw [eq_comm]
  unfold nextStep at h_step
  split_ifs at h_step
  cases h_step' : v (Finset.sup' ( Set.Finite.toFinset ( Classical.not_not.mp ‹_›))
    (by aesop) fun x => x)
  <;> simp_all +decide
  rename_i _ h1 h2 _ _
  convert Classical.choose_spec h1 |>.2.symm
  have h_sup : j ∈ achievingSet v i v_i (Classical.choose h1) := by
    have h_sup : j ∈ Set.Finite.toFinset (Classical.not_not.mp h2) := by
      exact h_step.1 ▸ Finset.max'_mem _ _;
    exact Set.Finite.mem_toFinset _ |>.1 h_sup;
  cases h_sup
  aesop

lemma segment_append_singleton_slopes_strictlyIncreasing (segs : List Segment) (seg : Segment)
    (h_sorted : slopes_strictlyIncreasing segs) (h_le : ∀ s ∈ segs.getLast?, s.slope < seg.slope) :
    slopes_strictlyIncreasing (segs ++ [seg]) := by
  intro k hk
  by_cases hk' : k < List.length segs
  · by_cases hk'' : k + 1 < segs.length
    <;> simp_all +decide only [Option.mem_def, List.getElem_append_left];
    · exact h_sorted k hk''
    · grind
  · grind

lemma foo (i j k : ℕ) (v_i v_j v_k : ℤ) (hnexti : nextStep v i v_i = StepResult.nextVertex j v_j)
    (hnextj : nextStep v j v_j = StepResult.nextVertex k v_k) :
    slopeRat i j v_i v_j < slopeRat j k v_j v_k := by
  by_contra
  simp only [not_lt, Decidable.le_iff_eq_or_lt] at this
  have hmin := nextStep_inf_eq_slope v i v_i j v_j hnexti
  unfold nextStep at *
  split_ifs at *
  simp_all +decide only [id_eq]
  rename_i nnemptyi nnemptyj mi mj ninfi ninfj hi hj
  cases H1 : v (Finset.sup' (Set.Finite.toFinset (Set.not_infinite.mp ninfj)) (by
    exact (Set.Finite.toFinset_nonempty (Set.not_infinite.mp ninfj)).mpr hj) fun x => x)
  <;> simp_all +decide
  cases H2 : v ( Finset.sup' ( Set.Finite.toFinset ( Set.not_infinite.mp ninfi ) ) ( by
    exact (Set.Finite.toFinset_nonempty (Set.not_infinite.mp ninfi)).mpr hi ) fun x => x ) <;> simp_all +decide
  rcases this with h | h
  ·
    sorry
  ·
    sorry
  -- this will be by contradiction
  -- assume this is not the case
  -- then if slopeRat i j v_i v_j = slopeRat j k v_j v_k then k is a later point that gives
  -- slopeRat i j v_i v_j i.e. j is not maximal
  -- if slopeRat i j v_i v_j > slopeRat j k v_j v_k then it is not minimal which is a contradiction

theorem build_slopes_strictlyIncreasing (v : ValSeq) (i : ℕ) (v_i : ℤ) (segs : List Segment) (fuel : ℕ)
    (h_sorted : slopes_strictlyIncreasing segs) (h_conn : ends_at segs i v_i) :
    slopes_strictlyIncreasing (getSegments (buildNewtonPolygon.build v i v_i segs fuel)) := by
  induction' fuel with fuel ih generalizing i v_i segs h_sorted h_conn
  · simpa [buildNewtonPolygon.build] using h_sorted
  · unfold buildNewtonPolygon.build
    split_ifs
    <;> simp_all +decide
    rcases h : nextStep v i v_i with ( _ | _ | _ | _ ) <;> simp_all +decide [getSegments]
    split_ifs 
    <;> simp_all +decide [ends_at]
    rename_i j v_j hij
    convert ih _ _ _ _ _
    · refine segment_append_singleton_slopes_strictlyIncreasing segs _ h_sorted ?_
      intro s hs
      have : (mkSegment i j v_i v_j hij).slope = slopeRat i j v_i v_j := by
        rfl
      simp_rw [this]
      -- now want to just rw s.slope as a slopeRat and apply nextVertex_slope_ge_last
      sorry
    · aesop

lemma newtonPolygon.slopes_strictlyIncreasing (cfg : ComputeConfig := {}) :
    (newtonPolygon v cfg).slopes_strictlyIncreasing := by
  cases h : findFirstFinite v 0
  · simpa [newtonPolygon, buildNewtonPolygon, h] using
      emptyPolygon_wellFormed.slopes_strictlyIncreasing
  · have h' := h
    unfold findFirstFinite at h
    simp only [ge_iff_le, zero_le, true_and, Option.dite_none_right_eq_some] at h
    obtain ⟨⟨i, hi⟩, H⟩ := h
    rename_i val
    obtain ⟨a,b⟩ := val
    have : getSegments (buildNewtonPolygon.build v a b [] cfg.maxSegments) =
        (newtonPolygon v cfg).segments := by
      unfold getSegments newtonPolygon buildNewtonPolygon
      aesop
    convert build_slopes_strictlyIncreasing v a b [] cfg.maxSegments
      emptyPolygon_wellFormed.slopes_strictlyIncreasing (by exact ((fun a ↦ a) ∘ fun a ↦ a) trivial)
    aesop


lemma newtonPolygon.ray_slope_valid (cfg : ComputeConfig := {}) :
    (newtonPolygon v cfg).ray_slope_valid := by

  sorry

open NewtonPolygon in
lemma newtPolygon.wellFormed (cfg : ComputeConfig := {}) :
    NewtonPolygonData.WellFormed (newtonPolygon v cfg) where
  connected := newtonPolygon.connected v cfg
  slopes_strictlyIncreasing := newtonPolygon.slopes_strictlyIncreasing v cfg
  ray_connected := newtonPolygon.ray_connected v cfg
  ray_slope_valid := newtonPolygon.ray_slope_valid v cfg

end work
