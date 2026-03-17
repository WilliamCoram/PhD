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
def mkSegment (x : ℕ) (y : Γ) (l : WithTop ℕ) (m : WithTop ℝ) (bool : Bool) : Segment Γ :=
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

def NewtonPolygonData.connected : List (Segment Γ) → Prop
  | [] => True
  | [_] => True
  | s₁ :: s₂ :: rest =>
      ∃ l : ℕ, s₁.l = l ∧ s₂.x = s₁.x + l ∧ v (s₁.x + l) = s₂.y ∧
        NewtonPolygonData.connected (s₂ :: rest)

def NewtonPolygonData.slopes_strictlyIncreasing : List (Segment Γ) → Prop
  | [] => True
  | [_] => True
  | s₁ :: s₂ :: rest =>
      ((∃ l : ℕ, s₂.l = l) → s₁.m < s₂.m) ∧
        NewtonPolygonData.slopes_strictlyIncreasing (s₂ :: rest)

def NewtonPolygonData.ray_slope_valid : List (Segment Γ) → Prop
  | [] => True
  | [_] => True
  | s₁ :: s₂ :: rest =>
      ((s₂.l = ⊤) → if s₂.hitsPoint then s₁.m < s₂.m else s₁.m ≤ s₂.m) ∧
        NewtonPolygonData.ray_slope_valid (s₂ :: rest)

structure NewtonPolygonData.WellFormed (npd : List (Segment Γ)) : Prop where
  connected : NewtonPolygonData.connected (v := v) npd
  slopes_strictlyIncreasing : NewtonPolygonData.slopes_strictlyIncreasing npd
  ray_slope_valid : NewtonPolygonData.ray_slope_valid npd
