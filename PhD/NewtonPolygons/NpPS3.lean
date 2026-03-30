import Mathlib

namespace NewtonPolygon

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ]

section Segments

variable (Γ) in
/-- A segment of the Newton polygon. -/
structure Segment where
  /-- Starting x-coordinate -/
  x : ℕ
  /-- Starting y-coordinate -/
  y : Γ
  /-- Length (projected) -/
  l : WithTop ℕ
  /-- Slope -/
  m : WithTop ℝ
  /-- Option whether it hits a point -/
  hitsPoint : Bool

/-- Create a single segment given valid data. -/
def mkSegment (x : ℕ) (y : Γ) (l : WithTop ℕ) (m : WithTop ℝ) (bool : Bool) : Segment Γ :=
  {x := x, y := y, l := l, m := m, hitsPoint := bool}

end Segments

section NPstructure

def connected (segs : ℕ → Segment Γ) : Prop :=
  ∀ k : ℕ,
  if (segs k).x ≠ (segs (k+1)).x then
    match (segs k).l with
    | some l =>
      (segs k).x + l = (segs (k+1)).x ∧
        match (segs k).m with
        | some m =>
          algebraMap Γ ℝ (segs (k+1)).y = algebraMap Γ ℝ (segs k).y + m * l
        | none => true
    | none => true
  else true -- a way to get around repeated segments

def increasing (segs : ℕ → Segment Γ) : Prop :=
  ∀ k : ℕ,
  if (segs k).x ≠ (segs (k+1)).x then
    match (segs (k+1)).l with
    | some l =>
      if l = 0 then
        (segs k).m < (segs (k+1)).m
      else
        (segs k).m < (segs (k+1)).m
    | none =>
      if (segs (k+1)).hitsPoint = true then
        (segs k).m < (segs (k+1)).m
      else
       (segs k).m ≤ (segs (k+1)).m
  else true -- a way to get around when we have repeated segments (i.e. when we have finite segments)

structure newtonPolygon where
  /-- Function indexing the list of segments -/
  segments : ℕ → Segment Γ
  /-- The segments are connected -/
  connected : connected segments
  /-- The segments have (strictly)-increasing slope -/
  slopes_increasing : increasing segments

end NPstructure

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

section NPmake

variable (Γ) in
/-- The empty Newton polygon (for the zero series or constant series). -/
def emptyPolygon : List (Segment Γ) := []

variable {R : Type*} [Semiring R]

noncomputable
def toValSeq (f : PowerSeries R) (v : R → WithTop Γ) : ValSeq Γ :=
  fun i => v (PowerSeries.coeff i f)

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
            -- No more nonzero coefficients
            BuildResult.complete npd
        | StepResult.unboundedBelow =>
            -- No more segments, valuation is unbounded below
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
def NPmake (n : ℕ)  : List (Segment Γ) :=
  match buildNewtonPolygon v n with
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

/-- NPmake builds off of previous NPmake -/
theorem NPmake_eq (n n' i : ℕ) (le : n < n') (hi : i < n) : (NPmake v n)[i]? = (NPmake v n')[i]? := by
  unfold NPmake buildNewtonPolygon
  -- how do I want to do this... induction on n and n' and i?

  -- Why do we want this?
  -- So when we show our increasing condition we can consider within one of the NPmake
  sorry

end NPmake

section NPmake_connected

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

lemma nextVertex_slope_eq_sInf' (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) :
    m = slopeReal i₀ j₀ i₁ j₁ := by
  have := nextVertex_slope_eq_sInf v h
  simp_rw [nextStep] at h
  split_ifs at h with _ _ H
  grind

lemma nextVertex_slope_eq_sInf'' (v : ValSeq Γ) {i₀ j₀ : ℕ} {i₁ j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = StepResult.nextVertex j₀ j₁ m) :
    m = sInf (slopeSet v i₀ i₁) := by
  simpa [← nextVertex_slope_eq_sInf v h] using nextVertex_slope_eq_sInf' v h

end nextVertexAPI

def NPmake_connected (segs : List (Segment Γ)) : Prop :=
  ∀ k : ℕ, ∀ hk : k+1 < segs.length,
    match segs[k].l with
    | some l =>
      segs[k].x + l = segs[k+1].x ∧
        match segs[k].m with
        | some m =>
          algebraMap Γ ℝ segs[k+1].y = algebraMap Γ ℝ segs[k].y + m * l
        | none => true
    | none => true

lemma emptyPolygon_connected : NPmake_connected (emptyPolygon Γ) := by
  simp [emptyPolygon, NPmake_connected]

def getSegments : BuildResult Γ → List (Segment Γ)
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

lemma getSegments_eq (n : ℕ) {i₀ : ℕ} {i₁ : Γ} (h : findFirstFinite v 0 = some (i₀, i₁)) :
    getSegments (buildNewtonPolygon.build v i₀ i₁ [] n) = NPmake v n := by
  unfold getSegments NPmake buildNewtonPolygon
  aesop

def ends_at (segs : List (Segment Γ)) (j₀ : ℕ) (j₁ : Γ) : Prop :=
  match segs.getLast? with
  | some s => ∃ l : ℕ, ∃ m : ℝ, s.l = l ∧ s.m = m ∧ s.x + l = j₀ ∧
      algebraMap Γ ℝ s.y + m * l = algebraMap Γ ℝ j₁
  | none => True

lemma connected_append_singleton {segs : List (Segment Γ)} (seg : Segment Γ)
    (h_conn : NPmake_connected segs) (h_end : ends_at segs seg.x seg.y) :
    NPmake_connected (segs ++ [seg]) := by
  simp_rw [NPmake_connected] at ⊢ h_conn
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
    obtain ⟨l, m, hl, hm, H⟩ := h_end
    simp [hl, hm]
    aesop

theorem build_connected (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ} (segs : List (Segment Γ)) (fuel : ℕ)
    (h_conn : NPmake_connected segs) (h_end : ends_at segs i₀ i₁) :
    NPmake_connected (getSegments (buildNewtonPolygon.build v i₀ i₁ segs fuel)) := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs
  · simp [getSegments, buildNewtonPolygon.build, h_conn]
  · unfold buildNewtonPolygon.build
    rcases h : nextStep v i₀ i₁ with (_ | _ | m | ⟨j₀, j₁, m⟩ | m)
    · simpa [getSegments] using h_conn
    · simpa [getSegments] using h_conn
    · exact connected_append_singleton (mkSegment i₀ i₁ ⊤ m true) h_conn h_end
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
      split_ifs with hij
      · refine ih (segs := segs ++ [mkSegment i₀ i₁ (j₀ - i₀) m true])
          (connected_append_singleton (mkSegment i₀ i₁ (j₀ - i₀) m true) h_conn h_end) ?_
        simp [ends_at, mkSegment]
        refine ⟨j₀ - i₀, rfl, Nat.add_sub_of_le hij.le, ?_⟩
        have : (j₀ : ℝ) - i₀ ≠ 0 := by
          exact ne_of_gt (by simpa using hij)
        simp_rw [nextVertex_slope_eq_sInf' v h, slopeReal, div_mul,
          Nat.cast_sub (Nat.le_of_succ_le hij)]
        grind
      · simpa [getSegments] using h_conn
    · exact connected_append_singleton (mkSegment i₀ i₁ ⊤ m false) h_conn h_end

lemma newtonPolygon_connected (v : ValSeq Γ) (n : ℕ) :
    NPmake_connected (NPmake v n) := by
  rcases h : findFirstFinite v 0 with _ | ⟨i₀, i₁⟩
  · simpa [NPmake, buildNewtonPolygon, h] using (emptyPolygon_connected (Γ := Γ))
  · convert build_connected v [] n (emptyPolygon_connected (Γ := Γ)) (by trivial)
    rw [getSegments_eq (Γ := Γ) v n h]

end NPmake_connected

section NPmake_increasing

def NPmake_increasing (segs : List (Segment Γ)) : Prop :=
  ∀ k : ℕ, ∀ hk : k+1 < segs.length,
    match segs[k+1].l with
    | some l =>
      if l = 0 then
        true
      else
        segs[k].m < segs[k+1].m
    | none =>
      if segs[k+1].hitsPoint = true then
        segs[k].m < segs[k+1].m
      else
        segs[k].m ≤ segs[k+1].m

lemma emptyPolygon_increasing : NPmake_increasing (emptyPolygon Γ) := by
  simp [emptyPolygon, NPmake_increasing]

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

section convexity

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

set_option maxHeartbeats 400000 in
theorem build_increasing (v : ValSeq Γ) {i₀ : ℕ} {i₁ : Γ}
    (segs : List (Segment Γ)) (fuel : ℕ)
    (h_slopes : NPmake_increasing segs)
    (h_end : ends_at segs i₀ i₁)
    (h_fin : ∀ s ∈ segs.getLast?, ∃ l : ℕ, s.l = l ∧ l ≠ 0)
    (h_m : ∀ s (hs : s ∈ segs.getLast?), ∃ m : ℝ, s.m = m)
    (h_point : ∀ s ∈ segs.getLast?, s.hitsPoint = true)
    (h_bdd :  ∀ s ∈ segs.getLast?, BddBelow (slopeSet v s.x s.y))
    (h_final1 : ∀ s ∈ segs.getLast?, s.m = sInf (slopeSet v s.x s.y))
    (h_final2 : ∀ s (hs : s ∈ segs.getLast?),
      Set.Finite (achievingSet v s.x s.y (Classical.choose (h_m s hs))))
    (h_final3 :  ∀ s (hs : s ∈ segs.getLast?),
      Set.Nonempty (achievingSet v s.x s.y (Classical.choose (h_m s hs))))
    (h_final4 : ∀ s (hs : s ∈ segs.getLast?), s.x + s.l = (Set.Finite.toFinset (h_final2 s hs)).max'
      ((h_final2 s hs).toFinset_nonempty.mpr (h_final3 s hs))) :
    NPmake_increasing (getSegments (buildNewtonPolygon.build v i₀ i₁ segs fuel)) := by
  induction' fuel with fuel ih generalizing i₀ i₁ segs
  all_goals unfold buildNewtonPolygon.build
  · trivial
  · simp only [getSegments]
    rcases h : nextStep v i₀ i₁ with ( _ | _ | m | ⟨j₀, j₁, m⟩ | m )
    all_goals try trivial
    swap
    · -- next vertex needs to be handled differently (at least for now it seems so)
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
        dite_eq_ite]
      split_ifs with hij
      swap
      exact h_slopes
      convert ih (segs ++ [mkSegment i₀ i₁ (↑j₀ - ↑i₀) (↑m) true]) _ _ _ _ _ _ _ _ _ _
      · simp_rw [NPmake_increasing]
        intro k hk
        have : k + 1 < segs.length ∨ k + 1 = segs.length := by
          grind
        rcases this with this | this
        · simpa [this, show k < segs.length from by grind] using h_slopes k this
        · simp [this]
          have : (mkSegment i₀ i₁ (↑j₀ - ↑i₀) (↑m) true).l = (j₀ - i₀) := by
            rfl
          simp [this]
          have : (j₀ : WithTop ℕ) - ↑i₀ = some (j₀ - i₀) := by
            norm_cast
          intro _
          have T : segs.getLast? = (segs ++ [mkSegment i₀ i₁ (↑j₀ - ↑i₀) (↑m) true])[k] := by grind
          let s := (segs ++ [mkSegment i₀ i₁ (↑j₀ - ↑i₀) (↑m) true])[k]
          by_contra
          simp at this
          specialize h_final1 s T
          simp_rw [ends_at, T] at h_end
          suffices slopeReal s.x j₀ s.y j₁ ≤ sInf (slopeSet v s.x s.y) by
            have : sInf (slopeSet v s.x s.y) = slopeReal s.x j₀ s.y j₁ := by

              sorry
            have : j₀ ∈ (achievingSet v s.x s.y m) := by

              sorry
            have := Finset.le_max' (h_final2 s T).toFinset j₀ (by sorry)
            -- i.e. this means j₀ ≤ i₀ which contradicts hij

            -- problem is I need to get all the typing done correctly again
            -- should see below for some of the work
            -- e.g. the l' stuff gives a condition on what the Finset.max is
            -- combined with h_final4
            sorry
          have m_eq : (mkSegment i₀ i₁ (↑j₀ - ↑i₀) (↑m) true).m = m := by rfl
          simp_rw [m_eq] at this
          have help := nextVertex_slope_eq_sInf' v h
          -- the following is also done below ... so more cleaning is required
          obtain ⟨l, m', hl, hm', hsum, halg⟩ := h_end
          obtain ⟨l', hl', hl''⟩ := h_fin _ T
          have leq : l = l' := by
            rw [hl] at hl'
            exact_mod_cast hl'
          subst leq
          have s.m_eq : s.m = (algebraMap Γ ℝ i₁ - algebraMap Γ ℝ s.y) / (i₀ - s.x : ℝ) := by
            have hlr : (l : ℝ) = (i₀ : ℝ) - (s.x : ℝ) := by
              rify at hsum
              grind
            rw [hm', WithTop.coe_eq_coe, eq_div_iff (by simpa [← hlr] using Nat.cast_ne_zero.mpr hl''),
              ← hlr]
            linarith
          -- 100 % can clean this soooo much more
          simp_rw [s.m_eq] at h_final1
          simp only [WithTop.coe_inj] at h_final1
          simp_rw [slopeReal, ← h_final1]
          have s_eq' : (segs ++ [mkSegment i₀ i₁ (↑j₀ - ↑i₀) (↑m) true])[k].m = s.m := by
            rfl
          simp_rw [s_eq', s.m_eq] at this
          simp only [WithTop.coe_le_coe] at this
          simp_rw [help] at this
          simp_rw [slopeReal] at this
          exact succSlope_le_Slope (Nat.cast_lt.mpr (by grind)) (Nat.cast_lt.mpr hij) this
      · simp [ends_at, mkSegment]
        have := nextVertex_slope_eq_sInf' v h
        use j₀ - i₀
        simp [this, slopeReal]
        -- more of a mess :( ; but see below where norm_cast solved part of it!
        sorry
      · simp [mkSegment]
        use j₀ - i₀
        constructor
        · norm_cast
        · grind
      · simp [mkSegment]
      . simp [mkSegment]
      · simpa using nextVertex_bddBelow v h
      · simpa [mkSegment] using nextVertex_slope_eq_sInf'' v h
      · -- think I may even need API saing that the Classical.choose is m
        -- then apply the nextVertex API I have ...

        -- this will also be how to do the sorry below

        sorry
      ·
        sorry
      · simp
        intro s hs


        -- think I will need new API for this
        -- that is API saying the RHS is j₀
        sorry
    all_goals
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, NPmake_increasing,
        if_true_left]
      intro k hk
      have : k + 1 < segs.length ∨ k + 1 = segs.length := by
       grind
      rcases this with this | this
      all_goals try simpa [this, show k < segs.length from by grind] using h_slopes k this
      try have T : segs.getLast? = (segs ++ [mkSegment i₀ i₁ ⊤ m true])[k] := by grind
      try have T : segs.getLast? = (segs ++ [mkSegment i₀ i₁ ⊤ m false])[k] := by grind
      simp_rw [ends_at, T] at h_end
      obtain ⟨l, m', hl, hm', hsum, halg⟩ := h_end
      obtain ⟨l', hl', hl''⟩ := h_fin _ T
      have leq : l = l' := by
        rw [hl] at hl'
        exact_mod_cast hl'
      subst leq
      simp only [this, le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero]
    let s := (segs ++ [mkSegment i₀ i₁ ⊤ (↑m) true])[k]
    swap; let s := (segs ++ [mkSegment i₀ i₁ ⊤ (↑m) false])[k]
    all_goals
      have s.m_eq : s.m = (algebraMap Γ ℝ i₁ - algebraMap Γ ℝ s.y) / (i₀ - s.x : ℝ) := by
        have hlr : (l : ℝ) = (i₀ : ℝ) - (s.x : ℝ) := by
          rify at hsum
          grind
        rw [hm', WithTop.coe_eq_coe, eq_div_iff (by simpa [← hlr] using Nat.cast_ne_zero.mpr hl''),
          ← hlr]
        linarith
    · have : (mkSegment i₀ i₁ ⊤ m false).l = ⊤ := by rfl
      simp only [this, show (mkSegment i₀ i₁ ⊤ (↑m) false).hitsPoint = false from rfl,
        Bool.false_eq_true, ↓reduceIte, h_final1 (segs ++ [mkSegment i₀ i₁ ⊤ m false])[k] (by grind),
        ge_iff_le]
      have sInfeq : (mkSegment i₀ i₁ ⊤ (↑(sInf (slopeSet v i₀ i₁))) false).m =
        ↑(sInf (slopeSet v i₀ i₁)) := by rfl
      simp_rw [limitingRay_slope_eq_sInf v h, sInfeq, WithTop.coe_le_coe]
      refine le_csInf (limitingRay_nonempty _ h) ?_
      by_contra
      simp only [not_forall, not_le] at this
      obtain ⟨n, hn, n_lt⟩ := this
      obtain ⟨a₀, ha₀, a₀_fin, a₁, ha₁, hn⟩ := hn
      suffices slopeReal s.x a₀ s.y a₁ < sInf (slopeSet v s.x s.y) by
        have contra : slopeReal s.x a₀ s.y a₁ ∈ slopeSet v s.x s.y := by
          -- this was extracted in the previous file; perhaps I can think of a way to do that
          simp_rw [slopeSet, Set.mem_setOf_eq]
          use a₀
          refine ⟨?_, a₀_fin, by use a₁⟩
          calc
            _ < i₀ := by grind
            _ < _ := ha₀
        have contra := csInf_le (h_bdd s T) contra
        grind
      specialize h_final1 s T
      simp_rw [s.m_eq, WithTop.coe_inj] at h_final1
      simp_rw [hn, slopeReal] at n_lt
      have n_lt' : ((algebraMap Γ ℝ) a₁ - (algebraMap Γ ℝ) i₁) / (↑a₀ - ↑i₀) <
          sInf (slopeSet v s.x s.y) := by
        unfold s
        simp_rw [limitingRay_slope_eq_sInf v h]
        exact n_lt -- should be able to not need this... but the let_I s is confusing it
      simp_rw [slopeReal, ← h_final1] at ⊢ n_lt'
      exact succSlope_lt_Slope (Nat.cast_lt.mpr (by grind)) (Nat.cast_lt.mpr ha₀) n_lt'
    · obtain ⟨k₀, hk₀1, hk₀2, k₁, hk₁, hkeq⟩ := infiniteRay_ex _ h
      have : (mkSegment i₀ i₁ ⊤ m true).l = ⊤ := by rfl
      simp only [this, show (mkSegment i₀ i₁ ⊤ (↑m) true).hitsPoint = true from rfl, ↓reduceIte,
          h_final1 (segs ++ [mkSegment i₀ i₁ ⊤ m true])[k] (by grind)]
      by_contra
      have s.x_le : s.x < i₀ := by grind
      specialize h_final1 s T
      suffices slopeReal s.x k₀ s.y k₁ ≤ sInf (slopeSet v s.x s.y) by
        have sInfeq : Classical.choose (h_m s T) = sInf (slopeSet v s.x s.y) := by
          rw [Classical.choose_spec (h_m s T), WithTop.coe_inj] at h_final1
          exact h_final1
        have k₀_in : k₀ ∈ achievingSet v s.x s.y (Classical.choose (h_m s T)) := by
          rw [sInfeq, le_antisymm (csInf_le (h_bdd s T) ⟨k₀, s.x_le.trans hk₀1, hk₀2, k₁, hk₁, rfl⟩)
            this]
          exact ⟨s.x_le.trans hk₀1, hk₀2, k₁, hk₁, rfl⟩
        have : k₀ ≤ i₀ := by
          specialize h_final4 s T
          rw [hl] at h_final4
          norm_cast at h_final4
          calc
            _ ≤ _ := Finset.le_max' (h_final2 s T).toFinset k₀ ((h_final2 s T).mem_toFinset.mpr k₀_in)
            _ ≤ _ := by grind
        omega
      simp_rw [s.m_eq, WithTop.coe_inj] at h_final1
      have bar : (mkSegment i₀ i₁ ⊤ (↑m) true).m = slopeReal i₀ k₀ i₁ k₁ := by
          simp only [← hkeq]
          rfl
      simp_rw [slopeReal, ← h_final1]
      rw [bar, slopeReal, WithTop.coe_lt_coe, ← h_final1, not_lt] at this
      exact succSlope_le_Slope (Nat.cast_lt.mpr s.x_le) (Nat.cast_lt.mpr hk₀1) this

lemma newtonPolygon_increasing (v : ValSeq Γ) (n : ℕ) :
    NPmake_increasing (NPmake v n) := by
  rcases h : findFirstFinite v 0 with _ | ⟨i₀, i₁⟩
  · simpa [NPmake, buildNewtonPolygon, h] using emptyPolygon_increasing
  · convert build_increasing v [] n emptyPolygon_increasing trivial (by aesop) (by aesop) (by aesop)
      (by grind) (by grind) (by grind) (by grind) (by grind) -- nicer way to write this?
    rw [getSegments_eq v n h]

end NPmake_increasing


section NPfull

noncomputable
def NPfull' : ℕ → Segment Γ
  | 0 => match (NPmake v 1)[0]? with
    | some s => s
    | none =>  match findFirstFinite v 0 with
                | none => mkSegment 0 0 0 0 false -- empty polygon; do I want top? 0?
                | some (i, v_i) => mkSegment i v_i 0 ⊤ false -- polynomial tail
  | n+1 => match (NPmake v (n+2))[n+1]? with
    | some s => s -- if there is a segment in n+1 i.e. we have added a new segment
    | none => NPfull' n
        -- I could instead do one of the following:
        -- if it is a segment of finite length then choose a vertical line upwards
        -- if it is a segment of infinite length then repeat

noncomputable
def NPfull : newtonPolygon (Γ := Γ) where
  segments := NPfull' v
  connected := sorry
  slopes_increasing := sorry

-- the idea of connected and slopes increasing is that we know NPbuild has these properties;
-- then we can just extrapolate outwards!

-- Probably will need some API saying that (NPmake v i)[j]? = (NPmake v (i+1))[j]?
-- or something similar ... ie replace i+1 with k for i < k

end NPfull


section examples

/-- Valuation sequence for f(X) = 1 + pX² + p³X⁵ under p-adic valuation.
    v_p(1) = 0, v_p(p) = 1, v_p(p³) = 3, and zero coefficients have v_p = ⊤. -/
def exampleValSeq : ValSeq ℤ
  | 0 => 0
  | 1 => ⊤
  | 2 => 1
  | 3 => ⊤
  | 4 => ⊤
  | 5 => 3
  | _ => ⊤

/-- First segment: (0, 0) → (2, 1) -/
noncomputable
def exampleSeg1 : Segment ℤ := mkSegment 0 0 2 (1/2 : ℝ) true

/-- Second segment: (2, 1) → (5, 3) -/
noncomputable
def exampleSeg2 : Segment ℤ := mkSegment 2 1 3 (2/3 : ℝ) true

noncomputable
def exampleNPfull : ℕ → Segment ℤ
  | 0 => exampleSeg1
  | _ => exampleSeg2

example : exampleNPfull 0 = exampleSeg1 := by rfl
example : exampleNPfull 1 = exampleSeg2 := by rfl
example : exampleNPfull 5 = exampleSeg2 := by rfl

-- how to do the example:
-- I need a proof that findFirstFinite is (0,0)
-- then a proof that it obtains (2,1) as point 1 with fuel 1
-- then a proof that it obtains (5,3) as point 2 with fuel 2
-- then show that for higher fuel the point n is empty (point -> segment)

-- need to find cleaner ways to do this
-- again perhaps this could be a tactic?
lemma example_findFirstFinite : findFirstFinite exampleValSeq 0 = (0, (0 : ℤ)) := by
  classical
  simp_rw [findFirstFinite, exampleValSeq]
  have : finite exampleValSeq 0 := by
    simp_rw [finite, exampleValSeq, ne_eq, WithTop.zero_ne_top, not_false_eq_true]
  split_ifs with h
  · have : Nat.find h = 0 := by
      simpa using this
    rw [this]
  · contrapose h
    use 0

-- perhaps I can make a tactic to solve things like this??
-- It would need to be a finite set on the RHS though (but this is fine for polynomials)
-- reasonably it should be easy to do as we just need to spam exactly what we have done below
-- in all the cases
lemma ex : slopeSet exampleValSeq 0 0 = {1/2, 3/5} := by
  simp_rw [slopeSet]
  simp [finite]
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨j₀, hj₀, ne, j₁, hj₁, eq⟩ := hx
    have : j₀ = 0 ∨ j₀ = 2 ∨ j₀ = 5 := by
      unfold exampleValSeq at *
      grind
    rcases this with h | h | h
    · simp_all
    · simp_all
      left
      simp [slopeReal]
      unfold exampleValSeq at hj₁
      aesop
    · simp_all
      right
      simp [slopeReal]
      unfold exampleValSeq at hj₁
      aesop
  · intro x hx
    simp_all
    rcases hx with H | H
    · use 2
      simp_rw [exampleValSeq]
      simp [slopeReal, H]
    · use 5
      simp_rw [exampleValSeq]
      simp [slopeReal, H]

lemma example_slopeset1 : slopeSet exampleValSeq 0 0 ≠ ∅ := by
  simp_rw [ex]
  grind

lemma example_bddbelow1 : BddBelow (slopeSet exampleValSeq 0 0) := by
  simp [ex]

lemma example_sInf1 : sInf (slopeSet exampleValSeq 0 0) = 1/2 := by
  simp [ex]
  linarith

lemma example_achievingSet1 : (achievingSet exampleValSeq 0 0 (1/2)) = {2} := by
  simp_rw [achievingSet]
  simp [finite]
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨a, b, c, d, e⟩ := hx
    have : x = 0 ∨ x = 2 ∨ x = 5 := by
      unfold exampleValSeq at *
      grind
    rcases this with h | h | h
    · grind
    · exact h
    · simp_all [slopeReal, exampleValSeq]
      simp [← d] at e
      grind
  · simp [exampleValSeq, slopeReal]

lemma example_nextStep1 : nextStep exampleValSeq 0 0 = StepResult.nextVertex 2 1 (1/2) := by
  simp_rw [nextStep]
  simp [example_slopeset1]
  simp [example_bddbelow1]
  simp [example_sInf1]
  split_ifs with h t
  · have : (Classical.choose h) = 1/2 := by
      -- cannot find an easy way to do this right now but it is obvious
      sorry
    simp_rw [this] at t
    simp_rw [example_achievingSet1] at t
    simp only [Set.finite_singleton, Set.Finite.not_infinite] at t
  · -- maybe I need to make the context nicer as it is horrible to work with
    sorry
  · simp_rw [example_sInf1, ex] at h
    aesop

lemma example_NPfull1' : (NPmake exampleValSeq 1)[0]? = exampleSeg1 := by
  simp_rw [NPmake, buildNewtonPolygon]
  have := example_findFirstFinite
  simp [this]
  unfold buildNewtonPolygon.build
  simp
  simp [example_nextStep1]
  unfold buildNewtonPolygon.build
  simp [exampleSeg1]

lemma example_NPfull1 : NPfull' exampleValSeq 0 = exampleSeg1 := by
  simp_rw [NPfull', example_NPfull1']

lemma example_nextStep2 : nextStep exampleValSeq 2 1 = StepResult.nextVertex 5 3 (2/3) := by
  -- trust that this is possible by repeating the method above...
  sorry

-- i.e. to do the work you first apply everything down until we are at the next step
lemma example_NPfull2' : (NPmake exampleValSeq 2)[1]? = exampleSeg2 := by
  simp_rw [NPmake, buildNewtonPolygon]
  have := example_findFirstFinite
  simp [this]
  unfold buildNewtonPolygon.build
  simp [example_nextStep1]
  unfold buildNewtonPolygon.build
  simp
  -- i.e. to do the work you first apply everything down until we are at the next step
  -- perhaps we can put all of this into a tactic??
  simp [example_nextStep2]
  unfold buildNewtonPolygon.build
  simp [exampleSeg2]
  rfl

lemma example_NPfull2 : NPfull' exampleValSeq 1 = exampleSeg2 := by
  simp [NPfull', example_NPfull2']

lemma example_slopeset3 : slopeSet exampleValSeq 5 3 = ∅ := by
  simp_rw [slopeSet]
  simp [finite]
  have h (x : ℕ) (hx : exampleValSeq x ≠ ⊤) : x = 0 ∨ x = 2 ∨ x = 5 := by
      unfold exampleValSeq at *
      grind
  refine Eq.symm (Set.ext ?_)
  intro x
  constructor -- has to be a better way to write this... image of the set of j₀ ... which is empty?
  · intro hx
    aesop
  · intro hx
    simp only [Set.mem_setOf_eq] at hx
    grind

lemma example_nextStep3 : nextStep exampleValSeq 5 3 = StepResult.Tail := by
  simp_rw [nextStep]
  simp [example_slopeset3]

lemma example_NPfull3' : (NPmake exampleValSeq 3)[2]? = none := by
  simp_rw [NPmake, buildNewtonPolygon]
  have := example_findFirstFinite
  simp [this]
  unfold buildNewtonPolygon.build
  simp [example_nextStep1]
  unfold buildNewtonPolygon.build
  simp
  simp [example_nextStep2]
  unfold buildNewtonPolygon.build
  simp [example_nextStep3]

lemma example_NPfull3 : NPfull' exampleValSeq 2 = exampleSeg2 := by
  simp_rw [NPfull']
  simp
  simp [example_NPfull3']
  simp [example_NPfull2']

lemma example_NPfulln (n : ℕ) : NPfull' exampleValSeq (n + 2) = exampleSeg2 := by
  induction n
  · simp [example_NPfull3]
  · rename_i n hn
    unfold NPfull'
    have : (NPmake exampleValSeq (n + 2 + 2))[n + 2 + 1]? = none := by
      simp_rw [NPmake, buildNewtonPolygon]
      have := example_findFirstFinite
      simp [this]
      unfold buildNewtonPolygon.build
      simp [example_nextStep1]
      unfold buildNewtonPolygon.build
      simp
      simp [example_nextStep2]
      unfold buildNewtonPolygon.build
      simp [example_nextStep3] -- i.e. once we get to none we can really stop already!
    simp [this, hn]

lemma example_eq : exampleNPfull = NPfull' exampleValSeq := by
  ext x
  simp_rw [exampleNPfull]
  split
  · exact example_NPfull1.symm
  · rename_i x' hx
    simp_all
    have : x = 1 ∨ x ≥ 2 := by grind
    rcases this with h | h
    · simpa [h] using example_NPfull2.symm
    · obtain ⟨a, rfl⟩ : ∃ a, x = a + 2 := by
        use x-2
        grind
      exact (example_NPfulln  a).symm -- dont like how this method works but it is done...

/-
  That is we have just shown that it is reasonably easy to work through with polynomials
  IF (big if) I can implement the suggested tactics then this could become much easier ...
-/

-- Now let us work through a power series

/-- Valuation sequence for 1 + pX + pX² + pX³ + ···
    v_p(1) = 0 at index 0, v_p(p) = 1 at all other indices. -/
def geometricValSeq : ValSeq ℤ
  | 0 => 0
  | _ => 1

/-- All indices have finite valuation. -/
theorem geometricValSeq_finite (n : ℕ) : finite geometricValSeq n := by
  cases n with
  | zero => simp [finite, geometricValSeq]
  | succ n => simp [finite, geometricValSeq]

/-- The slope from (0, 0) to (n, 1) is 1/n. -/
theorem slope_to_n (n : ℕ) (_hn : n > 0) : slopeReal 0 n 0 1 = 1 / n := by
  simp [slopeReal]

/-- The slope set from (0, 0) is exactly {1/n : n ≥ 1}. -/
theorem geometricValSeq_slopeSet :
    slopeSet geometricValSeq 0 0 = {m : ℝ | ∃ n : ℕ, n > 0 ∧ m = 1 / n} := by
  ext m
  simp only [slopeSet]
  constructor
  · intro ⟨i, hi, hfin, vi, hvi, hm⟩
    use i, hi
    have hvi' : vi = 1 := by
      cases i with
      | zero => omega
      | succ n =>
        simp only [geometricValSeq] at hvi
        exact WithTop.coe_injective hvi.symm
    subst hvi'
    rw [hm]
    simp [slopeReal]
  · intro ⟨n, hn, hm⟩
    use n, hn, geometricValSeq_finite n, 1
    constructor
    · simp [geometricValSeq, Nat.pos_iff_ne_zero.mp hn]
    · rw [hm]
      simp [slopeReal]

/-- The slope set is nonempty. -/
theorem geometricValSeq_slopeSet_nonempty : (slopeSet geometricValSeq 0 0).Nonempty := by
  use 1
  rw [geometricValSeq_slopeSet]
  use 1
  simp

/-! ### The infimum of slopes is 0 -/

/-- The slope set is bounded below by 0. -/
theorem geometricValSeq_slopeSet_bddBelow : BddBelow (slopeSet geometricValSeq 0 0) := by
  use 0
  intro m hm
  rw [geometricValSeq_slopeSet] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact div_nonneg (by norm_num) (le_of_lt hn')

/-- All slopes are positive. -/
theorem geometricValSeq_slopes_pos (m : ℝ) (hm : m ∈ slopeSet geometricValSeq 0 0) : m > 0 := by
  rw [geometricValSeq_slopeSet] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact div_pos (by norm_num) hn'

-- Old Aristotle example
/-- The infimum of the slope set is 0. -/
theorem geometricValSeq_sInf_eq_zero : sInf (slopeSet geometricValSeq 0 0) = 0 := by
  apply le_antisymm
  · -- sInf ≤ 0: Show any lower bound is ≤ 0
    rw [csInf_le_iff geometricValSeq_slopeSet_bddBelow geometricValSeq_slopeSet_nonempty]
    intro ε hε
    -- If ε > 0, find 1/n < ε in the set, contradicting that ε is a lower bound
    by_contra h
    push_neg at h
    -- Find n such that 1/n < ε
    have hpos : ε > 0 := h
    have hex : ∃ n : ℕ, ε⁻¹ < n := exists_nat_gt ε⁻¹
    obtain ⟨n, hn⟩ := hex
    -- 1/(n+1) is in the set
    have hmem : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ∈ slopeSet geometricValSeq 0 0 := by
      rw [geometricValSeq_slopeSet]
      exact ⟨n + 1, Nat.succ_pos n, rfl⟩
    -- ε is a lower bound, so ε ≤ 1/(n+1)
    have hle : ε ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := hε hmem
    -- But 1/(n+1) < ε
    have hlt : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < ε := by
      have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      rw [one_div_lt hn1 hpos, one_div]
      have h1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by simp
      linarith
    linarith
  · -- 0 ≤ sInf: all elements are positive
    apply le_csInf geometricValSeq_slopeSet_nonempty
    intro m hm
    exact le_of_lt (geometricValSeq_slopes_pos m hm)

/-- 0 is not achieved by any slope in the set (no n gives slope 0). -/
theorem geometricValSeq_zero_not_achieved :
    ¬∃ q ∈ slopeSet geometricValSeq 0 0, q = 0 := by
  intro ⟨q, hq, hq0⟩
  rw [geometricValSeq_slopeSet] at hq
  obtain ⟨n, hn, rfl⟩ := hq
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have : (1 : ℝ) / n > 0 := div_pos (by norm_num) hn'
  linarith

theorem geometricValSeq_nextStep_eq_limitingRay :
    nextStep geometricValSeq 0 0 = StepResult.limitingRay 0 := by
  unfold nextStep
  have := geometricValSeq_slopeSet_nonempty
  have : (slopeSet geometricValSeq 0 0) ≠ ∅ := by aesop
  simp [this] -- maybe a better way to rewrite the aristotle code for Nonempty ...
              -- or convert the build to Set.Empty instead of = ∅
  simp [geometricValSeq_slopeSet_bddBelow]
  have := geometricValSeq_zero_not_achieved
  simp_rw [← geometricValSeq_sInf_eq_zero] at this
  split
  · contradiction
  · simp_rw [geometricValSeq_sInf_eq_zero]

theorem geometricValSeq_findFirstFinite :
    findFirstFinite geometricValSeq 0 = some (0, 0) := by
  classical
  simp_rw [findFirstFinite, geometricValSeq]
  have : finite geometricValSeq 0 := by
    simp_rw [finite, geometricValSeq, ne_eq, WithTop.zero_ne_top, not_false_eq_true]
  split_ifs with h
  · have : Nat.find h = 0 := by
      simpa using this
    rw [this]
  · contrapose h
    use 0

lemma geometricValSeq_NPfull1' : (NPmake geometricValSeq 1)[0]? = mkSegment 0 (0 : ℤ) ⊤ 0 false := by
  simp [NPmake, buildNewtonPolygon]
  simp [geometricValSeq_findFirstFinite]
  unfold buildNewtonPolygon.build
  simp [geometricValSeq_nextStep_eq_limitingRay]

lemma geometricValSeq_NPfull1 : NPfull' geometricValSeq 0 = mkSegment 0 (0 : ℤ) ⊤ 0 false := by
  simp_rw [NPfull', geometricValSeq_NPfull1']

lemma geometricValSeq_NPfulln (n : ℕ) : NPfull' geometricValSeq (n+1) = mkSegment 0 (0 : ℤ) ⊤ 0 false := by
  induction n
  · simp [NPfull']
    have : (NPmake geometricValSeq 2)[1]? = none := by
      simp [NPmake, buildNewtonPolygon, geometricValSeq_findFirstFinite]
      unfold buildNewtonPolygon.build
      simp [geometricValSeq_nextStep_eq_limitingRay]
    simp [this]
    simp [geometricValSeq_NPfull1']
  · rename_i n hn
    unfold NPfull'
    have : (NPmake geometricValSeq (n + 1 + 2))[n + 1 + 1]? = none := by
      simp_rw [NPmake, buildNewtonPolygon]
      simp [geometricValSeq_findFirstFinite]
      unfold buildNewtonPolygon.build
      simp [geometricValSeq_nextStep_eq_limitingRay]
    simp [this, hn]

def geometricValSeq_NPfull : ℕ → Segment ℤ
 | _ => mkSegment 0 (0 : ℤ) ⊤ 0 false

lemma geometricValSeq_eq : geometricValSeq_NPfull = NPfull' exampleValSeq := by
  ext x
  -- cba to do the bad method as before... it is certainly true
  sorry

end examples
