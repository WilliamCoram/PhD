/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.Slope

/-!
# The vertex walk

The textbook construction of the Newton polygon: from the first point, take the infimum of the
slopes to all later points and move to the furthest point achieving it; repeat. Here the walk is
built as a height function `vertexWalk v` and proved to satisfy the specification, so that by
uniqueness it *is* `newtonPolygon v`. The walk is what makes the polygon computable and is where
its two terminal behaviours are read off: it stops when no later point exists (the polygon is `⊤`
beyond the last point), and it ends in a ray when the infimum of the slopes is not attained by
finitely many points.

Roadmap: §0.3. Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/Construction.lean`.

## Main definitions

* `NewtonPolygon.nextVertex v i` — the furthest index achieving the minimal slope out of `i`.
* `NewtonPolygon.vertexSeq v n` — the `n`-th vertex of the walk.
* `NewtonPolygon.vertexWalk v` — the walk, as a height function.

## Main results

* `NewtonPolygon.isNewtonPolygonOf_vertexWalk`, `NewtonPolygon.vertexWalk_eq_newtonPolygon`.
* `NewtonPolygon.exists_vertexSeq_of_isVertex`, `NewtonPolygon.isVertex_of_vertexSeq_eq` — the
  walk's vertices and the polygon's vertices.
* `NewtonPolygon.newtonPolygon_eq_top_of_slopeSet_eq_empty`, `NewtonPolygon.newtonPolygon_eq_ray`
  — the two terminal behaviours.
* `NewtonPolygon.iSup_unitSlope_eq_of_ray` — on a terminal ray the limiting slope is the supremum
  of the unit slopes.
* `NewtonPolygon.endsInRay_newtonPolygon_of_nextVertex_eq_top`,
  `NewtonPolygon.exists_vertexSeq_eq_of_endsInRay` — the walk detects the terminal ray.
* `NewtonPolygon.exists_vertexSeq_eq_top`, `NewtonPolygon.vertexSeq_eq_sSup_finiteSet` — for
  finitely many points the walk ends, at the last point.
-/

open scoped Classical

namespace NewtonPolygon

variable {v : ℕ → WithTop ℝ}

/-! ### One step of the walk -/

/-- The later points achieving the minimal slope out of `i`. -/
def achievingSet (v : ℕ → WithTop ℝ) (i : ℕ) : Set ℕ :=
  {k | i < k ∧ v k ≠ ⊤ ∧ slopeTo v i k = sInf (slopeSet v i)}

/-- **The next vertex** after `i`: the furthest index achieving the minimal slope out of `i`, when
finitely many points achieve it; `⊤` when there is no later point, when the infimum is not
attained, or when infinitely many points lie on the minimal line. -/
noncomputable def nextVertex (v : ℕ → WithTop ℝ) (i : ℕ) : WithTop ℕ :=
  if hfin : (achievingSet v i).Finite ∧ (achievingSet v i).Nonempty then
    ((hfin.1.toFinset.max' (hfin.1.toFinset_nonempty.mpr hfin.2) : ℕ) : WithTop ℕ)
  else ⊤

/-- The chord slopes out of `i`, `j` and `k` satisfy the splitting identity: the chord from `i` to
`k` is the weighted average of the chords `i → j` and `j → k`. -/
theorem slopeTo_split (v : ℕ → WithTop ℝ) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    ((k : ℝ) - i) * slopeTo v i k
      = ((j : ℝ) - i) * slopeTo v i j + ((k : ℝ) - j) * slopeTo v j k := by
  have h1 : ((j : ℝ) - i) ≠ 0 := sub_ne_zero.2 (Nat.cast_lt.2 hij).ne'
  have h2 : ((k : ℝ) - j) ≠ 0 := sub_ne_zero.2 (Nat.cast_lt.2 hjk).ne'
  have h3 : ((k : ℝ) - i) ≠ 0 := sub_ne_zero.2 (Nat.cast_lt.2 (hij.trans hjk)).ne'
  simp only [slopeTo]
  field_simp
  ring

/-- The next vertex lies in the achieving set. -/
theorem mem_achievingSet_of_nextVertex_eq {i j : ℕ} (hj : nextVertex v i = j) :
    j ∈ achievingSet v i := by
  rw [nextVertex] at hj
  split_ifs at hj with hfin
  · have heq : hfin.1.toFinset.max' (hfin.1.toFinset_nonempty.mpr hfin.2) = j :=
      WithTop.coe_injective hj
    have hmem := Finset.max'_mem hfin.1.toFinset (hfin.1.toFinset_nonempty.mpr hfin.2)
    rw [heq, Set.Finite.mem_toFinset] at hmem
    exact hmem
  · exact absurd hj WithTop.top_ne_coe

/-- The next vertex is the furthest point achieving the minimal slope. -/
theorem le_of_mem_achievingSet {i j k : ℕ} (hj : nextVertex v i = j) (hk : k ∈ achievingSet v i) :
    k ≤ j := by
  rw [nextVertex] at hj
  split_ifs at hj with hfin
  · have heq : hfin.1.toFinset.max' (hfin.1.toFinset_nonempty.mpr hfin.2) = j :=
      WithTop.coe_injective hj
    rw [← heq]
    exact Finset.le_max' _ _ (Set.Finite.mem_toFinset hfin.1 |>.2 hk)
  · exact absurd hj WithTop.top_ne_coe

/-- The next vertex lies strictly to the right. -/
theorem lt_of_nextVertex_eq {i j : ℕ} (hj : nextVertex v i = j) : i < j :=
  (mem_achievingSet_of_nextVertex_eq hj).1

/-- The next vertex carries a point. -/
theorem ne_top_of_nextVertex_eq {i j : ℕ} (hj : nextVertex v i = j) : v j ≠ ⊤ :=
  (mem_achievingSet_of_nextVertex_eq hj).2.1

/-- The next vertex achieves the minimal slope. -/
theorem slopeTo_nextVertex {i j : ℕ} (hj : nextVertex v i = j) :
    slopeTo v i j = sInf (slopeSet v i) :=
  (mem_achievingSet_of_nextVertex_eq hj).2.2

/-- At a terminal vertex, either no later point lies on the minimal line or infinitely many do:
`nextVertex` is `⊤` exactly when the achieving set is not a nonempty finite set. -/
theorem achievingSet_eq_empty_or_infinite_of_nextVertex_eq_top {i : ℕ}
    (htop : nextVertex v i = ⊤) : achievingSet v i = ∅ ∨ (achievingSet v i).Infinite := by
  by_cases hfin : (achievingSet v i).Finite
  · refine Or.inl (Set.not_nonempty_iff_eq_empty.1 fun hne ↦ ?_)
    rw [nextVertex, dif_pos ⟨hfin, hne⟩] at htop
    exact absurd htop WithTop.coe_ne_top
  · exact Or.inr hfin

/-- Every later point lies on or above the line of the minimal slope out of `i` (admissibility
makes the infimum honest). -/
theorem sInf_slopeSet_le_slopeTo (hv : IsAdmissible v) {i k : ℕ} (hi : v i ≠ ⊤) (hk : i < k)
    (hk' : v k ≠ ⊤) : sInf (slopeSet v i) ≤ slopeTo v i k :=
  csInf_le (isAdmissible_iff_bddBelow.1 hv i hi) ⟨k, hk, hk', rfl⟩

/-- No point beyond the next vertex achieves the minimal slope: they lie strictly above the line. -/
theorem sInf_slopeSet_lt_slopeTo_of_nextVertex_lt (hv : IsAdmissible v) {i j k : ℕ} (hi : v i ≠ ⊤)
    (hj : nextVertex v i = j) (hk : j < k) (hk' : v k ≠ ⊤) :
    sInf (slopeSet v i) < slopeTo v i k := by
  refine lt_of_le_of_ne (sInf_slopeSet_le_slopeTo hv hi ((lt_of_nextVertex_eq hj).trans hk) hk')
    fun heq ↦ ?_
  have hmem : k ∈ achievingSet v i := ⟨(lt_of_nextVertex_eq hj).trans hk, hk', heq.symm⟩
  exact absurd (le_of_mem_achievingSet hj hmem) (by omega)

/-- **The slopes increase along the walk**: the minimal slope out of the next vertex is at least the
minimal slope out of the current one. Strictness can fail: after `v 0 = 0, v 1 = 1, v k = k + 1/k`
the walk steps to `1` and then continues along a ray of the *same* slope `1`, approached but never
attained. See `sInf_slopeSet_lt_sInf_slopeSet_nextVertex` for the strict form. -/
theorem sInf_slopeSet_le_sInf_slopeSet_nextVertex (hv : IsAdmissible v) {i j : ℕ} (hi : v i ≠ ⊤)
    (hj : nextVertex v i = j) (hne : (slopeSet v j).Nonempty) :
    sInf (slopeSet v i) ≤ sInf (slopeSet v j) := by
  refine le_csInf hne ?_
  rintro s ⟨k, hjk, hk, rfl⟩
  have hij : i < j := lt_of_nextVertex_eq hj
  have hsplit := slopeTo_split v hij hjk
  have h1 : sInf (slopeSet v i) ≤ slopeTo v i k :=
    sInf_slopeSet_le_slopeTo hv hi (hij.trans hjk) hk
  have h2 : slopeTo v i j = sInf (slopeSet v i) := slopeTo_nextVertex hj
  have hji : (0 : ℝ) < (j : ℝ) - i := by
    have hx : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    linarith
  have hkj : (0 : ℝ) < (k : ℝ) - j := by
    have hx : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
    linarith
  nlinarith [hsplit, h1, h2, hji, hkj]

/-- **Strict increase when the walk continues to a vertex**: if the step after `j` is again
attained,
the minimal slope out of `j` is strictly larger — a later point achieving the old slope would lie on
the old line and contradict `j` being the furthest point on it. -/
theorem sInf_slopeSet_lt_sInf_slopeSet_nextVertex (hv : IsAdmissible v) {i j : ℕ} (hi : v i ≠ ⊤)
    (hj : nextVertex v i = j) (hj' : nextVertex v j ≠ ⊤) :
    sInf (slopeSet v i) < sInf (slopeSet v j) := by
  obtain ⟨j', hj'eq⟩ := WithTop.ne_top_iff_exists.1 hj'
  have hmem' := mem_achievingSet_of_nextVertex_eq hj'eq.symm
  have hne : (slopeSet v j).Nonempty := ⟨slopeTo v j j', j', hmem'.1, hmem'.2.1, rfl⟩
  refine lt_of_le_of_ne (sInf_slopeSet_le_sInf_slopeSet_nextVertex hv hi hj hne) fun heq ↦ ?_
  -- if the two minimal slopes agreed, `j'` would lie on the line through `i` as well
  have hij : i < j := lt_of_nextVertex_eq hj
  have hjj' : j < j' := hmem'.1
  have hsplit := slopeTo_split v hij hjj'
  have hji : (0 : ℝ) < (j : ℝ) - i := by
    have hx : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    linarith
  have hkj : (0 : ℝ) < (j' : ℝ) - j := by
    have hx : (j : ℝ) < (j' : ℝ) := by exact_mod_cast hjj'
    linarith
  have h2 : slopeTo v i j = sInf (slopeSet v i) := slopeTo_nextVertex hj
  have h3 : slopeTo v j j' = sInf (slopeSet v j) := hmem'.2.2
  have hsame : slopeTo v i j' = sInf (slopeSet v i) := by
    rw [← heq] at h3
    have hsum : ((j' : ℝ) - i) * slopeTo v i j' = ((j' : ℝ) - i) * sInf (slopeSet v i) := by
      rw [hsplit, h2, h3]
      ring
    have hne' : ((j' : ℝ) - i) ≠ 0 := by
      have hx : (i : ℝ) < (j' : ℝ) := by exact_mod_cast hij.trans hjj'
      intro hy
      rw [sub_eq_zero] at hy
      linarith
    exact mul_left_cancel₀ hne' hsum
  exact absurd (le_of_mem_achievingSet hj ⟨hij.trans hjj', hmem'.2.1, hsame⟩) (by omega)

/-! ### The walk -/

/-- **The vertices of the walk**: the first point, then successive next vertices; `⊤` once the
walk has ended. -/
noncomputable def vertexSeq (v : ℕ → WithTop ℝ) : ℕ → WithTop ℕ
  | 0 => if ∃ i, v i ≠ ⊤ then ((sInf (finiteSet v) : ℕ) : WithTop ℕ) else ⊤
  | n + 1 => WithTop.recTopCoe ⊤ (nextVertex v) (vertexSeq v n)

/-- The walk starts at the first point. -/
theorem vertexSeq_zero (hv' : ∃ i, v i ≠ ⊤) :
    vertexSeq v 0 = ((sInf (finiteSet v) : ℕ) : WithTop ℕ) := by
  rw [vertexSeq, if_pos hv']

/-- Each vertex of the walk is the next vertex out of its predecessor. -/
theorem vertexSeq_succ_of_eq {n i : ℕ} (hi : vertexSeq v n = i) :
    vertexSeq v (n + 1) = nextVertex v i := by
  rw [vertexSeq, hi]
  rfl

/-- Once the walk has ended it stays ended. -/
theorem vertexSeq_eq_top_of_le {m n : ℕ} (hm : vertexSeq v m = ⊤) (hmn : m ≤ n) :
    vertexSeq v n = ⊤ := by
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ p _ ih =>
      rw [vertexSeq, ih]
      rfl

/-- The vertices move strictly right. -/
theorem vertexSeq_lt {n i j : ℕ} (hi : vertexSeq v n = i) (hj : vertexSeq v (n + 1) = j) :
    i < j := by
  rw [vertexSeq_succ_of_eq hi] at hj
  exact lt_of_nextVertex_eq hj

/-- The vertices of the walk are strictly increasing. -/
theorem vertexSeq_lt_of_lt {m n i : ℕ} (hm : vertexSeq v m = i) (hmn : m < n) :
    ∀ j : ℕ, vertexSeq v n = j → i < j := by
  induction n, hmn using Nat.le_induction with
  | base =>
      intro j hj
      exact vertexSeq_lt hm hj
  | succ p hp ih =>
      intro j hj
      have hpne : vertexSeq v p ≠ ⊤ := by
        intro hx
        rw [vertexSeq_eq_top_of_le hx (by omega : p ≤ p + 1)] at hj
        exact absurd hj WithTop.top_ne_coe
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hpne
      exact lt_trans (ih k hk.symm) (vertexSeq_lt hk.symm hj)

/-- Every vertex of the walk is a point. -/
theorem ne_top_of_vertexSeq_eq {n i : ℕ} (hi : vertexSeq v n = i) : v i ≠ ⊤ := by
  cases n with
  | zero =>
      rw [vertexSeq] at hi
      split_ifs at hi with hex
      · have heq : sInf (finiteSet v) = i := WithTop.coe_injective hi
        rw [← heq]
        exact mem_finiteSet.1 (Nat.sInf_mem (hex.imp fun _ hx ↦ mem_finiteSet.2 hx))
      · exact absurd hi WithTop.top_ne_coe
  | succ p =>
      rcases eq_or_ne (vertexSeq v p) ⊤ with hp | hp
      · rw [vertexSeq, hp] at hi
        exact absurd hi WithTop.top_ne_coe
      · obtain ⟨i', hi'⟩ := WithTop.ne_top_iff_exists.1 hp
        rw [vertexSeq_succ_of_eq hi'.symm] at hi
        exact ne_top_of_nextVertex_eq hi

/-- While the walk has not ended, its `n`-th vertex is at an index at least `n`: the walk takes at
least one step right each time. -/
theorem exists_vertexSeq_eq_of_forall_ne_top (hx : ∀ n, vertexSeq v n ≠ ⊤) (n : ℕ) :
    ∃ i : ℕ, vertexSeq v n = (i : WithTop ℕ) ∧ n ≤ i := by
  induction n with
  | zero =>
      obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.1 (hx 0)
      exact ⟨i, hi.symm, Nat.zero_le i⟩
  | succ p ih =>
      obtain ⟨i, hi, hpi⟩ := ih
      obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 (hx (p + 1))
      refine ⟨j, hj.symm, ?_⟩
      have := vertexSeq_lt hi hj.symm
      omega

/-! ### The last vertex at or before an index -/

/-- The last vertex of the walk at or before `k` (junk `0` if none). -/
noncomputable def lastVertex (v : ℕ → WithTop ℝ) (k : ℕ) : ℕ :=
  sSup {i | ∃ n, vertexSeq v n = (i : WithTop ℕ) ∧ i ≤ k}

/-- The vertices at or before `k` are bounded above by `k`. -/
theorem bddAbove_vertexSet (v : ℕ → WithTop ℝ) (k : ℕ) :
    BddAbove {i : ℕ | ∃ n, vertexSeq v n = (i : WithTop ℕ) ∧ i ≤ k} := by
  refine ⟨k, ?_⟩
  rintro b ⟨-, -, hbk⟩
  exact hbk

/-- Every vertex at or before `k` is at or before the last one. -/
theorem le_lastVertex {n i k : ℕ} (hi : vertexSeq v n = i) (hik : i ≤ k) : i ≤ lastVertex v k :=
  le_csSup (bddAbove_vertexSet v k) ⟨n, hi, hik⟩

/-- The last vertex at or before `k` is a vertex, and it is at most `k`. -/
theorem exists_vertexSeq_lastVertex {n i k : ℕ} (hi : vertexSeq v n = i) (hik : i ≤ k) :
    ∃ m, vertexSeq v m = ((lastVertex v k : ℕ) : WithTop ℕ) ∧ lastVertex v k ≤ k := by
  have hmem : lastVertex v k ∈ {i : ℕ | ∃ n, vertexSeq v n = (i : WithTop ℕ) ∧ i ≤ k} := by
    rw [lastVertex]
    exact Nat.sSup_mem ⟨i, n, hi, hik⟩ (bddAbove_vertexSet v k)
  exact hmem

/-- A vertex is its own last vertex. -/
theorem lastVertex_eq_of_vertexSeq_eq {n i : ℕ} (hi : vertexSeq v n = i) : lastVertex v i = i := by
  refine le_antisymm ?_ (le_lastVertex hi le_rfl)
  rw [lastVertex]
  refine csSup_le ⟨i, n, hi, le_rfl⟩ ?_
  rintro b ⟨-, -, hbi⟩
  exact hbi

/-- Between two consecutive vertices the last vertex is the left one. -/
theorem lastVertex_eq_of_lt_next {n i j k : ℕ} (hi : vertexSeq v n = i)
    (hj : vertexSeq v (n + 1) = j) (hik : i ≤ k) (hkj : k < j) : lastVertex v k = i := by
  refine le_antisymm ?_ (le_lastVertex hi hik)
  rw [lastVertex]
  refine csSup_le ⟨i, n, hi, hik⟩ ?_
  rintro b ⟨m, hm, hbk⟩
  rcases lt_trichotomy m n with hmn | rfl | hmn
  · exact le_of_lt (vertexSeq_lt_of_lt hm hmn i hi)
  · exact le_of_eq (WithTop.coe_injective (hi.symm.trans hm)).symm
  · rcases eq_or_lt_of_le (show n + 1 ≤ m by omega) with heq | hlt
    · have : j = b := WithTop.coe_injective (hj.symm.trans (heq ▸ hm))
      omega
    · have := vertexSeq_lt_of_lt hj hlt b hm
      omega

/-- Beyond a terminal vertex the last vertex is that vertex. -/
theorem lastVertex_eq_of_next_eq_top {n i k : ℕ} (hi : vertexSeq v n = i)
    (hj : vertexSeq v (n + 1) = ⊤) (hik : i ≤ k) : lastVertex v k = i := by
  refine le_antisymm ?_ (le_lastVertex hi hik)
  rw [lastVertex]
  refine csSup_le ⟨i, n, hi, hik⟩ ?_
  rintro b ⟨m, hm, hbk⟩
  rcases lt_trichotomy m n with hmn | rfl | hmn
  · exact le_of_lt (vertexSeq_lt_of_lt hm hmn i hi)
  · exact le_of_eq (WithTop.coe_injective (hi.symm.trans hm)).symm
  · rw [vertexSeq_eq_top_of_le hj (by omega : n + 1 ≤ m)] at hm
    exact absurd hm.symm WithTop.coe_ne_top

/-- **The walk, as a height function**: `⊤` before the first point; at `k`, the line of the minimal
slope out of the last vertex at or before `k` — a segment when that slope is attained, a ray when it
is not — and `⊤` once no later point exists. -/
noncomputable def vertexWalk (v : ℕ → WithTop ℝ) (k : ℕ) : WithTop ℝ :=
  if (∀ i, v i = ⊤) ∨ k < sInf (finiteSet v) then ⊤
  else if (slopeSet v (lastVertex v k)).Nonempty ∨ k = lastVertex v k then
    v (lastVertex v k) +
      (k - lastVertex v k : ℕ) • ((sInf (slopeSet v (lastVertex v k)) : ℝ) : WithTop ℝ)
  else ⊤

/-- A point whose chord slope out of `i` is `σ` lies on the line of slope `σ` through `i`. -/
theorem eq_add_nsmul_of_slopeTo_eq {i j : ℕ} (hi : v i ≠ ⊤) (hj : v j ≠ ⊤) (hij : i < j) {σ : ℝ}
    (hσ : slopeTo v i j = σ) : v j = v i + (j - i : ℕ) • ((σ : ℝ) : WithTop ℝ) := by
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 hi
  obtain ⟨b, hB⟩ := WithTop.ne_top_iff_exists.1 hj
  have hne : ((j : ℝ) - i) ≠ 0 := sub_ne_zero.2 (Nat.cast_lt.2 hij).ne'
  rw [slopeTo, ← hA, ← hB] at hσ
  simp only [WithTop.untop₀_coe] at hσ
  rw [div_eq_iff hne] at hσ
  rw [← hA, ← hB, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_inj, nsmul_eq_mul,
    Nat.cast_sub hij.le]
  linarith

/-- Below the first point the walk is `⊤`. -/
theorem vertexWalk_eq_top_of_lt_sInf {k : ℕ} (hk : k < sInf (finiteSet v)) :
    vertexWalk v k = ⊤ := by
  rw [vertexWalk, if_pos (Or.inr hk)]

/-- The walk passes through its vertices. -/
theorem vertexWalk_eq_of_vertexSeq_eq {n i : ℕ} (hi : vertexSeq v n = i) :
    vertexWalk v i = v i := by
  have hine : v i ≠ ⊤ := ne_top_of_vertexSeq_eq hi
  have hlast : lastVertex v i = i := lastVertex_eq_of_vertexSeq_eq hi
  have hcond : ¬((∀ j, v j = ⊤) ∨ i < sInf (finiteSet v)) := by
    push Not
    exact ⟨⟨i, hine⟩, Nat.sInf_le (mem_finiteSet.2 hine)⟩
  rw [vertexWalk, if_neg hcond, if_pos (Or.inr hlast.symm), hlast, Nat.sub_self, zero_nsmul,
    add_zero]

/-- Between two consecutive vertices the walk is the segment joining them. -/
theorem vertexWalk_eq_of_le_of_le {n i j k : ℕ} (hi : vertexSeq v n = i)
    (hj : vertexSeq v (n + 1) = j) (hik : i ≤ k) (hkj : k ≤ j) :
    vertexWalk v k = v i + (k - i : ℕ) • ((sInf (slopeSet v i) : ℝ) : WithTop ℝ) := by
  have hine : v i ≠ ⊤ := ne_top_of_vertexSeq_eq hi
  have hjne : v j ≠ ⊤ := ne_top_of_vertexSeq_eq hj
  have hij : i < j := vertexSeq_lt hi hj
  have hnext : nextVertex v i = j := by rwa [vertexSeq_succ_of_eq hi] at hj
  have hslope : slopeTo v i j = sInf (slopeSet v i) := slopeTo_nextVertex hnext
  have hsne : (slopeSet v i).Nonempty := ⟨slopeTo v i j, j, hij, hjne, rfl⟩
  rcases eq_or_lt_of_le hkj with rfl | hlt
  · -- at the next vertex the segment ends exactly at the point
    rw [vertexWalk_eq_of_vertexSeq_eq hj]
    exact eq_add_nsmul_of_slopeTo_eq hine hjne hij hslope
  · have hlast : lastVertex v k = i := lastVertex_eq_of_lt_next hi hj hik hlt
    have hcond : ¬((∀ m, v m = ⊤) ∨ k < sInf (finiteSet v)) := by
      push Not
      refine ⟨⟨i, hine⟩, le_trans (Nat.sInf_le (mem_finiteSet.2 hine)) hik⟩
    rw [vertexWalk, if_neg hcond, if_pos (Or.inl (by rw [hlast]; exact hsne)), hlast]

/-- **The walk lies on or below the points**: the line bound at each step. -/
theorem vertexWalk_le (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) (k : ℕ) :
    vertexWalk v k ≤ v k := by
  by_cases hcond : (∀ m, v m = ⊤) ∨ k < sInf (finiteSet v)
  · rw [vertexWalk, if_pos hcond]
    rcases hcond with hall | hlt
    · rw [hall k]
    · rw [not_not.1 (Nat.notMem_of_lt_sInf hlt)]
  rw [vertexWalk, if_neg hcond]
  push Not at hcond
  obtain ⟨⟨m, hm⟩, hge⟩ := hcond
  have hfirst : vertexSeq v 0 = ((sInf (finiteSet v) : ℕ) : WithTop ℕ) := vertexSeq_zero hv'
  obtain ⟨p, hp, hpk⟩ := exists_vertexSeq_lastVertex hfirst hge
  have hLne : v (lastVertex v k) ≠ ⊤ := ne_top_of_vertexSeq_eq hp
  by_cases hsplit : (slopeSet v (lastVertex v k)).Nonempty ∨ k = lastVertex v k
  · rw [if_pos hsplit]
    rcases eq_or_lt_of_le hpk with heq | hlt
    · rw [heq, Nat.sub_self, zero_nsmul, add_zero]
    by_cases hkt : v k = ⊤
    · rw [hkt]
      exact le_top
    have hle := sInf_slopeSet_le_slopeTo hv hLne hlt hkt
    have hval := eq_add_nsmul_of_slopeTo_eq hLne hkt hlt (σ := slopeTo v (lastVertex v k) k) rfl
    rw [hval]
    refine add_le_add le_rfl ?_
    exact nsmul_le_nsmul_right (WithTop.coe_le_coe.2 hle) _
  · rw [if_neg hsplit, top_le_iff]
    push Not at hsplit
    obtain ⟨hempty, hne⟩ := hsplit
    by_contra hkt
    have hklt : lastVertex v k < k := by omega
    have hmem : slopeTo v (lastVertex v k) k ∈ slopeSet v (lastVertex v k) := ⟨k, hklt, hkt, rfl⟩
    rw [hempty] at hmem
    exact absurd hmem (Set.notMem_empty _)

/-- The last vertex at or before an index is monotone in that index. -/
theorem lastVertex_mono (v : ℕ → WithTop ℝ) {j k : ℕ} (hjk : j ≤ k) :
    lastVertex v j ≤ lastVertex v k := by
  rcases Set.eq_empty_or_nonempty {i : ℕ | ∃ n, vertexSeq v n = (i : WithTop ℕ) ∧ i ≤ j} with
    he | hne
  · rw [lastVertex, he]
    simp only [csSup_empty, Nat.bot_eq_zero, zero_le]
  · rw [lastVertex]
    refine csSup_le hne ?_
    rintro b ⟨p, hp, hbj⟩
    exact le_lastVertex hp (hbj.trans hjk)

/-- The minimal slopes increase along the walk. -/
theorem sInf_slopeSet_le_of_vertexSeq_le (hv : IsAdmissible v) {m n i : ℕ}
    (hi : vertexSeq v m = i) (hmn : m ≤ n) :
    ∀ j : ℕ, vertexSeq v n = j → (slopeSet v j).Nonempty →
      sInf (slopeSet v i) ≤ sInf (slopeSet v j) := by
  induction n, hmn using Nat.le_induction with
  | base =>
      intro j hj _
      have heq : i = j := WithTop.coe_injective (hi.symm.trans hj)
      rw [heq]
  | succ p hp ih =>
      intro j hj hne
      have hpne : vertexSeq v p ≠ ⊤ := by
        intro hx
        rw [vertexSeq_eq_top_of_le hx (by omega : p ≤ p + 1)] at hj
        exact absurd hj WithTop.top_ne_coe
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hpne
      have hqj : nextVertex v q = j := by rwa [vertexSeq_succ_of_eq hq.symm] at hj
      have hqne : (slopeSet v q).Nonempty :=
        ⟨slopeTo v q j, j, lt_of_nextVertex_eq hqj, ne_top_of_nextVertex_eq hqj, rfl⟩
      exact le_trans (ih q hq.symm hqne)
        (sInf_slopeSet_le_sInf_slopeSet_nextVertex hv (ne_top_of_vertexSeq_eq hq.symm) hqj hne)

/-- The walk's value, as soon as it is finite. -/
theorem vertexWalk_eq_of_ne_top {k : ℕ} (hk : vertexWalk v k ≠ ⊤) :
    vertexWalk v k = v (lastVertex v k)
      + (k - lastVertex v k : ℕ) • ((sInf (slopeSet v (lastVertex v k)) : ℝ) : WithTop ℝ) := by
  rw [vertexWalk] at hk ⊢
  split_ifs at hk ⊢ with h1 h2
  · exact absurd rfl hk
  · rfl
  · exact absurd rfl hk

/-- Vertices are ordered by their position in the walk. -/
theorem lt_of_vertexSeq_lt {m n i j : ℕ} (hm : vertexSeq v m = i) (hn : vertexSeq v n = j)
    (hij : i < j) : m < n := by
  by_contra hx
  rw [not_lt] at hx
  rcases eq_or_lt_of_le hx with heq | hlt
  · subst heq
    have heq' : i = j := WithTop.coe_injective (hm.symm.trans hn)
    omega
  · have hlt' := vertexSeq_lt_of_lt hn hlt i hm
    omega

/-- The last vertex either stays put or jumps to the new index, which is then the next vertex. -/
theorem lastVertex_succ (hv' : ∃ i, v i ≠ ⊤) {k : ℕ} (hk : sInf (finiteSet v) ≤ k) :
    lastVertex v (k + 1) = lastVertex v k ∨
      (lastVertex v (k + 1) = k + 1 ∧
        nextVertex v (lastVertex v k) = ((k + 1 : ℕ) : WithTop ℕ)) := by
  obtain ⟨m, hm, hmk⟩ := exists_vertexSeq_lastVertex (vertexSeq_zero hv') hk
  obtain ⟨m', hm', hmk'⟩ :=
    exists_vertexSeq_lastVertex (vertexSeq_zero hv') (by omega : sInf (finiteSet v) ≤ k + 1)
  rcases eq_or_lt_of_le (lastVertex_mono v (by omega : k ≤ k + 1)) with heq | hlt
  · exact Or.inl heq.symm
  have hk1 : lastVertex v (k + 1) = k + 1 := by
    by_contra hx
    exact absurd (le_lastVertex hm' (by omega : lastVertex v (k + 1) ≤ k)) (by omega)
  refine Or.inr ⟨hk1, ?_⟩
  rw [hk1] at hm'
  have hmm' : m < m' := lt_of_vertexSeq_lt hm hm' (by omega)
  have hnextne : nextVertex v (lastVertex v k) ≠ ⊤ := by
    intro hx
    rw [← vertexSeq_succ_of_eq hm] at hx
    have hxx := vertexSeq_eq_top_of_le hx (show m + 1 ≤ m' by omega)
    rw [hm'] at hxx
    exact absurd hxx WithTop.coe_ne_top
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 hnextne
  have hjv : vertexSeq v (m + 1) = ((j : ℕ) : WithTop ℕ) := by
    rw [vertexSeq_succ_of_eq hm]
    exact hj.symm
  have hjk : lastVertex v k < j := lt_of_nextVertex_eq hj.symm
  have hjgt : k < j := by
    by_contra hx
    exact absurd (le_lastVertex hjv (by omega : j ≤ k)) (by omega)
  have hjle : j ≤ k + 1 := by
    rcases eq_or_lt_of_le (show m + 1 ≤ m' by omega) with heq' | hlt'
    · have hcc : vertexSeq v (m + 1) = ((k + 1 : ℕ) : WithTop ℕ) := by
        rw [heq']
        exact hm'
      have hcc2 : ((j : ℕ) : WithTop ℕ) = ((k + 1 : ℕ) : WithTop ℕ) := by
        rw [← hjv]
        exact hcc
      exact le_of_eq (WithTop.coe_injective hcc2)
    · exact le_of_lt (vertexSeq_lt_of_lt hjv hlt' (k + 1) hm')
  have hjeq : j = k + 1 := by omega
  rw [← hj, hjeq]
  rfl

/-- **One step of the walk** adds the minimal slope out of the last vertex. -/
theorem vertexWalk_succ_eq (hv' : ∃ i, v i ≠ ⊤) {k : ℕ}
    (hk : vertexWalk v k ≠ ⊤) (hk1 : vertexWalk v (k + 1) ≠ ⊤) :
    vertexWalk v (k + 1)
      = vertexWalk v k + ((sInf (slopeSet v (lastVertex v k)) : ℝ) : WithTop ℝ) := by
  have hkS : sInf (finiteSet v) ≤ k := by
    by_contra hx
    exact hk (vertexWalk_eq_top_of_lt_sInf (not_le.1 hx))
  obtain ⟨m, hm, hmk⟩ := exists_vertexSeq_lastVertex (vertexSeq_zero hv') hkS
  have hLne : v (lastVertex v k) ≠ ⊤ := ne_top_of_vertexSeq_eq hm
  rw [vertexWalk_eq_of_ne_top hk, vertexWalk_eq_of_ne_top hk1]
  rcases lastVertex_succ hv' hkS with hstay | ⟨hjump, hnext⟩
  · rw [hstay, show k + 1 - lastVertex v k = (k - lastVertex v k) + 1 by omega, succ_nsmul,
      add_assoc]
  · -- the new index is the next vertex: the walk's value there is the point itself
    rw [hjump, Nat.sub_self, zero_nsmul, add_zero]
    have hval := eq_add_nsmul_of_slopeTo_eq hLne (ne_top_of_nextVertex_eq hnext)
      (lt_of_nextVertex_eq hnext) (slopeTo_nextVertex hnext)
    rw [hval, show k + 1 - lastVertex v k = (k - lastVertex v k) + 1 by omega, succ_nsmul,
      add_assoc]

/-- The walk is finite at `k` exactly when the last vertex has later points (or is `k` itself). -/
theorem vertexWalk_ne_top_iff (hv' : ∃ i, v i ≠ ⊤) {k : ℕ} (hk : sInf (finiteSet v) ≤ k) :
    vertexWalk v k ≠ ⊤ ↔ ((slopeSet v (lastVertex v k)).Nonempty ∨ k = lastVertex v k) := by
  obtain ⟨m, hm, hmk⟩ := exists_vertexSeq_lastVertex (vertexSeq_zero hv') hk
  have hLne : v (lastVertex v k) ≠ ⊤ := ne_top_of_vertexSeq_eq hm
  have hcond : ¬((∀ t, v t = ⊤) ∨ k < sInf (finiteSet v)) := by
    push Not
    exact ⟨⟨lastVertex v k, hLne⟩, hk⟩
  rw [vertexWalk, if_neg hcond]
  split_ifs with h2
  · refine iff_of_true ?_ h2
    rw [Ne, ← WithTop.coe_nsmul, WithTop.add_eq_top, not_or]
    exact ⟨hLne, WithTop.coe_ne_top⟩
  · exact iff_of_false (fun hx ↦ hx rfl) h2

/-- Where the walk is finite it is at or beyond the first point. -/
theorem sInf_le_of_vertexWalk_ne_top {k : ℕ} (hk : vertexWalk v k ≠ ⊤) :
    sInf (finiteSet v) ≤ k := by
  by_contra hx
  exact hk (vertexWalk_eq_top_of_lt_sInf (not_le.1 hx))

/-- The minimal slope out of the last vertex is nonempty as soon as the walk is finite one step
further. -/
theorem slopeSet_lastVertex_nonempty (hv' : ∃ i, v i ≠ ⊤) {k : ℕ} (hk : vertexWalk v k ≠ ⊤)
    (hk1 : vertexWalk v (k + 1) ≠ ⊤) : (slopeSet v (lastVertex v k)).Nonempty := by
  have hkS : sInf (finiteSet v) ≤ k := sInf_le_of_vertexWalk_ne_top hk
  obtain ⟨m, hm, hmk⟩ := exists_vertexSeq_lastVertex (vertexSeq_zero hv') hkS
  rcases (vertexWalk_ne_top_iff hv' (by omega : sInf (finiteSet v) ≤ k + 1)).1 hk1 with hs | hs
  · obtain ⟨m', hm', hmk'⟩ :=
      exists_vertexSeq_lastVertex (vertexSeq_zero hv') (by omega : sInf (finiteSet v) ≤ k + 1)
    obtain ⟨σ, t, hlt, htne, -⟩ := hs
    exact ⟨slopeTo v (lastVertex v k) t, t,
      lt_of_le_of_lt (lastVertex_mono v (by omega : k ≤ k + 1)) hlt, htne, rfl⟩
  · obtain ⟨m', hm', hmk'⟩ :=
      exists_vertexSeq_lastVertex (vertexSeq_zero hv') (by omega : sInf (finiteSet v) ≤ k + 1)
    refine ⟨slopeTo v (lastVertex v k) (k + 1), k + 1, by omega, ?_, rfl⟩
    rw [← hs] at hm'
    exact ne_top_of_vertexSeq_eq hm'

/-- The walk's finiteness set is an interval. -/
theorem ordConnected_finiteSet_vertexWalk (hv' : ∃ i, v i ≠ ⊤) :
    (finiteSet (vertexWalk v)).OrdConnected := by
  have hfirst := vertexSeq_zero hv'
  refine ⟨fun a ha c hc b hb ↦ ?_⟩
  refine mem_finiteSet.2 ?_
  have hab : a ≤ b := hb.1
  have hbc : b ≤ c := hb.2
  have hSa := sInf_le_of_vertexWalk_ne_top (mem_finiteSet.1 ha)
  have hSb : sInf (finiteSet v) ≤ b := le_trans hSa hab
  have hSc : sInf (finiteSet v) ≤ c := le_trans hSb hbc
  rw [vertexWalk_ne_top_iff hv' hSb]
  by_cases hbL : b = lastVertex v b
  · exact Or.inr hbL
  refine Or.inl ?_
  obtain ⟨mb, hmb, hmbk⟩ := exists_vertexSeq_lastVertex hfirst hSb
  obtain ⟨mc, hmc, hmck⟩ := exists_vertexSeq_lastVertex hfirst hSc
  rcases eq_or_lt_of_le (lastVertex_mono v hbc) with heq | hlt
  · rcases (vertexWalk_ne_top_iff hv' hSc).1 (mem_finiteSet.1 hc) with hs | hs
    · rwa [← heq] at hs
    · exfalso
      omega
  · exact ⟨slopeTo v (lastVertex v b) (lastVertex v c), lastVertex v c, hlt,
      ne_top_of_vertexSeq_eq hmc, rfl⟩

/-- **The walk is convex**: its slopes increase from vertex to vertex. -/
theorem isConvexSeq_vertexWalk (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) :
    IsConvexSeq (vertexWalk v) := by
  have hfirst := vertexSeq_zero hv'
  refine ⟨ordConnected_finiteSet_vertexWalk hv', fun a ha b hb hab ↦ ?_⟩
  by_cases hb1 : vertexWalk v (b + 1) = ⊤
  · have hx : unitSlope (vertexWalk v) b = ⊤ :=
      unitSlope_eq_top_iff.2 (Or.inr (by rwa [Order.succ_eq_add_one]))
    rw [hx]
    exact le_top
  have hane : vertexWalk v a ≠ ⊤ := mem_finiteSet.1 ha
  have hbne : vertexWalk v b ≠ ⊤ := mem_finiteSet.1 hb
  have ha1 : vertexWalk v (a + 1) ≠ ⊤ :=
    mem_finiteSet.1 ((ordConnected_finiteSet_vertexWalk hv').out ha (mem_finiteSet.2 hb1)
      ⟨by omega, by omega⟩)
  have hua : unitSlope (vertexWalk v) a
      = ((sInf (slopeSet v (lastVertex v a)) : ℝ) : WithTop ℝ) :=
    unitSlope_eq_of_succ_eq_add hane (by
      rw [Order.succ_eq_add_one]
      exact vertexWalk_succ_eq hv' hane ha1)
  have hub : unitSlope (vertexWalk v) b
      = ((sInf (slopeSet v (lastVertex v b)) : ℝ) : WithTop ℝ) :=
    unitSlope_eq_of_succ_eq_add hbne (by
      rw [Order.succ_eq_add_one]
      exact vertexWalk_succ_eq hv' hbne hb1)
  rw [hua, hub, WithTop.coe_le_coe]
  obtain ⟨ma, hma, -⟩ := exists_vertexSeq_lastVertex hfirst (sInf_le_of_vertexWalk_ne_top hane)
  obtain ⟨mb, hmb, -⟩ := exists_vertexSeq_lastVertex hfirst (sInf_le_of_vertexWalk_ne_top hbne)
  have hsne : (slopeSet v (lastVertex v b)).Nonempty :=
    slopeSet_lastVertex_nonempty hv' hbne hb1
  rcases eq_or_lt_of_le (lastVertex_mono v hab) with heq | hlt
  · rw [heq]
  · exact sInf_slopeSet_le_of_vertexSeq_le hv hma
      (le_of_lt (lt_of_vertexSeq_lt hma hmb hlt)) _ hmb hsne

/-- **The chord bound for a convex minorant**: between a point `L` and a later point `t`, a convex
minorant lies on or below the chord of the two points, hence below the line of slope
`slopeTo v L t` through `(L, v L)`. -/
theorem le_add_nsmul_slopeTo_of_isConvexMinorant {g : ℕ → WithTop ℝ} (hg : IsConvexMinorant v g)
    {L k t : ℕ} (hLne : v L ≠ ⊤) (htne : v t ≠ ⊤) (hLk : L ≤ k) (hkt : k ≤ t) :
    g k ≤ v L + (k - L : ℕ) • ((slopeTo v L t : ℝ) : WithTop ℝ) := by
  obtain ⟨hgc, hgv⟩ := hg
  rcases eq_or_lt_of_le hLk with rfl | hLklt
  · rw [Nat.sub_self, zero_nsmul, add_zero]
    exact hgv L
  rcases eq_or_lt_of_le hkt with rfl | hktlt
  · have hval := eq_add_nsmul_of_slopeTo_eq hLne htne hLklt (σ := slopeTo v L k) rfl
    rw [← hval]
    exact hgv k
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 hLne
  obtain ⟨c, hC⟩ := WithTop.ne_top_iff_exists.1 htne
  have hgL : g L ≤ ((a : ℝ) : WithTop ℝ) := by rw [hA]; exact hgv L
  have hgt : g t ≤ ((c : ℝ) : WithTop ℝ) := by rw [hC]; exact hgv t
  have hgLf : g L ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hgL
  have hgtf : g t ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hgt
  have hgkf : g k ≠ ⊤ :=
    mem_finiteSet.1 (hgc.ordConnected.out (mem_finiteSet.2 hgLf) (mem_finiteSet.2 hgtf)
      ⟨hLk, hkt⟩)
  obtain ⟨p, hP⟩ := WithTop.ne_top_iff_exists.1 hgLf
  obtain ⟨q, hQ⟩ := WithTop.ne_top_iff_exists.1 hgtf
  obtain ⟨r, hR⟩ := WithTop.ne_top_iff_exists.1 hgkf
  have hchord := hgc.le_chord hLk hkt
  rw [← hP, ← hQ, ← hR, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
    ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
    Nat.card_Ico, Nat.card_Ico, Nat.card_Ico, Nat.cast_sub (hLk.trans hkt), Nat.cast_sub hkt,
    Nat.cast_sub hLk] at hchord
  rw [← hP, WithTop.coe_le_coe] at hgL
  rw [← hQ, WithTop.coe_le_coe] at hgt
  have htL : (0 : ℝ) < (t : ℝ) - L := by
    have hx : (L : ℝ) < (t : ℝ) := by exact_mod_cast hLk.trans_lt hktlt
    linarith
  have hkL : (0 : ℝ) < (k : ℝ) - L := by
    have hx : (L : ℝ) < (k : ℝ) := by exact_mod_cast hLklt
    linarith
  have htk : (0 : ℝ) < (t : ℝ) - k := by
    have hx : (k : ℝ) < (t : ℝ) := by exact_mod_cast hktlt
    linarith
  have hslope : slopeTo v L t = (c - a) / ((t : ℝ) - L) := by
    rw [slopeTo, ← hA, ← hC]
    simp only [WithTop.untop₀_coe]
  rw [← hR, ← hA, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
    Nat.cast_sub hLk, hslope]
  have hmul : ((t : ℝ) - L) * r
      ≤ ((t : ℝ) - L) * (a + ((k : ℝ) - L) * ((c - a) / ((t : ℝ) - L))) := by
    have hexp : ((t : ℝ) - L) * (a + ((k : ℝ) - L) * ((c - a) / ((t : ℝ) - L)))
        = ((t : ℝ) - k) * a + ((k : ℝ) - L) * c := by
      field_simp
      ring
    rw [hexp]
    nlinarith [hchord, mul_nonneg htk.le (sub_nonneg.2 hgL), mul_nonneg hkL.le (sub_nonneg.2 hgt)]
  exact le_of_mul_le_mul_left hmul htL

/-- **Approximating the minimal slope beyond `k`**: out of the last vertex `L` at or before `k`,
points of chord slope arbitrarily close to the minimal slope can be found *at or beyond* `k`. When
the minimum is attained it is attained beyond `k` (the attaining points up to `k` would be later
vertices), and when it is not attained the finitely many points strictly between `L` and `k` have
strictly larger slope, so they can be avoided by shrinking `ε`. -/
theorem exists_le_and_slopeTo_lt (hv : IsAdmissible v) {m L k : ℕ} (hm : vertexSeq v m = L)
    (hlast : lastVertex v k = L) (hne : (slopeSet v L).Nonempty) {ε : ℝ}
    (hε : 0 < ε) : ∃ t, k ≤ t ∧ v t ≠ ⊤ ∧ slopeTo v L t < sInf (slopeSet v L) + ε := by
  have hLne : v L ≠ ⊤ := ne_top_of_vertexSeq_eq hm
  by_cases hnext : nextVertex v L = ⊤
  · rcases achievingSet_eq_empty_or_infinite_of_nextVertex_eq_top hnext with hA | hA
    · -- the minimum is not attained: the points strictly between `L` and `k` have a positive gap
      have hgap : ∃ δ, 0 < δ ∧ δ ≤ ε ∧ ∀ t ∈ (Finset.Ioo L k).filter (fun t ↦ v t ≠ ⊤),
          sInf (slopeSet v L) + δ ≤ slopeTo v L t := by
        rcases Finset.eq_empty_or_nonempty ((Finset.Ioo L k).filter (fun t ↦ v t ≠ ⊤)) with hT | hT
        · exact ⟨ε, hε, le_rfl, fun t ht ↦ absurd (hT ▸ ht) (Finset.notMem_empty t)⟩
        obtain ⟨t₀, ht₀, hinf⟩ := Finset.exists_mem_eq_inf' hT (fun t ↦ slopeTo v L t)
        obtain ⟨ht₀I, ht₀ne⟩ := Finset.mem_filter.1 ht₀
        have hLt₀ : L < t₀ := (Finset.mem_Ioo.1 ht₀I).1
        have hσlt : sInf (slopeSet v L) < slopeTo v L t₀ := by
          refine lt_of_le_of_ne (sInf_slopeSet_le_slopeTo hv hLne hLt₀ ht₀ne) fun heq ↦ ?_
          have hmem : t₀ ∈ achievingSet v L := ⟨hLt₀, ht₀ne, heq.symm⟩
          exact absurd (hA ▸ hmem) (Set.notMem_empty t₀)
        refine ⟨min ε (slopeTo v L t₀ - sInf (slopeSet v L)), lt_min hε (by linarith),
          min_le_left _ _, fun t ht ↦ ?_⟩
        have h1 : slopeTo v L t₀ ≤ slopeTo v L t := by
          rw [← hinf]
          exact Finset.inf'_le _ ht
        have h2 := min_le_right ε (slopeTo v L t₀ - sInf (slopeSet v L))
        linarith
      obtain ⟨δ, hδ, hδε, hδT⟩ := hgap
      obtain ⟨s, hs, hsl⟩ := exists_lt_of_csInf_lt hne (by linarith : sInf (slopeSet v L) <
        sInf (slopeSet v L) + δ)
      obtain ⟨t, hLt, htne, rfl⟩ := hs
      refine ⟨t, ?_, htne, by linarith⟩
      by_contra hx
      have hmem : t ∈ (Finset.Ioo L k).filter (fun t ↦ v t ≠ ⊤) :=
        Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨hLt, by omega⟩, htne⟩
      have := hδT t hmem
      linarith
    · -- the minimum is attained infinitely often: pick a point on the line beyond `k`
      obtain ⟨t, ht, hkt⟩ := hA.exists_gt k
      exact ⟨t, le_of_lt hkt, ht.2.1, by rw [← ht.2.2]; linarith⟩
  · -- the minimum is attained: the furthest attaining point is the next vertex, beyond `k`
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 hnext
    have hjv : vertexSeq v (m + 1) = ((j : ℕ) : WithTop ℕ) := by
      rw [vertexSeq_succ_of_eq hm]
      exact hj.symm
    have hLj : L < j := lt_of_nextVertex_eq hj.symm
    have hkj : k < j := by
      by_contra hx
      have := le_lastVertex hjv (by omega : j ≤ k)
      omega
    refine ⟨j, le_of_lt hkj, ne_top_of_nextVertex_eq hj.symm, ?_⟩
    rw [slopeTo_nextVertex hj.symm]
    linarith

/-- **Maximality of the walk**: a convex minorant of the points lies on or below the walk. On a
segment it lies below the chord between the two vertices, which is the walk; on a final ray it lies
below chords to points approximating the ray arbitrarily well. -/
theorem le_vertexWalk_of_isConvexMinorant (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤)
    {g : ℕ → WithTop ℝ} (hg : IsConvexMinorant v g) (k : ℕ) : g k ≤ vertexWalk v k := by
  by_cases hk : vertexWalk v k = ⊤
  · rw [hk]
    exact le_top
  rw [vertexWalk_eq_of_ne_top hk]
  obtain ⟨m, hm, hmk⟩ :=
    exists_vertexSeq_lastVertex (vertexSeq_zero hv') (sInf_le_of_vertexWalk_ne_top hk)
  have hne' : (slopeSet v (lastVertex v k)).Nonempty ∨ k = lastVertex v k :=
    (vertexWalk_ne_top_iff hv' (sInf_le_of_vertexWalk_ne_top hk)).1 hk
  obtain ⟨L, hLdef⟩ : ∃ L, lastVertex v k = L := ⟨_, rfl⟩
  rw [hLdef] at hm hmk hne' ⊢
  have hLne : v L ≠ ⊤ := ne_top_of_vertexSeq_eq hm
  rcases eq_or_lt_of_le hmk with heq | hlt
  · -- `k` is itself a vertex of the walk: the walk is the point
    rw [heq, Nat.sub_self, zero_nsmul, add_zero]
    exact hg.2 k
  have hne : (slopeSet v L).Nonempty := by
    rcases hne' with h | h
    · exact h
    · omega
  obtain ⟨a, hA⟩ := WithTop.ne_top_iff_exists.1 hLne
  have hbound : ∀ t, k ≤ t → v t ≠ ⊤ →
      g k ≤ ((a + (k - L : ℕ) * slopeTo v L t : ℝ) : WithTop ℝ) := by
    intro t hkt htne
    have hb := le_add_nsmul_slopeTo_of_isConvexMinorant hg hLne htne hmk hkt
    rwa [← hA, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul] at hb
  have hgk : g k ≠ ⊤ := by
    obtain ⟨t, hkt, htne, -⟩ := exists_le_and_slopeTo_lt hv hm hLdef hne one_pos
    exact ne_top_of_le_ne_top WithTop.coe_ne_top (hbound t hkt htne)
  obtain ⟨r, hR⟩ := WithTop.ne_top_iff_exists.1 hgk
  rw [← hA, ← hR, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul]
  by_contra hx
  rw [not_le] at hx
  have hc : (0 : ℝ) < ((k - L : ℕ) : ℝ) := by
    have hpos : 0 < k - L := by omega
    exact_mod_cast hpos
  have hc0 : ((k - L : ℕ) : ℝ) ≠ 0 := ne_of_gt hc
  have hpos : 0 < r - (a + ((k - L : ℕ) : ℝ) * sInf (slopeSet v L)) := by linarith
  obtain ⟨t, hkt, htne, hslt⟩ :=
    exists_le_and_slopeTo_lt hv hm hLdef hne (div_pos hpos hc)
  have hb := hbound t hkt htne
  rw [← hR, WithTop.coe_le_coe] at hb
  have hexp : ((k - L : ℕ) : ℝ) * (sInf (slopeSet v L) +
      (r - (a + ((k - L : ℕ) : ℝ) * sInf (slopeSet v L))) / ((k - L : ℕ) : ℝ)) = r - a := by
    field_simp
    ring
  have hmul := mul_lt_mul_of_pos_left hslt hc
  rw [hexp] at hmul
  linarith

/-- **Existence by construction** (roadmap §0.3.1): the walk is the Newton polygon. -/
theorem isNewtonPolygonOf_vertexWalk (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) :
    IsNewtonPolygonOf v (vertexWalk v) :=
  ⟨isConvexSeq_vertexWalk hv hv', vertexWalk_le hv hv',
    fun _ hg hgv k ↦ le_vertexWalk_of_isConvexMinorant hv hv' ⟨hg, hgv⟩ k⟩

/-- **The walk is the polygon**, by uniqueness of the greatest convex minorant. -/
theorem vertexWalk_eq_newtonPolygon (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) :
    vertexWalk v = newtonPolygon v :=
  (isNewtonPolygonOf_vertexWalk hv hv').eq_newtonPolygon

/-- Every vertex of the polygon is a vertex of the walk: the walk's unit slope is constant between
consecutive walk vertices, so it can only change at one. -/
theorem exists_vertexSeq_of_isVertex (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {i : ℕ}
    (hi : IsVertex (newtonPolygon v) i) : ∃ n, vertexSeq v n = (i : WithTop ℕ) := by
  rw [← vertexWalk_eq_newtonPolygon hv hv'] at hi
  obtain ⟨hine, hcase⟩ := hi
  have hS : sInf (finiteSet v) ≤ i := sInf_le_of_vertexWalk_ne_top hine
  obtain ⟨q, hq, hqi⟩ := exists_vertexSeq_lastVertex (vertexSeq_zero hv') hS
  suffices hL : lastVertex v i = i from ⟨q, by rwa [hL] at hq⟩
  rcases hcase with heq | hlt
  · -- the anchor is the first vertex of the walk
    rw [(isNewtonPolygonOf_vertexWalk hv hv').anchor_eq_sInf hv'] at heq
    rw [heq]
    exact lastVertex_eq_of_vertexSeq_eq (vertexSeq_zero hv')
  -- a genuine break: the unit slope is constant between two consecutive vertices
  by_contra hne
  have hLi : lastVertex v i < i := lt_of_le_of_ne hqi hne
  obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlt
  have hpne : unitSlope (vertexWalk v) p ≠ ⊤ := ne_top_of_lt hlt
  rw [Ne, unitSlope_eq_top_iff, not_or, Order.succ_eq_add_one] at hpne
  have hsne : (slopeSet v (lastVertex v (p + 1))).Nonempty := by
    rcases (vertexWalk_ne_top_iff hv' hS).1 hine with h | h
    · exact h
    · exact absurd h (by omega)
  have hLprev : lastVertex v p = lastVertex v (p + 1) :=
    le_antisymm (lastVertex_mono v (by omega)) (le_lastVertex hq (by omega))
  have hi1ne : vertexWalk v (p + 1 + 1) ≠ ⊤ := by
    rw [vertexWalk_ne_top_iff hv' (by omega : sInf (finiteSet v) ≤ p + 1 + 1)]
    rcases lastVertex_succ hv' hS with hstay | ⟨hjump, -⟩
    · exact Or.inl (by rw [hstay]; exact hsne)
    · exact Or.inr hjump.symm
  have hu1 : unitSlope (vertexWalk v) p
      = ((sInf (slopeSet v (lastVertex v p)) : ℝ) : WithTop ℝ) := by
    refine unitSlope_eq_of_succ_eq_add hpne.1 ?_
    rw [Order.succ_eq_add_one]
    exact vertexWalk_succ_eq hv' hpne.1 hpne.2
  have hu2 : unitSlope (vertexWalk v) (p + 1)
      = ((sInf (slopeSet v (lastVertex v (p + 1))) : ℝ) : WithTop ℝ) := by
    refine unitSlope_eq_of_succ_eq_add hine ?_
    rw [Order.succ_eq_add_one]
    exact vertexWalk_succ_eq hv' hine hi1ne
  rw [hu1, hu2, hLprev] at hlt
  exact absurd hlt (lt_irrefl _)

/-- A vertex of the walk followed by another vertex is a vertex of the polygon. (A walk vertex
followed by a ray of the same slope is not one: the slope does not change there.) The last point is
covered by `isVertex_of_succ_eq_top`. -/
theorem isVertex_of_vertexSeq_eq (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ}
    (hi : vertexSeq v n = i) (hnext : nextVertex v i ≠ ⊤) : IsVertex (newtonPolygon v) i := by
  rw [← vertexWalk_eq_newtonPolygon hv hv']
  have hine : v i ≠ ⊤ := ne_top_of_vertexSeq_eq hi
  have hwi : vertexWalk v i = v i := vertexWalk_eq_of_vertexSeq_eq hi
  refine ⟨by rw [hwi]; exact hine, ?_⟩
  -- the next vertex gives the unit slope on the right of `i`
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 hnext
  have hij : i < j := lt_of_nextVertex_eq hj.symm
  have hjv : vertexSeq v (n + 1) = ((j : ℕ) : WithTop ℕ) := by
    rw [vertexSeq_succ_of_eq hi]
    exact hj.symm
  have hslopeR : unitSlope (vertexWalk v) i = ((sInf (slopeSet v i) : ℝ) : WithTop ℝ) := by
    refine unitSlope_eq_of_succ_eq_add (by rw [hwi]; exact hine) ?_
    rw [Order.succ_eq_add_one, vertexWalk_eq_of_le_of_le hi hjv le_rfl (by omega),
      vertexWalk_eq_of_le_of_le hi hjv (by omega) (by omega), Nat.sub_self, zero_nsmul, add_zero,
      show i + 1 - i = 1 by omega, one_nsmul]
  rcases n with _ | m
  · -- the first vertex is the anchor
    refine Or.inl ?_
    rw [(isNewtonPolygonOf_vertexWalk hv hv').anchor_eq_sInf hv']
    exact WithTop.coe_injective (hi.symm.trans (vertexSeq_zero hv'))
  -- at a later vertex the minimal slope strictly increases
  refine Or.inr ?_
  have hmne : vertexSeq v m ≠ ⊤ := fun hx ↦ by
    rw [vertexSeq_eq_top_of_le hx (Nat.le_succ m)] at hi
    exact absurd hi.symm WithTop.coe_ne_top
  obtain ⟨i', hi'⟩ := WithTop.ne_top_iff_exists.1 hmne
  have hnexti' : nextVertex v i' = (i : WithTop ℕ) := by
    rw [← vertexSeq_succ_of_eq hi'.symm]
    exact hi
  have hi'i : i' < i := lt_of_nextVertex_eq hnexti'
  have hwprev : vertexWalk v (i - 1)
      = v i' + (i - 1 - i' : ℕ) • ((sInf (slopeSet v i') : ℝ) : WithTop ℝ) :=
    vertexWalk_eq_of_le_of_le hi'.symm hi (by omega) (by omega)
  have hslopeL : unitSlope (vertexWalk v) (i - 1) = ((sInf (slopeSet v i') : ℝ) : WithTop ℝ) := by
    refine unitSlope_eq_of_succ_eq_add ?_ ?_
    · rw [hwprev, Ne, ← WithTop.coe_nsmul, WithTop.add_eq_top, not_or]
      exact ⟨ne_top_of_vertexSeq_eq hi'.symm, WithTop.coe_ne_top⟩
    · rw [Order.succ_eq_add_one, show i - 1 + 1 = i by omega, hwprev,
        vertexWalk_eq_of_le_of_le hi'.symm hi (by omega) le_rfl,
        show i - i' = (i - 1 - i') + 1 by omega, succ_nsmul, add_assoc]
  rw [hslopeL, hslopeR, WithTop.coe_lt_coe]
  exact sInf_slopeSet_lt_sInf_slopeSet_nextVertex hv (ne_top_of_vertexSeq_eq hi'.symm) hnexti'
    hnext

/-! ### The two ways the walk ends -/

/-- **The polygon stops**: beyond a vertex with no later point the polygon is `⊤`. -/
theorem newtonPolygon_eq_top_of_slopeSet_eq_empty (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤)
    {n i : ℕ} (hi : vertexSeq v n = i) (he : slopeSet v i = ∅) {k : ℕ} (hk : i < k) :
    newtonPolygon v k = ⊤ := by
  rw [← vertexWalk_eq_newtonPolygon hv hv']
  have hine : v i ≠ ⊤ := ne_top_of_vertexSeq_eq hi
  have hnone : ∀ t, i < t → v t = ⊤ := by
    intro t hit
    by_contra hx
    exact absurd (show slopeTo v i t ∈ slopeSet v i from ⟨t, hit, hx, rfl⟩)
      (by rw [he]; exact Set.notMem_empty _)
  have htop : nextVertex v i = ⊤ := by
    rw [nextVertex, dif_neg]
    rintro ⟨-, t, hit, htne, -⟩
    exact htne (hnone t hit)
  have hlast : lastVertex v k = i :=
    lastVertex_eq_of_next_eq_top hi (by rw [vertexSeq_succ_of_eq hi]; exact htop) (le_of_lt hk)
  by_contra hx
  have hS : sInf (finiteSet v) ≤ k := le_trans (Nat.sInf_le (mem_finiteSet.2 hine)) (le_of_lt hk)
  rcases (vertexWalk_ne_top_iff hv' hS).1 hx with h | h
  · rw [hlast, he] at h
    exact absurd h Set.not_nonempty_empty
  · rw [hlast] at h
    omega

/-- **The polygon ends in a ray**: from a vertex whose minimal slope is not attained by finitely
many points, the polygon is the ray of that slope. -/
theorem newtonPolygon_eq_ray (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ}
    (hi : vertexSeq v n = i) (hne : (slopeSet v i).Nonempty) (htop : nextVertex v i = ⊤) {k : ℕ}
    (hik : i ≤ k) :
    newtonPolygon v k = v i + (k - i : ℕ) • ((sInf (slopeSet v i) : ℝ) : WithTop ℝ) := by
  rw [← vertexWalk_eq_newtonPolygon hv hv']
  have hine : v i ≠ ⊤ := ne_top_of_vertexSeq_eq hi
  have hlast : lastVertex v k = i :=
    lastVertex_eq_of_next_eq_top hi (by rw [vertexSeq_succ_of_eq hi]; exact htop) hik
  have hcond : ¬((∀ t, v t = ⊤) ∨ k < sInf (finiteSet v)) := by
    push Not
    exact ⟨⟨i, hine⟩, le_trans (Nat.sInf_le (mem_finiteSet.2 hine)) hik⟩
  rw [vertexWalk, if_neg hcond, if_pos (Or.inl (by rw [hlast]; exact hne)), hlast]

/-- On a final ray the polygon is finite from the ray's vertex on. -/
theorem ne_top_newtonPolygon_of_ray (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ}
    (hi : vertexSeq v n = i) (hne : (slopeSet v i).Nonempty) (htop : nextVertex v i = ⊤) {k : ℕ}
    (hik : i ≤ k) : newtonPolygon v k ≠ ⊤ := by
  rw [newtonPolygon_eq_ray hv hv' hi hne htop hik, Ne, ← WithTop.coe_nsmul, WithTop.add_eq_top,
    not_or]
  exact ⟨ne_top_of_vertexSeq_eq hi, WithTop.coe_ne_top⟩

/-- On a final ray every unit slope from the ray's vertex on is the ray's slope. -/
theorem unitSlope_newtonPolygon_of_ray (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ}
    (hi : vertexSeq v n = i) (hne : (slopeSet v i).Nonempty) (htop : nextVertex v i = ⊤) {k : ℕ}
    (hik : i ≤ k) :
    unitSlope (newtonPolygon v) k = ((sInf (slopeSet v i) : ℝ) : WithTop ℝ) := by
  refine unitSlope_eq_of_succ_eq_add (ne_top_newtonPolygon_of_ray hv hv' hi hne htop hik) ?_
  rw [Order.succ_eq_add_one, newtonPolygon_eq_ray hv hv' hi hne htop (by omega : i ≤ k + 1),
    newtonPolygon_eq_ray hv hv' hi hne htop hik, show k + 1 - i = (k - i) + 1 by omega,
    succ_nsmul, add_assoc]

/-- On a final ray the limiting slope is the supremum of the unit slopes (roadmap §0.3.2). -/
theorem iSup_unitSlope_eq_of_ray (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ}
    (hi : vertexSeq v n = i) (hne : (slopeSet v i).Nonempty) (htop : nextVertex v i = ⊤) :
    (⨆ j : ℕ, unitSlope (newtonPolygon v) (sInf (finiteSet v) + j))
      = ((sInf (slopeSet v i) : ℝ) : WithTop ℝ) := by
  have hP : IsNewtonPolygonOf v (newtonPolygon v) :=
    isNewtonPolygonOf_newtonPolygon (exists_isConvexMinorant_iff_isAdmissible.2 hv)
  have hine : v i ≠ ⊤ := ne_top_of_vertexSeq_eq hi
  have hane : v (sInf (finiteSet v)) ≠ ⊤ :=
    mem_finiteSet.1 (Nat.sInf_mem ⟨i, mem_finiteSet.2 hine⟩)
  have hai : sInf (finiteSet v) ≤ i := Nat.sInf_le (mem_finiteSet.2 hine)
  have hrayne : ∀ k, i ≤ k → newtonPolygon v k ≠ ⊤ :=
    fun k hk ↦ ne_top_newtonPolygon_of_ray hv hv' hi hne htop hk
  have hslope : ∀ k, i ≤ k →
      unitSlope (newtonPolygon v) k = ((sInf (slopeSet v i) : ℝ) : WithTop ℝ) :=
    fun k hk ↦ unitSlope_newtonPolygon_of_ray hv hv' hi hne htop hk
  refine le_antisymm (ciSup_le fun j ↦ ?_) ?_
  · rcases le_or_gt i (sInf (finiteSet v) + j) with hk | hk
    · exact le_of_eq (hslope _ hk)
    · rw [← hslope i le_rfl]
      exact hP.convex.monotoneOn
        (mem_finiteSet.2 (hP.ne_top_of_le_of_le hane hine (by omega) (by omega)))
        (mem_finiteSet.2 (hrayne i le_rfl)) (by omega)
  · have h0 : sInf (finiteSet v) + (i - sInf (finiteSet v)) = i := by omega
    refine le_trans (le_of_eq ?_) (le_ciSup
      (f := fun j : ℕ ↦ unitSlope (newtonPolygon v) (sInf (finiteSet v) + j))
      (OrderTop.bddAbove _) (i - sInf (finiteSet v)))
    rw [h0]
    exact (hslope i le_rfl).symm

/-- **The walk detects the terminal ray**: at a vertex with later points whose minimal slope is not
attained by finitely many of them, the polygon ends in the ray of that slope. -/
theorem endsInRay_newtonPolygon_of_nextVertex_eq_top (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤)
    {n i : ℕ} (hi : vertexSeq v n = i) (hne : (slopeSet v i).Nonempty) (htop : nextVertex v i = ⊤) :
    EndsInRay (newtonPolygon v) (sInf (slopeSet v i)) :=
  ⟨i, fun _ hij ↦ unitSlope_newtonPolygon_of_ray hv hv' hi hne htop hij⟩

/-- Conversely, a polygon ending in a ray of slope `m` comes from a terminal vertex of the walk
with later points, whose minimal slope is `m`; when finitely many points lie on the ray, this vertex
is the last of them. -/
theorem exists_vertexSeq_eq_of_endsInRay (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {m : ℝ}
    (hm : EndsInRay (newtonPolygon v) m) :
    ∃ n i : ℕ, vertexSeq v n = (i : WithTop ℕ) ∧ (slopeSet v i).Nonempty ∧ nextVertex v i = ⊤ ∧
      sInf (slopeSet v i) = m := by
  obtain ⟨N, hN⟩ := hm
  obtain ⟨M, hM⟩ := EndsInRay.ne_top ⟨N, hN⟩
  -- on a ray there are finitely many vertices, so the walk ends
  have hx : ∃ n, vertexSeq v n = ⊤ := by
    by_contra hx
    push Not at hx
    obtain ⟨i, hi, hNi⟩ := exists_vertexSeq_eq_of_forall_ne_top hx (N + 2)
    obtain ⟨hPi, hcase⟩ := isVertex_of_vertexSeq_eq hv hv' hi
      (by rw [← vertexSeq_succ_of_eq hi]; exact hx (N + 2 + 1))
    rcases hcase with heq | hlt
    · rw [((isNewtonPolygonOf_newtonPolygon
        (exists_isConvexMinorant_iff_isAdmissible.2 hv)).anchor_eq_sInf hv')] at heq
      have hlt0 := vertexSeq_lt_of_lt (vertexSeq_zero hv') (by omega : 0 < N + 2) i hi
      omega
    · rw [hN (i - 1) (by omega), hN i (by omega)] at hlt
      exact absurd hlt (lt_irrefl _)
  -- the last vertex of the walk is the ray's vertex
  have hmem : vertexSeq v (sInf {n | vertexSeq v n = ⊤}) = ⊤ := Nat.sInf_mem hx
  obtain ⟨p, hp⟩ : ∃ p, sInf {n | vertexSeq v n = ⊤} = p + 1 := by
    refine ⟨sInf {n | vertexSeq v n = ⊤} - 1, ?_⟩
    rcases Nat.eq_zero_or_pos (sInf {n | vertexSeq v n = ⊤}) with h0 | h
    · rw [h0, vertexSeq_zero hv'] at hmem
      exact absurd hmem WithTop.coe_ne_top
    · omega
  rw [hp] at hmem
  have hpnot : p ∉ {n | vertexSeq v n = ⊤} := Nat.notMem_of_lt_sInf (by rw [hp]; omega)
  have hpne : vertexSeq v p ≠ ⊤ := hpnot
  obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.1 hpne
  have htop : nextVertex v i = ⊤ := by rw [← vertexSeq_succ_of_eq hi.symm]; exact hmem
  have hne : (slopeSet v i).Nonempty := by
    rcases Set.eq_empty_or_nonempty (slopeSet v i) with he | h
    · refine absurd (hM (max M (i + 1)) (le_max_left _ _)) ?_
      rw [newtonPolygon_eq_top_of_slopeSet_eq_empty hv hv' hi.symm he
        (by omega : i < max M (i + 1))]
      exact fun hx ↦ hx rfl
    · exact h
  refine ⟨p, i, hi.symm, hne, htop, ?_⟩
  have h1 := unitSlope_newtonPolygon_of_ray hv hv' hi.symm hne htop
    (le_max_left i N : i ≤ max i N)
  rw [hN (max i N) (le_max_right i N)] at h1
  exact WithTop.coe_injective h1.symm

/-! ### Finitely supported sequences -/

/-- For finitely many points the walk ends (roadmap §0.3.3). -/
theorem exists_vertexSeq_eq_top (hfin : (finiteSet v).Finite) : ∃ n, vertexSeq v n = ⊤ := by
  by_contra hx
  push Not at hx
  obtain ⟨i, hi, hMi⟩ := exists_vertexSeq_eq_of_forall_ne_top hx (sSup (finiteSet v) + 1)
  have hle := le_csSup hfin.bddAbove (mem_finiteSet.2 (ne_top_of_vertexSeq_eq hi))
  omega

/-- For finitely many points the last vertex of the walk is the last point. -/
theorem vertexSeq_eq_sSup_finiteSet (hfin : (finiteSet v).Finite) {n : ℕ}
    (hn : vertexSeq v n ≠ ⊤) (hn1 : vertexSeq v (n + 1) = ⊤) :
    vertexSeq v n = ((sSup (finiteSet v) : ℕ) : WithTop ℕ) := by
  obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.1 hn
  have hine : v i ≠ ⊤ := ne_top_of_vertexSeq_eq hi.symm
  have htop : nextVertex v i = ⊤ := by rw [← vertexSeq_succ_of_eq hi.symm]; exact hn1
  -- with finitely many points the infimum is attained, so the walk can only end at the last point
  have hsub : achievingSet v i ⊆ finiteSet v := fun t ht ↦ mem_finiteSet.2 ht.2.1
  have he : slopeSet v i = ∅ := by
    by_contra hne
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hne
    have hsfin : (slopeSet v i).Finite := by
      refine Set.Finite.subset (hfin.image (slopeTo v i)) ?_
      rintro s ⟨t, hit, htne, rfl⟩
      exact ⟨t, mem_finiteSet.2 htne, rfl⟩
    obtain ⟨t, hit, htne, heq⟩ := hne.csInf_mem hsfin
    refine absurd htop ?_
    rw [nextVertex, dif_pos ⟨hfin.subset hsub, ⟨t, hit, htne, heq.symm⟩⟩]
    exact WithTop.coe_ne_top
  have hmax : ∀ t, v t ≠ ⊤ → t ≤ i := by
    intro t htne
    by_contra hx
    exact absurd (show slopeTo v i t ∈ slopeSet v i from ⟨t, by omega, htne, rfl⟩)
      (by rw [he]; exact Set.notMem_empty _)
  rw [← hi]
  refine congrArg _ (le_antisymm (le_csSup hfin.bddAbove (mem_finiteSet.2 hine)) ?_)
  exact csSup_le ⟨i, mem_finiteSet.2 hine⟩ fun t ht ↦ hmax t (mem_finiteSet.1 ht)

end NewtonPolygon
