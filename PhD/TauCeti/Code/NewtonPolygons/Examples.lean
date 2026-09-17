/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.IntervalCases
import PhD.TauCeti.Code.NewtonPolygons.Construction

/-!
# Examples

The worked examples of the roadmap's Layer 0, kept as theorems so that they are checked: a single
point, an affine sequence, the parabola `k²` (every point a vertex), the alternating sequence
`0, 1, 0, 1, …` (polygon the zero function), a collinear interior point (a point on the polygon
that is not a vertex), and `⌈k√2⌉`, whose polygon is the ray of irrational slope `√2` although
every point is integral.

Roadmap: Layer 0, "Examples".
-/

open scoped Classical

namespace NewtonPolygon

/-- A single point is its own polygon, `⊤` everywhere else. -/
theorem newtonPolygon_single (y : ℝ) :
    newtonPolygon (fun k : ℕ ↦ if k = 0 then (y : WithTop ℝ) else ⊤)
      = fun k ↦ if k = 0 then (y : WithTop ℝ) else ⊤ := by
  have hfs : finiteSet (fun k : ℕ ↦ if k = 0 then (y : WithTop ℝ) else ⊤) = {0} := by
    ext j
    rw [mem_finiteSet, Set.mem_singleton_iff]
    by_cases h : j = 0
    · rw [if_pos h]
      exact iff_of_true WithTop.coe_ne_top h
    · rw [if_neg h]
      exact iff_of_false (fun hx ↦ hx rfl) h
  refine newtonPolygon_eq_self ⟨?_, ?_⟩
  · rw [hfs]
    exact Set.ordConnected_singleton
  · rw [hfs]
    exact Set.subsingleton_singleton.monotoneOn _

/-- An affine sequence is its own polygon. -/
theorem newtonPolygon_affine (y σ : ℝ) :
    newtonPolygon (fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ))
      = fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ) :=
  newtonPolygon_eq_self (isConvexSeq_affine y σ)

/-- The unit slopes of the parabola are the odd numbers. -/
theorem unitSlope_sq (j : ℕ) :
    unitSlope (fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) j = ((2 * j + 1 : ℝ) : WithTop ℝ) := by
  refine unitSlope_eq_of_succ_eq_add WithTop.coe_ne_top ?_
  show (((((Order.succ j : ℕ)) : ℝ) ^ 2 : ℝ) : WithTop ℝ)
      = (((j : ℝ) ^ 2 : ℝ) : WithTop ℝ) + ((2 * j + 1 : ℝ) : WithTop ℝ)
  rw [← WithTop.coe_add, WithTop.coe_inj, Order.succ_eq_add_one]
  push_cast
  ring

/-- The parabola is convex. -/
theorem isConvexSeq_sq : IsConvexSeq (fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) := by
  have hfs : finiteSet (fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ mem_finiteSet.2 WithTop.coe_ne_top
  refine ⟨by rw [hfs]; exact Set.ordConnected_univ, fun a _ b _ hab ↦ ?_⟩
  rw [unitSlope_sq, unitSlope_sq, WithTop.coe_le_coe]
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  linarith

/-- A convex sequence is its own polygon; the parabola has every point a vertex and unit slopes
`1, 3, 5, …`. -/
theorem newtonPolygon_sq :
    newtonPolygon (fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ))
      = fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ) :=
  newtonPolygon_eq_self isConvexSeq_sq

/-- The parabola's polygon has the odd numbers as its unit slopes. -/
theorem unitSlope_newtonPolygon_sq (j : ℕ) :
    unitSlope (newtonPolygon fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) j
      = ((2 * j + 1 : ℝ) : WithTop ℝ) := by
  rw [newtonPolygon_sq]
  exact unitSlope_sq j

/-- The zero sequence has zero unit slopes. -/
theorem unitSlope_zero_fun (j : ℕ) :
    unitSlope (fun _ : ℕ ↦ (0 : WithTop ℝ)) j = ((0 : ℝ) : WithTop ℝ) := by
  refine unitSlope_eq_of_succ_eq_add WithTop.zero_ne_top ?_
  rw [WithTop.coe_zero, add_zero]

/-- The zero sequence is convex. -/
theorem isConvexSeq_zero_fun : IsConvexSeq (fun _ : ℕ ↦ (0 : WithTop ℝ)) := by
  have hfs : finiteSet (fun _ : ℕ ↦ (0 : WithTop ℝ)) = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ mem_finiteSet.2 WithTop.zero_ne_top
  exact ⟨by rw [hfs]; exact Set.ordConnected_univ,
    fun a _ b _ _ ↦ le_of_eq (by rw [unitSlope_zero_fun, unitSlope_zero_fun])⟩

/-- The polygon of `0, 1, 0, 1, …` is the zero function. -/
theorem newtonPolygon_alternating :
    newtonPolygon (fun k : ℕ ↦ if Even k then (0 : WithTop ℝ) else 1) = fun _ ↦ 0 := by
  have hzero : IsConvexSeq (fun _ : ℕ ↦ (0 : WithTop ℝ)) := isConvexSeq_zero_fun
  refine (IsNewtonPolygonOf.eq_newtonPolygon ⟨hzero, ?_, ?_⟩).symm
  · intro k
    by_cases h : Even k
    · rw [if_pos h]
    · rw [if_neg h]
      exact zero_le_one
  · intro g hg hgv k
    by_cases h : Even k
    · refine le_trans (hgv k) ?_
      rw [if_pos h]
    -- an odd index: the chord between its even neighbours is `0`
    have hodd : Odd k := Nat.not_even_iff_odd.1 h
    have hk1 : 1 ≤ k := hodd.pos
    have hprev : Even (k - 1) := Nat.Odd.sub_odd hodd odd_one
    have hnext : Even (k + 1) := hodd.add_one
    have hvprev : (if Even (k - 1) then (0 : WithTop ℝ) else 1) = 0 := if_pos hprev
    have hvnext : (if Even (k + 1) then (0 : WithTop ℝ) else 1) = 0 := if_pos hnext
    have hslope :
        slopeTo (fun k : ℕ ↦ if Even k then (0 : WithTop ℝ) else 1) (k - 1) (k + 1) = 0 := by
      rw [slopeTo, hvprev, hvnext]
      simp only [WithTop.untop₀_zero, sub_self, Nat.cast_add, Nat.cast_one, zero_div]
    have hb := le_add_nsmul_slopeTo_of_isConvexMinorant ⟨hg, hgv⟩
      (by rw [hvprev]; exact WithTop.zero_ne_top) (by rw [hvnext]; exact WithTop.zero_ne_top)
      (by omega : k - 1 ≤ k) (by omega : k ≤ k + 1)
    rw [hvprev, hslope, WithTop.coe_zero, nsmul_zero, add_zero] at hb
    exact hb

/-- The points `(0, 0), (1, 1), (2, 2), (3, 4)`: the point at `1` lies on the polygon but is not a
vertex, while `2` is. -/
noncomputable def collinearExample : ℕ → WithTop ℝ :=
  fun k ↦ if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 2 else if k = 3 then 4 else ⊤

/-- The collinear example carries points exactly at `0, 1, 2, 3`. -/
theorem finiteSet_collinearExample : finiteSet collinearExample = Set.Iic 3 := by
  ext j
  rw [mem_finiteSet, Set.mem_Iic, collinearExample]
  split_ifs with h0 h1 h2 h3
  · exact iff_of_true WithTop.coe_ne_top (by omega)
  · exact iff_of_true WithTop.coe_ne_top (by omega)
  · exact iff_of_true WithTop.coe_ne_top (by omega)
  · exact iff_of_true WithTop.coe_ne_top (by omega)
  · exact iff_of_false (fun hx ↦ hx rfl) (by omega)

/-- The collinear example is anchored at `0`. -/
theorem anchor_collinearExample : anchor collinearExample = 0 := by
  rw [anchor, finiteSet_collinearExample]
  exact Nat.sInf_eq_zero.2 (Or.inl (Set.mem_Iic.2 (by omega)))

/-- The first unit slope of the collinear example is `1`. -/
theorem unitSlope_collinearExample_zero : unitSlope collinearExample 0 = ((1 : ℝ) : WithTop ℝ) := by
  refine unitSlope_eq_of_succ_eq_add (by rw [collinearExample]; norm_num) ?_
  rw [Order.succ_eq_add_one, collinearExample, collinearExample]
  norm_num

/-- The second unit slope of the collinear example is again `1`: the point at `1` is collinear
with its neighbours. -/
theorem unitSlope_collinearExample_one : unitSlope collinearExample 1 = ((1 : ℝ) : WithTop ℝ) := by
  refine unitSlope_eq_of_succ_eq_add (by rw [collinearExample]; norm_num) ?_
  rw [Order.succ_eq_add_one, collinearExample, collinearExample]
  norm_num

/-- The third unit slope of the collinear example is `2`: the polygon breaks at `2`. -/
theorem unitSlope_collinearExample_two : unitSlope collinearExample 2 = ((2 : ℝ) : WithTop ℝ) := by
  refine unitSlope_eq_of_succ_eq_add (by rw [collinearExample]; norm_num) ?_
  rw [Order.succ_eq_add_one, collinearExample, collinearExample]
  norm_num

/-- Past the last point the unit slope of the collinear example is `⊤`. -/
theorem unitSlope_collinearExample_three : unitSlope collinearExample 3 = ⊤ := by
  refine unitSlope_eq_top_iff.2 (Or.inr ?_)
  rw [Order.succ_eq_add_one, collinearExample]
  norm_num

/-- The collinear example is convex, so it is its own polygon. -/
theorem isConvexSeq_collinearExample : IsConvexSeq collinearExample := by
  refine ⟨by rw [finiteSet_collinearExample]; exact Set.ordConnected_Iic, fun a ha b hb hab ↦ ?_⟩
  rw [finiteSet_collinearExample, Set.mem_Iic] at ha hb
  interval_cases a <;> interval_cases b <;>
    simp only [unitSlope_collinearExample_zero, unitSlope_collinearExample_one,
      unitSlope_collinearExample_two, unitSlope_collinearExample_three] <;>
    first | exact le_rfl | exact le_top | exact WithTop.coe_le_coe.2 (by norm_num)

/-- A finitely supported convex sequence is its own polygon. -/
theorem newtonPolygon_collinearExample : newtonPolygon collinearExample = collinearExample :=
  newtonPolygon_eq_self isConvexSeq_collinearExample

/-- The collinear point lies **on** the polygon. -/
theorem newtonPolygon_collinearExample_one :
    newtonPolygon collinearExample 1 = collinearExample 1 := by
  rw [newtonPolygon_collinearExample]

/-- But it is not a vertex: the unit slope does not increase there. -/
theorem not_isVertex_collinearExample_one : ¬ IsVertex (newtonPolygon collinearExample) 1 := by
  rw [newtonPolygon_collinearExample]
  rintro ⟨-, h | h⟩
  · rw [anchor_collinearExample] at h
    exact absurd h one_ne_zero
  · rw [show (1 : ℕ) - 1 = 0 from rfl, unitSlope_collinearExample_zero,
      unitSlope_collinearExample_one] at h
    exact absurd h (lt_irrefl _)

/-- The next point is a vertex: there the unit slope increases from `1` to `2`. -/
theorem isVertex_collinearExample_two : IsVertex (newtonPolygon collinearExample) 2 := by
  rw [newtonPolygon_collinearExample]
  refine ⟨by rw [collinearExample]; norm_num, Or.inr ?_⟩
  rw [show (2 : ℕ) - 1 = 1 from rfl, unitSlope_collinearExample_one,
    unitSlope_collinearExample_two, WithTop.coe_lt_coe]
  norm_num

/-- The ray of slope `√2` is convex. -/
theorem isConvexSeq_mul_sqrt_two :
    IsConvexSeq (fun k : ℕ ↦ (((k : ℝ) * Real.sqrt 2 : ℝ) : WithTop ℝ)) := by
  have heq : (fun k : ℕ ↦ (((k : ℝ) * Real.sqrt 2 : ℝ) : WithTop ℝ))
      = fun k : ℕ ↦ ((0 + Real.sqrt 2 * k : ℝ) : WithTop ℝ) := by
    funext k
    rw [WithTop.coe_inj]
    ring
  rw [heq]
  exact isConvexSeq_affine 0 (Real.sqrt 2)

/-- The chords of `⌈k√2⌉` out of `0` approach the slope `√2` from above, so every convex minorant
lies on or below the ray of slope `√2` — although no point of the sequence does. -/
theorem le_mul_sqrt_two_of_isConvexMinorant {g : ℕ → WithTop ℝ}
    (hg : IsConvexMinorant (fun k : ℕ ↦ ((⌈(k : ℝ) * Real.sqrt 2⌉ : ℝ) : WithTop ℝ)) g) (k : ℕ) :
    g k ≤ (((k : ℝ) * Real.sqrt 2 : ℝ) : WithTop ℝ) := by
  have hv0 : ((⌈((0 : ℕ) : ℝ) * Real.sqrt 2⌉ : ℝ) : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) := by
    norm_num
  have hgk : g k ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hg.2 k)
  obtain ⟨r, hR⟩ := WithTop.ne_top_iff_exists.1 hgk
  rw [← hR, WithTop.coe_le_coe]
  by_contra hx
  rw [not_le] at hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ((r : ℝ) : WithTop ℝ) ≤ ((⌈((0 : ℕ) : ℝ) * Real.sqrt 2⌉ : ℝ) : WithTop ℝ) := by
      rw [hR]
      exact hg.2 0
    rw [hv0, WithTop.coe_le_coe] at h0
    norm_num at hx
    linarith
  -- a far point whose chord slope out of `0` is within `r - k√2` of `√2`
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hδ : 0 < r - (k : ℝ) * Real.sqrt 2 := by linarith
  obtain ⟨t', ht'⟩ := exists_nat_gt ((k : ℝ) / (r - (k : ℝ) * Real.sqrt 2))
  have hkt : k ≤ max k t' := le_max_left _ _
  have htpos : (0 : ℝ) < ((max k t' : ℕ) : ℝ) := by
    refine lt_of_lt_of_le hkpos ?_
    exact_mod_cast hkt
  have hslope : slopeTo (fun k : ℕ ↦ ((⌈(k : ℝ) * Real.sqrt 2⌉ : ℝ) : WithTop ℝ)) 0 (max k t')
      = (⌈((max k t' : ℕ) : ℝ) * Real.sqrt 2⌉ : ℝ) / ((max k t' : ℕ) : ℝ) := by
    rw [slopeTo]
    norm_num
  have hb := le_add_nsmul_slopeTo_of_isConvexMinorant hg (L := 0) (t := max k t')
    (by rw [hv0]; exact WithTop.coe_ne_top) WithTop.coe_ne_top (Nat.zero_le k) hkt
  rw [← hR, hv0, hslope, Nat.sub_zero, ← WithTop.coe_nsmul, ← WithTop.coe_add,
    WithTop.coe_le_coe, nsmul_eq_mul, zero_add] at hb
  -- the chord slope is `< √2 + 1/t`, so `r < k√2 + k/t ≤ r`
  have hceil : (⌈((max k t' : ℕ) : ℝ) * Real.sqrt 2⌉ : ℝ)
      < ((max k t' : ℕ) : ℝ) * Real.sqrt 2 + 1 := Int.ceil_lt_add_one _
  have hdiv : (⌈((max k t' : ℕ) : ℝ) * Real.sqrt 2⌉ : ℝ) / ((max k t' : ℕ) : ℝ)
      < Real.sqrt 2 + 1 / ((max k t' : ℕ) : ℝ) := by
    rw [div_lt_iff₀ htpos]
    field_simp
    linarith
  have hkdiv : (k : ℝ) / ((max k t' : ℕ) : ℝ) < r - (k : ℝ) * Real.sqrt 2 := by
    rw [div_lt_iff₀ htpos, ← div_lt_iff₀' hδ]
    refine lt_of_lt_of_le ht' ?_
    exact_mod_cast le_max_right k t'
  have hfinal : r < (k : ℝ) * Real.sqrt 2 + (k : ℝ) / ((max k t' : ℕ) : ℝ) := by
    refine lt_of_le_of_lt hb ?_
    have := mul_lt_mul_of_pos_left hdiv hkpos
    rw [mul_add, mul_one_div] at this
    linarith
  linarith

/-- The polygon of `⌈k√2⌉` is the ray of slope `√2`: integral points, irrational heights (roadmap
convention 4). -/
theorem newtonPolygon_ceil_sqrt_two :
    newtonPolygon (fun k : ℕ ↦ ((⌈(k : ℝ) * Real.sqrt 2⌉ : ℝ) : WithTop ℝ))
      = fun k : ℕ ↦ (((k : ℝ) * Real.sqrt 2 : ℝ) : WithTop ℝ) :=
  (IsNewtonPolygonOf.eq_newtonPolygon ⟨isConvexSeq_mul_sqrt_two,
    fun _ ↦ WithTop.coe_le_coe.2 (Int.le_ceil _),
    fun _ hg hgv k ↦ le_mul_sqrt_two_of_isConvexMinorant ⟨hg, hgv⟩ k⟩).symm

end NewtonPolygon
