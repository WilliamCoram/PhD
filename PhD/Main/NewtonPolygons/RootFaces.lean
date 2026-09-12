/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.NewtonPolygons.PolynomialRoots
import PhD.Main.NewtonPolygons.Product
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The faces of a polynomial's Newton polygon count its roots

Blueprint §5.11 (`card_roots_slope`) counts the roots on one *sphere*, segment by segment.  This
file assembles those counts into the two face endpoints of `PhD/Main/NewtonPolygons/Face.lean`, which
are what the Atkin–Lehner reflection of [LWX, §3.23 Step III] consumes:

* `faceRight_eq_card_roots_le` — `faceRight σ` is the number of roots in the **closed** ball of
  radius `exp σ`;
* `faceLeft_eq_card_roots_lt` — `faceLeft σ` is the number of roots in the **open** ball of
  radius `exp σ`.

Both are read off the single equivalence `unitSlope_le_iff` / `unitSlope_lt_iff`: the `j`-th unit
slope is `≤ σ` exactly when the closed ball of radius `exp σ` contains more than `j` roots.  The
proof is the segment dichotomy of `NewtonPolygon₀.unitSlope_cases`: on a segment the unit slope
is the segment's slope and the two counts are the segment's endpoints
(`card_roots_le_slope`, `card_roots_lt_slope`); past the support the unit slope is `⊤` and the
index is past the degree.

Roots are measured in `AlgebraicClosure K` with a chosen valuation `w` extending the norm,
exactly as in `PhD/Main/NewtonPolygons/PolynomialRoots.lean`; `card_roots_le_of_isAlgClosed` transports
the counts back to `K` when `K` is already algebraically closed.
-/

open Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

namespace NewtonPolygon₀

variable (P : NewtonPolygon₀ (Γ := ℝ))

/-- **A segment carrying a finite unit slope is bounded on the right**, when the polygon has
unbounded slopes: otherwise every later unit interval would sit on that same segment and carry
the same finite slope. -/
theorem vertexX_succ_ne_top_of_unitSlope_eq (hunb : P.SlopesUnbounded) {k j : ℕ} {m : ℝ}
    (h1 : P.vertexX k ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ))
    (h2 : ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (k + 1))
    (hm : P.unitSlope j = (m : WithBotTop ℝ)) : P.vertexX (k + 1) ≠ ⊤ := by
  intro htop
  obtain ⟨j', hj'⟩ := hunb m
  have hmax : P.unitSlope (max j j') = P.slopes k :=
    P.unitSlope_eq_slopes
      (h1.trans (WithTop.coe_le_coe.2 (by have := le_max_left j j'; omega)))
      (by rw [htop]; exact lt_top_iff_ne_top.2 WithTop.coe_ne_top)
  rw [← P.unitSlope_eq_slopes h1 h2, hm] at hmax
  exact absurd ((hj'.trans_le (P.unitSlope_mono (le_max_right j j'))).trans_eq hmax) (lt_irrefl _)

/-- The segment lengths are finite where the vertices are. -/
theorem lengths_ne_top_of_vertexX_succ_ne_top {k : ℕ} (h : P.vertexX (k + 1) ≠ ⊤) :
    P.lengths k ≠ ⊤ := by
  intro htop
  rw [P.vertexX_succ, htop, WithTop.map_top, add_top] at h
  exact h rfl

end NewtonPolygon₀

section Roots

variable [CompleteSpace K]

/-- A `WithBotTop ℝ` value that is neither junk value is a real. -/
private theorem exists_coe_of_ne_bot_of_ne_top' {v : WithBotTop ℝ} (hb : v ≠ ⊥) (ht : v ≠ ⊤) :
    ∃ r : ℝ, v = (r : WithBotTop ℝ) := by
  induction v using WithBotTop.rec with
  | bot => exact absurd rfl hb
  | coe r => exact ⟨r, rfl⟩
  | top => exact absurd rfl ht

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The polygon of a series restricted at every radius lies below its coefficient valuations
(the `NewtonPolygons` form of `LWX.height_le_coeffVal`). -/
theorem height_le_coeffVal_of_isRestricted {g : PowerSeries K}
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hg0 : PowerSeries.coeff 0 g ≠ 0)
    (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm g).height n
      ≤ ((coeffVal g n : WithTop ℝ) : WithBotTop ℝ) := by
  have h := (isEntireNewtonPolygonOf_coeffVal hg hg0).toIsNewtonPolygonOf.height_le n
  rwa [pointHeight_eq_coe] at h

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Below the degree the unit slopes of a polynomial's polygon are finite. -/
theorem unitSlope_ne_top_of_lt_natDegree {f : Polynomial K} (hf0 : f.coeff 0 = 1) {i : ℕ}
    (hi : i < f.natDegree) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope i ≠ ⊤ := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) ≠ 0 := by
    rw [Polynomial.coeff_coe, hf0]; exact one_ne_zero
  have hres : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c (f : PowerSeries K) :=
    fun c _ => Polynomial.isRestricted_toPowerSeries _ _
  have hfne : f ≠ 0 := fun h0 => by rw [h0] at hf0; simp at hf0
  refine (newtonPolygon₀OfPowerSeries negLogNorm
    (f : PowerSeries K)).unitSlope_ne_top_of_height_natCast
    (isEntireNewtonPolygonOf_coeffVal hres hf0').starting_point_fst ?_ hi
  refine ne_top_of_le_ne_top ?_ (height_le_coeffVal_of_isRestricted hres hf0' f.natDegree)
  have hcne : PowerSeries.coeff f.natDegree (f : PowerSeries K) ≠ 0 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.2 hfne
  rw [coeffVal_apply, negLogNorm_of_ne_zero hcne]
  simp

open Classical in
/-- **The `j`-th unit slope is at most `σ` exactly when the closed ball of radius `exp σ` holds
more than `j` roots.**  On a segment this is `card_roots_le_slope` (for `≤`) and
`card_roots_lt_slope` (for `>`); past the support the unit slope is `⊤` and `j` is past the
degree, which bounds every ball count. -/
theorem unitSlope_le_iff_lt_card_roots_le (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊) (σ : ℝ) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope j
        ≤ ((σ : ℝ) : WithBotTop ℝ)
      ↔ j < (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp σ)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) ≠ 0 := by
    rw [Polynomial.coeff_coe, hf0]; exact one_ne_zero
  have hres : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c (f : PowerSeries K) :=
    fun c _ => Polynomial.isRestricted_toPowerSeries _ _
  have hent := isEntireNewtonPolygonOf_coeffVal hres hf0'
  have hx := hent.starting_point_fst
  have hunb := slopesUnbounded_newtonPolygon₀OfPowerSeries hres hf0'
  have hdeg : (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp σ)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card ≤ f.natDegree :=
    (Multiset.card_le_card (Multiset.filter_le _ _)).trans
      ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)
  constructor
  · intro hle
    have hne : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope j ≠ ⊤ := by
      intro htop
      rw [htop] at hle
      exact (WithBotTop.coe_ne_top σ) (top_le_iff.1 hle)
    obtain ⟨k, h1, h2⟩ | htop | hbot :=
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope_cases j
    · obtain ⟨m, hm⟩ := exists_coe_of_ne_bot_of_ne_top' (hent.unitSlope_ne_bot j) hne
      rw [hm, WithBotTop.coe_le_coe] at hle
      have hslope : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes k
          = (m : WithBotTop ℝ) :=
        ((newtonPolygon₀OfPowerSeries negLogNorm
          (f : PowerSeries K)).unitSlope_eq_slopes h1 h2).symm.trans hm
      have hvne := NewtonPolygon₀.vertexX_succ_ne_top_of_unitSlope_eq _ hunb h1 h2 hm
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hvne
      rw [hx, ← hz] at h2
      have hjz : (0 : ℤ) + j < z := WithTop.coe_lt_coe.1 h2
      have hcard := card_roots_le_slope f hf0 w hw hslope
        (show (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX (k + 1)
            = ((z.toNat : ℤ) : WithTop ℤ) by
          rw [← hz, Int.toNat_of_nonneg (by omega)])
      have hsub : (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp m)
            ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card
          ≤ (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp σ)
            ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card :=
        Multiset.card_le_card (Multiset.monotone_filter_right _ fun x hx' =>
          hx'.trans (Real.exp_le_exp.2 hle))
      omega
    · exact absurd htop hne
    · exact absurd hbot (hent.unitSlope_ne_bot j)
  · intro hj
    by_contra hgt
    rw [not_le] at hgt
    by_cases hne : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope j = ⊤
    · exact unitSlope_ne_top_of_lt_natDegree hf0 (show j < f.natDegree by omega) hne
    obtain ⟨k, h1, h2⟩ | htop | hbot :=
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope_cases j
    · obtain ⟨m, hm⟩ := exists_coe_of_ne_bot_of_ne_top' (hent.unitSlope_ne_bot j) hne
      rw [hm, WithBotTop.coe_lt_coe] at hgt
      have hslope : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes k
          = (m : WithBotTop ℝ) :=
        ((newtonPolygon₀OfPowerSeries negLogNorm
          (f : PowerSeries K)).unitSlope_eq_slopes h1 h2).symm.trans hm
      have hvne := NewtonPolygon₀.vertexX_succ_ne_top_of_unitSlope_eq _ hunb h1 h2 hm
      obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.1
        (NewtonPolygon₀.lengths_ne_top_of_vertexX_succ_ne_top _ hvne)
      obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1
        (ne_top_of_le_ne_top WithTop.coe_ne_top h1)
      have hy0 : (0 : ℤ) ≤ y := by
        have hmono := (newtonPolygon₀OfPowerSeries negLogNorm
          (f : PowerSeries K)).vertexX_mono (Nat.zero_le k)
        rw [(newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX_zero, hx,
          ← hy] at hmono
        exact_mod_cast hmono
      have hyj : y ≤ (0 : ℤ) + j := by rw [hx, ← hy] at h1; exact WithTop.coe_le_coe.1 h1
      have hsucc := (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX_succ k
      rw [← hy, ← hl, WithTop.map_coe, ← WithTop.coe_add] at hsucc
      have hcard := card_roots_lt_slope f hf0 w hw hslope hl.symm
        (show (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX (k + 1)
            = (((y + l).toNat : ℤ) : WithTop ℤ) by
          rw [hsucc, Int.toNat_of_nonneg (by omega)])
      have hsub : (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp σ)
            ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card
          ≤ (Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
            ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card :=
        Multiset.card_le_card (Multiset.monotone_filter_right _ fun x hx' =>
          hx'.trans_lt (Real.exp_lt_exp.2 hgt))
      have hz : ((y + l).toNat : ℤ) = y + l := Int.toNat_of_nonneg (by omega)
      omega
    · exact absurd htop hne
    · exact absurd hbot (hent.unitSlope_ne_bot j)

open Classical in
/-- **The `j`-th unit slope is below `σ` exactly when the open ball of radius `exp σ` holds more
than `j` roots** — the strict companion of `unitSlope_le_iff_lt_card_roots_le`. -/
theorem unitSlope_lt_iff_lt_card_roots_lt (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊) (σ : ℝ) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope j
        < ((σ : ℝ) : WithBotTop ℝ)
      ↔ j < (Multiset.filter (fun x => (w x : ℝ) < Real.exp σ)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card := by
  have hf0' : PowerSeries.coeff 0 (f : PowerSeries K) ≠ 0 := by
    rw [Polynomial.coeff_coe, hf0]; exact one_ne_zero
  have hres : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c (f : PowerSeries K) :=
    fun c _ => Polynomial.isRestricted_toPowerSeries _ _
  have hent := isEntireNewtonPolygonOf_coeffVal hres hf0'
  have hx := hent.starting_point_fst
  have hunb := slopesUnbounded_newtonPolygon₀OfPowerSeries hres hf0'
  have hdeg : (Multiset.filter (fun x => (w x : ℝ) < Real.exp σ)
      ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card ≤ f.natDegree :=
    (Multiset.card_le_card (Multiset.filter_le _ _)).trans
      ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)
  constructor
  · intro hlt
    have hne : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope j ≠ ⊤ :=
      ne_top_of_lt hlt
    obtain ⟨k, h1, h2⟩ | htop | hbot :=
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope_cases j
    · obtain ⟨m, hm⟩ := exists_coe_of_ne_bot_of_ne_top' (hent.unitSlope_ne_bot j) hne
      rw [hm, WithBotTop.coe_lt_coe] at hlt
      have hslope : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes k
          = (m : WithBotTop ℝ) :=
        ((newtonPolygon₀OfPowerSeries negLogNorm
          (f : PowerSeries K)).unitSlope_eq_slopes h1 h2).symm.trans hm
      have hvne := NewtonPolygon₀.vertexX_succ_ne_top_of_unitSlope_eq _ hunb h1 h2 hm
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hvne
      rw [hx, ← hz] at h2
      have hjz : (0 : ℤ) + j < z := WithTop.coe_lt_coe.1 h2
      have hcard := card_roots_le_slope f hf0 w hw hslope
        (show (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX (k + 1)
            = ((z.toNat : ℤ) : WithTop ℤ) by
          rw [← hz, Int.toNat_of_nonneg (by omega)])
      have hsub : (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp m)
            ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card
          ≤ (Multiset.filter (fun x => (w x : ℝ) < Real.exp σ)
            ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card :=
        Multiset.card_le_card (Multiset.monotone_filter_right _ fun x hx' =>
          hx'.trans_lt (Real.exp_lt_exp.2 hlt))
      omega
    · exact absurd htop hne
    · exact absurd hbot (hent.unitSlope_ne_bot j)
  · intro hj
    by_contra hge
    rw [not_lt] at hge
    by_cases hne : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope j = ⊤
    · exact unitSlope_ne_top_of_lt_natDegree hf0 (show j < f.natDegree by omega) hne
    obtain ⟨k, h1, h2⟩ | htop | hbot :=
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope_cases j
    · obtain ⟨m, hm⟩ := exists_coe_of_ne_bot_of_ne_top' (hent.unitSlope_ne_bot j) hne
      rw [hm, WithBotTop.coe_le_coe] at hge
      have hslope : (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).slopes k
          = (m : WithBotTop ℝ) :=
        ((newtonPolygon₀OfPowerSeries negLogNorm
          (f : PowerSeries K)).unitSlope_eq_slopes h1 h2).symm.trans hm
      have hvne := NewtonPolygon₀.vertexX_succ_ne_top_of_unitSlope_eq _ hunb h1 h2 hm
      obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.1
        (NewtonPolygon₀.lengths_ne_top_of_vertexX_succ_ne_top _ hvne)
      obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1
        (ne_top_of_le_ne_top WithTop.coe_ne_top h1)
      have hy0 : (0 : ℤ) ≤ y := by
        have hmono := (newtonPolygon₀OfPowerSeries negLogNorm
          (f : PowerSeries K)).vertexX_mono (Nat.zero_le k)
        rw [(newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX_zero, hx,
          ← hy] at hmono
        exact_mod_cast hmono
      have hyj : y ≤ (0 : ℤ) + j := by rw [hx, ← hy] at h1; exact WithTop.coe_le_coe.1 h1
      have hsucc := (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX_succ k
      rw [← hy, ← hl, WithTop.map_coe, ← WithTop.coe_add] at hsucc
      have hcard := card_roots_lt_slope f hf0 w hw hslope hl.symm
        (show (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).vertexX (k + 1)
            = (((y + l).toNat : ℤ) : WithTop ℤ) by
          rw [hsucc, Int.toNat_of_nonneg (by omega)])
      have hsub : (Multiset.filter (fun x => (w x : ℝ) < Real.exp σ)
            ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card
          ≤ (Multiset.filter (fun x => (w x : ℝ) < Real.exp m)
            ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card :=
        Multiset.card_le_card (Multiset.monotone_filter_right _ fun x hx' =>
          hx'.trans_le (Real.exp_le_exp.2 hge))
      have hz : ((y + l).toNat : ℤ) = y + l := Int.toNat_of_nonneg (by omega)
      omega
    · exact absurd htop hne
    · exact absurd hbot (hent.unitSlope_ne_bot j)

open Classical in
/-- **`faceRight σ` counts the roots in the closed ball of radius `exp σ`.** -/
theorem faceRight_eq_card_roots_le (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊) (σ : ℝ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).faceRight σ
      = (Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp σ)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card := by
  have hmem : ((σ : ℝ) : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope
        ((Multiset.filter (fun x => (w x : ℝ) ≤ Real.exp σ)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card) := by
    rw [← not_le, unitSlope_le_iff_lt_card_roots_le f hf0 w hw]
    exact lt_irrefl _
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have hin := Nat.sInf_mem (⟨_, hmem⟩ :
    {j : ℕ | ((σ : ℝ) : WithBotTop ℝ) <
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope j}.Nonempty)
  rw [Set.mem_ofPred_eq, ← not_le, unitSlope_le_iff_lt_card_roots_le f hf0 w hw] at hin
  exact not_lt.1 hin

open Classical in
/-- **`faceLeft σ` counts the roots in the open ball of radius `exp σ`.** -/
theorem faceLeft_eq_card_roots_lt (f : Polynomial K) (hf0 : f.coeff 0 = 1)
    (w : Valuation (AlgebraicClosure K) NNReal)
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊) (σ : ℝ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).faceLeft σ
      = (Multiset.filter (fun x => (w x : ℝ) < Real.exp σ)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card := by
  have hmem : ((σ : ℝ) : WithBotTop ℝ) ≤
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope
        ((Multiset.filter (fun x => (w x : ℝ) < Real.exp σ)
          ((f.map (algebraMap K (AlgebraicClosure K))).roots)).card) := by
    rw [← not_lt, unitSlope_lt_iff_lt_card_roots_lt f hf0 w hw]
    exact lt_irrefl _
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have hin := Nat.sInf_mem (⟨_, hmem⟩ :
    {j : ℕ | ((σ : ℝ) : WithBotTop ℝ) ≤
      (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).unitSlope j}.Nonempty)
  rw [Set.mem_ofPred_eq, ← not_lt, unitSlope_lt_iff_lt_card_roots_lt f hf0 w hw] at hin
  exact not_lt.1 hin

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- With `Γ = ℝ` the point height is the coefficient valuation itself. -/
theorem pointHeight_eq_coe_iff {v : ℕ → WithTop ℝ} {k : ℕ} {a : ℝ} :
    pointHeight v k = ((a : ℝ) : WithBotTop ℝ) ↔ v k = ((a : ℝ) : WithTop ℝ) := by
  cases hv : v k with
  | top =>
    simp only [pointHeight, hv]
    exact ⟨fun h => absurd h.symm (WithBotTop.coe_ne_top a),
      fun h => absurd h.symm (WithTop.coe_ne_top)⟩
  | coe r =>
    rw [pointHeight_coe hv, Algebra.algebraMap_self_apply]
    exact ⟨fun h => by rw [WithBotTop.coe_injective h], fun h => by rw [WithTop.coe_inj.1 h]⟩

/-! ### The face of slope `σ` through the origin

When every unit slope is at least `σ` the polygon starts on the supporting line of slope `σ`
through the origin, so the face of slope `σ` is `[0, faceRight σ]` and its right endpoint is the
**last** index at which the coefficient valuation still sits on that line.  This is the form in
which two Fredholm determinants differing by a rescaling are compared. -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- On the face of slope `σ` through the origin the polygon is that line. -/
theorem height_faceRight_of_forall_le {f : PowerSeries K}
    (hres : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f = 1)
    {σ : ℝ}
    (hlow : ∀ j, (σ : WithBotTop ℝ) ≤ (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j) :
    (newtonPolygon₀OfPowerSeries negLogNorm f).height
        (((newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ : ℕ) : ℤ)
      = ((σ * (((newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ : ℕ) : ℝ) : ℝ) :
          WithBotTop ℝ) := by
  have hf0' : PowerSeries.coeff 0 f ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hx := (isEntireNewtonPolygonOf_coeffVal hres hf0').starting_point_fst
  rw [(newtonPolygon₀OfPowerSeries negLogNorm f).height_eq_of_forall_unitSlope_eq hx
    (i₀ := 0) (σ := σ) (y := 0)
    (by rw [Nat.cast_zero, height_zero_newtonPolygon₀OfPowerSeries hf0]; rfl)
    (Nat.zero_le _) (fun t _ ht => le_antisymm
      ((newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope_le_of_lt_faceRight ht) (hlow t))]
  norm_num

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The right endpoint of that face is a point of the coefficient sequence on the line. -/
theorem pointHeight_faceRight_eq {f : PowerSeries K}
    (hres : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f = 1)
    {σ : ℝ}
    (hlow : ∀ j, (σ : WithBotTop ℝ) ≤ (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j) :
    pointHeight (coeffVal f) ((newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ)
      = ((σ * (((newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ : ℕ) : ℝ) : ℝ) :
          WithBotTop ℝ) := by
  have hf0' : PowerSeries.coeff 0 f ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hent := isEntireNewtonPolygonOf_coeffVal hres hf0'
  rw [← hent.toIsNewtonPolygonOf.height_faceRight_eq_pointHeight hent.starting_point_fst
      hent.unitSlope_ne_bot (slopesUnbounded_newtonPolygon₀OfPowerSeries hres hf0') σ]
  exact height_faceRight_of_forall_le hres hf0 hlow

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Past the right endpoint the sequence is strictly above the supporting line. -/
theorem lt_pointHeight_of_faceRight_lt {f : PowerSeries K}
    (hres : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f = 1)
    {σ : ℝ}
    (hlow : ∀ j, (σ : WithBotTop ℝ) ≤ (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j)
    {n : ℕ} (hn : (newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ < n) :
    ((σ * (n : ℝ) : ℝ) : WithBotTop ℝ) < pointHeight (coeffVal f) n := by
  have hf0' : PowerSeries.coeff 0 f ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hent := isEntireNewtonPolygonOf_coeffVal hres hf0'
  have hunb := slopesUnbounded_newtonPolygon₀OfPowerSeries hres hf0'
  have hlt := (newtonPolygon₀OfPowerSeries negLogNorm f).line_lt_height_of_lt_unitSlope
    hent.starting_point_fst hent.unitSlope_ne_bot
    (i₀ := (newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ) (σ := σ)
    (fun t ht => (newtonPolygon₀OfPowerSeries negLogNorm f).lt_unitSlope_of_faceRight_le hunb ht)
    (y := σ * (((newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ : ℕ) : ℝ))
    (height_faceRight_of_forall_le hres hf0 hlow) hn
  refine lt_of_lt_of_le ?_ (hent.toIsNewtonPolygonOf.height_le n)
  refine lt_of_le_of_lt (le_of_eq ?_) hlt
  congr 1
  ring


section AlgClosed

variable [IsAlgClosed K]

/-- The transported valuation used to read the root counts back over `K` itself. -/
private noncomputable def selfVal : Valuation (AlgebraicClosure K) NNReal :=
  (NormedField.valuation (K := K)).comap
    (RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm.toRingHom

omit [CompleteSpace K] in
private theorem selfVal_algebraMap (a : K) :
    selfVal (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊ := by
  show NormedField.valuation
    ((RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
      ((RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K))
        IsAlgClosed.algebraMap_bijective_of_isIntegral) a)) = ‖a‖₊
  rw [RingEquiv.symm_apply_apply, NormedField.valuation_apply]

open Classical in
/-- **`faceRight σ` over an algebraically closed `K`**: the number of roots of norm `≤ exp σ`. -/
theorem faceRight_eq_card_roots_le_self (f : Polynomial K) (hf0 : f.coeff 0 = 1) (σ : ℝ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).faceRight σ
      = (f.roots.filter fun z => ‖z‖ ≤ Real.exp σ).card := by
  rw [faceRight_eq_card_roots_le f hf0 selfVal selfVal_algebraMap,
    (IsAlgClosed.splits f).roots_map_of_injective
      (algebraMap K (AlgebraicClosure K)).injective,
    ← Multiset.countP_eq_card_filter, Multiset.countP_map, ← Multiset.countP_eq_card_filter,
    ← Multiset.countP_eq_card_filter]
  exact Multiset.countP_congr rfl fun z _ => by
    rw [selfVal_algebraMap, coe_nnnorm]

open Classical in
/-- **`faceLeft σ` over an algebraically closed `K`**: the number of roots of norm `< exp σ`. -/
theorem faceLeft_eq_card_roots_lt_self (f : Polynomial K) (hf0 : f.coeff 0 = 1) (σ : ℝ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f : PowerSeries K)).faceLeft σ
      = (f.roots.filter fun z => ‖z‖ < Real.exp σ).card := by
  rw [faceLeft_eq_card_roots_lt f hf0 selfVal selfVal_algebraMap,
    (IsAlgClosed.splits f).roots_map_of_injective
      (algebraMap K (AlgebraicClosure K)).injective,
    ← Multiset.countP_eq_card_filter, Multiset.countP_map, ← Multiset.countP_eq_card_filter,
    ← Multiset.countP_eq_card_filter]
  exact Multiset.countP_congr rfl fun z _ => by
    rw [selfVal_algebraMap, coe_nnnorm]

end AlgClosed

end Roots
