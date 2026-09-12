/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.TateFredholm.«09_Riesz»
import PhD.Main.NewtonPolygons.PowerSeriesZeros
import PhD.Main.NewtonPolygons.PolynomialRoots
import PhD.Main.NewtonPolygons.Product
import PhD.Main.NewtonPolygons.RootFaces
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The `TateFredholm` × `NewtonPolygons` seam: slopes are zeros

The composition point of the two pipelines of this development — `PhD.Main.TateFredholm.«09_Riesz»`
(zeros of the Fredholm determinant `det(1 − T·u)` of a compactoid operator are reciprocal
eigenvalues, [Serre1962, §7 Props. 11–12]) and `PhD.Main.NewtonPolygons` (every finite
Newton-polygon slope of an entire series is attained by a zero, via the Weierstrass
factorisation §5.13, the root count §5.11 and the zero identification §5.14).

## Main declarations

* `TateFredholm.exists_evalT_zero_of_slope` — over a complete algebraically closed ultrametric
  field, an entire power series with constant term `1` has, at every finite Newton-polygon
  slope `m` of a segment with finite right endpoint, a zero of norm `exp m` (in the
  `PowerSeries.evalT` sense).
* `TateFredholm.exists_evalT_zero_of_unitSlope` — the same reading off a **unit** slope, with
  no hypothesis on the segment: for an entire series the polygon has unbounded slopes
  (`slopesUnbounded_newtonPolygon₀OfPowerSeries`), so the segment carrying a finite unit slope
  is bounded on the right.

Both statements are **fully general** — arbitrary complete algebraically closed ultrametric
field `K`.  `IsAlgClosed` enters exactly once, through the §5.11 root count over
`AlgebraicClosure K` (transported back along the isomorphism `K ≃+* AlgebraicClosure K`).

These declarations were factored out of `PhD/Main/JacobsSlash/5_EigenSlopes.lean`, which had kept
them "until folder ownership with the eigenvalue board is settled"; `PhD/Main/LWX/15_StepThree.lean`
is the second consumer.  They cannot live in `PhD/Main/NewtonPolygons/` because `PowerSeries.evalT`
is `TateFredholm` API.
-/

namespace TateFredholm

open scoped TateFredholm

/-- A segment of the constructed Newton polygon with finite slope and finite right endpoint
has positive (finite) projected length: the step algorithm can only have produced a
`nextVertex` there, and its vertices strictly advance.  (The bridge lemmas of
`PhD.Main.NewtonPolygons.PolynomialRoots` are private, so the step inversion is re-derived.) -/
private lemma exists_pos_length_of_segment_data {K : Type*} [NontriviallyNormedField K]
    {f : PowerSeries K} {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (k + 1)
      = ((j₀ : ℤ) : WithTop ℤ)) :
    ∃ l : ℕ, 1 ≤ l ∧
      (newtonPolygon₀OfPowerSeries negLogNorm f).lengths k = (l : WithTop ℕ) := by
  have hlen : (newtonPolygon₀OfPowerSeries negLogNorm f).lengths k ≠ ⊤ := fun hltop => by
    rw [NewtonPolygon₀.vertexX_succ, hltop, WithTop.map_top, add_top] at hj
    exact WithTop.coe_ne_top hj.symm
  have hslopes : slopes' (newtonPolygon (coeffVal f) k) = (m : WithBotTop ℝ) := hm
  have hlengths : newtonPolygon_lengths (coeffVal f) k ≠ ⊤ := hlen
  cases hstep : newtonPolygon (coeffVal f) k with
  | none =>
      rw [hstep] at hslopes
      exact ((WithBotTop.coe_ne_top m) (show (m : WithBotTop ℝ) = ⊤ from hslopes.symm)).elim
  | some S =>
      rw [hstep] at hslopes
      cases S with
      | tail =>
          exact ((WithBotTop.coe_ne_top m)
            (show (m : WithBotTop ℝ) = ⊤ from hslopes.symm)).elim
      | unboundedBelow =>
          exact ((WithBotTop.coe_ne_bot m)
            (show (m : WithBotTop ℝ) = ⊥ from hslopes.symm)).elim
      | limitingRay m' => exact (hlengths (by simp only [newtonPolygon_lengths, hstep])).elim
      | infiniteRay m' => exact (hlengths (by simp only [newtonPolygon_lengths, hstep])).elim
      | nextVertex p₀ p₁ l m' =>
          obtain ⟨i₀, i₁, hst⟩ := nextStep_nextVertex _ hstep
          have h1 := nextVertex_l_eq _ hst
          have h2 := nextVertex_lt _ hst
          refine ⟨l, by omega, ?_⟩
          show newtonPolygon_lengths (coeffVal f) k = (l : WithTop ℕ)
          simp only [newtonPolygon_lengths, hstep]

/-- Over a complete algebraically closed ultrametric field, a polynomial normalised by
`g(0) = 1` whose polygon has finite slope `m` and positive length `l` at segment `k` has a
root of norm `exp m` in `K` itself: the §5.11 root count over `AlgebraicClosure K`
(`card_roots_slope`), pulled back along the isomorphism `K ≃+* AlgebraicClosure K`. -/
private lemma exists_aeval_zero_norm_eq_of_slope {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
    {g : Polynomial K} (hg0 : g.coeff 0 = 1) {k l : ℕ} {m : ℝ} (hl1 : 1 ≤ l)
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm (g : PowerSeries K)).slopes k
      = (m : WithBotTop ℝ))
    (hl : (newtonPolygon₀OfPowerSeries negLogNorm (g : PowerSeries K)).lengths k
      = (l : WithTop ℕ)) :
    ∃ x : K, Polynomial.aeval x g = 0 ∧ ‖x‖ = Real.exp m := by
  classical
  have hbij : Function.Bijective (algebraMap K (AlgebraicClosure K)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : K ≃+* AlgebraicClosure K := RingEquiv.ofBijective _ hbij
  let w : Valuation (AlgebraicClosure K) NNReal :=
    (NormedField.valuation (K := K)).comap e.symm.toRingHom
  have happ : ∀ y : AlgebraicClosure K, (w y : ℝ) = ‖e.symm y‖ := fun y => rfl
  have hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊ := fun a => by
    show NormedField.valuation (e.symm (e a)) = ‖a‖₊
    rw [RingEquiv.symm_apply_apply, NormedField.valuation_apply]
  have hcard := card_roots_slope g hg0 w hw hm hl
  obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp (hl1.trans_eq hcard.symm)
  obtain ⟨hyroot, hynorm⟩ := Multiset.mem_filter.mp hy
  refine ⟨e.symm y, ?_, by rw [← happ y]; exact hynorm⟩
  have h0 : (g.map (algebraMap K (AlgebraicClosure K))).eval y = 0 :=
    (Polynomial.mem_roots'.mp hyroot).2
  have hyx : algebraMap K (AlgebraicClosure K) (e.symm y) = y := e.apply_symm_apply y
  rw [← hyx, Polynomial.eval_map, Polynomial.eval₂_at_apply] at h0
  exact (congrFun (Polynomial.coe_aeval_eq_eval (e.symm y)) g).trans
    ((map_eq_zero_iff _ hbij.injective).mp h0)

/-- **Slopes are zeros** (Riesz–Newton bridge, blueprint §5.13 + §5.11 + §5.14): over a
complete algebraically closed ultrametric field, an entire series with constant term `1`
has, at every finite Newton-polygon slope `m`, a zero of norm `exp m` (in the `evalT` sense
of `TateFredholm`).  Public-API candidate for the `TateFredholm`/`NewtonPolygons` seam. -/
theorem exists_evalT_zero_of_slope {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
    (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1)
    (hent : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (k + 1)
        = ((j₀ : ℤ) : WithTop ℤ)) :
    ∃ x : K, PowerSeries.evalT x f = 0 ∧ ‖x‖ = Real.exp m := by
  have hconv : PowerSeries.IsRestricted (Real.exp m) f := hent _ (Real.exp_pos m)
  -- §5.13: Weierstrass factorisation along the polygon
  obtain ⟨g, h, hfeq, hdeg, hg0, -, hhconv, hh1, hpoly⟩ :=
    exists_weierstrass_factorisation f hf0 hm hj hconv
  -- the `k`-th segment has positive length, and `g` inherits the segment data of `f`
  obtain ⟨l, hl1, hlf⟩ := exists_pos_length_of_segment_data hm hj
  have hmg : (newtonPolygon₀OfPowerSeries negLogNorm (g : PowerSeries K)).slopes k
      = (m : WithBotTop ℝ) := (hpoly k le_rfl).1.trans hm
  have hlg : (newtonPolygon₀OfPowerSeries negLogNorm (g : PowerSeries K)).lengths k
      = (l : WithTop ℕ) := (hpoly k le_rfl).2.trans hlf
  -- §5.11: `g` has a root of norm `exp m`
  obtain ⟨x, hxroot, hxnorm⟩ := exists_aeval_zero_norm_eq_of_slope hg0 hl1 hmg hlg
  -- §5.14 at the trivial extension `L := K`: the root of `g` is a zero of `f`
  have hsum := (hasSum_zero_iff_aeval_eq_zero f hf0 hm hj hconv g h hfeq hdeg hhconv hh1
    (L := K) (fun a => by rw [Algebra.algebraMap_self, RingHom.id_apply]) hxnorm.le).mpr
    hxroot
  refine ⟨x, ?_, hxnorm⟩
  have hfun : (fun t => algebraMap K K (PowerSeries.coeff t f) * x ^ t)
      = fun t => PowerSeries.coeff t f * x ^ t := by
    funext t
    rw [Algebra.algebraMap_self, RingHom.id_apply]
  rw [hfun] at hsum
  exact hsum.tsum_eq

/-- **A finite unit slope of an entire series carries a zero of the matching norm.**  The
segment of the polygon containing the `j`-th unit interval has slope `m`; it is bounded on the
right because an entire series has unbounded slopes, so `exists_evalT_zero_of_slope` applies. -/
theorem exists_evalT_zero_of_unitSlope {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
    (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1)
    (hent : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) {j : ℕ} {m : ℝ}
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j = (m : WithBotTop ℝ)) :
    ∃ x : K, PowerSeries.evalT x f = 0 ∧ ‖x‖ = Real.exp m := by
  have hf0' : PowerSeries.coeff 0 f ≠ 0 := by rw [hf0]; exact one_ne_zero
  set P := newtonPolygon₀OfPowerSeries negLogNorm f with hP
  have hx : P.starting_point.1 = 0 :=
    (isEntireNewtonPolygonOf_coeffVal hent hf0').starting_point_fst
  have hunb : P.SlopesUnbounded := slopesUnbounded_newtonPolygon₀OfPowerSeries hent hf0'
  -- The `j`-th unit interval lies in an honest segment: the junk values are excluded by `hj`.
  obtain ⟨k, h1, h2⟩ | htop | hbot := P.unitSlope_cases j
  · have hslopes : P.slopes k = (m : WithBotTop ℝ) := (P.unitSlope_eq_slopes h1 h2).symm.trans hj
    -- That segment is bounded on the right: otherwise every later unit slope would equal `m`.
    have hne : P.vertexX (k + 1) ≠ ⊤ :=
      P.vertexX_succ_ne_top_of_unitSlope_eq hunb h1 h2 hj
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hne
    have hjz : (P.starting_point.1 + j : ℤ) < z := WithTop.coe_lt_coe.1 (hz ▸ h2)
    refine exists_evalT_zero_of_slope f hf0 hent (j₀ := z.toNat) hslopes ?_
    rw [← hz, Int.toNat_of_nonneg (by omega)]
  · exact absurd (htop.symm.trans hj) (WithBotTop.coe_ne_top m).symm
  · exact absurd (hbot.symm.trans hj) (WithBotTop.coe_ne_bot m).symm

end TateFredholm
