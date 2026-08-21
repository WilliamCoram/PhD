/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.«4_SlopeReading»
import PhD.JacobsSlash.«4_DiamondW»
import PhD.TateFredholm.Riesz
import PhD.NewtonPolygons.PowerSeriesZeros
import PhD.NewtonPolygons.PolynomialRoots
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Newton-polygon slopes are valuations of reciprocal eigenvalues

The composition point of the two pipelines of this development — `PhD.TateFredholm.Riesz`
(zeros of the Fredholm determinant `det(1 − T·u)` of a compactoid operator are reciprocal
eigenvalues, [Serre1962, §7 Props. 11–12]) and `PhD.NewtonPolygons` (every finite
Newton-polygon slope of an entire series is attained by a zero, via the Weierstrass
factorisation §5.13, the root count §5.11 and the zero identification §5.14):

* `JacobsSlash.exists_evalT_zero_of_slope` — over a complete algebraically closed ultrametric
  field, an entire power series with constant term `1` has, at every finite Newton-polygon
  slope `m`, a zero of norm `exp m` (in the `PowerSeries.evalT` sense of `TateFredholm`).
* `JacobsSlash.exists_eigenvector_of_slope_charPowerSeries` — every finite slope `m` of the
  Newton polygon of `det(1 − T·u)` of a compactoid operator is realised by an eigenvector
  `u x = a • x` with `‖a‖ = exp (−m)`: the zero of the determinant at `a⁻¹` is the
  reciprocal of the eigenvalue.

Both statements are **fully general** — arbitrary complete algebraically closed ultrametric
field `K`, arbitrary index type `I`, arbitrary compactoid operator — and Jacobs-free: they
are **public-API candidates for the `TateFredholm` × `NewtonPolygons` seam**, kept in this
folder only until folder ownership with the eigenvalue board is settled.  `IsAlgClosed`
enters exactly once, through the §5.11 root count over `AlgebraicClosure K` (transported
back along the isomorphism `K ≃+* AlgebraicClosure K`).

The second half instantiates the bridge at the thesis's middle block:

* the **strict-slope transport**: for partial sums of a *strictly* monotone slope
  sequence the step algorithm is completely forced — every step is a unit-advance
  `nextVertex` (`nextStep_eq_of_strict`), pinning the structure fields
  `slopes`/`lengths`/`vertexX` of the constructed polygon;
* `JacobsSlash.slopes_negLogNorm_charPowerSeries_M22op` /
  `vertexX_negLogNorm_charPowerSeries_M22op` — the `4_SlopeReading` slope data of
  `det(1 − T·M₂,₂)` rescaled from the `(ϖ₃ h3).val` normalisation to `negLogNorm`
  (factor `−log ‖3‖`);
* `JacobsSlash.exists_eigenvector_M22op` — eigenvectors of `M₂,₂` with
  `‖a‖² = ‖3‖^(2j+1)` (`3`-adic valuation `j + ½`) for every `j`;
* `JacobsSlash.exists_eigenvector_U3MatrixOp_of_M22` — the block transport along the
  diagonalising `B`: such eigenvectors embed as eigenvectors of the assembled
  `U₃`-matrix lying in the `ω`-eigenblock of the transcribed diamond operator.
-/

namespace JacobsSlash

open TateFredholm
open scoped TateFredholm

/-- A segment of the constructed Newton polygon with finite slope and finite right endpoint
has positive (finite) projected length: the step algorithm can only have produced a
`nextVertex` there, and its vertices strictly advance.  (The bridge lemmas of
`PhD.NewtonPolygons.PolynomialRoots` are private, so the step inversion is re-derived.) -/
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

/-- **Newton-polygon slopes are valuations of reciprocal eigenvalues** (the headline of the
bridge, fully general): over a complete algebraically closed ultrametric field, every finite
slope `m` of the Newton polygon of the Fredholm determinant `det(1 − T·u)` of a compactoid
operator is realised by an eigenvector `u x = a • x` with `‖a‖ = exp (−m)` — the zero of the
determinant at `a⁻¹` being the reciprocal of the eigenvalue [Serre1962, §7 Props 11–12 +
blueprint §5.11–5.14].  Public-API candidate for the `TateFredholm`/`NewtonPolygons` seam;
kept here for now, Jacobs-free by construction. -/
theorem exists_eigenvector_of_slope_charPowerSeries {K : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] {I : Type*} [DecidableEq I]
    (u : c(I, K) →L[K] c(I, K)) (hu : IsCompactoid u)
    {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm
        (charPowerSeries u)).slopes k = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm
        (charPowerSeries u)).vertexX (k + 1) = ((j₀ : ℤ) : WithTop ℤ)) :
    ∃ (a : K) (x : c(I, K)), a ≠ 0 ∧ x ≠ 0 ∧ u x = a • x ∧
      ‖a‖ = Real.exp (-m) := by
  obtain ⟨x₀, hx₀, hx₀norm⟩ := exists_evalT_zero_of_slope (charPowerSeries u) (by simp)
    (charPowerSeries_isEntire u hu) hm hj
  obtain ⟨hx₀ne, x, hxne, hx⟩ :=
    exists_eigenvector_of_evalT_charPowerSeries_eq_zero u hu hx₀
  refine ⟨x₀⁻¹, x, inv_ne_zero hx₀ne, hxne, hx, ?_⟩
  rw [norm_inv, hx₀norm, ← Real.exp_neg]

/-! ### The strict-slope transport

For a sequence of partial sums of a **strictly** monotone slope sequence, the step
algorithm is forced completely: every step is a `nextVertex` advancing by exactly one,
so the constructed polygon has unit lengths, `slopes k = s k`, and `vertexX k = k`.
(The height-level transport of `PhD.JacobsSlash.«4_SlopeReading»` pins `unitSlope`;
these are the structure fields the zero-existence theorems above consume.) -/

section StrictTransport

open Finset

variable {s : ℕ → ℝ} {y₀ : ℝ} {v : ℕ → WithTop ℝ}

private lemma finite_of_partial_sums
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) (m : ℕ) :
    finite v m := by
  rw [finite, hv m]
  exact WithTop.coe_ne_top

/-- The slope from the `k`-th partial-sum point to the `j`-th is the average of
`s` over `[k, j)`; for strictly monotone `s` it is minimised exactly at `j = k + 1`,
where it equals `s k`. -/
private lemma slopeSet_isLeast (hstrict : StrictMono s)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) (k : ℕ) :
    IsLeast (slopeSet v k (y₀ + ∑ i ∈ range k, s i)) (s k) := by
  constructor
  · refine ⟨k + 1, Nat.lt_succ_self k, finite_of_partial_sums hv (k + 1),
      y₀ + ∑ i ∈ range (k + 1), s i, hv (k + 1), ?_⟩
    rw [slopeReal, Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply,
      sum_range_succ]
    push_cast
    rw [show ((k : ℝ) + 1 - k) = 1 by ring]
    ring
  · rintro m ⟨j, hjk, -, j₁, hvj, rfl⟩
    have hj₁ : j₁ = y₀ + ∑ i ∈ range j, s i :=
      WithTop.coe_injective (hvj.symm.trans (hv j))
    rw [slopeReal, hj₁, Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]
    have hpos : (0 : ℝ) < (j : ℝ) - k := by
      have h := Nat.cast_lt (α := ℝ) |>.mpr hjk
      linarith
    rw [le_div_iff₀ hpos]
    have hsub : (y₀ + ∑ i ∈ range j, s i) - (y₀ + ∑ i ∈ range k, s i)
        = ∑ i ∈ Ico k j, s i := by
      rw [Finset.sum_Ico_eq_sub _ hjk.le]
      ring
    rw [hsub]
    have hbound : ∑ i ∈ Ico k j, s k ≤ ∑ i ∈ Ico k j, s i :=
      Finset.sum_le_sum fun i hi => hstrict.monotone (Finset.mem_Ico.mp hi).1
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hbound
    have hcast : ((j - k : ℕ) : ℝ) = (j : ℝ) - k := by
      push_cast [Nat.cast_sub hjk.le]
      ring
    calc s k * ((j : ℝ) - k) = ((j - k : ℕ) : ℝ) * s k := by rw [hcast]; ring
      _ ≤ ∑ i ∈ Ico k j, s i := hbound

/-- The minimal slope is achieved only at the immediate successor. -/
private lemma achievingSet_eq (hstrict : StrictMono s)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) (k : ℕ) :
    achievingSet v k (y₀ + ∑ i ∈ range k, s i) (s k) = {k + 1} := by
  ext j
  simp only [achievingSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hjk, -, j₁, hvj, heq⟩
    have hj₁ : j₁ = y₀ + ∑ i ∈ range j, s i :=
      WithTop.coe_injective (hvj.symm.trans (hv j))
    rw [slopeReal, hj₁, Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]
      at heq
    have hpos : (0 : ℝ) < (j : ℝ) - k := by
      linarith [Nat.cast_lt (α := ℝ) |>.mpr hjk]
    have hsub : (y₀ + ∑ i ∈ range j, s i) - (y₀ + ∑ i ∈ range k, s i)
        = ∑ i ∈ Ico k j, s i := by
      rw [Finset.sum_Ico_eq_sub _ hjk.le]; ring
    have hsum : ∑ i ∈ Ico k j, s i = s k * ((j : ℝ) - k) := by
      have := heq
      field_simp at this
      rw [hsub] at this
      linarith
    have hzero : ∑ i ∈ Ico k j, (s i - s k) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have hcast : ((j - k : ℕ) : ℝ) = (j : ℝ) - k := by
        push_cast [Nat.cast_sub hjk.le]; ring
      rw [hcast]
      ring
    by_contra hne
    have hj2 : k + 2 ≤ j := by omega
    have hmem : k + 1 ∈ Ico k j := Finset.mem_Ico.mpr ⟨Nat.le_succ k, by omega⟩
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i hi =>
      sub_nonneg.mpr (hstrict.monotone (Finset.mem_Ico.mp hi).1)).mp hzero
    have := sub_eq_zero.mp (hall (k + 1) hmem)
    exact absurd this (hstrict (Nat.lt_succ_self k)).ne'
  · rintro rfl
    refine ⟨Nat.lt_succ_self k, finite_of_partial_sums hv (k + 1),
      y₀ + ∑ i ∈ range (k + 1), s i, hv (k + 1), ?_⟩
    rw [slopeReal, Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply,
      sum_range_succ]
    push_cast
    rw [show ((k : ℝ) + 1 - k) = 1 by ring]
    ring

/-- **The forced step**: at a partial-sum anchor of a strictly monotone slope sequence,
the step algorithm advances by exactly one vertex, with slope `s k`. -/
private lemma nextStep_eq_of_strict (hstrict : StrictMono s)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) (k : ℕ) :
    nextStep v k (y₀ + ∑ i ∈ range k, s i)
      = Step.nextVertex (k + 1) (y₀ + ∑ i ∈ range (k + 1), s i) 1 (s k) := by
  classical
  have hleast := slopeSet_isLeast hstrict hv k
  have hne : slopeSet v k (y₀ + ∑ i ∈ range k, s i) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp ⟨s k, hleast.1⟩
  have hbdd : BddBelow (slopeSet v k (y₀ + ∑ i ∈ range k, s i)) := hleast.bddBelow
  have hsinf : sInf (slopeSet v k (y₀ + ∑ i ∈ range k, s i)) = s k := hleast.csInf_eq
  have hex : ∃ m ∈ slopeSet v k (y₀ + ∑ i ∈ range k, s i),
      m = sInf (slopeSet v k (y₀ + ∑ i ∈ range k, s i)) := ⟨s k, hleast.1, hsinf.symm⟩
  rw [nextStep, if_neg hne, if_neg (not_not_intro hbdd), dif_neg (not_not_intro hex)]
  have hch : (of_not_not (not_not_intro hex)).choose = s k := by
    obtain ⟨-, heq⟩ := (of_not_not (not_not_intro hex)).choose_spec
    rw [heq, hsinf]
  have hach : achievingSet v k (y₀ + ∑ i ∈ range k, s i)
      ((of_not_not (not_not_intro hex)).choose) = {k + 1} := by
    rw [hch]
    exact achievingSet_eq hstrict hv k
  have hnotinf : ¬ (achievingSet v k (y₀ + ∑ i ∈ range k, s i)
      ((of_not_not (not_not_intro hex)).choose)).Infinite := by
    rw [hach]
    exact Set.not_infinite.mpr (Set.finite_singleton _)
  rw [dif_neg hnotinf]
  have hmax : ∀ hne', ((Set.not_infinite.mp hnotinf).toFinset).max' hne' = k + 1 := by
    intro hne'
    have hmem := Finset.max'_mem ((Set.not_infinite.mp hnotinf).toFinset) hne'
    rw [Set.Finite.mem_toFinset] at hmem
    exact (Set.ext_iff.mp hach _).mp hmem
  dsimp only
  split
  · rename_i heq
    exfalso
    rw [hmax _, hv (k + 1)] at heq
    exact WithTop.coe_ne_top heq
  · rename_i j₁ heq
    rw [hmax _] at heq
    have hj₁ : j₁ = y₀ + ∑ i ∈ range (k + 1), s i := by
      rw [hv (k + 1)] at heq
      exact (WithTop.coe_injective heq).symm
    rw [hmax _, hj₁, hch]
    congr 1
    omega

/-- **The forced walk**: from strictly monotone partial-sum data, every step of the
constructed Newton polygon is the unit advance with slope `s k`. -/
private lemma newtonPolygon_eq_of_strict (hstrict : StrictMono s)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) :
    ∀ k : ℕ, newtonPolygon v k
      = some (Step.nextVertex (k + 1) (y₀ + ∑ i ∈ range (k + 1), s i) 1 (s k)) := by
  intro k
  induction k with
  | zero =>
    classical
    have hex : ∃ i ≥ 0, finite v i := ⟨0, le_refl 0, finite_of_partial_sums hv 0⟩
    cases hff : findFirstFinite v 0 with
    | none =>
      rw [findFirstFinite, dif_pos hex] at hff
      exact absurd hff (by simp)
    | some p =>
      obtain ⟨i, c⟩ := p
      have hffu : findFirstFinite v 0 = some (i, c) := hff
      rw [findFirstFinite, dif_pos hex] at hffu
      obtain ⟨hi, hc⟩ : Nat.find hex = i ∧
          (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose = c := by
        have := Option.some_injective _ hffu
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      have hi0 : i = 0 := by
        rw [← hi]
        exact Nat.find_eq_zero hex |>.mpr ⟨le_refl 0, finite_of_partial_sums hv 0⟩
      have hcv : (c : WithTop ℝ) = v i := by
        have hspec := (Option.ne_none_iff_exists.mp (Nat.find_spec hex).2).choose_spec
        rw [hc, hi] at hspec
        exact hspec
      have hc0 : c = y₀ + ∑ i ∈ range 0, s i := by
        rw [hi0, hv 0] at hcv
        exact WithTop.coe_injective hcv
      show newtonPolygon v 0 = _
      rw [show newtonPolygon v 0 = some (nextStep v i c) by
        simp only [newtonPolygon, hff], hi0, hc0]
      exact congrArg some (nextStep_eq_of_strict hstrict hv 0)
  | succ k ih =>
    show newtonPolygon v (k + 1) = _
    rw [show newtonPolygon v (k + 1)
        = some (nextStep v (k + 1) (y₀ + ∑ i ∈ range (k + 1), s i)) by
      simp only [newtonPolygon, ih]]
    exact congrArg some (nextStep_eq_of_strict hstrict hv (k + 1))

/-- Slopes of the constructed polygon at strict partial-sum data. -/
private lemma slopes_newtonPolygon₀OfSeq_of_strict (hstrict : StrictMono s)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) (k : ℕ) :
    (newtonPolygon₀OfSeq v).slopes k = ((s k : ℝ) : WithBotTop ℝ) := by
  show slopes' (newtonPolygon v k) = _
  rw [newtonPolygon_eq_of_strict hstrict hv k]
  rfl

/-- Vertex abscissae of the constructed polygon at strict partial-sum data. -/
private lemma vertexX_newtonPolygon₀OfSeq_of_strict (hstrict : StrictMono s)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) (k : ℕ) :
    (newtonPolygon₀OfSeq v).vertexX k = ((k : ℤ) : WithTop ℤ) := by
  induction k with
  | zero =>
    classical
    rw [NewtonPolygon₀.vertexX_zero]
    have hex : ∃ i ≥ 0, finite v i := ⟨0, le_refl 0, finite_of_partial_sums hv 0⟩
    cases hff : findFirstFinite v 0 with
    | none =>
      rw [findFirstFinite, dif_pos hex] at hff
      exact absurd hff (by simp)
    | some p =>
      obtain ⟨i, c⟩ := p
      have hffu : findFirstFinite v 0 = some (i, c) := hff
      rw [findFirstFinite, dif_pos hex] at hffu
      have hi : Nat.find hex = i := congrArg Prod.fst (Option.some_injective _ hffu)
      have hi0 : i = 0 := by
        rw [← hi]
        exact Nat.find_eq_zero hex |>.mpr ⟨le_refl 0, finite_of_partial_sums hv 0⟩
      have hsp : (newtonPolygon₀OfSeq v).starting_point = ((i : ℤ), c) := by
        simp only [newtonPolygon₀OfSeq, hff]
      rw [hsp, hi0]
  | succ k ih =>
    rw [NewtonPolygon₀.vertexX_succ, ih,
      show (newtonPolygon₀OfSeq v).lengths k = (1 : WithTop ℕ) by
        show newtonPolygon_lengths v k = _
        simp only [newtonPolygon_lengths, newtonPolygon_eq_of_strict hstrict hv k]
        rfl]
    rw [show WithTop.map (fun l : ℕ => (l : ℤ)) (1 : WithTop ℕ)
        = (((1 : ℤ) : WithTop ℤ)) from rfl, ← WithTop.coe_add]
    norm_cast

end StrictTransport

/-! ### The `M₂,₂` factor at `negLogNorm`, and its eigenvectors

The `(ϖ₃ h3).val`-normalised slope data of `PhD.JacobsSlash.«4_SlopeReading»` is
rescaled to the `negLogNorm` normalisation of the zero-existence theorems (the two
differ by the positive factor `−log ‖3‖`, `PseudoUniformizer.val_def`), and fed
through the strict-slope transport. -/

section M22

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

variable {t ν : K} (ω : K)

private lemma strictMono_add_half_mul {L : ℝ} (hL : 0 < L) :
    StrictMono (fun n : ℕ => ((n : ℝ) + 1 / 2) * L) := fun a b hab => by
  have h : (a : ℝ) < b := Nat.cast_lt.mpr hab
  have := mul_lt_mul_of_pos_right (show (a : ℝ) + 1 / 2 < (b : ℝ) + 1 / 2 by linarith) hL
  simpa using this

omit [IsUltrametricDist K] [CompleteSpace K] in
private lemma negLogNorm_eq_mul_of_val_eq (h3 : ‖(3 : K)‖ < 1) {r : K} {c : ℝ}
    (h : (ϖ₃ h3).val r = ((c : ℝ) : WithTop ℝ)) :
    negLogNorm r = ((c * (-Real.log ‖(3 : K)‖) : ℝ) : WithTop ℝ) := by
  have hL : (0 : ℝ) < -Real.log ‖(3 : K)‖ := neg_pos.mpr (ϖ₃ h3).log_norm_neg
  rw [PseudoUniformizer.val_def, coe_ϖ₃] at h
  cases hn : negLogNorm r with
  | top => rw [hn] at h; exact absurd h (by simp)
  | coe b =>
    rw [hn, WithTop.map_coe] at h
    have hb : b * (-Real.log ‖(3 : K)‖)⁻¹ = c := WithTop.coe_injective h
    rw [WithTop.coe_inj, ← hb, mul_assoc, inv_mul_cancel₀ hL.ne', mul_one]

/-- The `negLogNorm` coefficient data of `det(1 − T·M₂,₂)`: the partial sums of the
strictly increasing slopes `(k + ½)·(−log ‖3‖)`. -/
private lemma sum_range_add_half (m : ℕ) :
    ∑ i ∈ Finset.range m, ((i : ℝ) + 1 / 2) = (m : ℝ) ^ 2 / 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma coeffSeq_negLogNorm_charPowerSeries_M22op
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (m : ℕ) :
    coeffSeq negLogNorm (charPowerSeries (M22op ω hω h3 ht hνc)) m
      = ((0 + ∑ i ∈ Finset.range m,
          (((i : ℝ) + 1 / 2) * (-Real.log ‖(3 : K)‖)) : ℝ) : WithTop ℝ) := by
  rw [coeffSeq_apply, charPowerSeries_coeff,
    negLogNorm_eq_mul_of_val_eq h3 (val_charCoeff_M22op ω h3 ht hν2 hνc hω m),
    WithTop.coe_inj, zero_add, ← Finset.sum_mul, sum_range_add_half]

/-- The `negLogNorm` Newton polygon of `det(1 − T·M₂,₂)` has segment slopes
`(k + ½)·(−log ‖3‖)` — the `4_SlopeReading` slope data in the normalisation of the
zero-existence theorems. -/
theorem slopes_negLogNorm_charPowerSeries_M22op
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (k : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (charPowerSeries (M22op ω hω h3 ht hνc))).slopes k
      = (((((k : ℝ) + 1 / 2) * (-Real.log ‖(3 : K)‖) : ℝ)) : WithBotTop ℝ) := by
  have hL : (0 : ℝ) < -Real.log ‖(3 : K)‖ := neg_pos.mpr (ϖ₃ h3).log_norm_neg
  exact slopes_newtonPolygon₀OfSeq_of_strict (strictMono_add_half_mul hL)
    (coeffSeq_negLogNorm_charPowerSeries_M22op ω hω h3 ht hν2 hνc) k

/-- The vertices of the `negLogNorm` polygon of `det(1 − T·M₂,₂)` sit at the integers:
every segment has unit length. -/
theorem vertexX_negLogNorm_charPowerSeries_M22op
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (k : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (charPowerSeries (M22op ω hω h3 ht hνc))).vertexX (k + 1)
      = (((k + 1 : ℕ) : ℤ) : WithTop ℤ) := by
  have hL : (0 : ℝ) < -Real.log ‖(3 : K)‖ := neg_pos.mpr (ϖ₃ h3).log_norm_neg
  exact vertexX_newtonPolygon₀OfSeq_of_strict (strictMono_add_half_mul hL)
    (coeffSeq_negLogNorm_charPowerSeries_M22op ω hω h3 ht hν2 hνc) (k + 1)

/-- **Eigenvectors of `M₂,₂` at every half-integral valuation** ([Jacobs, Cor 2.16] as
an eigenvalue statement): over a complete algebraically closed ultrametric field, for
every `j : ℕ` the middle block has an eigenvector with eigenvalue of `3`-adic
valuation `j + ½` — normalised without `rpow` as `‖a‖² = ‖3‖^(2j+1)`. -/
theorem exists_eigenvector_M22op [IsAlgClosed K]
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (j : ℕ) :
    ∃ (a : K) (x : c(ℕ, K)), a ≠ 0 ∧ x ≠ 0 ∧
      M22op ω hω h3 ht hνc x = a • x ∧
      ‖a‖ ^ 2 = ‖(3 : K)‖ ^ (2 * j + 1) := by
  obtain ⟨a, x, ha0, hx0, hax, hnorm⟩ := exists_eigenvector_of_slope_charPowerSeries
    (M22op ω hω h3 ht hνc) (isCompactoid_M22op ω hω h3 ht hνc)
    (slopes_negLogNorm_charPowerSeries_M22op ω hω h3 ht hν2 hνc j)
    (vertexX_negLogNorm_charPowerSeries_M22op ω hω h3 ht hν2 hνc j)
  refine ⟨a, x, ha0, hx0, hax, ?_⟩
  have h30 : (0 : ℝ) < ‖(3 : K)‖ := (ϖ₃ h3).norm_pos
  rw [hnorm, ← Real.exp_nat_mul,
    show ((2 : ℕ) : ℝ) * -(((j : ℝ) + 1 / 2) * -Real.log ‖(3 : K)‖)
      = ((2 * j + 1 : ℕ) : ℝ) * Real.log ‖(3 : K)‖ by push_cast; ring,
    Real.exp_nat_mul, Real.exp_log h30]

/-! ### Block transport along `B`

An eigenvector of the middle block embeds, via the diagonalising conjugation `B` of
`PhD.JacobsSlash.«4_DiamondW»`, as an eigenvector of the assembled `U₃`-matrix lying in
the `ω`-eigenblock of the transcribed diamond operator (`Binvop_comp_Wop_comp_Bop` —
block `1` carries the scalar `ω`; the thesis's "`ω²`-eigenspace" wording is the same
statement under the relabeling `ω ↦ ω²`). -/

private lemma U3diag_blockIncl_one (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1)
    (ht : ‖t‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (w : c(ℕ, K)) :
    blockOp
        ![![M11op h3 ht hνc, 0, 0],
          ![0, M22op ω hω h3 ht hνc, 0],
          ![0, 0, M33op ω hω h3 ht hνc]] (cSpace.blockIncl 1 w)
      = cSpace.blockIncl 1 (M22op ω hω h3 ht hνc w) := by
  rw [blockOp_blockIncl, Fin.sum_univ_three]
  simp

omit [CharZero K] in
private lemma Wdiag_blockIncl_one (w : c(ℕ, K)) :
    blockOp
        ![![1, 0, 0],
          ![0, ω • (1 : c(ℕ, K) →L[K] c(ℕ, K)), 0],
          ![0, 0, ω ^ 2 • (1 : c(ℕ, K) →L[K] c(ℕ, K))]] (cSpace.blockIncl 1 w)
      = cSpace.blockIncl 1 (ω • w) := by
  rw [blockOp_blockIncl, Fin.sum_univ_three]
  simp

/-- **Block transport along `B`**: an eigenvector of `M₂,₂` embeds as an eigenvector of
the assembled `U₃`-matrix with the same eigenvalue, lying in the `ω`-eigenblock of the
transcribed diamond operator `Wop`. -/
theorem exists_eigenvector_U3MatrixOp_of_M22 (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10)
    {a : K} {x : c(ℕ, K)} (hx0 : x ≠ 0)
    (hx : M22op ω hω h3 ht hνc x = a • x) :
    ∃ y : c(Fin 3 × ℕ, K), y ≠ 0 ∧
      U3MatrixOp h3 ht hνc y = a • y ∧
      Wop h3 ht y = ω • y := by
  have hBiB : ∀ z, Binvop ω h3 ht hω (Bop ω h3 ht hω z) = z := fun z => by
    have h := DFunLike.congr_fun (Binvop_comp_Bop ω h3 ht hω) z
    simpa using h
  have hBBi : ∀ z, Bop ω h3 ht hω (Binvop ω h3 ht hω z) = z := fun z => by
    have h := DFunLike.congr_fun (Bop_comp_Binvop ω h3 ht hω) z
    simpa using h
  refine ⟨Bop ω h3 ht hω (cSpace.blockIncl 1 x), ?_, ?_, ?_⟩
  · intro h0
    apply hx0
    have h1 : cSpace.blockIncl 1 x = (0 : c(Fin 3 × ℕ, K)) := by
      calc cSpace.blockIncl 1 x
          = Binvop ω h3 ht hω (Bop ω h3 ht hω (cSpace.blockIncl 1 x)) := (hBiB _).symm
        _ = Binvop ω h3 ht hω 0 := by rw [h0]
        _ = 0 := map_zero _
    calc x = cSpace.blockProj (1 : Fin 3) (cSpace.blockIncl (1 : Fin 3) x) := by
          rw [cSpace.blockProj_blockIncl]; simp
      _ = cSpace.blockProj (1 : Fin 3) (0 : c(Fin 3 × ℕ, K)) := by rw [h1]
      _ = 0 := map_zero _
  · have hkey := DFunLike.congr_fun (lemma210 ω h3 ht hνc hω) (cSpace.blockIncl 1 x)
    simp only [ContinuousLinearMap.comp_apply] at hkey
    rw [U3diag_blockIncl_one ω hω h3 ht hνc x, hx, map_smul] at hkey
    calc U3MatrixOp h3 ht hνc (Bop ω h3 ht hω (cSpace.blockIncl 1 x))
        = Bop ω h3 ht hω (Binvop ω h3 ht hω
            (U3MatrixOp h3 ht hνc (Bop ω h3 ht hω (cSpace.blockIncl 1 x)))) := (hBBi _).symm
      _ = Bop ω h3 ht hω (a • cSpace.blockIncl 1 x) := by rw [hkey]
      _ = a • Bop ω h3 ht hω (cSpace.blockIncl 1 x) := map_smul _ _ _
  · have hkey := DFunLike.congr_fun (Binvop_comp_Wop_comp_Bop ω h3 ht hω)
      (cSpace.blockIncl 1 x)
    simp only [ContinuousLinearMap.comp_apply] at hkey
    rw [Wdiag_blockIncl_one ω x, map_smul] at hkey
    calc Wop h3 ht (Bop ω h3 ht hω (cSpace.blockIncl 1 x))
        = Bop ω h3 ht hω (Binvop ω h3 ht hω
            (Wop h3 ht (Bop ω h3 ht hω (cSpace.blockIncl 1 x)))) := (hBBi _).symm
      _ = Bop ω h3 ht hω (ω • cSpace.blockIncl 1 x) := by rw [hkey]
      _ = ω • Bop ω h3 ht hω (cSpace.blockIncl 1 x) := map_smul _ _ _

end M22

end JacobsSlash
