/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Slopes

/-!
# The abstract slope theorem ([Jacobs, Theorem 2.12])

[Jacobs, *Slopes of Compact Hecke Operators*, Theorem 2.12]: if `M` is a compact
`ℕ × ℕ` matrix over `𝒪₃` such that `N_{j,i} := M_{j,i} / 3^j` still has entries in `𝒪₃`
and every top-left minor of `N` is a unit, then the slopes of `M` are `0, 1, 2, 3, …` —
equivalently, the characteristic power series `det (1 - T M) = ∑ c_m T^m` has
`v₃(c_m) = m(m-1)/2` exactly, so its Newton polygon is the parabola `½ x (x - 1)`.

We phrase everything in norms over an abstract complete ultrametric field `K` with
`‖3‖ < 1`, with `c_m = TateFredholm.charCoeff u m`, and `m(m-1)/2 = m.choose 2`.

## Slope reading (proved in `PhD.JacobsSlash.SlopeReading`)

The theorems below compute the exact valuations `v₃(c_m)` — i.e. the *points*
`(m, m(m−1)/2)` of the Newton polygon — and stop there: the polygon-level step, showing
that the polygon defined by this valuation sequence (its lower convex hull) has the
wanted slopes `0, 1, 2, …` (the points lie on a strictly convex parabola, hence are all
vertices, hence the successive slopes are the increments), is
`JacobsSlash.unitSlope_newtonPolygon₀OfPowerSeries_charPowerSeries` in
`PhD.JacobsSlash.SlopeReading`, which consumes the `val`-form theorem below.  That file also
proves the general spec-level theorem `isNewtonPolygonOf_ofSlopes` behind both readings.

The proof follows the thesis's:  `c_m = (-1)^m ∑_{|S| = m} det (M_S)`; the principal
block `S_m = {0, …, m-1}` contributes exactly `‖3‖ ^ (m.choose 2)` (unit-minor
hypothesis), and every other block strictly less (each Leibniz term of `det M_S` has
norm `≤ ∏_{j ∈ S} ‖3‖^j` and `∑_{j ∈ S} j > m(m-1)/2` for `S ≠ S_m`).

The two *inequality* halves of that argument are σ-general and weight-free, and live in
`PhD.TateFredholm.Slopes` (`norm_det_le_pow_of_row_bound`, `norm_minor_le_pow_sum`,
`choose_two_lt_sum_of_ne_range`); this file supplies only what is special to the unit-minor
hypothesis — the exact contribution of the principal block — and assembles the equality
(slopes-hecke board A2, 2026-08-20).
-/

open TateFredholm
open scoped TateFredholm

namespace JacobsSlash

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The normalisation.**  `3` as a pseudo-uniformizer of `K`: the choice that makes
`PseudoUniformizer.val` the thesis's `v₃`, normalised by `v₃(3) = 1`.

`3` need not be a *uniformizer* of `K`, and under `hω : ω ^ 2 + ω + 1 = 0` (case B) it is not
— `K` is then ramified over `ℚ₃` with `v₃(K^×) = (1/2)ℤ`; see the `PhD.JacobsSlash.U3Data` module
header.  `PseudoUniformizer` asks only for a topologically nilpotent unit with multiplicative
norm, which is all the valuation needs, and `[CharZero K]` supplies `(3 : K) ≠ 0`.

Defining this instead of assuming `(ϖ : PseudoUniformizer K) (hϖ : (ϖ : K) = 3)` is what keeps
the normalisation out of every downstream signature: a normalisation is a choice, not a
hypothesis. -/
def ϖ₃ [CharZero K] (h3 : ‖(3 : K)‖ < 1) : PseudoUniformizer K :=
  PseudoUniformizer.ofNormLtOne three_ne_zero h3

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem coe_ϖ₃ [CharZero K] (h3 : ‖(3 : K)‖ < 1) :
    ((ϖ₃ h3 : PseudoUniformizer K) : K) = 3 := rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
set_option linter.unusedSectionVars false in
/-- Row rescaling of determinants: if `A j i = 3 ^ (j : ℕ) * B j i` then
`det A = 3 ^ (∑ j, j) * det B`.  (The factorisation `det M_S = 3^{∑ rows} det N_S`
implicit in the thesis's "`v₃(c_{S_m}) = v₃(det D_m(3))`".) -/
theorem det_row_smul_pow {n : ℕ} (B : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun j i : Fin n => (3 : K) ^ (j : ℕ) * B j i).det =
      (3 : K) ^ (∑ j : Fin n, (j : ℕ)) * B.det := by
  rw [Matrix.det_mul_column (fun j : Fin n => (3 : K) ^ (j : ℕ)) B,
    Finset.prod_pow_eq_pow_sum]

omit [CompleteSpace K] in
set_option linter.unusedSectionVars false in
/-- A summable family with one term of norm `b` and all others of norm `≤ c < b` has
`‖tsum‖ = b` (ultrametric isolated-dominant-term principle). -/
theorem norm_tsum_eq_of_dominant {ι : Type*} {f : ι → K} (hf : Summable f) (i₀ : ι)
    {c : ℝ} (hc : c < ‖f i₀‖) (h : ∀ i ≠ i₀, ‖f i‖ ≤ c) : ‖∑' i, f i‖ = ‖f i₀‖ := by
  classical
  rw [hf.tsum_eq_add_tsum_ite i₀]
  by_cases hall : ∀ i, i = i₀
  · -- Degenerate case: no other index, so the tail vanishes identically.  (This case must be
    -- separated because `c` may be negative, in which case `h` is vacuous.)
    rw [tsum_congr fun i => if_pos (hall i), tsum_zero, add_zero]
  · obtain ⟨i₁, hi₁⟩ := not_forall.1 hall
    have hc0 : 0 ≤ c := (norm_nonneg (f i₁)).trans (h i₁ hi₁)
    have htail : ‖∑' i, if i = i₀ then (0 : K) else f i‖ ≤ c := by
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hc0 fun i => ?_
      by_cases hi : i = i₀
      · simpa [hi] using hc0
      · simpa [hi] using h i hi
    have hlt : ‖∑' i, if i = i₀ then (0 : K) else f i‖ < ‖f i₀‖ := htail.trans_lt hc
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

/-- Scalars scale the characteristic coefficients geometrically:
`c_m (λ • u) = λ^m c_m (u)` (each `m × m` minor is `m`-homogeneous). -/
theorem charCoeff_smul (lam : K) (u : c(ℕ, K) →L[K] c(ℕ, K)) (m : ℕ) :
    charCoeff (lam • u) m = lam ^ m * charCoeff u m := by
  have hmc : ∀ j i : ℕ, matrixCoeff (lam • u) j i = lam * matrixCoeff u j i := fun _ _ => rfl
  have hminor : ∀ S : {S : Finset ℕ // S.card = m},
      minor (lam • u) (S : Finset ℕ) = lam ^ m * minor u (S : Finset ℕ) := by
    rintro ⟨S, hS⟩
    have hmat : (Matrix.of fun j i : S => matrixCoeff (lam • u) (j : ℕ) (i : ℕ)) =
        lam • Matrix.of fun j i : S => matrixCoeff u (j : ℕ) (i : ℕ) := by
      ext j i
      exact hmc _ _
    show (Matrix.of fun j i : S => matrixCoeff (lam • u) (j : ℕ) (i : ℕ)).det = _
    rw [hmat, Matrix.det_smul, Fintype.card_coe, hS]
    rfl
  rw [charCoeff, charCoeff, tsum_congr hminor, tsum_mul_left]
  ring

/-- The tautological identification `Fin m ≃ ↥(Finset.range m)` (both directions are `rfl`,
and `↑(finEquivRange m j) = ↑j` definitionally).  `minor` is indexed by the subtype `↥S`,
while `hmin` and `det_row_smul_pow` are indexed by `Fin m`; this
is the transport used for the principal block `S_m = {0, …, m-1}`. -/
private def finEquivRange (m : ℕ) : Fin m ≃ ↥(Finset.range m) where
  toFun j := ⟨(j : ℕ), Finset.mem_range.2 j.2⟩
  invFun x := ⟨(x : ℕ), Finset.mem_range.1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `3 ≠ 0` in `K`.  No characteristic hypothesis is available, so this is *derived* from the
unit-minor hypothesis at `n = 2`: were `3 = 0` then `3⁻¹ = 0`, so the second row of the
rescaled `2 × 2` matrix would vanish and its determinant would have norm `0`, not `1`. -/
private theorem three_ne_zero_of_unit_minors {u : c(ℕ, K) →L[K] c(ℕ, K)}
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1) :
    (3 : K) ≠ 0 := by
  intro h30
  have hrow : ∀ i : Fin 2,
      (Matrix.of fun j i : Fin 2 => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i) 1 i = 0 := by
    intro i
    show (3 : K)⁻¹ ^ (((1 : Fin 2) : ℕ)) * matrixCoeff u 1 i = 0
    rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, h30, inv_zero, pow_one, zero_mul]
  have h := hmin 2
  rw [Matrix.det_eq_zero_of_row_eq_zero 1 hrow, norm_zero] at h
  exact zero_ne_one h

/-- The row decay `‖a_{ji}‖ ≤ ‖3‖ ^ j` makes `u` a compactoid, which is what feeds the
summability of the minors (`TateFredholm.summable_minor`). -/
private theorem isCompactoid_of_norm_matrixCoeff_le (h3 : ‖(3 : K)‖ < 1)
    {u : c(ℕ, K) →L[K] c(ℕ, K)} (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖(3 : K)‖ ^ j) :
    IsCompactoid u := by
  refine squeeze_zero (rowNorm_nonneg u)
    (fun j => Real.iSup_le (fun i => hdiv j i) (pow_nonneg (norm_nonneg _) j)) ?_
  rw [Nat.cofinite_eq_atTop]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h3

/-- The principal block contributes exactly `‖3‖ ^ (m(m-1)/2)`: factoring `3 ^ j` out of the
`j`-th row of `M_{S_m}` leaves the matrix `N_m` of the unit-minor hypothesis, whence
`‖det M_{S_m}‖ = ‖3‖ ^ (∑_{j < m} j) · 1`. -/
private theorem norm_minor_range (h3ne : (3 : K) ≠ 0) {u : c(ℕ, K) →L[K] c(ℕ, K)}
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1)
    (m : ℕ) : ‖minor u (Finset.range m)‖ = ‖(3 : K)‖ ^ m.choose 2 := by
  have hsum : ∑ j : Fin m, (j : ℕ) = m.choose 2 := by
    have hfin : ∑ j : Fin m, (j : ℕ) = ∑ i ∈ Finset.range m, i :=
      Fin.sum_univ_eq_sum_range (fun i => i) m
    rw [hfin, Finset.sum_range_id, Nat.choose_two_right]
  have hdet : minor u (Finset.range m)
      = (Matrix.of fun j i : Fin m => matrixCoeff u (j : ℕ) (i : ℕ)).det :=
    (Matrix.det_submatrix_equiv_self (finEquivRange m) _).symm
  have hfac : (Matrix.of fun j i : Fin m => matrixCoeff u (j : ℕ) (i : ℕ))
      = Matrix.of fun j i : Fin m => (3 : K) ^ (j : ℕ) *
          (Matrix.of fun j i : Fin m => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i) j i := by
    ext j i
    show matrixCoeff u (j : ℕ) (i : ℕ)
      = (3 : K) ^ (j : ℕ) * ((3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u (j : ℕ) (i : ℕ))
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h3ne, one_pow, one_mul]
  rw [hdet, hfac, det_row_smul_pow, norm_mul, norm_pow, hmin m, mul_one, hsum]

variable (h3 : ‖(3 : K)‖ < 1)
include h3

/-- **[Jacobs, Theorem 2.12]** (norm form).  Let `u` be an operator on `c(ℕ, K)` whose
matrix satisfies the divisibility `‖matrixCoeff u j i‖ ≤ ‖3‖ ^ j` and whose rescaled
matrix `N j i = 3⁻ʲ · matrixCoeff u j i` has every top-left minor of norm `1`.  Then
`‖c_m(u)‖ = ‖3‖ ^ (m.choose 2)` for every `m` — the vertex data of the Newton polygon
of `det (1 - Tu)`: the points `(m, m(m−1)/2)` lie on the parabola `½ x (x-1)`.
NOTE (module header): the *slope* statement — that the polygon through these points has
slopes `0, 1, 2, 3, …` — is proved separately, in `PhD.JacobsSlash.SlopeReading`. -/
theorem norm_charCoeff_of_unit_minors (u : c(ℕ, K) →L[K] c(ℕ, K))
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖(3 : K)‖ ^ j)
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1)
    (m : ℕ) : ‖charCoeff u m‖ = ‖(3 : K)‖ ^ m.choose 2 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : {S : Finset ℕ // S.card = m}, (i₀ : Finset ℕ) = Finset.range m :=
    ⟨⟨Finset.range m, Finset.card_range m⟩, rfl⟩
  have h3ne : (3 : K) ≠ 0 := three_ne_zero_of_unit_minors hmin
  have h30 : (0 : ℝ) < ‖(3 : K)‖ := norm_pos_iff.2 h3ne
  -- The principal block `S_m = {0, …, m-1}` contributes exactly `‖3‖ ^ m(m-1)/2`.
  have hdom : ‖minor u (i₀ : Finset ℕ)‖ = ‖(3 : K)‖ ^ m.choose 2 := by
    rw [hi₀]
    exact norm_minor_range h3ne hmin m
  -- Every other block is strictly smaller: its row sum exceeds `m(m-1)/2`.
  have hoff : ∀ S ≠ i₀, ‖minor u (S : Finset ℕ)‖ ≤ ‖(3 : K)‖ ^ (m.choose 2 + 1) := by
    intro S hS
    refine (norm_minor_le_pow_sum (norm_nonneg _) (fun j => j) hdiv _).trans
      (pow_le_pow_of_le_one (norm_nonneg _) h3.le ?_)
    exact choose_two_lt_sum_of_ne_range S.2 fun h => hS (Subtype.ext (h.trans hi₀.symm))
  have hc : ‖(3 : K)‖ ^ (m.choose 2 + 1) < ‖minor u (i₀ : Finset ℕ)‖ := by
    rw [hdom]
    exact pow_lt_pow_right_of_lt_one₀ h30 h3 (Nat.lt_succ_self _)
  have htsum : ‖∑' S : {S : Finset ℕ // S.card = m}, minor u (S : Finset ℕ)‖
      = ‖minor u (i₀ : Finset ℕ)‖ :=
    norm_tsum_eq_of_dominant
      (summable_minor u (isCompactoid_of_norm_matrixCoeff_le h3 hdiv) m) i₀ hc hoff
  rw [charCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, htsum, hdom]

/-- The slope reading of `norm_charCoeff_of_unit_minors` through the additive valuation
`v₃ = PseudoUniformizer.val` normalised by `v₃ 3 = 1`:  `v₃ (c_m) = m(m-1)/2`.
This is the exact valuation-sequence input consumed by the Newton-polygon machinery
(`PhD.NewtonPolygons`); the reading "hence the slopes are `0, 1, 2, 3, …`" is
`JacobsSlash.unitSlope_newtonPolygon₀OfPowerSeries_charPowerSeries` in
`PhD.JacobsSlash.SlopeReading` (module header). -/
theorem val_charCoeff_of_unit_minors [CharZero K]
    (u : c(ℕ, K) →L[K] c(ℕ, K))
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖(3 : K)‖ ^ j)
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1)
    (m : ℕ) : (ϖ₃ h3).val (charCoeff u m) = (m.choose 2 : ℝ) := by
  have hnorm := norm_charCoeff_of_unit_minors h3 u hdiv hmin m
  have h30 : (0 : ℝ) < ‖(3 : K)‖ := (ϖ₃ h3).norm_pos
  have hlog : Real.log ‖(3 : K)‖ ≠ 0 := (ϖ₃ h3).log_norm_neg.ne
  have hne : charCoeff u m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (pow_pos h30 (m.choose 2)).ne' hnorm.symm
  rw [PseudoUniformizer.val_of_ne_zero (ϖ₃ h3) hne, hnorm, coe_ϖ₃, Real.log_pow, mul_div_assoc,
    div_self hlog, mul_one]

end JacobsSlash
