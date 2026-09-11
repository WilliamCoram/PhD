/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.NumberTheory.Padics.MahlerBasis
import PhD.TateFredholm.«05_GenFun»
import PhD.TateFredholm.«06_BlockOp»
import PhD.QMF.Weight.«04_Char»

/-!
# Colmez's basis of the Tate algebra, and the Mahler coordinates of monomials

[LWX, §2.16] cites [Colmez, Théorème 1.29]: the functions `⌊n/(q⁻¹pᵐ)⌋!·(z choose n)` form an
orthonormal basis of the space of functions analytic on the discs `a + q⁻¹pᵐℤ_p`.  At `m = 1`
(`p` odd, `q = p`) this is the closed unit disc, the space is the Tate algebra `K⟨z⟩ = c(ℕ, K)`
(monomial coordinates), and the basis is `n!·(z choose n) = descPochhammer n = z(z−1)⋯(z−n+1)`
— monic polynomials with integer coefficients.  This file provides:

* `mahlerCoeffPow m k = Δ^m(n ↦ nᵏ)(0)` — the (integral, finitely supported) Mahler
  coordinates of the monomials, with Newton's forward-difference formula
  `zᵏ = ∑_m (z choose m)·Δ^m(nᵏ)(0)` on `ℕ` and hence on `ℤ_p` (density of `ℕ`);
* the change of coordinates `colmezToMonomial : c(ℕ, K) →L[K] c(ℕ, K)`, Colmez coordinates to
  monomial coordinates, an isometry with dense range, hence a continuous linear equivalence
  `colmezEquiv` ([Colmez, Thm 1.29] at `m = 1`: the Colmez basis is orthonormal);
* `monomialToMahler = diagFactorial ∘ colmezEquiv.symm` — the monomial-to-Mahler
  coordinate map factors through the Colmez basis by the diagonal `diag(m!)`, which is
  [LWX, Prop 2.17, proof]'s "conjugated by an infinite diagonal matrix with entries
  `⌊n/(q⁻¹pᵐ)⌋!`" at `m = 1`;
* `fwdDiff_iter_evalAt_natCast` — the Mahler coordinates of a convergent power series
  evaluated at `ℕ`-points, termwise.

## Main declarations

* `LWX.mahlerCoeffPow`, `LWX.pow_eq_sum_choose_mul_mahlerCoeffPow`.
* `LWX.colmezToMonomial`, `LWX.norm_colmezToMonomial`, `LWX.colmezEquiv`.
* `LWX.monomialToMahler`, `LWX.diagFactorial`, `LWX.monomialToMahler_eq`.
* `LWX.fwdDiff_iter_evalAt_natCast`.
-/

open Filter Topology TateFredholm

open scoped Nat TateFredholm fwdDiff

noncomputable section

namespace LWX

section Integers

/-- The Mahler coordinates of the monomial `n ↦ nᵏ`: `Δ^m(nᵏ)(0) ∈ ℤ` (equal to
`m!·S(k, m)`, `S` the Stirling numbers of the second kind — not needed). -/
def mahlerCoeffPow (m k : ℕ) : ℤ := Δ_[1]^[m] (fun n : ℤ => n ^ k) 0

/-- `Δ^m(nᵏ) = 0` for `k < m` (`fwdDiff_iter_pow_eq_zero_of_lt`). -/
theorem mahlerCoeffPow_eq_zero_of_lt {m k : ℕ} (h : k < m) : mahlerCoeffPow m k = 0 := by
  unfold mahlerCoeffPow
  rw [fwdDiff_iter_pow_eq_zero_of_lt h]
  rfl

/-- `Δ^k(nᵏ)(0) = k!` (`fwdDiff_iter_eq_factorial`). -/
theorem mahlerCoeffPow_self (k : ℕ) : mahlerCoeffPow k k = (k ! : ℤ) := by
  unfold mahlerCoeffPow
  rw [fwdDiff_iter_eq_factorial]
  rfl

/-- **Newton's forward-difference formula** for the monomials on `ℕ`
(`shift_eq_sum_fwdDiff_iter` at `y = 0`, trimmed by the vanishing for `m > k`):
`nᵏ = ∑_{m ≤ k} C(n, m)·Δ^m(nᵏ)(0)`. -/
theorem natCast_pow_eq_sum_choose_mul_mahlerCoeffPow (n k : ℕ) :
    (n : ℤ) ^ k = ∑ m ∈ Finset.range (k + 1), (n.choose m : ℤ) * mahlerCoeffPow m k := by
  have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℤ)) (fun r : ℤ => r ^ k) n 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h
  unfold mahlerCoeffPow
  rw [h]
  have hL : ∑ m ∈ Finset.range (n + 1), (n.choose m : ℤ) * Δ_[1]^[m] (fun r : ℤ => r ^ k) 0
      = ∑ m ∈ Finset.range (n + k + 1), (n.choose m : ℤ) * Δ_[1]^[m] (fun r : ℤ => r ^ k) 0 :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => by
      rw [Finset.mem_range, not_lt] at hm
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have hR : ∑ m ∈ Finset.range (k + 1), (n.choose m : ℤ) * Δ_[1]^[m] (fun r : ℤ => r ^ k) 0
      = ∑ m ∈ Finset.range (n + k + 1), (n.choose m : ℤ) * Δ_[1]^[m] (fun r : ℤ => r ^ k) 0 :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => by
      rw [Finset.mem_range, not_lt] at hm
      rw [fwdDiff_iter_pow_eq_zero_of_lt (by omega)]
      simp
  rw [hL, hR]

/-- The forward differences of `descPochhammer m = m!·(n choose m)` at `0`:
`Δ^j(descPochhammer_m)(0) = m!·δ_{jm}` (`descPochhammer_eval_eq_descFactorial`,
`fwdDiff_iter_choose_zero`). -/
theorem fwdDiff_iter_descPochhammer_eval_zero (j m : ℕ) :
    Δ_[1]^[j] (fun n : ℤ => (descPochhammer ℤ m).eval n) 0
      = if j = m then (m ! : ℤ) else 0 := by
  have hval : ∀ n : ℕ, (descPochhammer ℤ m).eval (n : ℤ) = (m ! : ℤ) * (n.choose m : ℤ) := by
    intro n
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.cast_mul]
  calc Δ_[1]^[j] (fun n : ℤ => (descPochhammer ℤ m).eval n) 0
      = ∑ i ∈ Finset.range (j + 1),
          ((-1 : ℤ) ^ (j - i) * j.choose i) • (descPochhammer ℤ m).eval ((0 : ℤ) + i • 1) :=
        fwdDiff_iter_eq_sum_shift _ _ _ _
    _ = (m ! : ℤ) * ∑ i ∈ Finset.range (j + 1),
          ((-1 : ℤ) ^ (j - i) * j.choose i) • ((0 + i • 1 : ℕ).choose m : ℤ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [zero_add, nsmul_eq_mul, smul_eq_mul, mul_one, hval]
        ring
    _ = (m ! : ℤ) * Δ_[1]^[j] (fun x : ℕ => (x.choose m : ℤ)) 0 := by
        rw [fwdDiff_iter_eq_sum_shift]
    _ = if j = m then (m ! : ℤ) else 0 := by
        rw [fwdDiff_iter_choose_zero, mul_ite, mul_one, mul_zero]

/-- Forward differences commute with additive maps (the iterated difference is a finite
integer combination of shifts, `fwdDiff_iter_eq_sum_shift`). -/
theorem map_fwdDiff_iter {M N A : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommMonoid A] (e : M →+ N) (f : A → M) (h : A) (m : ℕ) (y : A) :
    Δ_[h]^[m] (fun a => e (f a)) y = e (Δ_[h]^[m] f y) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, map_sum]
  exact Finset.sum_congr rfl fun k _ => (map_zsmul e _ _).symm

end Integers

section PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Newton's formula on `ℤ_p`**: `zᵏ = ∑_{m ≤ k} (z choose m)·Δ^m(nᵏ)(0)` — both sides
are continuous in `z` and agree on the dense subset `ℕ` (`PadicInt.denseRange_natCast`,
`Ring.choose_natCast`). -/
theorem pow_eq_sum_choose_mul_mahlerCoeffPow (z : ℤ_[p]) (k : ℕ) :
    z ^ k = ∑ m ∈ Finset.range (k + 1), Ring.choose z m * (mahlerCoeffPow m k : ℤ_[p]) := by
  have hcont : Continuous fun z : ℤ_[p] =>
      ∑ m ∈ Finset.range (k + 1), Ring.choose z m * (mahlerCoeffPow m k : ℤ_[p]) :=
    continuous_finsetSum _ fun m _ => Continuous.mul (mahler m).continuous continuous_const
  refine congrFun (PadicInt.denseRange_natCast.equalizer (continuous_pow k) hcont
    (funext fun n => ?_)) z
  have h := congrArg (fun x : ℤ => (x : ℤ_[p])) (natCast_pow_eq_sum_choose_mul_mahlerCoeffPow n k)
  push_cast at h
  rw [Function.comp_apply, Function.comp_apply, h]
  exact Finset.sum_congr rfl fun m _ => by rw [Ring.choose_natCast]

end PadicInt

section TateAlgebra

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Colmez coordinates to monomial coordinates**: `e_m ↦` the coefficient sequence of
`descPochhammer m = z(z−1)⋯(z−m+1)` (integer coefficients, finitely many per column). -/
def colmezToMonomial : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun k m => (((descPochhammer ℤ m).coeff k : ℤ) : K))
    ⟨1, fun _ _ => IsUltrametricDist.norm_intCast_le_one K _⟩ (fun m => by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Finset.range (m + 1)).finite_toSet.subset fun k hk => ?_
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      rw [not_lt] at hcon
      refine hk ?_
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; omega),
        Int.cast_zero])

/-- The matrix of `colmezToMonomial`. -/
theorem matrixCoeff_colmezToMonomial (k m : ℕ) :
    matrixCoeff (colmezToMonomial K) k m = (((descPochhammer ℤ m).coeff k : ℤ) : K) :=
  matrixCoeff_ofCoeffs _ _ _ k m

/-- `colmezToMonomial` in coordinates: `(Ψ⁻¹ a)_k = ∑' m, (descPochhammer m)_k · a_m`. -/
theorem colmezToMonomial_apply (a : c(ℕ, K)) (k : ℕ) :
    colmezToMonomial K a k = ∑' m, (((descPochhammer ℤ m).coeff k : ℤ) : K) * a m :=
  ofCoeffs_apply _ _ _ a k

/-- The sup norm of a nonzero `c₀`-sequence is attained, and at a largest index. -/
theorem exists_norm_apply_eq_of_ne_zero (a : c(ℕ, K)) (ha : a ≠ 0) :
    ∃ n₀, ‖a n₀‖ = ‖a‖ ∧ ∀ m, n₀ < m → ‖a m‖ < ‖a‖ := by
  classical
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hle : ∀ n, ‖a n‖ ≤ ‖a‖ := cSpace.norm_apply_le a
  have hfin : {n | ‖a‖ / 2 ≤ ‖a n‖}.Finite := by
    have h := cSpace.tendsto_cofinite a
    rw [NormedAddGroup.tendsto_nhds_zero] at h
    exact (Filter.eventually_cofinite.mp (h (‖a‖ / 2) (by positivity))).subset fun n hn =>
      not_lt.mpr hn
  set T := hfin.toFinset with hT
  have hmemT : ∀ n, n ∈ T ↔ ‖a‖ / 2 ≤ ‖a n‖ := fun n => by rw [hT, Set.Finite.mem_toFinset]; rfl
  obtain ⟨n₁, hn₁⟩ : ∃ n, ‖a‖ / 2 < ‖a n‖ := by
    have : ‖a‖ / 2 < ⨆ n, ‖a n‖ := by rw [← cSpace.norm_eq_iSup]; linarith
    exact exists_lt_of_lt_ciSup this
  have hTne : T.Nonempty := ⟨n₁, (hmemT n₁).mpr hn₁.le⟩
  obtain ⟨n₂, hn₂T, hn₂max⟩ := T.exists_max_image (fun n => ‖a n‖) hTne
  have hattain : ‖a n₂‖ = ‖a‖ := by
    refine le_antisymm (hle n₂) ?_
    rw [cSpace.norm_eq_iSup]
    refine ciSup_le fun n => ?_
    by_cases hn : n ∈ T
    · exact hn₂max n hn
    · rw [hmemT, not_le] at hn
      exact hn.le.trans ((hmemT n₂).mp hn₂T)
  set A := T.filter (fun n => ‖a n‖ = ‖a‖)
  have hAne : A.Nonempty := ⟨n₂, Finset.mem_filter.mpr ⟨hn₂T, hattain⟩⟩
  refine ⟨A.max' hAne, (Finset.mem_filter.mp (A.max'_mem hAne)).2, fun m hm => ?_⟩
  refine lt_of_le_of_ne (hle m) fun heq => ?_
  have hmA : m ∈ A := Finset.mem_filter.mpr ⟨(hmemT m).mpr (by rw [heq]; linarith), heq⟩
  exact absurd (A.le_max' m hmA) (not_le.mpr hm)

/-- Past an index `n₀` beyond which every coordinate is strictly smaller than `‖a‖`, the
coordinates are *uniformly* smaller: `‖a m‖ ≤ β < ‖a‖` for all `m > n₀` (cofinite decay leaves
only finitely many `m` with `‖a m‖ ≥ ‖a‖/2`). -/
theorem exists_lt_norm_forall_norm_apply_le (a : c(ℕ, K)) (ha : a ≠ 0) {n₀ : ℕ}
    (hmax : ∀ m, n₀ < m → ‖a m‖ < ‖a‖) :
    ∃ β : ℝ, 0 ≤ β ∧ β < ‖a‖ ∧ ∀ m, n₀ < m → ‖a m‖ ≤ β := by
  classical
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hfin : {m | ‖a‖ / 2 ≤ ‖a m‖ ∧ n₀ < m}.Finite := by
    have h := cSpace.tendsto_cofinite a
    rw [NormedAddGroup.tendsto_nhds_zero] at h
    exact (Filter.eventually_cofinite.mp (h (‖a‖ / 2) (by positivity))).subset fun m hm =>
      not_lt.mpr hm.1
  obtain ⟨β₀, hβ₀, hβ₀T⟩ : ∃ β₀ : ℝ, β₀ < ‖a‖ ∧ ∀ m ∈ hfin.toFinset, ‖a m‖ ≤ β₀ := by
    rcases hfin.toFinset.eq_empty_or_nonempty with hTe | hTne
    · exact ⟨0, hpos, fun m hm => by rw [hTe] at hm; exact absurd hm (Finset.notMem_empty m)⟩
    · obtain ⟨m₂, hm₂T, hm₂max⟩ := hfin.toFinset.exists_max_image (fun m => ‖a m‖) hTne
      exact ⟨‖a m₂‖, hmax m₂ (hfin.mem_toFinset.mp hm₂T).2, hm₂max⟩
  refine ⟨max (‖a‖ / 2) β₀, le_max_of_le_left (by positivity), max_lt (by linarith) hβ₀,
    fun m hm => ?_⟩
  by_cases hmT : m ∈ hfin.toFinset
  · exact le_max_of_le_right (hβ₀T m hmT)
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_le] at hmT
    rcases hmT with h1 | h2
    · exact le_max_of_le_left h1.le
    · exact absurd hm h2

/-- **The Colmez basis is orthonormal** ([Colmez, Thm 1.29] at `m = 1`; [LWX, §2.16]):
`colmezToMonomial` is an isometry.  Unitriangular with integral entries: at the largest index
`n₀` where `‖a n₀‖ = ‖a‖`, the `n₀`-th monomial coordinate is `a n₀` plus strictly smaller
terms. -/
theorem norm_colmezToMonomial (a : c(ℕ, K)) : ‖colmezToMonomial K a‖ = ‖a‖ := by
  classical
  have hterm : ∀ k m, ‖(((descPochhammer ℤ m).coeff k : ℤ) : K) * a m‖ ≤ ‖a m‖ := fun k m => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K _)
  have htend : ∀ k, Filter.Tendsto (fun m => (((descPochhammer ℤ m).coeff k : ℤ) : K) * a m)
      Filter.cofinite (𝓝 0) := fun k =>
    squeeze_zero_norm (hterm k) (by simpa using (cSpace.tendsto_cofinite a).norm)
  refine le_antisymm ?_ ?_
  · rw [cSpace.norm_eq_iSup]
    refine ciSup_le fun k => ?_
    rw [colmezToMonomial_apply]
    exact (TateFredholm.norm_tsum_le_iSup (htend k)).trans
      (ciSup_le fun m => (hterm k m).trans (cSpace.norm_apply_le a m))
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    obtain ⟨n₀, hn₀, hmax⟩ := exists_norm_apply_eq_of_ne_zero K a ha
    obtain ⟨β, hβ0, hβ, hβle⟩ := exists_lt_norm_forall_norm_apply_le K a ha hmax
    have hβbound : ∀ m,
        ‖if m = n₀ then 0 else (((descPochhammer ℤ m).coeff n₀ : ℤ) : K) * a m‖ ≤ β := fun m => by
      split_ifs with hm
      · rw [norm_zero]
        exact hβ0
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; exact hlt),
          Int.cast_zero, zero_mul, norm_zero]
        exact hβ0
      · exact (hterm n₀ m).trans (hβle m hgt)
    have hsplit : colmezToMonomial K a n₀
        = a n₀ + ∑' m, if m = n₀ then 0 else (((descPochhammer ℤ m).coeff n₀ : ℤ) : K) * a m := by
      rw [colmezToMonomial_apply,
        (TateFredholm.summable_of_tendsto_cofinite (htend n₀)).tsum_eq_add_tsum_ite n₀]
      congr 1
      rw [show (descPochhammer ℤ n₀).coeff n₀ = 1 from
        (monic_descPochhammer ℤ n₀).coeff_natDegree.symm ▸ by rw [descPochhammer_natDegree],
        Int.cast_one, one_mul]
    have htail : ‖∑' m, if m = n₀ then 0 else (((descPochhammer ℤ m).coeff n₀ : ℤ) : K) * a m‖
        < ‖a n₀‖ := by
      refine lt_of_le_of_lt (TateFredholm.norm_tsum_le_iSup ?_) ((ciSup_le hβbound).trans_lt ?_)
      · refine squeeze_zero_norm (fun m => ?_) (by simpa using (cSpace.tendsto_cofinite a).norm)
        split_ifs
        · simp
        · exact hterm n₀ m
      · rw [hn₀]; exact hβ
    calc ‖a‖ = ‖a n₀‖ := hn₀.symm
      _ = ‖colmezToMonomial K a n₀‖ := by
          rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm htail.ne',
            max_eq_left htail.le]
      _ ≤ ‖colmezToMonomial K a‖ := cSpace.norm_apply_le _ n₀

/-- Every monomial `zᵏ` is a finite combination of the `descPochhammer m`, `m ≤ k`
(triangular solving), so every `single k 1` lies in the range. -/
theorem single_mem_range_colmezToMonomial (k : ℕ) :
    cSpace.single k (1 : K) ∈ LinearMap.range (colmezToMonomial K).toLinearMap := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hΨ : colmezToMonomial K (cSpace.single k 1) = cSpace.single k (1 : K)
        + ∑ m ∈ Finset.range k,
            (((descPochhammer ℤ k).coeff m : ℤ) : K) • cSpace.single m (1 : K) := by
      refine DFunLike.ext _ _ fun j => ?_
      rw [colmezToMonomial_apply,
        tsum_eq_single k (fun i hi => by rw [cSpace.single_apply_of_ne hi, mul_zero]),
        cSpace.single_apply_self, mul_one]
      change _ = cSpace.single k (1 : K) j + (∑ m ∈ Finset.range k,
        (((descPochhammer ℤ k).coeff m : ℤ) : K) • cSpace.single m (1 : K)) j
      rw [cSpace.sum_apply]
      by_cases hjk : j = k
      · subst hjk
        rw [cSpace.single_apply_self, Finset.sum_eq_zero fun m hm => ?_, add_zero,
          show (descPochhammer ℤ j).coeff j = 1 from
            (monic_descPochhammer ℤ j).coeff_natDegree.symm ▸ by rw [descPochhammer_natDegree],
          Int.cast_one]
        rw [Finset.mem_range] at hm
        change (_ : K) * cSpace.single m (1 : K) j = 0
        rw [cSpace.single_apply_of_ne (ne_of_gt hm), mul_zero]
      · rw [cSpace.single_apply_of_ne hjk, zero_add]
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · rw [Finset.sum_eq_single j (fun m _ hm => by
            change (_ : K) * cSpace.single m (1 : K) j = 0
            rw [cSpace.single_apply_of_ne (Ne.symm hm), mul_zero])
            (fun h => absurd (Finset.mem_range.mpr hlt) h)]
          change _ = (_ : K) * cSpace.single j (1 : K) j
          rw [cSpace.single_apply_self, mul_one]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [descPochhammer_natDegree]; exact hgt), Int.cast_zero,
            Finset.sum_eq_zero fun m hm => by
              change (_ : K) * cSpace.single m (1 : K) j = 0
              rw [Finset.mem_range] at hm
              rw [cSpace.single_apply_of_ne (by omega), mul_zero]]
    have hk : cSpace.single k (1 : K) = colmezToMonomial K (cSpace.single k 1)
        - ∑ m ∈ Finset.range k,
            (((descPochhammer ℤ k).coeff m : ℤ) : K) • cSpace.single m (1 : K) := by
      rw [hΨ, add_sub_cancel_right]
    rw [hk]
    exact Submodule.sub_mem _ (LinearMap.mem_range_self _ _)
      (Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (ih m (Finset.mem_range.mp hm)))

/-- An isometry whose range contains the finitely supported sequences is surjective
(closed range + dense range). -/
theorem surjective_colmezToMonomial : Function.Surjective (colmezToMonomial K) := by
  have hiso : Isometry (colmezToMonomial K) := Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_colmezToMonomial]
  have hclosed : IsClosed (Set.range (colmezToMonomial K)) :=
    hiso.isClosedEmbedding.isClosed_range
  intro f
  have hmem : f ∈ closure (Set.range (colmezToMonomial K)) := by
    refine mem_closure_of_tendsto (cSpace.hasSum_single f).tendsto_sum_nat
      (Filter.Eventually.of_forall fun n => ?_)
    have : ∑ i ∈ Finset.range n, f i • cSpace.single i (1 : K)
        ∈ LinearMap.range (colmezToMonomial K).toLinearMap :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (single_mem_range_colmezToMonomial K i)
    exact LinearMap.mem_range.mp this
  rwa [hclosed.closure_eq] at hmem

/-- `colmezToMonomial` is injective (it is an isometry). -/
theorem injective_colmezToMonomial : Function.Injective (colmezToMonomial K) := fun x y hxy => by
  rw [← sub_eq_zero, ← norm_eq_zero, ← norm_colmezToMonomial, map_sub, hxy, sub_self, norm_zero]

/-- **The Colmez basis change as a continuous linear equivalence** of the Tate algebra: the
bijective isometry `colmezToMonomial`, whose inverse is again an isometry (hence continuous;
no open mapping theorem). -/
def colmezEquiv : c(ℕ, K) ≃L[K] c(ℕ, K) :=
  let e := LinearEquiv.ofBijective (colmezToMonomial K).toLinearMap
    ⟨injective_colmezToMonomial K, surjective_colmezToMonomial K⟩
  { e with
    continuous_toFun := (colmezToMonomial K).continuous
    continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm 1 fun b => by
      rw [one_mul]
      have h := norm_colmezToMonomial K (e.symm b)
      rw [show colmezToMonomial K (e.symm b) = b from e.apply_symm_apply b] at h
      exact h.symm.le }

/-- The underlying operator of `colmezEquiv` is `colmezToMonomial`. -/
@[simp] theorem coe_colmezEquiv :
    (colmezEquiv K : c(ℕ, K) →L[K] c(ℕ, K)) = colmezToMonomial K := rfl

/-- **Monomial coordinates to Mahler coordinates**: `e_k ↦ ∑_m Δ^m(nᵏ)(0)·e_m`
(integral entries, finitely many per column). -/
def monomialToMahler : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun m k => (mahlerCoeffPow m k : K))
    ⟨1, fun _ _ => IsUltrametricDist.norm_intCast_le_one K _⟩ (fun k => by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Finset.range (k + 1)).finite_toSet.subset fun m hm => ?_
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      rw [not_lt] at hcon
      refine hm ?_
      rw [mahlerCoeffPow_eq_zero_of_lt (by omega), Int.cast_zero])

/-- The matrix of `monomialToMahler`. -/
theorem matrixCoeff_monomialToMahler (m k : ℕ) :
    matrixCoeff (monomialToMahler K) m k = (mahlerCoeffPow m k : K) :=
  matrixCoeff_ofCoeffs _ _ _ m k

/-- The diagonal operator `diag(m!)` — [LWX, Prop 2.17]'s "infinite diagonal matrix" at
`m = 1`. -/
def diagFactorial : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun m k => if m = k then ((m ! : ℕ) : K) else 0)
    ⟨1, fun m k => by
      split_ifs
      · exact IsUltrametricDist.norm_natCast_le_one K _
      · simp⟩
    (fun k => by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Set.finite_singleton k).subset fun m hm => ?_
      rw [Set.mem_singleton_iff]
      by_contra hcon
      exact hm (by simp [hcon]))

/-- The matrix of `diagFactorial`. -/
theorem matrixCoeff_diagFactorial (m k : ℕ) :
    matrixCoeff (diagFactorial K) m k = if m = k then ((m ! : ℕ) : K) else 0 :=
  matrixCoeff_ofCoeffs _ _ _ m k

/-- The Mahler coordinates of `descPochhammer m` are `m!·e_m`:
`monomialToMahler ∘ colmezToMonomial = diag(m!)` (`fwdDiff_iter_descPochhammer_eval_zero`
through `Polynomial.eval_eq_sum_range`). -/
theorem monomialToMahler_comp_colmezToMonomial :
    (monomialToMahler K).comp (colmezToMonomial K) = diagFactorial K := by
  refine ext_matrixCoeff fun j m => ?_
  rw [matrixCoeff_comp, matrixCoeff_diagFactorial]
  simp only [matrixCoeff_colmezToMonomial, matrixCoeff_monomialToMahler]
  rw [tsum_eq_sum (s := Finset.range (m + 1)) (fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; omega),
      Int.cast_zero, zero_mul])]
  have hdeg : (descPochhammer ℤ m).natDegree < m + 1 := by
    rw [descPochhammer_natDegree]
    exact Nat.lt_succ_self m
  have key : ∑ k ∈ Finset.range (m + 1), (descPochhammer ℤ m).coeff k * mahlerCoeffPow j k
      = Δ_[1]^[j] (fun n : ℤ => (descPochhammer ℤ m).eval n) 0 := by
    unfold mahlerCoeffPow
    simp_rw [fwdDiff_iter_eq_sum_shift, Polynomial.eval_eq_sum_range' hdeg, Finset.smul_sum,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, smul_eq_mul]
    ring
  rw [show ∑ k ∈ Finset.range (m + 1),
      (((descPochhammer ℤ m).coeff k : ℤ) : K) * (mahlerCoeffPow j k : K)
      = ((∑ k ∈ Finset.range (m + 1), (descPochhammer ℤ m).coeff k * mahlerCoeffPow j k : ℤ) : K)
      by push_cast; rfl, key, fwdDiff_iter_descPochhammer_eval_zero]
  split_ifs with h
  · subst h
    simp
  · simp

/-- **The factorisation** `monomialToMahler = diag(m!) ∘ colmezEquiv.symm` — the
monomial-to-Mahler coordinate change is the Colmez basis change followed by the diagonal
`diag(m!)` ([LWX, Prop 2.17, proof]). -/
theorem monomialToMahler_eq :
    monomialToMahler K = (diagFactorial K).comp ((colmezEquiv K).symm : c(ℕ, K) →L[K] c(ℕ, K)) := by
  have h1 : (colmezToMonomial K).comp ((colmezEquiv K).symm : c(ℕ, K) →L[K] c(ℕ, K))
      = ContinuousLinearMap.id K c(ℕ, K) := by
    ext x
    exact (colmezEquiv K).apply_symm_apply x
  calc monomialToMahler K
      = (monomialToMahler K).comp ((colmezToMonomial K).comp
          ((colmezEquiv K).symm : c(ℕ, K) →L[K] c(ℕ, K))) := by
        rw [h1, ContinuousLinearMap.comp_id]
    _ = ((monomialToMahler K).comp (colmezToMonomial K)).comp
          ((colmezEquiv K).symm : c(ℕ, K) →L[K] c(ℕ, K)) :=
        (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = (diagFactorial K).comp ((colmezEquiv K).symm : c(ℕ, K) →L[K] c(ℕ, K)) := by
        rw [monomialToMahler_comp_colmezToMonomial]

/-- **Mahler coordinates of an evaluated Tate series at `ℕ`-points**, termwise: for a series
with decaying coefficients, `Δ^m(n ↦ F(n))(0) = ∑_k F_k·Δ^m(nᵏ)(0)` (the iterated difference
is a finite combination of shifts, and the sum converges termwise). -/
theorem fwdDiff_iter_evalAt_natCast {F : PowerSeries K} (hF : QMF.TendstoCoeff F) (m : ℕ) :
    Δ_[1]^[m] (fun n : ℕ => QMF.evalAt F (n : K)) 0
      = ∑' k, PowerSeries.coeff k F * (mahlerCoeffPow m k : K) := by
  rw [fwdDiff_iter_eq_sum_shift]
  have hsum : ∀ i : ℕ, Summable fun k => PowerSeries.coeff k F * (i : K) ^ k := fun i =>
    hF.summable_terms (IsUltrametricDist.norm_natCast_le_one K i)
  have hev : ∀ i : ℕ, QMF.evalAt F ((0 + i • 1 : ℕ) : K)
      = ∑' k, PowerSeries.coeff k F * (i : K) ^ k := fun i => by
    rw [zero_add, nsmul_eq_mul, mul_one]
    rfl
  simp_rw [hev]
  have hHS : HasSum (fun k => ∑ i ∈ Finset.range (m + 1),
      ((-1 : ℤ) ^ (m - i) * m.choose i) • (PowerSeries.coeff k F * (i : K) ^ k))
      (∑ i ∈ Finset.range (m + 1),
        ((-1 : ℤ) ^ (m - i) * m.choose i) • ∑' k, PowerSeries.coeff k F * (i : K) ^ k) :=
    hasSum_sum fun i _ => (hsum i).hasSum.const_smul _
  rw [← hHS.tsum_eq]
  refine tsum_congr fun k => ?_
  unfold mahlerCoeffPow
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end TateAlgebra

end LWX

end
