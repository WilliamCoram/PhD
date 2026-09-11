/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.«05_GenFun»
import PhD.LWX.«00_Colmez»

/-!
# Perturbed unitriangular operators on `c(ℕ, K)` are isometric equivalences — SKELETON

The orthonormality criterion behind Colmez's proof of Amice's theorem ([Colmez, Thm 1.4.7 via
Prop 1.1.5]): an infinite matrix `M` with entries of norm `≤ 1`, unit diagonal, whose entries
*below* the diagonal (row `> column`) have norm `≤ q < 1`, and whose columns are finitely
supported, defines an operator of `c(ℕ, K)` which is an **isometry with dense range**, hence a
continuous linear equivalence.  Colmez states this through the residue field of a discretely
valued `L`; the argument here (the `lwx-seam` largest-index argument for the lower bound, and a
`q`-adic successive approximation for surjectivity) needs only a complete ultrametric `K`.

## Main declarations

* `TateFredholm.IsUnitriangularPerturbation M q` — the hypotheses on the matrix.
* `TateFredholm.ofPerturbation` — the operator; `matrixCoeff_ofPerturbation`.
* `TateFredholm.norm_ofPerturbation` — isometry; `surjective_ofPerturbation`;
  `equivOfPerturbation : c(ℕ, K) ≃L[K] c(ℕ, K)`.
* `TateFredholm.surjective_of_forall_exists_approx` — the abstract successive-approximation
  criterion.
-/

open Filter Topology

open scoped TateFredholm

noncomputable section

namespace TateFredholm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Perturbed unitriangular matrices**: entries of norm `≤ 1`, unit diagonal, entries below
the diagonal of norm `≤ q`, finitely supported columns.  (`q` plays the role of `‖p‖`.) -/
structure IsUnitriangularPerturbation (M : ℕ → ℕ → K) (q : ℝ) : Prop where
  q_pos : 0 < q
  q_lt_one : q < 1
  norm_le_one : ∀ k n, ‖M k n‖ ≤ 1
  norm_diag : ∀ n, ‖M n n‖ = 1
  norm_le_of_lt : ∀ k n, n < k → ‖M k n‖ ≤ q
  col_finite : ∀ n, {k | M k n ≠ 0}.Finite

variable {M : ℕ → ℕ → K} {q : ℝ}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The columns of a perturbed unitriangular matrix decay (they are finitely supported). -/
theorem IsUnitriangularPerturbation.tendsto_col (hM : IsUnitriangularPerturbation M q) (n : ℕ) :
    Tendsto (fun k => M k n) cofinite (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_cofinite]
  exact (hM.col_finite n).subset fun k hk => Ne.symm hk

/-- The operator `a ↦ (k ↦ ∑' n, M k n * a n)` of a perturbed unitriangular matrix. -/
def ofPerturbation (hM : IsUnitriangularPerturbation M q) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs M ⟨1, hM.norm_le_one⟩ hM.tendsto_col

@[simp] theorem matrixCoeff_ofPerturbation (hM : IsUnitriangularPerturbation M q) (k n : ℕ) :
    matrixCoeff (ofPerturbation hM) k n = M k n :=
  matrixCoeff_ofCoeffs _ _ _ k n

theorem ofPerturbation_apply (hM : IsUnitriangularPerturbation M q) (a : c(ℕ, K)) (k : ℕ) :
    ofPerturbation hM a k = ∑' n, M k n * a n :=
  ofCoeffs_apply _ _ _ a k

/-- Entrywise-bounded matrices are norm-nonincreasing. -/
theorem norm_ofPerturbation_le (hM : IsUnitriangularPerturbation M q) (a : c(ℕ, K)) :
    ‖ofPerturbation hM a‖ ≤ ‖a‖ := by
  have hterm : ∀ k n, ‖M k n * a n‖ ≤ ‖a n‖ := fun k n => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hM.norm_le_one k n)
  have htend : ∀ k, Tendsto (fun n => M k n * a n) cofinite (𝓝 0) := fun k =>
    squeeze_zero_norm (hterm k) (by simpa using (cSpace.tendsto_cofinite a).norm)
  rw [cSpace.norm_eq_iSup]
  refine ciSup_le fun k => ?_
  rw [ofPerturbation_apply]
  exact (norm_tsum_le_iSup (htend k)).trans
    (ciSup_le fun n => (hterm k n).trans (cSpace.norm_apply_le a n))

/-- **The lower bound**: at the largest index `n₀` where `‖a n₀‖ = ‖a‖`, the `n₀`-th coordinate
of the image is `M n₀ n₀ · a n₀` plus terms of norm `< ‖a‖` (entries below the diagonal are
`≤ q < 1`, coordinates beyond `n₀` are strictly smaller). -/
theorem norm_ofPerturbation (hM : IsUnitriangularPerturbation M q) (a : c(ℕ, K)) :
    ‖ofPerturbation hM a‖ = ‖a‖ := by
  classical
  have hterm : ∀ k n, ‖M k n * a n‖ ≤ ‖a n‖ := fun k n => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hM.norm_le_one k n)
  have htend : ∀ k, Tendsto (fun n => M k n * a n) cofinite (𝓝 0) := fun k =>
    squeeze_zero_norm (hterm k) (by simpa using (cSpace.tendsto_cofinite a).norm)
  refine le_antisymm (norm_ofPerturbation_le hM a) ?_
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨n₀, hn₀, hmax⟩ := LWX.exists_norm_apply_eq_of_ne_zero K a ha
  obtain ⟨β, hβ0, hβ, hβle⟩ := LWX.exists_lt_norm_forall_norm_apply_le K a ha hmax
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hγlt : max (q * ‖a‖) β < ‖a‖ :=
    max_lt (mul_lt_of_lt_one_left hapos hM.q_lt_one) hβ
  have hbound : ∀ n, ‖if n = n₀ then 0 else M n₀ n * a n‖ ≤ max (q * ‖a‖) β := fun n => by
    split_ifs with hn
    · rw [norm_zero]
      exact le_max_of_le_right hβ0
    · rcases lt_or_gt_of_ne hn with hlt | hgt
      · refine le_max_of_le_left ?_
        rw [norm_mul]
        exact mul_le_mul (hM.norm_le_of_lt n₀ n hlt) (cSpace.norm_apply_le a n) (norm_nonneg _)
          hM.q_pos.le
      · exact le_max_of_le_right ((hterm n₀ n).trans (hβle n hgt))
  have hsplit : ofPerturbation hM a n₀
      = M n₀ n₀ * a n₀ + ∑' n, if n = n₀ then 0 else M n₀ n * a n := by
    rw [ofPerturbation_apply, (summable_of_tendsto_cofinite (htend n₀)).tsum_eq_add_tsum_ite n₀]
  have htail : ‖∑' n, if n = n₀ then 0 else M n₀ n * a n‖ < ‖a n₀‖ := by
    refine lt_of_le_of_lt (norm_tsum_le_iSup ?_) ((ciSup_le hbound).trans_lt ?_)
    · refine squeeze_zero_norm (fun n => ?_) (by simpa using (cSpace.tendsto_cofinite a).norm)
      split_ifs
      · simp
      · exact hterm n₀ n
    · rw [hn₀]
      exact hγlt
  have hdiag : ‖M n₀ n₀ * a n₀‖ = ‖a n₀‖ := by rw [norm_mul, hM.norm_diag n₀, one_mul]
  calc ‖a‖ = ‖a n₀‖ := hn₀.symm
    _ = ‖ofPerturbation hM a n₀‖ := by
        rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
          (by rw [hdiag]; exact htail.ne'), hdiag, max_eq_left htail.le]
    _ ≤ ‖ofPerturbation hM a‖ := cSpace.norm_apply_le _ n₀

/-- **Successive approximation**: a norm-nonincreasing operator into a complete space which
solves every equation up to a fixed factor `q' < 1` (with a control on the size of the
approximate solution) is surjective. -/
theorem surjective_of_forall_exists_approx {I J : Type*} (Ψ : c(I, K) →L[K] c(J, K)) {q' : ℝ}
    (hq' : q' < 1)
    (happ : ∀ t : c(J, K), ∃ b : c(I, K), ‖b‖ ≤ ‖t‖ ∧ ‖t - Ψ b‖ ≤ q' * ‖t‖) :
    Function.Surjective Ψ := by
  classical
  choose f hf1 hf2 using happ
  intro t
  have hr0 : (0 : ℝ) ≤ max q' 0 := le_max_right _ _
  have hr1 : max q' 0 < 1 := max_lt hq' one_pos
  let T : ℕ → c(J, K) := fun n => Nat.rec t (fun _ x => x - Ψ (f x)) n
  have hTs : ∀ n, T (n + 1) = T n - Ψ (f (T n)) := fun _ => rfl
  have hTnorm : ∀ n, ‖T n‖ ≤ max q' 0 ^ n * ‖t‖ := by
    intro n
    induction n with
    | zero => simp [T]
    | succ n ih =>
      calc ‖T (n + 1)‖ = ‖T n - Ψ (f (T n))‖ := by rw [hTs]
        _ ≤ q' * ‖T n‖ := hf2 (T n)
        _ ≤ max q' 0 * ‖T n‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max q' 0 * (max q' 0 ^ n * ‖t‖) := mul_le_mul_of_nonneg_left ih hr0
        _ = max q' 0 ^ (n + 1) * ‖t‖ := by ring
  have hsummable : Summable fun n => f (T n) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => (hf1 (T n)).trans (hTnorm n))
      ((summable_geometric_of_lt_one hr0 hr1).mul_right ‖t‖))
  refine ⟨∑' n, f (T n), ?_⟩
  have hpartial : ∀ N, ∑ n ∈ Finset.range N, Ψ (f (T n)) = t - T N := by
    intro N
    induction N with
    | zero => simp [T]
    | succ N ih => rw [Finset.sum_range_succ, ih, hTs]; abel
  have hTto0 : Tendsto T atTop (𝓝 0) :=
    squeeze_zero_norm hTnorm (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const ‖t‖)
  have hmap : HasSum (fun n => Ψ (f (T n))) (Ψ (∑' n, f (T n))) :=
    hsummable.hasSum.map Ψ Ψ.continuous
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, Ψ (f (T n))) atTop (𝓝 t) := by
    simp only [hpartial]
    simpa using tendsto_const_nhds.sub hTto0
  exact tendsto_nhds_unique hmap.tendsto_sum_nat hlim

/-- Scalars are norm-nonincreasing on the model space (there is no `NormSMulClass` instance on
`c(I, K)`, so the pointwise bound is used directly). -/
private theorem norm_smul_le_mul {I : Type*} (a : K) (f : c(I, K)) : ‖a • f‖ ≤ ‖a‖ * ‖f‖ := by
  refine cSpace.norm_le_of_forall (by positivity) fun i => ?_
  show ‖a * f i‖ ≤ ‖a‖ * ‖f‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (cSpace.norm_apply_le f i) (norm_nonneg a)

/-- A finite combination of basis vectors, read off coordinatewise. -/
private theorem sum_smul_single_apply {I : Type*} [DecidableEq I] (S : Finset I) (f : I → K)
    (i : I) : (∑ n ∈ S, f n • cSpace.single n (1 : K)) i = if i ∈ S then f i else 0 := by
  classical
  rw [cSpace.sum_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi, Finset.sum_eq_single i (fun j _ hj => by
      show f j * cSpace.single j (1 : K) i = 0
      rw [cSpace.single_apply_of_ne (Ne.symm hj), mul_zero]) fun h => absurd hi h]
    show f i * cSpace.single i (1 : K) i = f i
    rw [cSpace.single_apply_self, mul_one]
  · rw [if_neg hi, Finset.sum_eq_zero fun j hj => by
      show f j * cSpace.single j (1 : K) i = 0
      rw [cSpace.single_apply_of_ne (fun h => hi (by rw [h]; exact hj)), mul_zero]]

/-- Every basis vector `single k 1` is hit up to `q`, by a vector of norm `≤ 1` (strong induction
on `k`: divide the `k`-th column by its unit diagonal entry and correct the finitely many
above-diagonal entries by the induction hypothesis). -/
theorem exists_approx_single (hM : IsUnitriangularPerturbation M q) (k : ℕ) :
    ∃ b : c(ℕ, K), ‖b‖ ≤ 1 ∧ ‖cSpace.single k (1 : K) - ofPerturbation hM b‖ ≤ q := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have hq0 : (0 : ℝ) ≤ q := hM.q_pos.le
  have hkk : ‖M k k‖ = 1 := hM.norm_diag k
  have hkk0 : M k k ≠ 0 := fun h => zero_ne_one (by rw [h, norm_zero] at hkk; exact hkk)
  have hcn : ‖(M k k)⁻¹‖ = 1 := by rw [norm_inv, hkk, inv_one]
  set b₀ : c(ℕ, K) := (M k k)⁻¹ • cSpace.single k (1 : K) with hb₀def
  have hb₀ : ‖b₀‖ ≤ 1 := by
    rw [hb₀def]
    refine (norm_smul_le_mul _ _).trans ?_
    rw [hcn, cSpace.norm_single_one, one_mul]
  have hval : ∀ j, ofPerturbation hM b₀ j = (M k k)⁻¹ * M j k := by
    intro j
    rw [ofPerturbation_apply, tsum_eq_single k fun n hn => by
      show M j n * ((M k k)⁻¹ * cSpace.single k (1 : K) n) = 0
      rw [cSpace.single_apply_of_ne hn, mul_zero, mul_zero]]
    show M j k * ((M k k)⁻¹ * cSpace.single k (1 : K) k) = _
    rw [cSpace.single_apply_self, mul_one, mul_comm]
  set r : c(ℕ, K) := cSpace.single k (1 : K) - ofPerturbation hM b₀ with hrdef
  have hrapp : ∀ j, r j = cSpace.single k (1 : K) j - (M k k)⁻¹ * M j k := fun j => by
    rw [hrdef]
    show cSpace.single k (1 : K) j - ofPerturbation hM b₀ j = _
    rw [hval j]
  have hrk : r k = 0 := by
    rw [hrapp k, cSpace.single_apply_self, inv_mul_cancel₀ hkk0, sub_self]
  have hrne : ∀ j, j ≠ k → ‖r j‖ = ‖M j k‖ := fun j hj => by
    rw [hrapp j, cSpace.single_apply_of_ne hj, zero_sub, norm_neg, norm_mul, hcn, one_mul]
  have hrgt : ∀ j, k < j → ‖r j‖ ≤ q := fun j hj => by
    rw [hrne j (Nat.ne_of_gt hj)]
    exact hM.norm_le_of_lt j k hj
  have hrle : ∀ j, ‖r j‖ ≤ 1 := fun j => by
    rcases eq_or_ne j k with rfl | hj
    · rw [hrk, norm_zero]
      exact zero_le_one
    · rw [hrne j hj]
      exact hM.norm_le_one j k
  have hex : ∀ j : ℕ, ∃ b : c(ℕ, K), ‖b‖ ≤ 1 ∧
      (j < k → ‖cSpace.single j (1 : K) - ofPerturbation hM b‖ ≤ q) := by
    intro j
    by_cases hj : j < k
    · obtain ⟨b, hb1, hb2⟩ := ih j hj
      exact ⟨b, hb1, fun _ => hb2⟩
    · exact ⟨0, by simp, fun h => absurd h hj⟩
  choose g hg1 hg2 using hex
  refine ⟨b₀ + ∑ j ∈ Finset.range k, r j • g j, ?_, ?_⟩
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb₀ ?_)
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
    exact (norm_smul_le_mul _ _).trans (mul_le_one₀ (hrle j) (norm_nonneg _) (hg1 j))
  · have hsum : ∑ j ∈ Finset.range k, r j • (cSpace.single j (1 : K) - ofPerturbation hM (g j))
        = (∑ j ∈ Finset.range k, r j • cSpace.single j (1 : K))
          - ∑ j ∈ Finset.range k, r j • ofPerturbation hM (g j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _
    have hlin : cSpace.single k (1 : K)
          - ofPerturbation hM (b₀ + ∑ j ∈ Finset.range k, r j • g j)
        = (r - ∑ j ∈ Finset.range k, r j • cSpace.single j (1 : K))
          + ∑ j ∈ Finset.range k, r j • (cSpace.single j (1 : K) - ofPerturbation hM (g j)) := by
      rw [hsum, map_add, map_sum, hrdef]
      simp only [map_smul]
      abel
    rw [hlin]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine cSpace.norm_le_of_forall hq0 fun i => ?_
      have hEi : (r - ∑ j ∈ Finset.range k, r j • cSpace.single j (1 : K)) i
          = r i - (if i < k then r i else 0) := by
        show r i - (∑ j ∈ Finset.range k, r j • cSpace.single j (1 : K)) i = _
        simp only [sum_smul_single_apply, Finset.mem_range]
      rw [hEi]
      by_cases hi : i < k
      · rw [if_pos hi, sub_self, norm_zero]
        exact hq0
      · rw [if_neg hi, sub_zero]
        rcases eq_or_lt_of_le (not_lt.mp hi) with h | h
        · subst h
          rw [hrk, norm_zero]
          exact hq0
        · exact hrgt i h
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hq0 fun j hj => ?_
      refine (norm_smul_le_mul _ _).trans ?_
      calc ‖r j‖ * ‖cSpace.single j (1 : K) - ofPerturbation hM (g j)‖
          ≤ 1 * q := mul_le_mul (hrle j) (hg2 j (Finset.mem_range.mp hj)) (norm_nonneg _)
            zero_le_one
        _ = q := one_mul q

/-- Every target is hit up to `q` (truncate to a finite support, then sum the approximate
solutions of the basis vectors). -/
theorem exists_approx (hM : IsUnitriangularPerturbation M q) (t : c(ℕ, K)) :
    ∃ b : c(ℕ, K), ‖b‖ ≤ ‖t‖ ∧ ‖t - ofPerturbation hM b‖ ≤ q * ‖t‖ := by
  classical
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨0, by simp, by simp⟩
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hqt : 0 < q * ‖t‖ := mul_pos hM.q_pos htpos
  have hfin : {n | q * ‖t‖ ≤ ‖t n‖}.Finite := by
    have h1 : Tendsto (fun n => ‖t n‖) cofinite (𝓝 0) := by
      simpa using (cSpace.tendsto_cofinite t).norm
    simpa [not_lt] using Filter.eventually_cofinite.mp (h1.eventually_lt_const hqt)
  choose u hu1 hu2 using fun n => exists_approx_single hM n
  refine ⟨∑ n ∈ hfin.toFinset, t n • u n, ?_, ?_⟩
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg t) fun n _ => ?_
    refine (norm_smul_le_mul _ _).trans ?_
    calc ‖t n‖ * ‖u n‖ ≤ ‖t‖ * 1 :=
        mul_le_mul (cSpace.norm_apply_le t n) (hu1 n) (norm_nonneg _) (norm_nonneg t)
      _ = ‖t‖ := mul_one _
  · have hsum : ∑ n ∈ hfin.toFinset, t n • (cSpace.single n (1 : K) - ofPerturbation hM (u n))
        = (∑ n ∈ hfin.toFinset, t n • cSpace.single n (1 : K))
          - ofPerturbation hM (∑ n ∈ hfin.toFinset, t n • u n) := by
      rw [map_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by rw [map_smul, smul_sub]
    have hlin : t - ofPerturbation hM (∑ n ∈ hfin.toFinset, t n • u n)
        = (t - ∑ n ∈ hfin.toFinset, t n • cSpace.single n (1 : K))
          + ∑ n ∈ hfin.toFinset, t n • (cSpace.single n (1 : K) - ofPerturbation hM (u n)) := by
      rw [hsum]
      abel
    rw [hlin]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine cSpace.norm_le_of_forall hqt.le fun i => ?_
      show ‖t i - (∑ n ∈ hfin.toFinset, t n • cSpace.single n (1 : K)) i‖ ≤ _
      rw [sum_smul_single_apply]
      by_cases hi : i ∈ hfin.toFinset
      · rw [if_pos hi, sub_self, norm_zero]
        exact hqt.le
      · rw [if_neg hi, sub_zero]
        rw [hfin.mem_toFinset, Set.mem_ofPred_eq, not_le] at hi
        exact hi.le
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hqt.le fun n _ => ?_
      refine (norm_smul_le_mul _ _).trans ?_
      calc ‖t n‖ * ‖cSpace.single n (1 : K) - ofPerturbation hM (u n)‖ ≤ ‖t‖ * q :=
          mul_le_mul (cSpace.norm_apply_le t n) (hu2 n) (norm_nonneg _) (norm_nonneg t)
        _ = q * ‖t‖ := mul_comm _ _

theorem surjective_ofPerturbation (hM : IsUnitriangularPerturbation M q) :
    Function.Surjective (ofPerturbation hM) :=
  surjective_of_forall_exists_approx _ hM.q_lt_one (exists_approx hM)

theorem injective_ofPerturbation (hM : IsUnitriangularPerturbation M q) :
    Function.Injective (ofPerturbation hM) := fun x y hxy => by
  rw [← sub_eq_zero, ← norm_eq_zero, ← norm_ofPerturbation hM, map_sub, hxy, sub_self, norm_zero]

/-- **The equivalence**: an isometric continuous linear equivalence of `c(ℕ, K)`. -/
def equivOfPerturbation (hM : IsUnitriangularPerturbation M q) : c(ℕ, K) ≃L[K] c(ℕ, K) :=
  let e := LinearEquiv.ofBijective (ofPerturbation hM).toLinearMap
    ⟨injective_ofPerturbation hM, surjective_ofPerturbation hM⟩
  { e with
    continuous_toFun := (ofPerturbation hM).continuous
    continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm 1 fun b => by
      rw [one_mul]
      have h := norm_ofPerturbation hM (e.symm b)
      rw [show ofPerturbation hM (e.symm b) = b from e.apply_symm_apply b] at h
      exact h.symm.le }

@[simp] theorem coe_equivOfPerturbation (hM : IsUnitriangularPerturbation M q) :
    (equivOfPerturbation hM : c(ℕ, K) →L[K] c(ℕ, K)) = ofPerturbation hM := rfl

/-- The inverse is an isometry too. -/
theorem norm_equivOfPerturbation_symm (hM : IsUnitriangularPerturbation M q) (b : c(ℕ, K)) :
    ‖(equivOfPerturbation hM).symm b‖ = ‖b‖ := by
  have h := norm_ofPerturbation hM ((equivOfPerturbation hM).symm b)
  rw [show ofPerturbation hM ((equivOfPerturbation hM).symm b) = b from
    (equivOfPerturbation hM).apply_symm_apply b] at h
  exact h.symm

end TateFredholm

end
