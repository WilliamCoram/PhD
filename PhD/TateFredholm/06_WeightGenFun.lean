/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.«05_GenFun»
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The weight-action generating-function shapes

The two universal factors of a weight-`κ` generating function
`κ(cx + d) / ((cx + d)(cx + d − axy − by))` ([Jacobs, Proposition 2.6]), as two-variable
power series attached to a `2×2` matrix — character-free, so they live with the
`ofGenFun` calculus rather than with any particular weight.

* `TateFredholm.linSeries γ` — the linear factor `cx + d`.
* `TateFredholm.quadSeries γ` — the full denominator `cx + d − axy − by`.
* `TateFredholm.RowIntAt ρ φ` — the row-decay predicate `‖coeff (x^m y^r) φ‖ ≤ ρ ^ m`,
  the level-`ρ` generalisation of the `‖3‖`-based `RowInt` of the Jacobs development.

Moved here (from `PhD/JacobsSlash/2_U3Data.lean`) so the general weight layer
(`PhD/QMF/Weight/`) can consume them without importing the thesis fork.
-/

open TateFredholm MvPowerSeries

namespace TateFredholm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The linear factor `cx + d` of a weight action, as a two-variable power series. -/
noncomputable def linSeries (γ : Matrix (Fin 2) (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  C (γ 1 1) + C (γ 1 0) * X 0

/-- The full denominator `cx + d − axy − by` of a weight action. -/
noncomputable def quadSeries (γ : Matrix (Fin 2) (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  C (γ 1 1) + C (γ 1 0) * X 0 -
    C (γ 0 0) * (X 0 * X 1) - C (γ 0 1) * X 1

section Map

variable {L : Type*} [NontriviallyNormedField L]

omit [IsUltrametricDist K] in
/-- The linear denominator series maps entrywise. -/
theorem map_linSeries (f : K →+* L) (γ : Matrix (Fin 2) (Fin 2) K) :
    MvPowerSeries.map f (linSeries γ) = linSeries (γ.map f) := by
  simp [linSeries]

omit [IsUltrametricDist K] in
/-- The quadratic denominator series maps entrywise. -/
theorem map_quadSeries (f : K →+* L) (γ : Matrix (Fin 2) (Fin 2) K) :
    MvPowerSeries.map f (quadSeries γ) = quadSeries (γ.map f) := by
  simp [quadSeries]

end Map

omit [IsUltrametricDist K] in
lemma linSeries_eq {γ : Matrix (Fin 2) (Fin 2) K} :
    linSeries γ = monomial 0 (γ 1 1) + monomial (Finsupp.single (0 : Fin 2) 1) (γ 1 0) := by
  rw [linSeries, X_def, ← monomial_zero_eq_C_apply, ← monomial_zero_eq_C_apply,
    monomial_mul_monomial, zero_add, mul_one]

omit [IsUltrametricDist K] in
lemma quadSeries_eq {γ : Matrix (Fin 2) (Fin 2) K} :
    quadSeries γ = monomial 0 (γ 1 1) + monomial (Finsupp.single (0 : Fin 2) 1) (γ 1 0)
      - monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) (γ 0 0)
      - monomial (Finsupp.single (1 : Fin 2) 1) (γ 0 1) := by
  rw [quadSeries, X_def, X_def, ← monomial_zero_eq_C_apply, ← monomial_zero_eq_C_apply,
    ← monomial_zero_eq_C_apply, ← monomial_zero_eq_C_apply, monomial_mul_monomial,
    monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial]
  simp

omit [IsUltrametricDist K] in
lemma constantCoeff_linSeries {γ : Matrix (Fin 2) (Fin 2) K} :
    constantCoeff (linSeries γ) = γ 1 1 := by simp [linSeries]

omit [IsUltrametricDist K] in
lemma constantCoeff_quadSeries {γ : Matrix (Fin 2) (Fin 2) K} :
    constantCoeff (quadSeries γ) = γ 1 1 := by simp [quadSeries]

omit [IsUltrametricDist K] in
/-- A multidegree in two variables with both components zero is zero. -/
lemma fin2_eq_zero {p : Fin 2 →₀ ℕ} (h0 : p 0 = 0) (h1 : p 1 = 0) : p = 0 := by
  ext i
  fin_cases i <;> simpa

/-- **Row decay at level `ρ`**: the `x^m y^r` coefficient has norm at most `ρ ^ m` — the
series becomes integral after the substitution `x ↦ x / ϖ` for any `‖ϖ‖ = ρ`.  The
`ρ = ‖3‖` case is the Jacobs development's `RowInt` ([Jacobs, Lemma 2.7]). -/
def RowIntAt (ρ : ℝ) (φ : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ p : Fin 2 →₀ ℕ, ‖coeff p φ‖ ≤ ρ ^ p 0

variable {ρ : ℝ}

omit [IsUltrametricDist K] in
/-- A monomial whose coefficient obeys the row bound is row-integral at level `ρ`. -/
lemma rowIntAt_monomial (hρ0 : 0 ≤ ρ) {n : Fin 2 →₀ ℕ} {v : K} (hv : ‖v‖ ≤ ρ ^ n 0) :
    RowIntAt ρ (monomial n v : MvPowerSeries (Fin 2) K) := by
  intro p
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact hv
  · simp [pow_nonneg hρ0 (p 0)]

/-- Row decay is preserved by sums (the ultrametric inequality). -/
lemma RowIntAt.add {φ ψ : MvPowerSeries (Fin 2) K} (hφ : RowIntAt ρ φ)
    (hψ : RowIntAt ρ ψ) : RowIntAt ρ (φ + ψ) := fun p => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ p) (hψ p))

omit [IsUltrametricDist K] in
/-- Row decay is preserved by negation. -/
lemma RowIntAt.neg {φ : MvPowerSeries (Fin 2) K} (hφ : RowIntAt ρ φ) :
    RowIntAt ρ (-φ) := fun p => by
  rw [map_neg, norm_neg]; exact hφ p

/-- Row decay is preserved by differences. -/
lemma RowIntAt.sub {φ ψ : MvPowerSeries (Fin 2) K} (hφ : RowIntAt ρ φ)
    (hψ : RowIntAt ρ ψ) : RowIntAt ρ (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

/-- Row decay is multiplicative: the `x`-degrees add along the antidiagonal. -/
lemma RowIntAt.mul (hρ0 : 0 ≤ ρ) {φ ψ : MvPowerSeries (Fin 2) K} (hφ : RowIntAt ρ φ)
    (hψ : RowIntAt ρ ψ) : RowIntAt ρ (φ * ψ) := by
  intro p
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hρ0 _)
    fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have h0 : x.1 0 + x.2 0 = p 0 := by rw [← hx]; simp
  calc ‖coeff x.1 φ * coeff x.2 ψ‖ ≤ ρ ^ x.1 0 * ρ ^ x.2 0 := by
        rw [norm_mul]
        exact mul_le_mul (hφ _) (hψ _) (norm_nonneg _) (pow_nonneg hρ0 _)
    _ = ρ ^ p 0 := by rw [← pow_add, h0]

/-- Row decay passes to inverses with unit constant coefficient: strong induction on
`p 0 + p 1` through the recurrence `MvPowerSeries.coeff_inv`. -/
lemma RowIntAt.inv (hρ0 : 0 ≤ ρ) {φ : MvPowerSeries (Fin 2) K} (hφ : RowIntAt ρ φ)
    (h1 : ‖constantCoeff φ‖ = 1) : RowIntAt ρ φ⁻¹ := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N → ‖coeff p φ⁻¹‖ ≤ ρ ^ p 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp
      rw [coeff_inv]
      split_ifs with hp0
      · subst hp0
        simp [norm_inv, h1]
      · rw [norm_mul, norm_neg, norm_inv, h1, inv_one, one_mul]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
          (pow_nonneg hρ0 _) fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        split_ifs with hlt
        · have e0 : x.1 0 + x.2 0 = p 0 := by rw [← hx]; simp
          have e1 : x.1 1 + x.2 1 = p 1 := by rw [← hx]; simp
          have hne : x.1 ≠ 0 := by
            rintro h
            rw [h, zero_add] at hx
            exact absurd hx (ne_of_lt hlt)
          have hpos : 0 < x.1 0 + x.1 1 := by
            rcases Nat.eq_zero_or_pos (x.1 0 + x.1 1) with h | h
            · exact absurd (fin2_eq_zero (by omega) (by omega)) hne
            · exact h
          calc ‖coeff x.1 φ * coeff x.2 φ⁻¹‖ ≤ ρ ^ x.1 0 * ρ ^ x.2 0 := by
                rw [norm_mul]
                exact mul_le_mul (hφ _) (ih (x.2 0 + x.2 1) (by omega) x.2 rfl)
                  (norm_nonneg _) (pow_nonneg hρ0 _)
            _ = ρ ^ p 0 := by rw [← pow_add, e0]
        · simp [pow_nonneg hρ0 (p 0)]
  exact fun p => key (p 0 + p 1) p rfl

omit [IsUltrametricDist K] in
/-- Row integrality is monotone in the level: `ρ ≤ σ` and `RowIntAt ρ φ` give
`RowIntAt σ φ`. -/
lemma RowIntAt.mono {σ : ℝ} (hρ0 : 0 ≤ ρ) (hρσ : ρ ≤ σ) {φ : MvPowerSeries (Fin 2) K}
    (hφ : RowIntAt ρ φ) : RowIntAt σ φ := fun p =>
  (hφ p).trans (pow_le_pow_left₀ hρ0 hρσ _)

/-- The linear factor is row-integral at level `ρ` when `‖d‖ ≤ 1` and `‖c‖ ≤ ρ`. -/
lemma rowIntAt_linSeries (hρ0 : 0 ≤ ρ) {γ : Matrix (Fin 2) (Fin 2) K}
    (hd : ‖γ 1 1‖ ≤ 1) (hc : ‖γ 1 0‖ ≤ ρ) : RowIntAt ρ (linSeries γ) := by
  rw [linSeries_eq]
  refine (rowIntAt_monomial hρ0 ?_).add (rowIntAt_monomial hρ0 ?_)
  · simpa using hd
  · simpa using hc

/-- The quadratic factor is row-integral at level `ρ` under the entry bounds of
[Jacobs, Lemma 2.7]. -/
lemma rowIntAt_quadSeries (hρ0 : 0 ≤ ρ) {γ : Matrix (Fin 2) (Fin 2) K}
    (hd : ‖γ 1 1‖ ≤ 1) (hc : ‖γ 1 0‖ ≤ ρ) (ha : ‖γ 0 0‖ ≤ ρ) (hb : ‖γ 0 1‖ ≤ 1) :
    RowIntAt ρ (quadSeries γ) := by
  rw [quadSeries_eq]
  refine (((rowIntAt_monomial hρ0 ?_).add (rowIntAt_monomial hρ0 ?_)).sub
    (rowIntAt_monomial hρ0 ?_)).sub (rowIntAt_monomial hρ0 ?_)
  · simpa using hd
  · simpa using hc
  · simpa using ha
  · simpa using hb

/-- Coefficientwise integrality: every coefficient has norm `≤ 1` (the weight-`0` form
of the decay predicates; the level-uniform statement the weight generating functions
satisfy — recorded adversarial finding: full row decay is FALSE at `γ = 1`). -/
def CoeffInt (φ : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ p : Fin 2 →₀ ℕ, ‖coeff p φ‖ ≤ 1

omit [IsUltrametricDist K] in
lemma CoeffInt.of_rowIntAt (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {φ : MvPowerSeries (Fin 2) K}
    (hφ : RowIntAt ρ φ) : CoeffInt φ := fun p =>
  (hφ p).trans (pow_le_one₀ hρ0 hρ1)

omit [IsUltrametricDist K] in
lemma coeffInt_monomial {n : Fin 2 →₀ ℕ} {v : K} (hv : ‖v‖ ≤ 1) :
    CoeffInt (monomial n v : MvPowerSeries (Fin 2) K) := by
  intro p
  rw [coeff_monomial]
  split_ifs with h
  · exact hv
  · simp

lemma CoeffInt.add {φ ψ : MvPowerSeries (Fin 2) K} (hφ : CoeffInt φ) (hψ : CoeffInt ψ) :
    CoeffInt (φ + ψ) := fun p => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ p) (hψ p))

omit [IsUltrametricDist K] in
lemma CoeffInt.neg {φ : MvPowerSeries (Fin 2) K} (hφ : CoeffInt φ) : CoeffInt (-φ) :=
  fun p => by rw [map_neg, norm_neg]; exact hφ p

lemma CoeffInt.sub {φ ψ : MvPowerSeries (Fin 2) K} (hφ : CoeffInt φ) (hψ : CoeffInt ψ) :
    CoeffInt (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

lemma CoeffInt.mul {φ ψ : MvPowerSeries (Fin 2) K} (hφ : CoeffInt φ) (hψ : CoeffInt ψ) :
    CoeffInt (φ * ψ) := by
  intro p
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hφ _) (norm_nonneg _) (hψ _)

/-- Coefficientwise integrality passes to inverses with unit constant coefficient. -/
lemma CoeffInt.inv {φ : MvPowerSeries (Fin 2) K} (hφ : CoeffInt φ)
    (h1 : ‖constantCoeff φ‖ = 1) : CoeffInt φ⁻¹ := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N → ‖coeff p φ⁻¹‖ ≤ 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp
      rw [coeff_inv]
      split_ifs with hp0
      · subst hp0
        simp [norm_inv, h1]
      · rw [norm_mul, norm_neg, norm_inv, h1, inv_one, one_mul]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
          fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        split_ifs with hlt
        · have hne : x.1 ≠ 0 := by
            rintro h
            rw [h, zero_add] at hx
            exact absurd hx (ne_of_lt hlt)
          have hpos : 0 < x.1 0 + x.1 1 := by
            rcases Nat.eq_zero_or_pos (x.1 0 + x.1 1) with h | h
            · exact absurd (fin2_eq_zero (by omega) (by omega)) hne
            · exact h
          have e0 : x.1 0 + x.2 0 = p 0 := by rw [← hx]; simp
          have e1 : x.1 1 + x.2 1 = p 1 := by rw [← hx]; simp
          rw [norm_mul]
          exact mul_le_one₀ (hφ _) (norm_nonneg _)
            (ih (x.2 0 + x.2 1) (by omega) x.2 rfl)
        · simp
  exact fun p => key (p 0 + p 1) p rfl

/-- The **shifted** row bound `‖coeff p φ‖ ≤ ρ ^ (p 0 − p 1)` (truncated
`ℕ`-subtraction).  Between `RowIntAt ρ` (too strong on a general level element) and
`CoeffInt` (too weak to give column decay), this is exactly what the level supports and
exactly what `ofGenFun`'s column hypothesis needs: at a fixed column `r`, the bound is
`ρ^(m−r) → 0`. -/
def ShiftIntAt (ρ : ℝ) (φ : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ p : Fin 2 →₀ ℕ, ‖coeff p φ‖ ≤ ρ ^ (p 0 - p 1)

omit [IsUltrametricDist K] in
lemma ShiftIntAt.of_rowIntAt (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {φ : MvPowerSeries (Fin 2) K}
    (hφ : RowIntAt ρ φ) : ShiftIntAt ρ φ := fun p =>
  (hφ p).trans (pow_le_pow_of_le_one hρ0 hρ1 (Nat.sub_le _ _))

omit [IsUltrametricDist K] in
lemma shiftIntAt_monomial (hρ0 : 0 ≤ ρ) {n : Fin 2 →₀ ℕ} {v : K}
    (hv : ‖v‖ ≤ ρ ^ (n 0 - n 1)) :
    ShiftIntAt ρ (monomial n v : MvPowerSeries (Fin 2) K) := by
  intro p
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact hv
  · simp [pow_nonneg hρ0]

lemma ShiftIntAt.add {φ ψ : MvPowerSeries (Fin 2) K} (hφ : ShiftIntAt ρ φ)
    (hψ : ShiftIntAt ρ ψ) : ShiftIntAt ρ (φ + ψ) := fun p => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ p) (hψ p))

omit [IsUltrametricDist K] in
lemma ShiftIntAt.neg {φ : MvPowerSeries (Fin 2) K} (hφ : ShiftIntAt ρ φ) :
    ShiftIntAt ρ (-φ) := fun p => by
  rw [map_neg, norm_neg]; exact hφ p

lemma ShiftIntAt.sub {φ ψ : MvPowerSeries (Fin 2) K} (hφ : ShiftIntAt ρ φ)
    (hψ : ShiftIntAt ρ ψ) : ShiftIntAt ρ (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

omit [IsUltrametricDist K] in
/-- The shift weight is superadditive along the antidiagonal:
`(a−b) + (c−d) ≥ (a+c) − (b+d)` in `ℕ`. -/
private lemma shift_mul_le (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {x y : Fin 2 →₀ ℕ} :
    ρ ^ (x 0 - x 1) * ρ ^ (y 0 - y 1) ≤ ρ ^ ((x + y) 0 - (x + y) 1) := by
  rw [← pow_add]
  refine pow_le_pow_of_le_one hρ0 hρ1 ?_
  simp only [Finsupp.add_apply]
  omega

lemma ShiftIntAt.mul (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {φ ψ : MvPowerSeries (Fin 2) K}
    (hφ : ShiftIntAt ρ φ) (hψ : ShiftIntAt ρ ψ) : ShiftIntAt ρ (φ * ψ) := by
  intro p
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hρ0 _)
    fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [norm_mul]
  refine le_trans (mul_le_mul (hφ _) (hψ _) (norm_nonneg _) (pow_nonneg hρ0 _)) ?_
  rw [← hx]
  exact shift_mul_le hρ0 hρ1

lemma ShiftIntAt.inv (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {φ : MvPowerSeries (Fin 2) K}
    (hφ : ShiftIntAt ρ φ) (h1 : ‖constantCoeff φ‖ = 1) : ShiftIntAt ρ φ⁻¹ := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N →
      ‖coeff p φ⁻¹‖ ≤ ρ ^ (p 0 - p 1) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp
      rw [coeff_inv]
      split_ifs with hp0
      · subst hp0
        simp [norm_inv, h1]
      · rw [norm_mul, norm_neg, norm_inv, h1, inv_one, one_mul]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
          (pow_nonneg hρ0 _) fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        split_ifs with hlt
        · have hne : x.1 ≠ 0 := by
            rintro h
            rw [h, zero_add] at hx
            exact absurd hx (ne_of_lt hlt)
          have e0 : x.1 0 + x.2 0 = p 0 := by rw [← hx]; simp
          have e1 : x.1 1 + x.2 1 = p 1 := by rw [← hx]; simp
          have hpos : 0 < x.1 0 + x.1 1 := by
            rcases Nat.eq_zero_or_pos (x.1 0 + x.1 1) with h | h
            · exact absurd (fin2_eq_zero (by omega) (by omega)) hne
            · exact h
          rw [norm_mul]
          refine le_trans (mul_le_mul (hφ _) (ih (x.2 0 + x.2 1) (by omega) x.2 rfl)
            (norm_nonneg _) (pow_nonneg hρ0 _)) ?_
          rw [← pow_add]
          exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
        · simp [pow_nonneg hρ0]
  exact fun p => key (p 0 + p 1) p rfl

end TateFredholm
