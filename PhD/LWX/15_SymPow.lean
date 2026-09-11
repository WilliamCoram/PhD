/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«14_Touching»

/-!
# The `Sym^k` action on polynomials of degree `≤ k`

The classical weight-`(k+2)` action of an *arbitrary* matrix `γ = (a b; c d)` on polynomials of
degree `≤ k`,

  `(f ∣ γ)(z) = (cz + d)^k · f((az + b)/(cz + d))`,

read on coefficient sequences: the `i`-th basis vector `z^i` goes to the polynomial
`(cz+d)^{k−i}(az+b)^i` ([Bu04, §4]'s `Sym^k`, [LWX, (2.3.2)] at a classical character with the
nebentypus factor stripped).  Unlike the halo weight's `kappaSlash`, this needs no unit
condition on `d`: it is defined for every `γ`, in particular for the Atkin–Lehner element and
for the `U'_p`-representatives `(1 b; 0 p)`, which is why the classical layer of the Atkin–Lehner
argument lives here.

* `LWX.hsub` — the homogeneous substitution `P ↦ ∑_{i ≤ k} P_i · L^{k−i} N^i`, multiplicative on
  products of polynomials (`hsub_mul`), which is what makes `symAct` a right action.
* `LWX.symAct` — the action, as a continuous linear map on `c(ℕ, K)`.
* `LWX.symAct_mul` — the right-action law `(f ∣ γ) ∣ γ' = f ∣ (γ γ')` on polynomials.
* `LWX.kappaSlash_eq_smul_symAct_of_shape` — at a classical-shape weight, `kappaSlash` is the
  nebentypus constant times `symAct`: the bridge to the disc model.
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat TateFredholm

noncomputable section

namespace LWX

variable {K : Type*} [NontriviallyNormedField K]

/-! ### The homogeneous substitution -/

/-- **The homogeneous substitution** `hsub k P N L = ∑_{i ≤ k} P_i · L^{k−i} N^i`: read `P` (a
polynomial of degree `≤ k`) as the binary form `∑ P_i X^i Y^{k−i}` and substitute `(N, L)`. -/
def hsub (k : ℕ) (P N L : PowerSeries K) : PowerSeries K :=
  ∑ i ∈ Finset.range (k + 1), PowerSeries.C (PowerSeries.coeff i P) * (L ^ (k - i) * N ^ i)

/-- The substitution is multiplicative on products of polynomials of the declared degrees
(the Cauchy product of the coefficients matches the exponent bookkeeping). -/
theorem hsub_mul (k₁ k₂ : ℕ) {P Q : PowerSeries K}
    (hP : ∀ i, k₁ < i → PowerSeries.coeff i P = 0) (hQ : ∀ i, k₂ < i → PowerSeries.coeff i Q = 0)
    (N L : PowerSeries K) :
    hsub (k₁ + k₂) (P * Q) N L = hsub k₁ P N L * hsub k₂ Q N L := by
  classical
  have hdisj : (↑(Finset.range (k₁ + k₂ + 1)) : Set ℕ).PairwiseDisjoint
      (fun n : ℕ => Finset.antidiagonal n) := by
    intro m _ m' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_antidiagonal]
    intro q hq hq'
    exact hne (hq ▸ hq')
  have hLHS : hsub (k₁ + k₂) (P * Q) N L
      = ∑ q ∈ (Finset.range (k₁ + k₂ + 1)).biUnion (fun n : ℕ => Finset.antidiagonal n),
          PowerSeries.C (PowerSeries.coeff q.1 P * PowerSeries.coeff q.2 Q) *
            (L ^ (k₁ + k₂ - (q.1 + q.2)) * N ^ (q.1 + q.2)) := by
    rw [Finset.sum_biUnion hdisj, hsub]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_antidiagonal] at hq
    rw [hq]
  have hRHS : hsub k₁ P N L * hsub k₂ Q N L
      = ∑ q ∈ Finset.range (k₁ + 1) ×ˢ Finset.range (k₂ + 1),
          PowerSeries.C (PowerSeries.coeff q.1 P * PowerSeries.coeff q.2 Q) *
            (L ^ (k₁ + k₂ - (q.1 + q.2)) * N ^ (q.1 + q.2)) := by
    rw [hsub, hsub, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi hj
    rw [map_mul, show k₁ + k₂ - (i + j) = k₁ - i + (k₂ - j) by omega, pow_add]
    ring
  rw [hLHS, hRHS]
  refine (Finset.sum_subset (fun q hq => ?_) (fun q _ hq => ?_)).symm
  · simp only [Finset.mem_product, Finset.mem_range] at hq
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
    exact ⟨q.1 + q.2, by omega, rfl⟩
  · simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt, Nat.succ_le_iff] at hq
    rcases hq with h | h
    · rw [hP q.1 h, zero_mul, map_zero, zero_mul]
    · rw [hQ q.2 h, mul_zero, map_zero, zero_mul]

/-- The substitution of the linear factor `cz + d` is `c·N + d·L`. -/
theorem hsub_linX (γ : Matrix (Fin 2) (Fin 2) K) (N L : PowerSeries K) :
    hsub 1 (linX γ) N L = PowerSeries.C (γ 1 0) * N + PowerSeries.C (γ 1 1) * L := by
  have h0 : PowerSeries.coeff 0 (linX γ) = γ 1 1 := by simp [linX]
  have h1 : PowerSeries.coeff 1 (linX γ) = γ 1 0 := by simp [linX]
  rw [hsub, Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
  simp only [Nat.sub_zero, Nat.sub_self, pow_zero, pow_one, mul_one, one_mul]
  ring

/-- The substitution of the numerator `az + b` is `a·N + b·L`. -/
theorem hsub_numX (γ : Matrix (Fin 2) (Fin 2) K) (N L : PowerSeries K) :
    hsub 1 (numX γ) N L = PowerSeries.C (γ 0 0) * N + PowerSeries.C (γ 0 1) * L := by
  have h0 : PowerSeries.coeff 0 (numX γ) = γ 0 1 := by simp [numX]
  have h1 : PowerSeries.coeff 1 (numX γ) = γ 0 0 := by simp [numX]
  rw [hsub, Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
  simp only [Nat.sub_zero, Nat.sub_self, pow_zero, pow_one, mul_one, one_mul]
  ring

/-- A product of power series with coefficients vanishing above `k₁`, `k₂` has coefficients
vanishing above `k₁ + k₂`. -/
theorem coeff_mul_eq_zero_of_lt {k₁ k₂ : ℕ} {P Q : PowerSeries K}
    (hP : ∀ i, k₁ < i → PowerSeries.coeff i P = 0) (hQ : ∀ j, k₂ < j → PowerSeries.coeff j Q = 0)
    {m : ℕ} (hm : k₁ + k₂ < m) : PowerSeries.coeff m (P * Q) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.mem_antidiagonal] at hq
  rcases lt_or_ge k₁ q.1 with h | h
  · rw [hP q.1 h, zero_mul]
  · rw [hQ q.2 (by omega), mul_zero]

/-- A power of a power series with coefficients vanishing above `k` has coefficients vanishing
above `n·k`. -/
theorem coeff_pow_eq_zero_of_lt {k : ℕ} {P : PowerSeries K}
    (hP : ∀ i, k < i → PowerSeries.coeff i P = 0) (n : ℕ) {m : ℕ} (hm : n * k < m) :
    PowerSeries.coeff m (P ^ n) = 0 := by
  induction n generalizing m with
  | zero =>
    rw [zero_mul] at hm
    rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega)]
  | succ n ih =>
    rw [Nat.succ_mul] at hm
    rw [pow_succ]
    exact coeff_mul_eq_zero_of_lt (fun i hi => ih hi) hP hm

/-- A polynomial of degree `≤ 1` has vanishing coefficients above `1`. -/
theorem coeff_linear_eq_zero {a b : K} {m : ℕ} (hm : 1 < m) :
    PowerSeries.coeff m (PowerSeries.C a + PowerSeries.C b * PowerSeries.X) = 0 := by
  rw [map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
    if_neg (by omega), if_neg (by omega), mul_zero, add_zero]

/-- `cz + d` has vanishing coefficients above `1`. -/
theorem coeff_linX_eq_zero (γ : Matrix (Fin 2) (Fin 2) K) {m : ℕ} (hm : 1 < m) :
    PowerSeries.coeff m (linX γ) = 0 := by
  rw [linX]; exact coeff_linear_eq_zero hm

/-- `az + b` has vanishing coefficients above `1`. -/
theorem coeff_numX_eq_zero (γ : Matrix (Fin 2) (Fin 2) K) {m : ℕ} (hm : 1 < m) :
    PowerSeries.coeff m (numX γ) = 0 := by
  rw [numX]; exact coeff_linear_eq_zero hm

/-- The substitution of a power of a polynomial of degree `≤ 1` is the power of the
substitution (`hsub_mul` iterated). -/
theorem hsub_pow_of_degree_le_one (n : ℕ) {P : PowerSeries K}
    (hP : ∀ i, 1 < i → PowerSeries.coeff i P = 0) (N L : PowerSeries K) :
    hsub n (P ^ n) N L = (hsub 1 P N L) ^ n := by
  induction n with
  | zero => simp [hsub]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact hsub_mul n 1 (fun i hi => coeff_pow_eq_zero_of_lt hP n (by rw [mul_one]; exact hi))
      hP N L

/-- **The cocycle**: substituting `(numX γ', linX γ')` into the `i`-th column polynomial of `γ`
gives the `i`-th column polynomial of `γ * γ'`. -/
theorem hsub_linX_pow_mul_numX_pow (k i : ℕ) (hi : i ≤ k) (γ γ' : Matrix (Fin 2) (Fin 2) K) :
    hsub k (linX γ ^ (k - i) * numX γ ^ i) (numX γ') (linX γ')
      = linX (γ * γ') ^ (k - i) * numX (γ * γ') ^ i := by
  have hl : PowerSeries.C (γ 1 0) * numX γ' + PowerSeries.C (γ 1 1) * linX γ' = linX (γ * γ') :=
    (WeightSeries.linX_mul γ' γ).symm
  have hn : PowerSeries.C (γ 0 0) * numX γ' + PowerSeries.C (γ 0 1) * linX γ' = numX (γ * γ') :=
    (WeightSeries.numX_mul γ' γ).symm
  obtain ⟨j, rfl⟩ : ∃ j, k = j + i := ⟨k - i, by omega⟩
  have hlz : ∀ m, 1 < m → PowerSeries.coeff m (linX γ) = 0 := fun _ hm => coeff_linX_eq_zero γ hm
  have hnz : ∀ m, 1 < m → PowerSeries.coeff m (numX γ) = 0 := fun _ hm => coeff_numX_eq_zero γ hm
  rw [Nat.add_sub_cancel,
    hsub_mul j i (fun m hm => coeff_pow_eq_zero_of_lt hlz j (by rw [mul_one]; exact hm))
      (fun m hm => coeff_pow_eq_zero_of_lt hnz i (by rw [mul_one]; exact hm)),
    hsub_pow_of_degree_le_one j hlz, hsub_pow_of_degree_le_one i hnz, hsub_linX, hsub_numX, hl, hn]

/-- The `i`-th column polynomial `(cz+d)^{k−i}(az+b)^i` has degree `≤ k`. -/
theorem coeff_linX_pow_mul_numX_pow_eq_zero (k i : ℕ) (hi : i ≤ k)
    (γ : Matrix (Fin 2) (Fin 2) K) {j : ℕ} (hj : k < j) :
    PowerSeries.coeff j (linX γ ^ (k - i) * numX γ ^ i) = 0 := by
  refine coeff_mul_eq_zero_of_lt
    (fun m hm => coeff_pow_eq_zero_of_lt (fun _ h => coeff_linX_eq_zero γ h) (k - i)
      (by rw [mul_one]; exact hm))
    (fun m hm => coeff_pow_eq_zero_of_lt (fun _ h => coeff_numX_eq_zero γ h) i
      (by rw [mul_one]; exact hm)) ?_
  omega

/-! ### The action -/

variable [IsUltrametricDist K] [CompleteSpace K]

/-- The coefficient sequence of a power series with coefficients vanishing above `k`, as an
element of `c(ℕ, K)`. -/
def polySeq (k : ℕ) (P : PowerSeries K) (hP : ∀ i, k < i → PowerSeries.coeff i P = 0) :
    c(ℕ, K) :=
  cSpace.ofTendsto (fun j => PowerSeries.coeff j P) (by
    refine tendsto_const_nhds.congr' ?_
    rw [Filter.EventuallyEq, Filter.eventually_cofinite]
    refine (Set.finite_Iic k).subset fun j hj => ?_
    rw [Set.mem_Iic]
    by_contra hcon
    exact hj (by simp [hP j (not_le.mp hcon)]))

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem polySeq_apply (k : ℕ) (P : PowerSeries K) (hP : ∀ i, k < i → PowerSeries.coeff i P = 0)
    (j : ℕ) : polySeq k P hP j = PowerSeries.coeff j P := rfl

variable (K) in
/-- **The `Sym^k` action** of `γ` on coefficient sequences: `z^i ↦ (cz+d)^{k−i}(az+b)^i` for
`i ≤ k`, and `z^i ↦ 0` for `i > k`.  A finite-rank continuous linear map. -/
def symAct (k : ℕ) (γ : Matrix (Fin 2) (Fin 2) K) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ∑ i ∈ (Finset.range (k + 1)).attach, (cSpace.evalCLM (i : ℕ)).smulRight
    (polySeq k (linX γ ^ (k - (i : ℕ)) * numX γ ^ (i : ℕ)) fun _ hj =>
      coeff_linX_pow_mul_numX_pow_eq_zero k i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp i.2)) γ hj)

theorem symAct_apply (k : ℕ) (γ : Matrix (Fin 2) (Fin 2) K) (f : c(ℕ, K)) (j : ℕ) :
    symAct K k γ f j
      = ∑ i ∈ Finset.range (k + 1), f i * PowerSeries.coeff j (linX γ ^ (k - i) * numX γ ^ i) := by
  rw [symAct, _root_.sum_apply, cSpace.sum_apply,
    ← Finset.sum_attach (Finset.range (k + 1))
      (fun i => f i * PowerSeries.coeff j (linX γ ^ (k - i) * numX γ ^ i))]
  rfl

/-- The action lands in polynomials of degree `≤ k`. -/
theorem symAct_mem_polySubmodule (k : ℕ) (γ : Matrix (Fin 2) (Fin 2) K) (f : c(ℕ, K)) :
    symAct K k γ f ∈ polySubmodule K k := by
  intro j hj
  rw [symAct_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [coeff_linX_pow_mul_numX_pow_eq_zero k i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) γ hj,
    mul_zero]

/-- **The right-action law** on polynomials: `(f ∣ γ) ∣ γ' = f ∣ (γ γ')` (`hsub_linX_pow_mul_numX_pow`). -/
theorem symAct_mul (k : ℕ) (γ γ' : Matrix (Fin 2) (Fin 2) K) {f : c(ℕ, K)}
    (_hf : f ∈ polySubmodule K k) :
    symAct K k γ' (symAct K k γ f) = symAct K k (γ * γ') f := by
  refine DFunLike.ext _ _ fun j => ?_
  have key : ∀ i ≤ k, ∑ i' ∈ Finset.range (k + 1),
      PowerSeries.coeff i' (linX γ ^ (k - i) * numX γ ^ i) *
        PowerSeries.coeff j (linX γ' ^ (k - i') * numX γ' ^ i')
      = PowerSeries.coeff j (linX (γ * γ') ^ (k - i) * numX (γ * γ') ^ i) := by
    intro i hi
    rw [← hsub_linX_pow_mul_numX_pow k i hi γ γ', hsub, map_sum]
    exact Finset.sum_congr rfl fun i' _ => by rw [PowerSeries.coeff_C_mul]
  rw [symAct_apply, symAct_apply]
  simp_rw [symAct_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← key i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i' _ => by ring

/-- The identity acts trivially on polynomials. -/
theorem symAct_one (k : ℕ) {f : c(ℕ, K)} (hf : f ∈ polySubmodule K k) :
    symAct K k 1 f = f := by
  refine DFunLike.ext _ _ fun j => ?_
  have hl : linX (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [linX]; simp
  have hn : numX (1 : Matrix (Fin 2) (Fin 2) K) = PowerSeries.X := by
    rw [numX]; simp
  rw [symAct_apply]
  simp only [hl, hn, one_pow, one_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hjk : j < k + 1
  · rw [if_pos (Finset.mem_range.mpr hjk)]
  · rw [if_neg (fun h => hjk (Finset.mem_range.mp h))]
    exact (hf j (by omega)).symm

/-- A scalar matrix acts by its `k`-th power. -/
theorem symAct_smul_one (k : ℕ) (x : K) {f : c(ℕ, K)} (hf : f ∈ polySubmodule K k) :
    symAct K k (x • (1 : Matrix (Fin 2) (Fin 2) K)) f = x ^ k • f := by
  refine DFunLike.ext _ _ fun j => ?_
  have hl : linX (x • (1 : Matrix (Fin 2) (Fin 2) K)) = PowerSeries.C x := by
    rw [linX]; simp
  have hn : numX (x • (1 : Matrix (Fin 2) (Fin 2) K)) = PowerSeries.C x * PowerSeries.X := by
    rw [numX]; simp
  have key : ∀ i ∈ Finset.range (k + 1),
      f i * PowerSeries.coeff j (linX (x • (1 : Matrix (Fin 2) (Fin 2) K)) ^ (k - i) *
        numX (x • (1 : Matrix (Fin 2) (Fin 2) K)) ^ i)
        = x ^ k * (f i * (if j = i then 1 else 0)) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have hcol : linX (x • (1 : Matrix (Fin 2) (Fin 2) K)) ^ (k - i) *
        numX (x • (1 : Matrix (Fin 2) (Fin 2) K)) ^ i
          = PowerSeries.C (x ^ k) * PowerSeries.X ^ i := by
      rw [hl, hn, mul_pow, ← map_pow, ← map_pow, ← mul_assoc, ← map_mul, ← pow_add,
        Nat.sub_add_cancel hi]
    rw [hcol, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    ring
  rw [symAct_apply, Finset.sum_congr rfl key, ← Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hjk : j < k + 1
  · rw [if_pos (Finset.mem_range.mpr hjk)]
    rfl
  · rw [if_neg (fun h => hjk (Finset.mem_range.mp h)), mul_zero]
    rw [show ((x ^ k • f) j) = x ^ k * f j from rfl, hf j (by omega), mul_zero]

/-! ### The bridge to the disc model -/

variable {UK : Subgroup Kˣ} {ρ : ℝ}

/-- **At a classical-shape matrix, `kappaSlash` is the constant times `symAct`**
(`kappaSlash_apply` and `autFactor_mul_mobius_pow_of_shape`, column by column). -/
theorem kappaSlash_eq_smul_symAct_of_shape {S : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    (κ : AnalyticWeight UK S ρ) (g : S) {k : ℕ} {u : K}
    (hA : κ.toWeightSeries.autFactor g.1 * linX g.1 = PowerSeries.C u * linX g.1 ^ (k + 1))
    {f : c(ℕ, K)} (hf : f ∈ polySubmodule K k) :
    κ.kappaSlash g f = u • symAct K k g.1 f := by
  refine DFunLike.ext _ _ fun j => ?_
  rw [AnalyticWeight.kappaSlash_def, WeightSeries.kappaSlash_apply,
    tsum_eq_sum (s := Finset.range (k + 1))
      (fun i hi => by rw [hf i (by simpa using hi), mul_zero]),
    show ((u • symAct K k g.1 f) j) = u * symAct K k g.1 f j from rfl, symAct_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [autFactor_mul_mobius_pow_of_shape κ (κ.toWeightSeries.bounds.d_ne_zero g.2) hA
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)), PowerSeries.coeff_C_mul]
  ring

end LWX

end
