/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«15_StepThree»
import PhD.Main.TateFredholm.«07_Conjugation»

/-!
# Hypothesis H2 from the classical shapes

[LWX, §3.23 Step III] uses the exact sequence
`0 → S^D_{k+2}(K^p Iw_{q²}, ψ) → S^{D,†}_{(k,ψ)} → S^{D,†}_{(−k−2,ψ)} → 0`, "equivariant for the
`U_p`-action on the first two spaces, and the `p^{k+1}U_p`-action on the third", to conclude
that the characteristic power series of `U_p` on the complement of the classical subspace is
that of `p^{k+1}U_p` on the target space.  `15_StepThree.lean` records exactly this determinant
identity as the hypothesis `IsThetaExact` (H2).  This file discharges it from the classical
shapes of the two weights.

**Route.**  On the disc model `θ^{k+1} = D ∘ σ`, where `σ = shiftBlock` is the coordinate shift
`c ↦ (j ↦ c (j + k + 1))` and `D = diagBlock` the diagonal `diag((j+1)⋯(j+k+1))`
(`thetaBlock_eq_diagBlock_comp_shiftBlock`).  The shift has the section `τ = insertBlock`
(`e_j ↦ e_{j+k+1}`), with `σ ∘ τ = 1` and `τ ∘ σ = 1 − π_{≤ k}`, the projection off the
classical coordinates.  Composing the intertwining `θ ∘ U = p^{k+1} U' ∘ θ` (a consequence of
the classical shapes, `thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape`) with `τ` on the
right gives `D ∘ (σ U τ) = (p^{k+1} U') ∘ D`: the operators `σ U τ` and `p^{k+1}U'` are
*diagonally intertwined*, so every principal minor agrees
(`TateFredholm.charPowerSeries_eq_of_diag_intertwine`).  Finally
`det(1 − X·U(1 − π)) = det(1 − X·(Uτ)σ) = det(1 − X·σ(Uτ))` (`charPowerSeries_comm`), and
`det(1 − X·(c • U')) = det(1 − cX·U')` (`TateFredholm.charPowerSeries_smul`).

**What is and is not claimed.**  `D` is *not* invertible as a bounded operator (its inverse
`diag(1/((j+1)⋯(j+k+1)))` is unbounded), so `θ` is not surjective onto the target model at a
fixed radius and no exactness of spaces is asserted; the diagonal intertwining of matrix
coefficients is exactly what the Fredholm determinant sees, and is exactly what Step III
consumes.  No Jacquet–Langlands input (see `.mathlib-quality/lwx-stepone/JL-AUDIT.md`, §"The
other hard input": H2 is locally-analytic representation theory in [LWX], cited to [Jo11]; the
disc-model argument here replaces that import).
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The shift, its section, and the diagonal on one disc -/

variable (K) in
/-- **The shift** `σ^r : c ↦ (j ↦ c (j + r))` on Taylor coefficients (matrix
`if i = j + r then 1 else 0`): the coordinate part of `θ^r`. -/
def shiftOne (r : ℕ) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun j i => if i = j + r then 1 else 0)
    ⟨1, fun j i => by split_ifs <;> simp⟩
    (fun i => by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Set.finite_singleton (i - r)).subset fun j hj => ?_
      rw [Set.mem_singleton_iff]
      by_contra hcon
      exact hj (by simp [show i ≠ j + r by omega]))

variable (K) in
/-- **The section of the shift** `τ^r : e_j ↦ e_{j+r}` (matrix `if j = i + r then 1 else 0`):
`σ^r ∘ τ^r = 1` and `τ^r ∘ σ^r = 1 − π_{<r}`. -/
def insertOne (r : ℕ) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun j i => if j = i + r then 1 else 0)
    ⟨1, fun j i => by split_ifs <;> simp⟩
    (fun i => by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Set.finite_singleton (i + r)).subset fun j hj => ?_
      rw [Set.mem_singleton_iff]
      by_contra hcon
      exact hj (by simp [hcon]))

variable (K) in
/-- **The diagonal** `D^r = diag((j+1)(j+2)⋯(j+r))` of the falling factorials: the scalar part
of `θ^r`. -/
def diagOne (r : ℕ) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun j i => if i = j then ((Nat.descFactorial (j + r) r : ℕ) : K) else 0)
    ⟨1, fun j i => by
      split_ifs
      · exact IsUltrametricDist.norm_natCast_le_one K _
      · simp⟩
    (fun i => by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Set.finite_singleton i).subset fun j hj => ?_
      rw [Set.mem_singleton_iff]
      by_contra hcon
      exact hj (by simp [Ne.symm hcon]))

omit [CharZero K] in
/-- The matrix of the shift: `σ^r_{ji} = [i = j + r]`. -/
theorem matrixCoeff_shiftOne (r j i : ℕ) :
    matrixCoeff (shiftOne K r) j i = if i = j + r then 1 else 0 :=
  matrixCoeff_ofCoeffs _ _ _ j i

omit [CharZero K] in
/-- The matrix of the section: `τ^r_{ji} = [j = i + r]`. -/
theorem matrixCoeff_insertOne (r j i : ℕ) :
    matrixCoeff (insertOne K r) j i = if j = i + r then 1 else 0 :=
  matrixCoeff_ofCoeffs _ _ _ j i

omit [CharZero K] in
/-- The matrix of the diagonal: `D^r_{ji} = [i = j]·(j+1)⋯(j+r)`. -/
theorem matrixCoeff_diagOne (r j i : ℕ) :
    matrixCoeff (diagOne K r) j i
      = if i = j then ((Nat.descFactorial (j + r) r : ℕ) : K) else 0 :=
  matrixCoeff_ofCoeffs _ _ _ j i

omit [CharZero K] in
/-- `θ^r = D^r ∘ σ^r` on one disc: `(θ^r c) j = (j+1)⋯(j+r) · c (j+r)`. -/
theorem thetaOne_eq_diagOne_comp_shiftOne (r : ℕ) :
    thetaOne K r = (diagOne K r).comp (shiftOne K r) := by
  refine ext_matrixCoeff fun j i => ?_
  rw [matrixCoeff_comp,
    tsum_eq_single j (fun l hl => by rw [matrixCoeff_diagOne, if_neg hl, mul_zero]),
    matrixCoeff_diagOne, if_pos rfl, matrixCoeff_shiftOne, matrixCoeff_thetaOne]
  split_ifs <;> simp

omit [CharZero K] in
/-- `σ^r ∘ τ^r = 1`. -/
theorem shiftOne_comp_insertOne (r : ℕ) : (shiftOne K r).comp (insertOne K r) = 1 := by
  refine ext_matrixCoeff fun j i => ?_
  rw [matrixCoeff_comp, matrixCoeff_one,
    tsum_eq_single (i + r) (fun l hl => by rw [matrixCoeff_insertOne, if_neg hl, zero_mul]),
    matrixCoeff_insertOne, if_pos rfl, one_mul, matrixCoeff_shiftOne]
  by_cases h : j = i
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

omit [CharZero K] in
/-- `τ^r ∘ σ^r = 1 − π_{<r}`: the section composed with the shift kills exactly the first `r`
coordinates. -/
theorem insertOne_comp_shiftOne (r : ℕ) :
    (insertOne K r).comp (shiftOne K r) = 1 - truncation (Finset.range r) := by
  refine ext_matrixCoeff fun j i => ?_
  rw [matrixCoeff_comp, matrixCoeff_sub, matrixCoeff_one, matrixCoeff_truncation]
  simp only [Finset.mem_range]
  rcases le_or_gt r i with hri | hri
  · have hii : i - r + r = i := by omega
    rw [tsum_eq_single (i - r) (fun l hl => by
        rw [matrixCoeff_shiftOne, if_neg (by omega), zero_mul]),
      matrixCoeff_shiftOne, if_pos hii.symm, one_mul, matrixCoeff_insertOne, hii]
    by_cases h : j = i
    · subst h
      rw [if_pos rfl, if_neg (by omega), sub_zero]
    · rw [if_neg h, if_neg (fun hc => h hc.1), sub_zero]
  · rw [tsum_congr (fun l => by rw [matrixCoeff_shiftOne, if_neg (by omega), zero_mul]),
      tsum_zero]
    by_cases h : j = i
    · subst h
      rw [if_pos rfl, if_pos ⟨rfl, hri⟩, sub_self]
    · rw [if_neg h, if_neg (fun hc => h hc.1), sub_zero]

/-! ### The same on the block model -/

variable (p ι K) in
/-- The shift on the block model (`shiftOne` in every disc of every class). -/
def shiftBlock (h r : ℕ) : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K) :=
  blockMap (σ := ι) (blockMap (σ := ZMod (p ^ h)) (shiftOne K r))

variable (p ι K) in
/-- The section of the shift on the block model. -/
def insertBlock (h r : ℕ) : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K) :=
  blockMap (σ := ι) (blockMap (σ := ZMod (p ^ h)) (insertOne K r))

variable (p ι K) in
/-- The diagonal of falling factorials on the block model. -/
def diagBlock (h r : ℕ) : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K) :=
  blockMap (σ := ι) (blockMap (σ := ZMod (p ^ h)) (diagOne K r))

omit [CharZero K] in
theorem matrixCoeff_shiftBlock (h r : ℕ) (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff (shiftBlock p ι K h r) x y = if y = (x.1, (x.2.1, x.2.2 + r)) then 1 else 0 := by
  obtain ⟨i₁, a₁, j₁⟩ := x
  obtain ⟨i₂, a₂, j₂⟩ := y
  simp only [shiftBlock, matrixCoeff_blockMap, matrixCoeff_shiftOne]
  by_cases hi : i₁ = i₂
  · subst hi
    by_cases ha : a₁ = a₂
    · subst ha
      by_cases hj : j₂ = j₁ + r <;> simp [hj]
    · simp [ha, Ne.symm ha]
  · simp [hi, Ne.symm hi]

omit [CharZero K] in
theorem matrixCoeff_insertBlock (h r : ℕ) (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff (insertBlock p ι K h r) x y
      = if x = (y.1, (y.2.1, y.2.2 + r)) then 1 else 0 := by
  obtain ⟨i₁, a₁, j₁⟩ := x
  obtain ⟨i₂, a₂, j₂⟩ := y
  simp only [insertBlock, matrixCoeff_blockMap, matrixCoeff_insertOne]
  by_cases hi : i₁ = i₂
  · subst hi
    by_cases ha : a₁ = a₂
    · subst ha
      by_cases hj : j₁ = j₂ + r <;> simp [hj]
    · simp [ha]
  · simp [hi]

omit [CharZero K] in
theorem matrixCoeff_diagBlock (h r : ℕ) (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff (diagBlock p ι K h r) x y
      = if x = y then ((Nat.descFactorial (x.2.2 + r) r : ℕ) : K) else 0 := by
  obtain ⟨i₁, a₁, j₁⟩ := x
  obtain ⟨i₂, a₂, j₂⟩ := y
  simp only [diagBlock, matrixCoeff_blockMap, matrixCoeff_diagOne]
  by_cases hi : i₁ = i₂
  · subst hi
    by_cases ha : a₁ = a₂
    · subst ha
      by_cases hj : j₂ = j₁
      · simp [hj]
      · simp [hj, Ne.symm hj]
    · simp [ha]
  · simp [hi]

omit [CharZero K] in
/-- `θ^r = D^r ∘ σ^r` on the block model (`blockMap_comp` twice). -/
theorem thetaBlock_eq_diagBlock_comp_shiftBlock (h r : ℕ) :
    thetaBlock (p := p) (K := K) (ι := ι) h r
      = (diagBlock p ι K h r).comp (shiftBlock p ι K h r) := by
  rw [thetaBlock, thetaDisc, diagBlock, shiftBlock, blockMap_comp, blockMap_comp,
    thetaOne_eq_diagOne_comp_shiftOne]

omit [CharZero K] in
/-- `σ ∘ τ = 1` on the block model. -/
theorem shiftBlock_comp_insertBlock (h r : ℕ) :
    (shiftBlock p ι K h r).comp (insertBlock p ι K h r) = 1 := by
  simp only [shiftBlock, insertBlock, blockMap_comp, shiftOne_comp_insertOne,
    ContinuousLinearMap.one_def, blockMap_id]

omit [CharZero K] in
/-- `τ ∘ σ = 1 − π_{≤ k}` on the block model, for `r = k + 1`: the section composed with the
shift is the projection off the classical coordinates. -/
theorem insertBlock_comp_shiftBlock (h k : ℕ) :
    (insertBlock p ι K h (k + 1)).comp (shiftBlock p ι K h (k + 1))
      = 1 - truncation (classicalSupport p ι h k) := by
  rw [insertBlock, shiftBlock, blockMap_comp, blockMap_comp, insertOne_comp_shiftOne]
  refine ext_matrixCoeff fun x y => ?_
  obtain ⟨i₁, a₁, j₁⟩ := x
  obtain ⟨i₂, a₂, j₂⟩ := y
  simp only [matrixCoeff_blockMap, matrixCoeff_sub, matrixCoeff_one, matrixCoeff_truncation,
    mem_classicalSupport_iff, Finset.mem_range]
  by_cases hi : i₁ = i₂
  · subst hi
    by_cases ha : a₁ = a₂
    · subst ha
      by_cases hj : j₁ = j₂
      · simp [hj]
      · simp [hj]
    · simp [ha]
  · simp [hi]

omit [CharZero K] in
/-- Left composition with the diagonal scales the rows. -/
theorem matrixCoeff_diagBlock_comp (h r : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff ((diagBlock p ι K h r).comp T) x y
      = ((Nat.descFactorial (x.2.2 + r) r : ℕ) : K) * matrixCoeff T x y := by
  have hsingle : ∀ z : ι × (ZMod (p ^ h) × ℕ), z ≠ x →
      matrixCoeff T z y * matrixCoeff (diagBlock p ι K h r) x z = 0 := by
    intro z hz
    rw [matrixCoeff_diagBlock, if_neg (Ne.symm hz), mul_zero]
  rw [matrixCoeff_comp, tsum_eq_single x hsingle, matrixCoeff_diagBlock, if_pos rfl, mul_comm]

omit [CharZero K] in
/-- Right composition with the diagonal scales the columns. -/
theorem matrixCoeff_comp_diagBlock (h r : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff (T.comp (diagBlock p ι K h r)) x y
      = matrixCoeff T x y * ((Nat.descFactorial (y.2.2 + r) r : ℕ) : K) := by
  have hsingle : ∀ z : ι × (ZMod (p ^ h) × ℕ), z ≠ y →
      matrixCoeff (diagBlock p ι K h r) z y * matrixCoeff T x z = 0 := by
    intro z hz
    rw [matrixCoeff_diagBlock, if_neg hz, zero_mul]
  rw [matrixCoeff_comp, tsum_eq_single y hsingle, matrixCoeff_diagBlock, if_pos rfl, mul_comm]

/-! ### The determinant identity from an intertwining -/

omit [CharZero K] in
/-- **Transport of the intertwining along the section**: from `θ ∘ U = c • U' ∘ θ` and
`θ = D ∘ σ`, `σ ∘ τ = 1`, we get `D ∘ (σ U τ) = (c • U') ∘ D`. -/
theorem diagBlock_comp_eq_of_intertwine (h k : ℕ)
    {U U' : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)} (c : K)
    (hint : (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp U
      = c • (U'.comp (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)))) :
    (diagBlock p ι K h (k + 1)).comp
        ((shiftBlock p ι K h (k + 1)).comp (U.comp (insertBlock p ι K h (k + 1))))
      = (c • U').comp (diagBlock p ι K h (k + 1)) := by
  have hτ : (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp
      (insertBlock p ι K h (k + 1)) = diagBlock p ι K h (k + 1) := by
    rw [thetaBlock_eq_diagBlock_comp_shiftBlock, ContinuousLinearMap.comp_assoc,
      shiftBlock_comp_insertBlock, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  have h1 : ((thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp U).comp
      (insertBlock p ι K h (k + 1))
      = (c • (U'.comp (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)))).comp
        (insertBlock p ι K h (k + 1)) := by rw [hint]
  rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc, hτ] at h1
  rw [← ContinuousLinearMap.comp_assoc, ← thetaBlock_eq_diagBlock_comp_shiftBlock,
    ContinuousLinearMap.smul_comp]
  exact h1

/-- **The shifted operator and the scaled target have the same Fredholm determinant**: they are
diagonally intertwined by the units `(j+1)⋯(j+k+1)` (`charPowerSeries_eq_of_diag_intertwine`). -/
theorem charPowerSeries_shiftBlock_comp_eq_of_intertwine (h k : ℕ)
    {U U' : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)} (c : K)
    (hint : (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp U
      = c • (U'.comp (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)))) :
    charPowerSeries ((shiftBlock p ι K h (k + 1)).comp (U.comp (insertBlock p ι K h (k + 1))))
      = charPowerSeries (c • U') := by
  refine charPowerSeries_eq_of_diag_intertwine
    (fun x => ((Nat.descFactorial (x.2.2 + (k + 1)) (k + 1) : ℕ) : K))
    (fun x => isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2
      (Nat.descFactorial_pos.2 (Nat.le_add_left _ _)).ne')) fun x y => ?_
  have hxy : matrixCoeff ((diagBlock p ι K h (k + 1)).comp
        ((shiftBlock p ι K h (k + 1)).comp (U.comp (insertBlock p ι K h (k + 1))))) x y
      = matrixCoeff ((c • U').comp (diagBlock p ι K h (k + 1))) x y := by
    rw [diagBlock_comp_eq_of_intertwine h k c hint]
  rw [matrixCoeff_diagBlock_comp, matrixCoeff_comp_diagBlock] at hxy
  exact hxy

omit [CharZero K] in
/-- `det(1 − X·U(1 − π)) = det(1 − X·σ U τ)`: `1 − π = τσ` and the trace property
`charPowerSeries_comm`. -/
theorem charPowerSeries_comp_one_sub_truncation_eq (h k : ℕ)
    {U : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hU : IsCompactoid U) :
    charPowerSeries (U.comp (1 - truncation (classicalSupport p ι h k)))
      = charPowerSeries
          ((shiftBlock p ι K h (k + 1)).comp (U.comp (insertBlock p ι K h (k + 1)))) := by
  rw [← insertBlock_comp_shiftBlock, ← ContinuousLinearMap.comp_assoc,
    charPowerSeries_comm _ _ (hU.comp_right _)]

/-- **The determinant identity of H2, from an intertwining `θ^{k+1} ∘ U = c • U' ∘ θ^{k+1}`**:
`det(1 − X·U|_{complement}) = det(1 − cX·U')`. -/
theorem charPowerSeries_comp_one_sub_truncation_eq_rescale (h k : ℕ)
    {U U' : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hU : IsCompactoid U) (hU' : IsCompactoid U') (c : K)
    (hint : (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp U
      = c • (U'.comp (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)))) :
    charPowerSeries (U.comp (1 - truncation (classicalSupport p ι h k)))
      = PowerSeries.rescale c (charPowerSeries U') := by
  rw [charPowerSeries_comp_one_sub_truncation_eq h k hU,
    charPowerSeries_shiftBlock_comp_eq_of_intertwine h k c hint,
    charPowerSeries_smul c U' hU']

/-! ### H2 at a classical-shape pair -/

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable (h : ℕ) (ψ : ℚ_[p] →+* K) {UK UK' : Subgroup Kˣ} {ρ ρ' : ℝ}
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
  (uu : ι → Fin p → U)

/-- **Hypothesis H2 holds at every classical-shape pair with common constants**: the
intertwining `thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape` and
`charPowerSeries_comp_one_sub_truncation_eq_rescale`, with `U_p` compactoid at both weights
(`isCompactoid_discHeckeBlockOp`). -/
theorem isThetaExact_of_isClassicalShape
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') {k : ℕ}
    {u : ι → Fin p → ZMod (p ^ h) → K} (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hcl' : IsClassicalShape' θG h ψ U hU vRep hvΔ uu κ' k u)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    (hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1) (hρ' : 0 ≤ ρ') (hσ' : max ρ' (p : ℝ)⁻¹ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape) :
    IsThetaExact θG h ψ U hU vRep hvΔ idx uu κ κ' k :=
  charPowerSeries_comp_one_sub_truncation_eq_rescale h k
    (isCompactoid_discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu hρ hσ hshape)
    (isCompactoid_discHeckeBlockOp θG h ψ κ' U hU vRep hvΔ idx uu hρ' hσ' hshape)
    (ψ p ^ (k + 1))
    (thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape θG h ψ U hU vRep hvΔ idx uu κ κ'
      hcl hcl' hdet)

variable {θG h ψ U hU vRep hvΔ uu}

/-- **Hypothesis H2 at a classical datum and its theta target**: the shapes are the fields of
`ClassicalData` and `TargetData`, and the halo weights are compactoid (`haloRhoH_nonneg`,
`haloRhoH_lt_one`). -/
theorem isThetaExact_classicalData {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}
    {ω ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₁ : K} {k : ℕ}
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) (d : TargetData c ω₁ T₁) :
    IsThetaExact θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight k :=
  isThetaExact_of_isClassicalShape θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight
    c.shape d.shape hdet (haloRhoH_nonneg 1 T₀)
    (max_lt (haloRhoH_lt_one 1 T₀ c.hT) inv_lt_one_p) (haloRhoH_nonneg 1 T₁)
    (max_lt (haloRhoH_lt_one 1 T₁ d.hT) inv_lt_one_p) hshape

end LWX

end
