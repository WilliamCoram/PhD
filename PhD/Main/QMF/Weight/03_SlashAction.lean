/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.Weight.«00_Series»
import PhD.Main.QMF.Slash.«01_Sigma0»
import PhD.Main.QMF.Slash.«02_Basic»

/-!
# The weight-`κ` action of an abstract weight on the Tate algebra

[Jacobs, Ch. 1 §1.5 Definition 1.27]: the weight-`κ` action
`z^k ↦ κ(cz + d)/(cz + d)² ((az+b)/(cz+d))^k` and its "easy check": "It is an easy
check that Σ_α is a monoid and that ‖_κ is a right-action of Σ_α on A_p."

This file makes the easy check honest **once, for every abstract weight**
`W : QMF.WeightSeries S ρ`, by the same design as the Jacobs fork
(the former `PhD/Main/JacobsSlash/U3/4_KappaSlash.lean`, retired 2026-08-19, of which everything here was the
character-abstracted port): the action of `g` is `ofGenFun` of `W.genFun g`, so
[Jacobs, Prop 2.6] holds by construction, and the action laws reduce to the Möbius
composition (`mobius_mul`, character-free) plus the κ-cocycle (a `WeightSeries` field).

**Status: engine, not API.**  Everything here is stated for the implementation record
`WeightSeries`; the public weight is `QMF.AnalyticWeight` (`PhD/Main/QMF/Weight/04_Char.lean`),
which re-exports `kappaSlash`, `kappaSlash_one/_mul`, `matrixCoeff_kappaSlash`,
`kappaSlashAction`, `smulSlashClass` on itself.  Use those downstream.

## Main definitions

* `QMF.WeightSeries.kappaSlash` — the action of a single `g ∈ S` on `c(ℕ, K)`.
* `QMF.WeightSeries.kappaSlashAction : RightSlashAction S c(ℕ, K)`.
* `QMF.WeightSeries.autFactor` — the automorphy factor `j_γ = κ(cx+d)/(cx+d)²`.
* `RightSlashAction.comap` — transport of a right slash action along a monoid hom.
* `RightSlashAction.twist` — twist of a right slash action by a scalar character
  `χ : Δ →* Rˣ` (the vessel for the classical determinant character; Def 1.27 is χ = 1).
* `QMF.Sigma0'.levelBounds` — a valued-field `Σ₀'(γ)` satisfies the norm-form level
  bounds, via the valuation ↔ norm dictionary.

## Main results

* `QMF.WeightSeries.matrixCoeff_kappaSlash` — [Jacobs, Prop 2.6], by construction.
* `QMF.WeightSeries.yCoeff_genFun` — column `r` is `j_γ · w_γ^r` ([Jacobs, (2.1.3)]).
* `QMF.WeightSeries.mobius_mul` — `w_{δγ} = w_δ ∘ w_γ`, formally.
* `QMF.WeightSeries.kappaSlash_one`, `kappaSlash_mul` — the action laws.
-/

open TateFredholm PowerSeries
open scoped TateFredholm QMF

namespace QMF

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The `y`-column of a two-variable generating function, as a one-variable series:
`yCoeff F r` is the `r`-th column of the operator's matrix (general-`K` form of the
Jacobs fork's `yCoeff`). -/
noncomputable def yCoeff (F : MvPowerSeries (Fin 2) K) (r : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => MvPowerSeries.coeff (idx n r) F

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The coefficients of a `y`-column (definitional). -/
@[simp] theorem coeff_yCoeff (F : MvPowerSeries (Fin 2) K) (r n : ℕ) :
    PowerSeries.coeff n (yCoeff F r) = MvPowerSeries.coeff (idx n r) F :=
  PowerSeries.coeff_mk _ _

section YGrading

omit [IsUltrametricDist K] [CompleteSpace K]

private theorem finsupp_fin2_ext {p q : Fin 2 →₀ ℕ} (h0 : p 0 = q 0) (h1 : p 1 = q 1) :
    p = q := by
  ext k
  fin_cases k <;> assumption

private theorem eq_idx (p : Fin 2 →₀ ℕ) : p = idx (p 0) (p 1) :=
  finsupp_fin2_ext (by simp) (by simp)

/-- Multiplying by a series concentrated in `y`-degree `0` acts on each `y`-column as a
one-variable convolution: the `y`-grading is respected. -/
theorem coeff_mul_of_yDeg0 {F G : MvPowerSeries (Fin 2) K}
    (hG : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G = 0) (n r : ℕ) :
    MvPowerSeries.coeff (idx n r) (F * G)
      = ∑ ij ∈ Finset.antidiagonal n,
          MvPowerSeries.coeff (idx ij.1 r) F * MvPowerSeries.coeff (idx ij.2 0) G := by
  classical
  rw [MvPowerSeries.coeff_mul]
  rw [← Finset.sum_filter_of_ne (p := fun x : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) => x.2 1 = 0)
    (fun x _ hx => by
      by_contra hc
      exact hx (by rw [hG x.2 hc, mul_zero]))]
  refine Finset.sum_nbij' (i := fun x => (x.1 0, x.2 0))
    (j := fun ij => (idx ij.1 r, idx ij.2 0)) ?_ ?_ ?_ ?_ ?_
  · rintro x hx
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hx
    rw [Finset.mem_antidiagonal]
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hx.1
    simpa using this
  · rintro ij hij
    rw [Finset.mem_antidiagonal] at hij
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    refine ⟨finsupp_fin2_ext (by simp [idx, hij]) (by simp [idx]), by simp [idx]⟩
  · rintro x hx
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hx
    have h1 : x.1 1 = r := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hx.1
      simp only [Finsupp.add_apply, idx_apply_one] at this
      omega
    refine Prod.ext ?_ ?_
    · exact ((eq_idx x.1).trans (by rw [h1])).symm
    · exact ((eq_idx x.2).trans (by rw [hx.2])).symm
  · rintro ij hij
    simp [idx]
  · rintro x hx
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hx
    have h1 : x.1 1 = r := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hx.1
      simp only [Finsupp.add_apply, idx_apply_one] at this
      omega
    rw [← (eq_idx x.1).trans (by rw [h1] : idx (x.1 0) (x.1 1) = idx (x.1 0) r),
      ← (eq_idx x.2).trans (by rw [hx.2] : idx (x.2 0) (x.2 1) = idx (x.2 0) 0)]

/-- Multiplying by a series concentrated in `y`-degree `1` shifts the `y`-column down by
one (and annihilates the `0`-column). -/
theorem coeff_mul_of_yDeg1 {F H : MvPowerSeries (Fin 2) K}
    (hH : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 1 → MvPowerSeries.coeff p H = 0) (n r : ℕ) :
    MvPowerSeries.coeff (idx n (r + 1)) (F * H)
      = ∑ ij ∈ Finset.antidiagonal n,
          MvPowerSeries.coeff (idx ij.1 r) F * MvPowerSeries.coeff (idx ij.2 1) H := by
  classical
  rw [MvPowerSeries.coeff_mul]
  rw [← Finset.sum_filter_of_ne (p := fun x : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) => x.2 1 = 1)
    (fun x _ hx => by
      by_contra hc
      exact hx (by rw [hH x.2 hc, mul_zero]))]
  refine Finset.sum_nbij' (i := fun x => (x.1 0, x.2 0))
    (j := fun ij => (idx ij.1 r, idx ij.2 1)) ?_ ?_ ?_ ?_ ?_
  · rintro x hx
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hx
    rw [Finset.mem_antidiagonal]
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hx.1
    simpa using this
  · rintro ij hij
    rw [Finset.mem_antidiagonal] at hij
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    refine ⟨finsupp_fin2_ext (by simp [idx, hij]) (by simp [idx]), by simp [idx]⟩
  · rintro x hx
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hx
    have h1 : x.1 1 = r := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hx.1
      simp only [Finsupp.add_apply, idx_apply_one] at this
      omega
    refine Prod.ext ?_ ?_
    · exact ((eq_idx x.1).trans (by rw [h1])).symm
    · exact ((eq_idx x.2).trans (by rw [hx.2])).symm
  · rintro ij hij
    simp [idx]
  · rintro x hx
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hx
    have h1 : x.1 1 = r := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hx.1
      simp only [Finsupp.add_apply, idx_apply_one] at this
      omega
    rw [← (eq_idx x.1).trans (by rw [h1] : idx (x.1 0) (x.1 1) = idx (x.1 0) r),
      ← (eq_idx x.2).trans (by rw [hx.2] : idx (x.2 0) (x.2 1) = idx (x.2 0) 1)]

/-- Multiplying by a `y`-degree-`1` series annihilates the `0`-column. -/
theorem coeff_zero_mul_of_yDeg1 {F H : MvPowerSeries (Fin 2) K}
    (hH : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 1 → MvPowerSeries.coeff p H = 0) (n : ℕ) :
    MvPowerSeries.coeff (idx n 0) (F * H) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have h1 : x.1 1 + x.2 1 = 0 := by
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hx
    simpa using this
  rw [hH x.2 (by omega), mul_zero]

/-- The `y`-linear part of `quadSeries`: `y·(a·x + b)`. -/
noncomputable def yNum (γ : Matrix (Fin 2) (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1)
      (γ 0 0)
    + MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) 1) (γ 0 1)

theorem quadSeries_eq_sub (γ : Matrix (Fin 2) (Fin 2) K) :
    quadSeries γ = linSeries γ - yNum γ := by
  rw [quadSeries_eq, linSeries_eq, yNum]
  abel

private theorem yDeg0_linSeries (γ : Matrix (Fin 2) (Fin 2) K) :
    ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p (linSeries γ) = 0 := by
  intro p hp
  rw [linSeries_eq, map_add, MvPowerSeries.coeff_monomial,
    MvPowerSeries.coeff_monomial, if_neg, if_neg, add_zero]
  · rintro rfl; simp at hp
  · rintro rfl; simp at hp

private theorem yDeg1_yNum (γ : Matrix (Fin 2) (Fin 2) K) :
    ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 1 → MvPowerSeries.coeff p (yNum γ) = 0 := by
  intro p hp
  rw [yNum, map_add, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial,
    if_neg, if_neg, add_zero]
  · rintro rfl; simp at hp
  · rintro rfl; simp at hp

@[simp] theorem yCoeff_linSeries (γ : Matrix (Fin 2) (Fin 2) K) :
    yCoeff (linSeries γ) 0 = linX γ := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, linSeries_eq, linX, map_add, map_add,
    MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
  rcases n with _ | _ | n
  · simp [idx, PowerSeries.coeff_C, Finsupp.ext_iff, Fin.forall_fin_two]
  · simp [idx, PowerSeries.coeff_C, Finsupp.ext_iff, Fin.forall_fin_two]
  · rw [if_neg, if_neg]
    · simp
    · intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp [idx] at this
    · intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp [idx] at this

@[simp] theorem yCoeff_yNum (γ : Matrix (Fin 2) (Fin 2) K) :
    yCoeff (yNum γ) 1 = numX γ := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, yNum, numX, map_add, map_add,
    MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
  rcases n with _ | _ | n
  · rw [if_neg, if_pos]
    · simp [PowerSeries.coeff_C]
    · simp [idx]
    · intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp [idx] at this
  · rw [if_pos, if_neg]
    · simp
    · intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp [idx] at this
    · simp [idx]
  · rw [if_neg, if_neg]
    · simp
    · intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp [idx] at this
    · intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp [idx] at this

theorem yCoeff_mul_yDeg0 {F G : MvPowerSeries (Fin 2) K}
    (hG : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G = 0) (r : ℕ) :
    yCoeff (F * G) r = yCoeff F r * yCoeff G 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, coeff_mul_of_yDeg0 hG, PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl fun ij _ => by rw [coeff_yCoeff, coeff_yCoeff]

theorem yCoeff_mul_yDeg1 {F H : MvPowerSeries (Fin 2) K}
    (hH : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 1 → MvPowerSeries.coeff p H = 0) (r : ℕ) :
    yCoeff (F * H) (r + 1) = yCoeff F r * yCoeff H 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, coeff_mul_of_yDeg1 hH, PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl fun ij _ => by rw [coeff_yCoeff, coeff_yCoeff]

theorem yCoeff_zero_mul_yDeg1 {F H : MvPowerSeries (Fin 2) K}
    (hH : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 1 → MvPowerSeries.coeff p H = 0) :
    yCoeff (F * H) 0 = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, coeff_zero_mul_of_yDeg1 hH, map_zero]

/-- The inverse of a series concentrated in `y`-degree `0` is again concentrated
there. -/
theorem yDeg0_inv {G : MvPowerSeries (Fin 2) K}
    (hG : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G = 0) :
    ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G⁻¹ = 0 := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N → p 1 ≠ 0 →
      MvPowerSeries.coeff p G⁻¹ = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp hp1
      rw [MvPowerSeries.coeff_inv, if_neg (fun hc => hp1 (by rw [hc]; simp)),
        mul_eq_zero]
      refine Or.inr (Finset.sum_eq_zero fun x hx => ?_)
      rw [Finset.mem_antidiagonal] at hx
      split_ifs with hlt
      · have e1 : x.1 1 + x.2 1 = p 1 := by rw [← hx]; simp
        rcases Nat.eq_zero_or_pos (x.1 1) with h | h
        · rw [ih (x.2 0 + x.2 1) ?_ x.2 rfl (by omega), mul_zero]
          have e0 : x.1 0 + x.2 0 = p 0 := by rw [← hx]; simp
          have hne : x.1 ≠ 0 := by
            rintro hz
            rw [hz, zero_add] at hx
            exact absurd hx (ne_of_lt hlt)
          have hpos : 0 < x.1 0 + x.1 1 := by
            rcases Nat.eq_zero_or_pos (x.1 0 + x.1 1) with hh | hh
            · exact absurd (TateFredholm.fin2_eq_zero (by omega) (by omega)) hne
            · exact hh
          omega
        · rw [hG x.1 (by omega), zero_mul]
      · rfl
  exact fun p hp => key (p 0 + p 1) p rfl hp

@[simp] theorem yCoeff_sub (F G : MvPowerSeries (Fin 2) K) (r : ℕ) :
    yCoeff (F - G) r = yCoeff F r - yCoeff G r := by
  refine PowerSeries.ext fun n => ?_
  simp [coeff_yCoeff]

@[simp] theorem yCoeff_one_zero : yCoeff (1 : MvPowerSeries (Fin 2) K) 0 = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
  rcases n with _ | n
  · simp [idx]
  · rw [if_neg, if_neg]
    · exact Nat.succ_ne_zero n
    · intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp [idx] at this

/-- The `y`-column of `(linSeries γ)⁻¹` is `(linX γ)⁻¹`. -/
theorem yCoeff_linSeries_inv {γ : Matrix (Fin 2) (Fin 2) K} (hd : γ 1 1 ≠ 0) :
    yCoeff (linSeries γ)⁻¹ 0 = (linX γ)⁻¹ := by
  have hc : MvPowerSeries.constantCoeff (linSeries γ) ≠ 0 := by
    rw [constantCoeff_linSeries]; exact hd
  have h1 : linSeries γ * (linSeries γ)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ hc
  have h2 := congrArg (fun F => yCoeff F 0) h1
  simp only [yCoeff_mul_yDeg0 (yDeg0_inv (yDeg0_linSeries γ)) 0, yCoeff_linSeries,
    yCoeff_one_zero] at h2
  refine (PowerSeries.eq_inv_iff_mul_eq_one (k := K)
    (φ := yCoeff (linSeries γ)⁻¹ 0) (ψ := linX γ) ?_).mpr ?_
  · rw [constantCoeff_linX]; exact hd
  · rw [mul_comm]; exact h2

theorem yCoeff_eq_zero_of_yDeg0 {G : MvPowerSeries (Fin 2) K}
    (hG : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G = 0) {r : ℕ}
    (hr : r ≠ 0) : yCoeff G r = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, hG _ (by simpa using hr), map_zero]

/-- The `0`-column of a `y`-extended one-variable series is the series itself. -/
@[simp] theorem yCoeff_yExtend_zero (φ : PowerSeries K) :
    yCoeff (WeightSeries.yExtend φ) 0 = φ := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, WeightSeries.coeff_yExtend]
  simp [idx]

end YGrading

namespace WeightSeries

variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}

/-- **The automorphy factor** `j_γ = κ(c·x + d)/(c·x + d)²` of the weight `W`, as a
one-variable series. -/
noncomputable def autFactor (W : WeightSeries S ρ) (γ : Matrix (Fin 2) (Fin 2) K) :
    PowerSeries K :=
  W.col (γ 1 0) (γ 1 1) * ((linX γ)⁻¹) ^ 2

/-- The weight-`κ` action of a single `g ∈ S` on the Tate algebra `c(ℕ, K)`:
`ofGenFun` of the weight generating function ([Jacobs, Def 1.27 + (2.1.3)]). -/
noncomputable def kappaSlash (W : WeightSeries S ρ) (g : S) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofGenFun (W.genFun g.1)
    ⟨1, fun j i => W.norm_coeff_genFun_le_one g.2 j i⟩
    (fun i => W.tendsto_coeff_genFun g.2 i)

/-- **[Jacobs, Proposition 2.6]** (by design): the matrix of `kappaSlash g` is the
coefficient array of `κ(cx+d)/((cx+d)(cx+d−axy−by))`. -/
theorem matrixCoeff_kappaSlash (W : WeightSeries S ρ) (g : S) (j i : ℕ) :
    matrixCoeff (W.kappaSlash g) j i
      = MvPowerSeries.coeff (idx j i) (W.genFun g.1) :=
  matrixCoeff_ofGenFun _ _ _ j i

/-- The action of a matrix depends only on the weight's column at its lower row:
weight data (at possibly different levels) agreeing there act identically. -/
theorem kappaSlash_congr {S₁ S₂ : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ₁ ρ₂ : ℝ}
    {W₁ : WeightSeries S₁ ρ₁} {W₂ : WeightSeries S₂ ρ₂} {g₁ : S₁} {g₂ : S₂}
    (hg : g₁.1 = g₂.1) (h : W₁.col (g₁.1 1 0) (g₁.1 1 1) = W₂.col (g₁.1 1 0) (g₁.1 1 1)) :
    W₁.kappaSlash g₁ = W₂.kappaSlash g₂ :=
  ext_matrixCoeff fun j i => by
    rw [matrixCoeff_kappaSlash, matrixCoeff_kappaSlash, genFun, genFun, ← hg, h]

/-- **Row decay of the matrix of the action at a `U_ϖ`-type element** ([Jacobs, Lemma
2.7], [Jacobs, Cor 1.10]'s hypothesis): if `‖g₀₀‖ ≤ σ` with `ρ ≤ σ`, then
`‖matrixCoeff (kappaSlash g) j i‖ ≤ σ^j`. -/
theorem norm_matrixCoeff_kappaSlash_le (W : WeightSeries S ρ) (g : S) {σ : ℝ}
    (hρσ : ρ ≤ σ) (ha : ‖g.1 0 0‖ ≤ σ) (j i : ℕ) :
    ‖matrixCoeff (W.kappaSlash g) j i‖ ≤ σ ^ j := by
  rw [W.matrixCoeff_kappaSlash g j i]
  simpa [idx_apply_zero] using W.rowIntAt_genFun g.2 hρσ ha (idx j i)

/-- **[Jacobs, Lemma 2.7] at an abstract weight**: the action of a `U_ϖ`-type element
(`‖g₀₀‖ ≤ σ < 1`, `ρ ≤ σ`) is compactoid. -/
theorem isCompactoid_kappaSlash (W : WeightSeries S ρ) (g : S) {σ : ℝ} (hρσ : ρ ≤ σ)
    (hσ : σ < 1) (ha : ‖g.1 0 0‖ ≤ σ) : IsCompactoid (W.kappaSlash g) :=
  isCompactoid_of_row_decay' (C := 1) (W.bounds.rho_nonneg.trans hρσ) hσ fun j i => by
    simpa using W.norm_matrixCoeff_kappaSlash_le g hρσ ha j i

/-- [Jacobs, Lemma 2.7] in the determinant form of [Buzzard, Lemma 12.2]: the action of
`g ∈ S` with `‖det g‖ ≤ σ < 1` (`ρ ≤ σ`) is compactoid. -/
theorem isCompactoid_kappaSlash_of_norm_det_le (W : WeightSeries S ρ) (g : S) {σ : ℝ}
    (hρσ : ρ ≤ σ) (hσ : σ < 1) (hdet : ‖g.1.det‖ ≤ σ) : IsCompactoid (W.kappaSlash g) :=
  W.isCompactoid_kappaSlash g hρσ hσ (W.bounds.norm_apply_zero_zero_le_of_norm_det_le hρσ g.2 hdet)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The column identity for an arbitrary column** ([Jacobs, (2.1.3)]): for any one-variable
series `φ` (the κ-column), the `r`-th `y`-column of `yExtend φ · linSeries⁻¹ · quadSeries⁻¹`
is `φ · (linX γ)⁻² · w_γ^r`. -/
theorem yCoeff_yExtend_mul_inv (φ : PowerSeries K) {γ : Matrix (Fin 2) (Fin 2) K}
    (hd : γ 1 1 ≠ 0) (r : ℕ) :
    yCoeff (yExtend φ * (linSeries γ)⁻¹ * (quadSeries γ)⁻¹) r
      = φ * ((linX γ)⁻¹) ^ 2 * (mobius γ) ^ r := by
  set F := yExtend φ * (linSeries γ)⁻¹ * (quadSeries γ)⁻¹ with hF
  have hquad0 : MvPowerSeries.constantCoeff (quadSeries γ) ≠ 0 := by
    rw [constantCoeff_quadSeries]; exact hd
  have hlinX0 : PowerSeries.constantCoeff (linX γ) ≠ 0 := by
    rw [constantCoeff_linX]; exact hd
  have hinv : linX γ * (linX γ)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hlinX0
  have key : F * linSeries γ - F * yNum γ = yExtend φ * (linSeries γ)⁻¹ := by
    rw [← mul_sub, ← quadSeries_eq_sub, hF, mul_assoc,
      mul_comm (quadSeries γ)⁻¹ (quadSeries γ),
      MvPowerSeries.mul_inv_cancel _ hquad0, mul_one]
  have base : yCoeff F 0 = φ * ((linX γ)⁻¹) ^ 2 := by
    have h := congrArg (fun G => yCoeff G 0) key
    simp only [yCoeff_sub, yCoeff_mul_yDeg0 (yDeg0_linSeries γ) 0,
      yCoeff_zero_mul_yDeg1 (yDeg1_yNum γ), yCoeff_linSeries, sub_zero,
      yCoeff_mul_yDeg0 (yDeg0_inv (yDeg0_linSeries γ)) 0, yCoeff_linSeries_inv hd,
      yCoeff_yExtend_zero] at h
    calc yCoeff F 0
        = yCoeff F 0 * (linX γ * (linX γ)⁻¹) := by rw [hinv, mul_one]
      _ = yCoeff F 0 * linX γ * (linX γ)⁻¹ := by ring
      _ = φ * (linX γ)⁻¹ * (linX γ)⁻¹ := by rw [h]
      _ = φ * ((linX γ)⁻¹) ^ 2 := by ring
  have step : ∀ k : ℕ, yCoeff F (k + 1) = yCoeff F k * mobius γ := by
    intro k
    have h := congrArg (fun G => yCoeff G (k + 1)) key
    simp only [yCoeff_sub, yCoeff_mul_yDeg0 (yDeg0_linSeries γ) (k + 1),
      yCoeff_mul_yDeg1 (yDeg1_yNum γ) k, yCoeff_linSeries, yCoeff_yNum,
      yCoeff_mul_yDeg0 (yDeg0_inv (yDeg0_linSeries γ)) (k + 1),
      yCoeff_eq_zero_of_yDeg0 (yExtend_yDeg0 φ) (Nat.succ_ne_zero k),
      zero_mul] at h
    have h' : yCoeff F (k + 1) * linX γ = yCoeff F k * numX γ := by
      rw [sub_eq_zero] at h; exact h
    calc yCoeff F (k + 1)
        = yCoeff F (k + 1) * (linX γ * (linX γ)⁻¹) := by rw [hinv, mul_one]
      _ = yCoeff F (k + 1) * linX γ * (linX γ)⁻¹ := by ring
      _ = yCoeff F k * numX γ * (linX γ)⁻¹ := by rw [h']
      _ = yCoeff F k * mobius γ := by rw [mobius]; ring
  induction r with
  | zero => simpa using base
  | succ k ih => rw [step k, ih, pow_succ]; ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The column identity** ([Jacobs, (2.1.3)]): the `r`-th column of the operator is
`j_γ · w_γ^r` — the operator is the weight-2-normalised slash `f ↦ j_γ · (f ∘ w_γ)`. -/
theorem yCoeff_genFun (W : WeightSeries S ρ) {γ : Matrix (Fin 2) (Fin 2) K}
    (hd : γ 1 1 ≠ 0) (r : ℕ) :
    yCoeff (W.genFun γ) r = W.autFactor γ * (mobius γ) ^ r :=
  yCoeff_yExtend_mul_inv (W.col (γ 1 0) (γ 1 1)) hd r

/-- `kappaSlash` acts by the slash formula, read coefficientwise. -/
theorem kappaSlash_apply (W : WeightSeries S ρ) (g : S) (f : c(ℕ, K)) (j : ℕ) :
    W.kappaSlash g f j
      = ∑' i, PowerSeries.coeff j (W.autFactor g.1 * (mobius g.1) ^ i) * f i := by
  have hd : g.1 1 1 ≠ 0 := W.bounds.d_ne_zero g.2
  rw [kappaSlash, ofGenFun, ofCoeffs_apply]
  refine tsum_congr fun i => ?_
  rw [← coeff_yCoeff, W.yCoeff_genFun hd i]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Möbius composition in linear form: `lin(δγ) = δ₁₀·num(γ) + δ₁₁·lin(γ)`. -/
theorem linX_mul (γ δ : Matrix (Fin 2) (Fin 2) K) :
    linX (δ * γ) = PowerSeries.C (δ 1 0) * numX γ + PowerSeries.C (δ 1 1) * linX γ := by
  rw [linX, linX, numX, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The numerator of `δ·γ`: `num(δγ) = δ₀₀·num(γ) + δ₀₁·lin(γ)`. -/
theorem numX_mul (γ δ : Matrix (Fin 2) (Fin 2) K) :
    numX (δ * γ) = PowerSeries.C (δ 0 0) * numX γ + PowerSeries.C (δ 0 1) * linX γ := by
  rw [numX, numX, linX, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The denominator of `δ·γ` factors through `w_γ`:
`lin(δγ) = lin(γ) · (δ₁₀·w_γ + δ₁₁)`. -/
theorem linX_mul_eq (γ δ : Matrix (Fin 2) (Fin 2) K) (hγ : γ 1 1 ≠ 0) :
    linX (δ * γ)
      = linX γ * (PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1)) := by
  have hinv : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hγ)
  rw [linX_mul, mobius]
  symm
  calc linX γ * (PowerSeries.C (δ 1 0) * (numX γ * (linX γ)⁻¹) + PowerSeries.C (δ 1 1))
      = PowerSeries.C (δ 1 0) * numX γ * (linX γ * (linX γ)⁻¹)
        + PowerSeries.C (δ 1 1) * linX γ := by ring
    _ = PowerSeries.C (δ 1 0) * numX γ + PowerSeries.C (δ 1 1) * linX γ := by
        rw [hinv, mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The numerator of `δ·γ` factors the same way:
`num(δγ) = lin(γ) · (δ₀₀·w_γ + δ₀₁)`. -/
theorem numX_mul_eq (γ δ : Matrix (Fin 2) (Fin 2) K) (hγ : γ 1 1 ≠ 0) :
    numX (δ * γ)
      = linX γ * (PowerSeries.C (δ 0 0) * mobius γ + PowerSeries.C (δ 0 1)) := by
  have hinv : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hγ)
  rw [numX_mul, mobius]
  symm
  calc linX γ * (PowerSeries.C (δ 0 0) * (numX γ * (linX γ)⁻¹) + PowerSeries.C (δ 0 1))
      = PowerSeries.C (δ 0 0) * numX γ * (linX γ * (linX γ)⁻¹)
        + PowerSeries.C (δ 0 1) * linX γ := by ring
    _ = PowerSeries.C (δ 0 0) * numX γ + PowerSeries.C (δ 0 1) * linX γ := by
        rw [hinv, mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Möbius composition in closed form**: `w_{δγ} = (δ₀₀·w_γ + δ₀₁)·(δ₁₀·w_γ + δ₁₁)⁻¹`,
proved with no substitution — the `lin`/`num` factorisations do all the work. -/
theorem mobius_mul_eq (γ δ : Matrix (Fin 2) (Fin 2) K) (hγ : γ 1 1 ≠ 0)
    (hδγ : (δ * γ) 1 1 ≠ 0) :
    mobius (δ * γ)
      = (PowerSeries.C (δ 0 0) * mobius γ + PowerSeries.C (δ 0 1))
        * (PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1))⁻¹ := by
  have hlin : PowerSeries.constantCoeff (linX (δ * γ)) ≠ 0 := by
    rw [constantCoeff_linX]; exact hδγ
  have hfac := linX_mul_eq γ δ hγ
  have hlinγ : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hγ)
  rw [mobius, numX_mul_eq γ δ hγ, hfac, PowerSeries.mul_inv_rev]
  calc linX γ * (PowerSeries.C (δ 0 0) * mobius γ + PowerSeries.C (δ 0 1))
        * ((PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1))⁻¹ * (linX γ)⁻¹)
      = (linX γ * (linX γ)⁻¹)
        * ((PowerSeries.C (δ 0 0) * mobius γ + PowerSeries.C (δ 0 1))
          * (PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1))⁻¹) := by ring
    _ = _ := by rw [hlinγ, one_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Möbius composition** `w_{δγ} = w_δ ∘ w_γ` in cross-multiplied (substitution-free)
form: `w_{δγ} · (δ₁₀·w_γ + δ₁₁·1) = δ₀₀·w_γ + δ₀₁`. -/
theorem mobius_mul {γ δ : Matrix (Fin 2) (Fin 2) K} (hγ : γ 1 1 ≠ 0)
    (hδγ : (δ * γ) 1 1 ≠ 0) :
    mobius (δ * γ) * (PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1))
      = PowerSeries.C (δ 0 0) * mobius γ + PowerSeries.C (δ 0 1) := by
  have hden : PowerSeries.constantCoeff
      (PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1)) ≠ 0 := by
    intro hc
    apply (show PowerSeries.constantCoeff (linX (δ * γ)) ≠ 0 by
      rw [constantCoeff_linX]; exact hδγ)
    rw [linX_mul_eq γ δ hγ, map_mul, hc, mul_zero]
  rw [mobius_mul_eq γ δ hγ hδγ, mul_assoc,
    PowerSeries.inv_mul_cancel _ hden, mul_one]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem absSummable_linX (δ : Matrix (Fin 2) (Fin 2) K) : AbsSummable (linX δ) := by
  rw [linX]
  exact absSummable_add (absSummable_C _)
    (absSummable_mul (absSummable_C _) absSummable_X)

theorem compAn_linX (δ : Matrix (Fin 2) (Fin 2) K) {w : PowerSeries K}
    (hw : CoeffLeOne w) :
    compAn (linX δ) w = PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w := by
  rw [linX, compAn_add (absSummable_C _)
      (absSummable_mul (absSummable_C _) absSummable_X) hw,
    compAn_mul (absSummable_C _) absSummable_X hw, compAn_C, compAn_C, compAn_X]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The explicit geometric inverse of the linear factor `d + c·x`. -/
theorem linX_inv_eq {δ : Matrix (Fin 2) (Fin 2) K} (hd : δ 1 1 ≠ 0) :
    (linX δ)⁻¹ = PowerSeries.mk fun n => (-(δ 1 0)) ^ n / (δ 1 1) ^ (n + 1) := by
  refine ((PowerSeries.eq_inv_iff_mul_eq_one
    (by rw [constantCoeff_linX]; exact hd)).mpr ?_).symm
  refine PowerSeries.ext fun n => ?_
  rw [mul_comm, linX, add_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_mk, if_pos rfl]
    field_simp
    ring
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      if_neg (Nat.succ_ne_zero m)]
    field_simp
    ring

omit [CompleteSpace K] in
omit [IsUltrametricDist K] in
/-- The inverse of the linear factor is absolutely summable when `‖c‖ < ‖d‖` — a
geometric series with ratio `‖c‖/‖d‖`. -/
theorem absSummable_linX_inv {δ : Matrix (Fin 2) (Fin 2) K} (hd : δ 1 1 ≠ 0)
    (h : ‖δ 1 0‖ < ‖δ 1 1‖) : AbsSummable (linX δ)⁻¹ := by
  have hdpos : (0 : ℝ) < ‖δ 1 1‖ := norm_pos_iff.mpr hd
  have hr : ‖δ 1 0‖ / ‖δ 1 1‖ < 1 := (div_lt_one hdpos).mpr h
  have hgeo := (summable_geometric_of_lt_one (by positivity) hr).mul_right (1 / ‖δ 1 1‖)
  rw [AbsSummable, linX_inv_eq hd]
  refine hgeo.congr fun n => ?_
  rw [PowerSeries.coeff_mk, norm_div, norm_pow, norm_neg, norm_pow, div_pow]
  field_simp
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem absSummable_numX (δ : Matrix (Fin 2) (Fin 2) K) : AbsSummable (numX δ) := by
  rw [numX]
  exact absSummable_add (absSummable_C _)
    (absSummable_mul (absSummable_C _) absSummable_X)

theorem compAn_numX (δ : Matrix (Fin 2) (Fin 2) K) {w : PowerSeries K}
    (hw : CoeffLeOne w) :
    compAn (numX δ) w = PowerSeries.C (δ 0 1) + PowerSeries.C (δ 0 0) * w := by
  rw [numX, compAn_add (absSummable_C _)
      (absSummable_mul (absSummable_C _) absSummable_X) hw,
    compAn_mul (absSummable_C _) absSummable_X hw, compAn_C, compAn_C, compAn_X]

omit [CompleteSpace K] in
theorem coeffLeOne_numX {δ : Matrix (Fin 2) (Fin 2) K} (h00 : ‖δ 0 0‖ ≤ 1)
    (h01 : ‖δ 0 1‖ ≤ 1) : CoeffLeOne (numX δ) := by
  intro n
  rw [numX, map_add, PowerSeries.coeff_C]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · split_ifs
    · exact h01
    · simp
  · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X, norm_mul]
    refine mul_le_one₀ h00 (norm_nonneg _) ?_
    split_ifs
    · simp
    · simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coeffLeOne_linX_inv {δ : Matrix (Fin 2) (Fin 2) K} (hd : ‖δ 1 1‖ = 1)
    (hc : ‖δ 1 0‖ ≤ 1) : CoeffLeOne (linX δ)⁻¹ := by
  have hd0 : δ 1 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
  intro n
  rw [linX_inv_eq hd0, PowerSeries.coeff_mk, norm_div, norm_pow, norm_neg, norm_pow,
    hd, one_pow, div_one]
  exact pow_le_one₀ (norm_nonneg _) hc

omit [CompleteSpace K] in
/-- The Möbius series of a matrix with integral entries and unit `d`-entry has
coefficients of norm at most one. -/
theorem coeffLeOne_mobius' {δ : Matrix (Fin 2) (Fin 2) K} (h00 : ‖δ 0 0‖ ≤ 1)
    (h01 : ‖δ 0 1‖ ≤ 1) (hd : ‖δ 1 1‖ = 1) (hc : ‖δ 1 0‖ ≤ 1) :
    CoeffLeOne (mobius δ) := by
  rw [mobius]
  exact (coeffLeOne_numX h00 h01).mul (coeffLeOne_linX_inv hd hc)

theorem constantCoeff_compAn_linX_ne_zero {δ : Matrix (Fin 2) (Fin 2) K}
    (hd : ‖δ 1 1‖ = 1) (hc : ‖δ 1 0‖ < 1) {w : PowerSeries K} (hw : CoeffLeOne w) :
    PowerSeries.constantCoeff (compAn (linX δ) w) ≠ 0 := by
  rw [compAn_linX δ hw, map_add, PowerSeries.constantCoeff_C, map_mul,
    PowerSeries.constantCoeff_C]
  intro h
  have hval : δ 1 1 = -(δ 1 0 * PowerSeries.constantCoeff w) := by linear_combination h
  have : (1 : ℝ) < 1 := by
    calc (1 : ℝ) = ‖δ 1 1‖ := hd.symm
      _ = ‖δ 1 0 * PowerSeries.constantCoeff w‖ := by rw [hval, norm_neg]
      _ ≤ ‖δ 1 0‖ * 1 := by
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          simpa using hw 0
      _ < 1 := by rw [mul_one]; exact hc
  exact lt_irrefl 1 this

/-- **The Möbius map composes analytically**:
`w_δ ∘ w = (δ₀₁ + δ₀₀·w)/(δ₁₁ + δ₁₀·w)`. -/
theorem compAn_mobius {δ : Matrix (Fin 2) (Fin 2) K} (hd : ‖δ 1 1‖ = 1)
    (hc : ‖δ 1 0‖ < 1) {w : PowerSeries K} (hw : CoeffLeOne w) :
    compAn (mobius δ) w
      = (PowerSeries.C (δ 0 1) + PowerSeries.C (δ 0 0) * w)
        * (PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w)⁻¹ := by
  have hd0 : δ 1 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
  have hlt : ‖δ 1 0‖ < ‖δ 1 1‖ := by rw [hd]; exact hc
  rw [mobius, compAn_mul (absSummable_numX δ) (absSummable_linX_inv hd0 hlt) hw,
    compAn_numX δ hw, compAn_inv (absSummable_linX δ) (absSummable_linX_inv hd0 hlt) hw
      (by rw [constantCoeff_linX]; exact hd0)
      (constantCoeff_compAn_linX_ne_zero hd hc hw),
    compAn_linX δ hw]

omit [CompleteSpace K] in
/-- The Möbius series of a level element has coefficients of norm at most one. -/
theorem coeffLeOne_mobius (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : CoeffLeOne (mobius g) :=
  coeffLeOne_mobius' (W.bounds.integral hg 0 0) (W.bounds.integral hg 0 1)
    (W.bounds.d_unit hg)
    ((W.bounds.c_le hg).trans W.bounds.rho_lt_one.le)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem absSummable_mobius (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : AbsSummable (mobius g) := by
  refine absSummable_mul (absSummable_numX _) (absSummable_linX_inv
    (W.bounds.d_ne_zero hg) ?_)
  rw [W.bounds.d_unit hg]
  exact (W.bounds.c_le hg).trans_lt W.bounds.rho_lt_one

/-- **Analytic Möbius composition**: `compAn (mobius δ) (mobius γ) = mobius (δ * γ)`
on the level (the convergent form of `mobius_mul`). -/
theorem compAn_mobius_mobius (W : WeightSeries S ρ) {γ δ : Matrix (Fin 2) (Fin 2) K}
    (hγ : γ ∈ S) (hδ : δ ∈ S) :
    compAn (mobius δ) (mobius γ) = mobius (δ * γ) := by
  have hγ0 : γ 1 1 ≠ 0 := W.bounds.d_ne_zero hγ
  have hδγ0 : (δ * γ) 1 1 ≠ 0 := W.bounds.d_ne_zero (S.mul_mem hδ hγ)
  rw [compAn_mobius (W.bounds.d_unit hδ)
      ((W.bounds.c_le hδ).trans_lt W.bounds.rho_lt_one) (W.coeffLeOne_mobius hγ),
    mobius_mul_eq γ δ hγ0 hδγ0,
    add_comm (PowerSeries.C (δ 0 1)), add_comm (PowerSeries.C (δ 1 1))]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The automorphy factor of a level element is absolutely summable. -/
theorem absSummable_autFactor (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) : AbsSummable (W.autFactor g) := by
  refine absSummable_mul (W.absSummable hg) (absSummable_pow (absSummable_linX_inv
    (W.bounds.d_ne_zero hg) ?_) 2)
  rw [W.bounds.d_unit hg]
  exact (W.bounds.c_le hg).trans_lt W.bounds.rho_lt_one

/-- **The automorphy-factor cocycle**: `j_{δγ} = j_γ · (j_δ ∘ w_γ)` — the κ-cocycle
field, upgraded through the `(cx+d)⁻²` normalisation. -/
theorem autFactor_cocycle (W : WeightSeries S ρ) {γ δ : Matrix (Fin 2) (Fin 2) K}
    (hγ : γ ∈ S) (hδ : δ ∈ S) :
    W.autFactor (δ * γ) = W.autFactor γ * compAn (W.autFactor δ) (mobius γ) := by
  set w := mobius γ with hwd
  have hγ0 : γ 1 1 ≠ 0 := W.bounds.d_ne_zero hγ
  have hδ0 : δ 1 1 ≠ 0 := W.bounds.d_ne_zero hδ
  have hwc : CoeffLeOne w := W.coeffLeOne_mobius hγ
  have hAS : AbsSummable (W.col (δ 1 0) (δ 1 1)) := W.absSummable hδ
  have hlt : ‖δ 1 0‖ < ‖δ 1 1‖ := by
    rw [W.bounds.d_unit hδ]
    exact (W.bounds.c_le hδ).trans_lt W.bounds.rho_lt_one
  have hAI : AbsSummable (linX δ)⁻¹ := absSummable_linX_inv hδ0 hlt
  have hLinv : compAn ((linX δ)⁻¹) w = (compAn (linX δ) w)⁻¹ :=
    compAn_inv (absSummable_linX δ) hAI hwc
      (by rw [constantCoeff_linX]; exact hδ0)
      (constantCoeff_compAn_linX_ne_zero (W.bounds.d_unit hδ)
        (by rw [← W.bounds.d_unit hδ]; exact hlt) hwc)
  have hcoc := W.cocycle hγ hδ
  have hfac : linX (δ * γ) = linX γ * compAn (linX δ) w := by
    rw [compAn_linX δ hwc, linX_mul_eq γ δ hγ0, add_comm]
  have hlin : (δ * γ) 1 0 = (δ * γ) 1 0 := rfl
  rw [autFactor, autFactor, autFactor, hcoc, hfac, PowerSeries.mul_inv_rev,
    compAn_mul hAS (absSummable_pow hAI 2) hwc, compAn_pow hAI hwc 2, hLinv]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Every column of the generating function is absolutely summable on the level. -/
theorem absSummable_yCoeff_genFun (W : WeightSeries S ρ)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ S) (r : ℕ) :
    AbsSummable (yCoeff (W.genFun g) r) := by
  rw [W.yCoeff_genFun (W.bounds.d_ne_zero hg) r]
  exact absSummable_mul (W.absSummable_autFactor hg)
    (absSummable_pow (W.absSummable_mobius hg) r)

/-- **The column cocycle**, the generating-function form of `kappaSlash_mul`:
`yCoeff (genFun (δγ)) r = j_γ · ((yCoeff (genFun δ) r) ∘ w_γ)`. -/
theorem yCoeff_genFun_mul (W : WeightSeries S ρ) {γ δ : Matrix (Fin 2) (Fin 2) K}
    (hγ : γ ∈ S) (hδ : δ ∈ S) (r : ℕ) :
    yCoeff (W.genFun (δ * γ)) r
      = W.autFactor γ * compAn (yCoeff (W.genFun δ) r) (mobius γ) := by
  have hγ0 : γ 1 1 ≠ 0 := W.bounds.d_ne_zero hγ
  have hδ0 : δ 1 1 ≠ 0 := W.bounds.d_ne_zero hδ
  have hδγ0 : (δ * γ) 1 1 ≠ 0 := W.bounds.d_ne_zero (S.mul_mem hδ hγ)
  have hwc : CoeffLeOne (mobius γ) := W.coeffLeOne_mobius hγ
  rw [W.yCoeff_genFun hδγ0 r, W.yCoeff_genFun hδ0 r,
    compAn_mul (W.absSummable_autFactor hδ)
      (absSummable_pow (W.absSummable_mobius hδ) r) hwc,
    compAn_pow (W.absSummable_mobius hδ) hwc r, W.compAn_mobius_mobius hγ hδ,
    W.autFactor_cocycle hγ hδ]
  ring

/-- The diagonal series `∑ₘ xᵐyᵐ = (1 − xy)⁻¹`. -/
private noncomputable def diagSeries : MvPowerSeries (Fin 2) K :=
  fun p => if p 0 = p 1 then 1 else 0

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem coeff_diagSeries (p : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff p (diagSeries (K := K)) = if p 0 = p 1 then 1 else 0 := rfl

/-- The action of the identity is the identity ([Jacobs, Def 1.27]'s easy check,
identity half): at `γ = 1` the generating function collapses to `1/(1 − xy)`. -/
theorem kappaSlash_one (W : WeightSeries S ρ) :
    W.kappaSlash 1 = ContinuousLinearMap.id K c(ℕ, K) := by
  refine ext_matrixCoeff fun j i => ?_
  rw [W.matrixCoeff_kappaSlash 1 j i]
  have hF : W.genFun ((1 : S) : Matrix (Fin 2) (Fin 2) K) = diagSeries := by
    have h11 : ((1 : S) : Matrix (Fin 2) (Fin 2) K) = 1 := rfl
    have hc0 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp
    have hd1 : (1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by simp
    have hquad : quadSeries (1 : Matrix (Fin 2) (Fin 2) K)
        = 1 - MvPowerSeries.X 0 * MvPowerSeries.X 1 := by
      rw [quadSeries]; simp
    have hlin : linSeries (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [linSeries]; simp
    rw [WeightSeries.genFun, h11, hc0, hd1, W.col_zero_one, yExtend_one, hlin, hquad,
      inv_one, one_mul, one_mul]
    refine (MvPowerSeries.inv_eq_iff_mul_eq_one ?_).mpr ?_
    · simp
    · have hXX : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)
          = MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) 1
              + Finsupp.single (1 : Fin 2) 1) 1 := by
        rw [MvPowerSeries.X_def, MvPowerSeries.X_def,
          MvPowerSeries.monomial_mul_monomial, mul_one]
      refine MvPowerSeries.ext fun p => ?_
      rw [mul_sub, mul_one, map_sub, hXX, MvPowerSeries.coeff_mul_monomial,
        coeff_diagSeries, MvPowerSeries.coeff_one]
      set n : Fin 2 →₀ ℕ :=
        Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 with hn
      have hn0 : n 0 = 1 := by simp [n]
      have hn1 : n 1 = 1 := by simp [n]
      by_cases hle : n ≤ p
      · have h0 : (p - n) 0 = p 0 - 1 := by simp [Finsupp.tsub_apply, hn0]
        have h1 : (p - n) 1 = p 1 - 1 := by simp [Finsupp.tsub_apply, hn1]
        have hp0 : 1 ≤ p 0 := by simpa [hn0] using hle 0
        have hp1 : 1 ≤ p 1 := by simpa [hn1] using hle 1
        rw [if_pos hle, mul_one, coeff_diagSeries, h0, h1]
        by_cases hd : p 0 = p 1
        · rw [if_pos hd, if_pos (by omega), if_neg, sub_self]
          intro hc
          rw [hc] at hp0
          simp at hp0
        · rw [if_neg hd, if_neg (by omega), if_neg, sub_zero]
          intro hc
          rw [hc] at hp0
          simp at hp0
      · rw [if_neg hle, sub_zero]
        by_cases hp : p = 0
        · subst hp
          simp
        · rw [if_neg hp, if_neg]
          intro hd
          exact hle (by
            intro k
            fin_cases k
            · simpa [hn0] using Nat.one_le_iff_ne_zero.mpr (by
                intro hz
                exact hp (TateFredholm.fin2_eq_zero hz (hd ▸ hz)))
            · simpa [hn1] using Nat.one_le_iff_ne_zero.mpr (by
                intro hz
                exact hp (TateFredholm.fin2_eq_zero (hd.symm ▸ hz) hz)))
  rw [hF, coeff_diagSeries]
  simp only [idx_apply_zero, idx_apply_one]
  rw [TateFredholm.matrixCoeff]
  show (if j = i then (1 : K) else 0) = (Pi.single i (1 : K) : ℕ → K) j
  rw [Pi.single_apply]

/-- **The right-action law** ([Jacobs, Def 1.27]'s easy check, composition half):
via the column identity, reduces to Möbius composition plus the κ-cocycle field. -/
theorem kappaSlash_mul (W : WeightSeries S ρ) (g h : S) :
    W.kappaSlash (g * h) = (W.kappaSlash h).comp (W.kappaSlash g) := by
  have hadj : ((g * h) : S).1 = g.1 * h.1 := rfl
  have hwc : CoeffLeOne (mobius h.1) := W.coeffLeOne_mobius h.2
  refine ext_matrixCoeff fun j i => ?_
  rw [W.matrixCoeff_kappaSlash, TateFredholm.matrixCoeff_comp, hadj, ← coeff_yCoeff,
    W.yCoeff_genFun_mul h.2 g.2 i,
    coeff_mul_compAn (W.absSummable_yCoeff_genFun g.2 i) hwc]
  refine tsum_congr fun k => ?_
  rw [W.matrixCoeff_kappaSlash, W.matrixCoeff_kappaSlash, ← coeff_yCoeff,
    ← coeff_yCoeff, W.yCoeff_genFun (W.bounds.d_ne_zero h.2) k, autFactor]

/-- The Tate algebra `c(ℕ, K)` as a right `S`-module via `kappaSlash` — [Jacobs,
Def 1.27] for the abstract weight `W`, natively right-handed. -/
@[instance_reducible]
noncomputable def kappaSlashAction (W : WeightSeries S ρ) :
    RightSlashAction S c(ℕ, K) where
  slash f g := W.kappaSlash g f
  zero_slash g := map_zero (W.kappaSlash g)
  slash_one f := by
    show W.kappaSlash 1 f = f
    rw [W.kappaSlash_one]
    rfl
  slash_mul f g h := by
    show W.kappaSlash (g * h) f = W.kappaSlash h (W.kappaSlash g f)
    rw [W.kappaSlash_mul g h]
    rfl
  add_slash f₁ f₂ g := map_add (W.kappaSlash g) f₁ f₂

/-- The weight action commutes with scalars (each `kappaSlash g` is `K`-linear). -/
theorem smulSlashClass (W : WeightSeries S ρ) :
    letI := W.kappaSlashAction
    RightSlashAction.SMulSlashClass K S c(ℕ, K) :=
  letI := W.kappaSlashAction
  ⟨fun r f g => map_smul (W.kappaSlash g) r f⟩

end WeightSeries

end QMF

namespace RightSlashAction

/-- Transport of a right slash action along a monoid homomorphism: `a ∣ₛ δ := a ∣ₛ τ δ`.
(A `def`, not an instance: the source action is a value.) -/
@[instance_reducible]
noncomputable def comap {Δ' Δ A : Type*} [Monoid Δ'] [Monoid Δ] [AddMonoid A]
    (τ : Δ' →* Δ) (act : RightSlashAction Δ A) : RightSlashAction Δ' A where
  slash a δ := act.slash a (τ δ)
  zero_slash δ := act.zero_slash (τ δ)
  slash_one a := by rw [map_one, act.slash_one]
  slash_mul a δ₁ δ₂ := by rw [map_mul, act.slash_mul]
  add_slash a b δ := act.add_slash a b (τ δ)

@[simp] theorem comap_slash {Δ' Δ A : Type*} [Monoid Δ'] [Monoid Δ] [AddMonoid A]
    (τ : Δ' →* Δ) (act : RightSlashAction Δ A) (a : A) (δ : Δ') :
    (comap τ act).slash a δ = act.slash a (τ δ) :=
  rfl

/-- Twist of a right slash action by a scalar character `χ : Δ →* Rˣ`:
`a ∣ₛ' δ := χ δ • (a ∣ₛ δ)`.  Because `χ` is multiplicative and central, the axioms
survive; this is the vessel for the classical determinant character `ν` on top of
[Jacobs, Def 1.27] (which is the `χ = 1` case). -/
@[instance_reducible]
noncomputable def twist {R Δ A : Type*} [Monoid Δ] [AddCommMonoid A] [CommSemiring R]
    [Module R A] (act : RightSlashAction Δ A)
    (hsmul : ∀ (r : R) (a : A) (δ : Δ), act.slash (r • a) δ = r • act.slash a δ)
    (χ : Δ →* Rˣ) : RightSlashAction Δ A where
  slash a δ := χ δ • act.slash a δ
  zero_slash δ := by rw [act.zero_slash, smul_zero]
  slash_one a := by rw [map_one, act.slash_one, one_smul]
  slash_mul a δ₁ δ₂ := by
    rw [map_mul, act.slash_mul, Units.smul_def, Units.smul_def, Units.smul_def,
      hsmul, Units.val_mul, mul_smul, smul_comm]
  add_slash a b δ := by rw [act.add_slash, smul_add]

@[simp] theorem twist_slash {R Δ A : Type*} [Monoid Δ] [AddCommMonoid A] [CommSemiring R]
    [Module R A] (act : RightSlashAction Δ A) (hsmul) (χ : Δ →* Rˣ) (a : A) (δ : Δ) :
    (twist (R := R) act hsmul χ).slash a δ = χ δ • act.slash a δ :=
  rfl

end RightSlashAction

namespace QMF

open Valued

variable {K : Type*} [NontriviallyNormedField K]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-- **The valuation ↔ norm dictionary for levels**: a valued-field `Σ₀'(γ)` satisfies
the norm-form level bounds, given the two dictionary facts tying the valuation to the
norm (discharged at a rank-one completion by `Valued.toNormedField`, as in the Jacobs
fork's `norm_le_of_valued_le` / `norm_eq_one_of_valued_eq_one`). -/
theorem Sigma0'.levelBounds {γv : Γ₀} {hγv : γv < 1} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < 1)
    (hdict1 : ∀ x : K, Valued.v x ≤ 1 → ‖x‖ ≤ 1)
    (hdict1' : ∀ x : K, Valued.v x = 1 → ‖x‖ = 1)
    (hdictρ : ∀ x : K, Valued.v x ≤ γv → ‖x‖ ≤ ρ) :
    LevelBounds (Sigma0' K γv hγv) ρ where
  rho_nonneg := hρ0
  rho_lt_one := hρ
  integral hg i j := hdict1 _ (hg.1 i j)
  c_le hg := hdictρ _ hg.2.1
  d_unit hg := hdict1' _ hg.2.2.1

end QMF
