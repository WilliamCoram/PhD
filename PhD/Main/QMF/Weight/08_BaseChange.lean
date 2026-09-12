/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.Weight.«07_Fredholm»
import PhD.Main.TateFredholm.«08_BaseChange»
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Base change of weights, Hecke blocks and Fredholm determinants

Given two analytic weights — `κ` over `K` at level `(S, ρ)` and `κ'` over `L` at level
`(S', ρ')` — whose expansions match along a ring homomorphism `ι : K →+* L` on the image of
the level (`κ'.col (ι c) (ι d) = map ι (κ.col c d)`), the weight actions have `ι`-related
matrix coefficients, hence so do the certificate blocks of `[UηU]`, and (for bounded `ι`) the
Fredholm determinant of `[UηU]` over `L` is the coefficientwise image of the one over `K`
([Buzzard, *Eigenvarieties*, Lemma 2.13]: "the characteristic power series is compatible with
base change"; `TateFredholm.charPowerSeries_baseChange`).  Nothing here constructs the weight
over `L` — that is the business of whoever has the character (the Jacobs weight is generic in
the field, `JacobsSlash.jacobsWeightOf`).

## Main declarations

* `QMF.map_yExtend`, `QMF.WeightSeries.map_genFun`,
  `QMF.WeightSeries.matrixCoeff_kappaSlash_map`, `QMF.AnalyticWeight.matrixCoeff_kappaSlash_map` —
  the weight action commutes with `ι` on the level.
* `QMF.Weight.mapTheta` — the component map composed with `ι` (`Matrix.map`).
* `QMF.Weight.matrixCoeff_heckeBlock_map`, `QMF.Weight.matrixCoeff_heckeBlockOp_map`,
  `QMF.Weight.heckeCharPowerSeries_map` — blocks and determinant commute with `ι`.
-/

open TateFredholm
open scoped TateFredholm QMF Pointwise

namespace QMF

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
/-- The `y`-extension commutes with coefficientwise maps. -/
theorem map_yExtend (ι : K →+* L) (φ : PowerSeries K) :
    MvPowerSeries.map ι (WeightSeries.yExtend φ) = WeightSeries.yExtend (PowerSeries.map ι φ) := by
  refine MvPowerSeries.ext fun p => ?_
  rw [MvPowerSeries.coeff_map, WeightSeries.coeff_yExtend, WeightSeries.coeff_yExtend]
  split_ifs with h
  · rw [PowerSeries.coeff_map]
  · rw [map_zero]

variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}
  {S' : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ' : ℝ}

namespace WeightSeries

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
/-- **The generating function commutes with `ι`** when the columns do: [Jacobs, Prop 2.6]'s
formula `κ(cx+d)/((cx+d)(cx+d−axy−by))` is a field expression in the entries and the column. -/
theorem map_genFun (W : WeightSeries S ρ) (W' : WeightSeries S' ρ') (ι : K →+* L)
    (g : Matrix (Fin 2) (Fin 2) K)
    (hcol : W'.col (ι (g 1 0)) (ι (g 1 1)) = PowerSeries.map ι (W.col (g 1 0) (g 1 1))) :
    MvPowerSeries.map ι (W.genFun g) = W'.genFun (g.map ι) := by
  rw [WeightSeries.genFun, WeightSeries.genFun, map_mul, map_mul, MvPowerSeries.map_inv₀,
    MvPowerSeries.map_inv₀, TateFredholm.map_linSeries, TateFredholm.map_quadSeries,
    map_yExtend]
  rw [show (g.map ι) 1 0 = ι (g 1 0) from rfl, show (g.map ι) 1 1 = ι (g 1 1) from rfl, hcol]

/-- The weight actions have `ι`-related matrix coefficients on the level. -/
theorem matrixCoeff_kappaSlash_map (W : WeightSeries S ρ) (W' : WeightSeries S' ρ') (ι : K →+* L)
    (g : S) (hg' : g.1.map ι ∈ S')
    (hcol : W'.col (ι (g.1 1 0)) (ι (g.1 1 1)) = PowerSeries.map ι (W.col (g.1 1 0) (g.1 1 1)))
    (j i : ℕ) :
    matrixCoeff (W'.kappaSlash ⟨g.1.map ι, hg'⟩) j i = ι (matrixCoeff (W.kappaSlash g) j i) := by
  rw [WeightSeries.matrixCoeff_kappaSlash, WeightSeries.matrixCoeff_kappaSlash,
    ← W.map_genFun W' ι g.1 hcol, MvPowerSeries.coeff_map]

end WeightSeries

namespace AnalyticWeight

variable {UK : Subgroup Kˣ} {UL : Subgroup Lˣ}

/-- The weight actions of two analytic weights with `ι`-matching expansions have `ι`-related
matrix coefficients on the level. -/
theorem matrixCoeff_kappaSlash_map (κ : AnalyticWeight UK S ρ) (κ' : AnalyticWeight UL S' ρ')
    (ι : K →+* L) (g : S) (hg' : g.1.map ι ∈ S')
    (hcol : κ'.expansion.col (ι (g.1 1 0)) (ι (g.1 1 1))
      = PowerSeries.map ι (κ.expansion.col (g.1 1 0) (g.1 1 1))) (j i : ℕ) :
    matrixCoeff (κ'.kappaSlash ⟨g.1.map ι, hg'⟩) j i = ι (matrixCoeff (κ.kappaSlash g) j i) :=
  WeightSeries.matrixCoeff_kappaSlash_map κ.toWeightSeries κ'.toWeightSeries ι g hg' hcol j i

end AnalyticWeight

namespace Weight

variable {G : Type*} [Group G] {Γ : Subgroup G}

/-- The component map composed with `ι`: `g ↦ (θ g).map ι`. -/
noncomputable def mapTheta (ι : K →+* L) (θ : G →* Matrix (Fin 2) (Fin 2) K) :
    G →* Matrix (Fin 2) (Fin 2) L :=
  (ι.mapMatrix : Matrix (Fin 2) (Fin 2) K →+* Matrix (Fin 2) (Fin 2) L).toMonoidHom.comp θ

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
@[simp] theorem mapTheta_apply (ι : K →+* L) (θ : G →* Matrix (Fin 2) (Fin 2) K) (g : G) :
    mapTheta ι θ g = (θ g).map ι :=
  rfl

variable (ι : K →+* L) (θ : G →* Matrix (Fin 2) (Fin 2) K)
variable {UK : Subgroup Kˣ} {UL : Subgroup Lˣ}
variable {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {T : Type*} [Fintype T]
variable (κ : AnalyticWeight UK S ρ) (κ' : AnalyticWeight UL S' ρ') (U : Subgroup G)
  (hU : (U : Set G) ⊆ levelMonoidOf θ S) (hU' : (U : Set G) ⊆ levelMonoidOf (mapTheta ι θ) S')
  (χ : S →* Kˣ) (χ' : S' →* Lˣ)

omit [Fintype ι'] in
/-- The certificate blocks of `[UηU]` over `L` are the `ι`-images of those over `K`. -/
theorem matrixCoeff_heckeBlock_map (hS' : ∀ g ∈ S, g.map ι ∈ S')
    (hcol : ∀ g ∈ S, κ'.expansion.col (ι (g 1 0)) (ι (g 1 1))
      = PowerSeries.map ι (κ.expansion.col (g 1 0) (g 1 1)))
    (hχ : ∀ g (hg : g ∈ S), ((χ' ⟨g.map ι, hS' g hg⟩ : Lˣ) : L) = ι ((χ ⟨g, hg⟩ : Kˣ) : K))
    (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hvΔ' : ∀ t, vRep t ∈ levelMonoidOf (mapTheta ι θ) S')
    (idx : ι' → T → ι') (u : ι' → T → U) (i j : ι') (m r : ℕ) :
    matrixCoeff (heckeBlock (mapTheta ι θ) κ' U hU' χ' vRep hvΔ' idx u i j) m r
      = ι (matrixCoeff (heckeBlock θ κ U hU χ vRep hvΔ idx u i j) m r) := by
  simp only [heckeBlock, matrixCoeff_sum, matrixCoeff_smul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hmem : θ ((u i t : G) * vRep t) ∈ S := mul_mem (hU (u i t).2) (hvΔ t)
  have hθ : mapTheta ι θ ((u i t : G) * vRep t) = (θ ((u i t : G) * vRep t)).map ι := rfl
  rw [show (levelMonoidOfToS (mapTheta ι θ) S'
      ⟨(u i t : G) * vRep t, mul_mem (hU' (u i t).2) (hvΔ' t)⟩)
      = ⟨(θ ((u i t : G) * vRep t)).map ι, hS' _ hmem⟩ from Subtype.ext hθ,
    show (levelMonoidOfToS θ S ⟨(u i t : G) * vRep t, mul_mem (hU (u i t).2) (hvΔ t)⟩)
      = ⟨θ ((u i t : G) * vRep t), hmem⟩ from rfl,
    hχ _ hmem,
    AnalyticWeight.matrixCoeff_kappaSlash_map κ κ' ι ⟨θ ((u i t : G) * vRep t), hmem⟩
      (hS' _ hmem) (hcol _ hmem) m r]

/-- The block operator of `[UηU]` over `L` is the `ι`-image of the one over `K`. -/
theorem matrixCoeff_heckeBlockOp_map (hS' : ∀ g ∈ S, g.map ι ∈ S')
    (hcol : ∀ g ∈ S, κ'.expansion.col (ι (g 1 0)) (ι (g 1 1))
      = PowerSeries.map ι (κ.expansion.col (g 1 0) (g 1 1)))
    (hχ : ∀ g (hg : g ∈ S), ((χ' ⟨g.map ι, hS' g hg⟩ : Lˣ) : L) = ι ((χ ⟨g, hg⟩ : Kˣ) : K))
    (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hvΔ' : ∀ t, vRep t ∈ levelMonoidOf (mapTheta ι θ) S')
    (idx : ι' → T → ι') (u : ι' → T → U) (p q : ι' × ℕ) :
    matrixCoeff (heckeBlockOp (mapTheta ι θ) κ' U hU' χ' vRep hvΔ' idx u) p q
      = ι (matrixCoeff (heckeBlockOp θ κ U hU χ vRep hvΔ idx u) p q) := by
  obtain ⟨i, m⟩ := p
  obtain ⟨j, r⟩ := q
  rw [heckeBlockOp, heckeBlockOp, matrixCoeff_blockOp, matrixCoeff_blockOp]
  exact matrixCoeff_heckeBlock_map ι θ κ κ' U hU hU' χ χ' hS' hcol hχ vRep hvΔ hvΔ' idx u i j m r

/-- **The Fredholm determinant commutes with bounded base change** ([Buzzard,
*Eigenvarieties*, Lemma 2.13]; `TateFredholm.charPowerSeries_baseChange`). -/
theorem heckeCharPowerSeries_map (hι : ∀ x, ‖ι x‖ ≤ ‖x‖) (hS' : ∀ g ∈ S, g.map ι ∈ S')
    (hcol : ∀ g ∈ S, κ'.expansion.col (ι (g 1 0)) (ι (g 1 1))
      = PowerSeries.map ι (κ.expansion.col (g 1 0) (g 1 1)))
    (hχ : ∀ g (hg : g ∈ S), ((χ' ⟨g.map ι, hS' g hg⟩ : Lˣ) : L) = ι ((χ ⟨g, hg⟩ : Kˣ) : K))
    (vRep : T → G) (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S)
    (hvΔ' : ∀ t, vRep t ∈ levelMonoidOf (mapTheta ι θ) S')
    (idx : ι' → T → ι') (u : ι' → T → U)
    (hcomp : IsCompactoid (heckeBlockOp θ κ U hU χ vRep hvΔ idx u)) :
    heckeCharPowerSeries (mapTheta ι θ) κ' U hU' χ' vRep hvΔ' idx u
      = PowerSeries.map ι (heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u) :=
  charPowerSeries_baseChange _ ι 1 (fun r => by simpa using hι r) _ hcomp _
    fun p q => matrixCoeff_heckeBlockOp_map ι θ κ κ' U hU hU' χ χ' hS' hcol hχ vRep hvΔ hvΔ'
      idx u p q

end Weight

end QMF
