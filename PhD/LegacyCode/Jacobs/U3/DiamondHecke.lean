/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3.Fredholm

/-!
# AG-W-ID: the diamond operator `W` is the genuine `[U₁(9)·μ·U₁(9)]`

The identification of the transcribed diamond operator (`Jacobs.Wop`, the block-cyclic
`δ`-operator of `PhD.Jacobs.DiamondW`) with the Hecke operator `W = [U₁(9)·μ·U₁(9)]`,
`μ = diag(1,4)` at `3` in the thesis's right-handed convention — `diag(4,1)` here (the
left-handed adjugate transport, as for every matrix of this development).  Board
`.mathlib-quality/jacobs-endgame/`, WI-tickets; see `decomposition.md` §AG-W-ID.

Three layers:

* **The wide acting monoid `Σ₁(3)`** (`Sigma1₃`): the `μ`-acting elements have
  `(0,0)`-entry `≡ 1` only mod `3`, not mod `9`, so `Sigma1` is too narrow.  The
  `κ`-analytics only ever use the mod-`3` threshold (all three `γ₉`-uses in
  `KappaAction.lean` immediately weaken via `hγ9le3 : γ₉ ≤ v(3)`), so the action
  extends: `kappaOpW` with `kappaOpW_restrict` pinning it against `kappaOp`.
* **The certificate layer**: `U₁(9)·μ·U₁(9) = μ·U₁(9)` is a SINGLE left coset (`μ`
  normalises `U₁(9)` — diagonal conjugation scales the off-diagonal entries by the
  `3`-unit `4^{±1}`), and the three factorisations `cᵢ·μ = d·c_{σ(i)}·u(i)` have
  `σ = (1, 2, 0)` (the 3-cycle matching `Wop`'s block layout) and `d ∈ {±1}` —
  computed by exhaustive search (`certificate_search_w.py`, unique hit per class over
  the 312 candidates; the `u(i)` are rational diagonal: `diag(−4/5, −1/2)`,
  `diag(−20/7, −1/2)`, `diag(28, 4)`).
* **The identification**: the acting matrices are diagonal with
  `a/d ∈ {2/5, 10/7, 7/4}` — exactly the `D`-arguments of `δ₀,₁, δ₁,₂, δ₂,₀` — and
  `weightGenFun` of a diagonal matrix is `κ(d)·d⁻²` times the geometric diagonal
  (`coeff_weightGenFun_diagonal`), so each acting operator is the transcribed `δ` up to
  the same `classWeight` coboundary as AG-B's B15 (`acting = (φᵢ⁻¹·φ_{σ(i)}) • δ`).
  `heckeW_apply_classRep` is then the `W`-analogue of the AG-B headline, and
  `Binvop_comp_Wop_comp_Bop` diagonalises `Wop` to `diag(1, ω²·1, ω·1)` — with
  `lemma210`, the wording "`M₂,₂` is the `ω²`-eigenblock of the diamond operator" is a
  theorem.
-/

open Quaternion IsDedekindDomain NumberField QMF TateFredholm
open scoped Pointwise

namespace Jacobs.U3

/-! ### The wide acting monoid `Σ₁(3)` -/

/-- The tame threshold `v(3)`. -/
def γ₃ : WithZero (Multiplicative ℤ) := (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ)

theorem γ₃_lt_one : γ₃ < 1 := by sorry

theorem valued_three_eq_γ₃ : Valued.v (3 : K₃) = γ₃ := by sorry

/-- The wide acting monoid `Σ₁(3)`: `Σ₀`-integrality at level `9` but the `1`-unit
condition on the `(0,0)`-entry only mod `3` — the honest domain of the `κ`-analytics. -/
def Sigma1₃ : Submonoid (Matrix (Fin 2) (Fin 2) K₃) where
  carrier := {g | g ∈ Sigma0 K₃ γ₉ γ₉_lt_one ∧ Valued.v (g 0 0 - 1) ≤ γ₃}
  one_mem' := by sorry
  mul_mem' := by sorry

theorem sigma1_le_sigma1₃ : Sigma1 ≤ Sigma1₃ := by sorry

/-- The wide level monoid in `D_f^×`. -/
noncomputable def levelMonoid1₃ : Submonoid (Dfx ℚ D) :=
  Sigma1₃.comap (toMatrix ℚ D v₃)

theorem levelMonoid1_le_levelMonoid1₃ : levelMonoid1 ≤ levelMonoid1₃ := by sorry

theorem U1_9_subset_levelMonoid1₃ : (U1_9 : Set (Dfx ℚ D)) ⊆ levelMonoid1₃ := by sorry

/-! ### The adelic `μ` and the single-coset decomposition -/

/-- `4` as a (central) unit of `D`. -/
noncomputable def fourUnit : Dˣ :=
  Units.map (algebraMap ℚ D).toMonoidHom (Units.mk0 4 (by norm_num))

theorem invFour_ne_zero : ((4 : K₃)⁻¹) ≠ 0 := by sorry

/-- The adelic diamond element: `diag(4,1)` at `3` (left-handed form of the thesis's
`μ = diag(1,4)`), `1` elsewhere — realised as central `4` times `etaAdelic (4⁻¹)`. -/
noncomputable def mu3 : Dfx ℚ D :=
  unitsIncl ℚ D fourUnit * etaAdelic ℚ D v₃ ((4 : K₃)⁻¹) invFour_ne_zero

theorem toMatrix_mu3 : toMatrix ℚ D v₃ mu3 = Matrix.of ![![4, 0], ![0, 1]] := by sorry

theorem mu3_mem_levelMonoid1₃ : mu3 ∈ levelMonoid1₃ := by sorry

/-- `μ` normalises `U₁(9)`: diagonal conjugation scales the off-diagonal entries by the
`3`-unit `4^{±1}` and fixes both congruence conditions. -/
theorem mu3_inv_mul_mem_U1_9 {u : Dfx ℚ D} (hu : u ∈ U1_9) : mu3⁻¹ * u * mu3 ∈ U1_9 := by
  sorry

theorem cosets_mu3_finite :
    (QuotientGroup.mk '' ((U1_9 : Set (Dfx ℚ D)) * {mu3}) :
      Set (Dfx ℚ D ⧸ U1_9)).Finite := by
  sorry

/-- `U₁(9)·μ·U₁(9)` is the single left coset `μ·U₁(9)` ([Jacobs, Lemma 2.9]'s coset
content at `μ`): the `Fin 1`-family `t ↦ μ` is a bijective system of representatives. -/
theorem bijOn_muRep :
    Set.BijOn QuotientGroup.mk (Set.range (fun _ : Fin 1 => mu3))
      (QuotientGroup.mk '' ((U1_9 : Set (Dfx ℚ D)) * {mu3}) :
        Set (Dfx ℚ D ⧸ U1_9)) := by
  sorry

/-! ### The three certificates (`certificate_search_w.py`, 2026-08-06) -/

/-- The class permutation of the diamond action: the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` (matching
`Wop`'s block layout: block `(i, σ i)` is the nonzero one in row `i`). -/
def sigmaTableW : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The certificate factors: central signs `−1, −1, 1`. -/
noncomputable def dTableW : Fin 3 → Dˣ := ![-1, -1, 1]

theorem dTableW_mem (i : Fin 3) : unitsIncl ℚ D (dTableW i) ∈ globalUnits ℚ D :=
  ⟨dTableW i, rfl⟩

/-- The `U₁(9)`-factor, defined by the factorisation equation; at `3` these are the
rational diagonals `diag(−4/5, −1/2)`, `diag(−20/7, −1/2)`, `diag(28, 4)`. -/
noncomputable def uCandW (i : Fin 3) : Dfx ℚ D :=
  (unitsIncl ℚ D (dTableW i) * classRep (sigmaTableW i))⁻¹ * (classRep i * mu3)

theorem uCandW_mem (i : Fin 3) : uCandW i ∈ U1_9 := by sorry

noncomputable def uTableW : Fin 3 → U1_9 := fun i => ⟨uCandW i, uCandW_mem i⟩

theorem factorisationW (i : Fin 3) :
    classRep i * mu3
      = unitsIncl ℚ D (dTableW i) * classRep (sigmaTableW i) * (uTableW i : Dfx ℚ D) := by
  sorry

theorem toMatrix_mu3_mul_inv_uTableW_mem_sigma1₃ (i : Fin 3) :
    toMatrix ℚ D v₃ (mu3 * ((uTableW i : Dfx ℚ D))⁻¹) ∈ Sigma1₃ := by
  sorry

/-! ### The `κ`-action on the wide monoid -/

variable (t : K₃) (ht : ‖t‖ < 1)

/-- The weight-`κ` action of the wide monoid `Σ₁(3)`.  Def-hole (WI3): the honest
construction re-runs `kappaOp`'s definition with the three `γ₉`-lemmas of
`KappaAction.lean` generalised to the `v(3)` threshold their proofs already establish
(`hγ9le3`-pattern at lines 294/349/1312). -/
noncomputable def kappaOpW (g : Sigma1₃) : c(ℕ, K₃) →L[K₃] c(ℕ, K₃) := sorry

/-- `kappaOpW` restricts to `kappaOp` on `Σ₁(9)` — the compatibility contract. -/
theorem kappaOpW_restrict (g : Sigma1) :
    kappaOpW t ht ⟨(g : Matrix (Fin 2) (Fin 2) K₃), sigma1_le_sigma1₃ g.2⟩
      = kappaOp t ht g := by
  sorry

/-- The action law on the wide monoid ([Jacobs, Def 1.27] extended). -/
theorem kappaOpW_mul (g h : Sigma1₃) :
    kappaOpW t ht (g * h) = (kappaOpW t ht g).comp (kappaOpW t ht h) := by
  sorry

/-- The matrix of the wide action is the weight generating function at the adjugate
parameters ([Jacobs, Prop 2.6], wide form; mirrors `matrixCoeff_kappaOp`). -/
theorem matrixCoeff_kappaOpW (g : Sigma1₃) (m r : ℕ) :
    matrixCoeff (kappaOpW t ht g) m r
      = MvPowerSeries.coeff (Jacobs.idx m r)
          (Jacobs.weightGenFun t (adjParams (g : Matrix (Fin 2) (Fin 2) K₃))) := by
  sorry

/-! ### `W = [U₁(9)·μ·U₁(9)]` and its matrix -/

/-- The weight-`κ` space, presented over the wide acting monoid.  Def-hole (WI4): the
honest body is the `levelSubmodule` under the `kappaOpW`-module action pulled back along
the corestriction `levelMonoid1₃ →* Sigma1₃` — the `kappaForms`/`heckeU3` `letI` pattern
of `PhD.Jacobs.U3.Matrix` at the wide monoid. -/
noncomputable def kappaFormsW :
    Submodule K₃ (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) :=
  sorry

/-- The wide presentation is the same submodule: `kappaFormsW = kappaForms` (membership
only quantifies over `U₁(9) ⊆` both monoids, and the two actions agree there by
`kappaOpW_restrict`). -/
theorem kappaFormsW_eq_kappaForms : kappaFormsW t ht = kappaForms t ht := by sorry

/-- **The genuine diamond operator** `W = [U₁(9)·μ·U₁(9)]` on weight-`κ` forms. -/
noncomputable def heckeW : kappaFormsW t ht →ₗ[K₃] kappaFormsW t ht := sorry

/-- **AG-W-ID headline (unconditional)**: the diamond operator evaluated at the class
representatives is the single-certificate action, `(Wφ)(cᵢ) = ⟨μ·u(i)⁻¹⟩ • φ(c_{σ(i)})`
— the `W`-analogue of `heckeU3_apply_classRep`, via `heckeOperator_apply_rep` at the
`Fin 1` coset family. -/
theorem heckeW_apply_classRep (φ : kappaFormsW t ht) (i : Fin 3) :
    ((heckeW t ht φ : kappaFormsW t ht) :
        AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
      = kappaOpW t ht
          ⟨toMatrix ℚ D v₃ (mu3 * ((uTableW i : Dfx ℚ D))⁻¹),
            toMatrix_mu3_mul_inv_uTableW_mem_sigma1₃ i⟩
          ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
            (classRep (sigmaTableW i))) := by
  sorry

/-! ### Identification with the transcribed `δ`'s -/

/-- `weightGenFun` of a diagonal matrix is `κ(d)·d⁻²` times the geometric diagonal:
the coefficient at `(m, r)` is `κ(d)·d⁻²·(a/d)^m` on the diagonal `m = r`, else `0`. -/
theorem _root_.Jacobs.coeff_weightGenFun_diagonal {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [CharZero K] (t a d : K) (hd : d ≠ 0)
    (m r : ℕ) :
    MvPowerSeries.coeff (Jacobs.idx m r)
        (Jacobs.weightGenFun t (Matrix.of ![![a, 0], ![0, d]]))
      = if m = r then Jacobs.unitPow t d * d⁻¹ * d⁻¹ * (a / d) ^ m else 0 := by
  sorry

/-- The three acting operators of the diamond certificates. -/
noncomputable def actingW (i : Fin 3) : c(ℕ, K₃) →L[K₃] c(ℕ, K₃) :=
  kappaOpW t ht
    ⟨toMatrix ℚ D v₃ (mu3 * ((uTableW i : Dfx ℚ D))⁻¹),
      toMatrix_mu3_mul_inv_uTableW_mem_sigma1₃ i⟩

/-- The transcribed `δ`-operators, indexed by the source class. -/
noncomputable def deltaOf (i : Fin 3) : c(ℕ, K₃) →L[K₃] c(ℕ, K₃) :=
  ![Jacobs.delta01 norm_three_lt_one ht, Jacobs.delta12 norm_three_lt_one ht,
    Jacobs.delta20 norm_three_lt_one ht] i

/-- **The `δ`-identification** (B15-analogue): each certificate acting operator is the
transcribed `δ` scaled by the same `classWeight` coboundary as AG-B's blocks — the
acting diagonals are `(classDet σ(i)/classDet i)`-multiples of the thesis's
`(a, d)`-data, and `κ(s·d)·(s·d)⁻² = (κ(s)·s⁻²)·(κ(d)·d⁻²)`. -/
theorem actingW_eq_smul_delta (i : Fin 3) :
    actingW t ht i
      = ((classWeight t i)⁻¹ * classWeight t (sigmaTableW i)) • deltaOf t ht i := by
  sorry

/-! ### The eigen-reading: `Wop` diagonalises to `diag(1, ω², ω)` -/

/-- **`B` diagonalises the diamond operator**: `B⁻¹·W·B = diag(1, ω²·1, ω·1)` — the
blockwise-scalar diagonal whose `r`-th block is the `ω^{2r}`-eigenvalue (block `1` is
the `ω²`-eigenspace, matching `M₂,₂ = the (1,1)-block` of `lemma210`; block `2` is the
`ω`-eigenspace).  With `lemma210` this makes "`M₂,₂` is the restriction of `U₃` to the
`ω²`-eigenblock of the diamond operator" a theorem about the transcribed matrices, and
with `heckeW_apply_classRep`/`actingW_eq_smul_delta` a theorem about the genuine `W`. -/
theorem Binvop_comp_Wop_comp_Bop (ω : K₃) (hω : ω ^ 2 + ω + 1 = 0) :
    (Jacobs.Binvop ω norm_three_lt_one ht hω).comp
        ((Jacobs.Wop norm_three_lt_one ht).comp
          (Jacobs.Bop ω norm_three_lt_one ht hω))
      = TateFredholm.blockOp
          ![![1, 0, 0], ![0, ω ^ 2 • 1, 0], ![0, 0, ω • 1]] := by
  sorry

end Jacobs.U3
