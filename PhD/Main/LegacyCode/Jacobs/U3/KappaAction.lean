/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import PhD.Jacobs.BinomialTheorem
import PhD.Jacobs.U3.Compose
import PhD.Jacobs.U3.Setting
import PhD.Jacobs.U3Data

/-!
# The weight-`κ` action of `Σ₁(9)` on the Tate algebra

[Jacobs, Ch. 1 §1.5 Definition 1.27]:

> "The weight κ action of γ = (a b; c d) ∈ Σ_ν on A_p is given by the continuous
> C_p-linear extension of the map sending z^k ↦ κ(cz + d)/(cz + d)^{2ν} ((az+b)/(cz+d))^k"

and [Jacobs, p. 29 + Proposition 2.6]: on the matrices in play (`c ≡ 0`, `d ≡ 1 mod 9`)
the character is `κ(cx+d) = (cx+d)^t = exp₃(t·log(cx+d))`, and

> "The generating function of the operator |κ (a b; c d) is given by
> κ(cx + d) / ((cx + d)(cx + d − axy − by))."

**Design** (records the AG-B glue noted in `.mathlib-quality/jacobs/decomposition.md`):
the action of a matrix is *defined* as `Jacobs.ofGenFun` of *`Jacobs.weightGenFun`* — the
transcription `PhD.Jacobs.U3Data` already uses — so Proposition 2.6 holds by construction
(`matrixCoeff_kappaOp` below is `Jacobs.matrixCoeff_ofGenFun`), and the mathematical
content moves to where it belongs: the action laws (`kappaOp_mul`), Jacobs's "easy check
that `|κ` is a right-action" (Def 1.27) made honest.  The model of the Tate algebra `A₃`
is `TateFredholm`'s coefficient space `c(ℕ, K₃)` (basis `e_k ↔ z^k`).

The library acts on the *left* (`Sigma0` conventions); a left-form matrix `g` acts as
Jacobs's `|κ (adj g)`, and the adjugate anti-homomorphism turns the right-action law into
the left one.  `weightGenFun` takes the Jacobs-form (right-convention) matrix, so the
translation appears below as `adjParams`.

## Main definitions

* `Jacobs.U3.kappaOp`: the weight-`κ` action of `g ∈ Σ₁(9)` on `c(ℕ, K₃)`.
* `Jacobs.U3.kappaModuleAction`: the resulting `DistribMulAction Σ₁(9) c(ℕ, K₃)`.
* `Jacobs.U3.linX`, `Jacobs.U3.numX`, `Jacobs.U3.mobius`, `Jacobs.U3.autFactor`: the
  denominator `cx + d`, the numerator `ax + b`, the Möbius map `w_γ`, and the automorphy
  factor `j_γ`, as one-variable series.
* `Jacobs.U3.yCoeff`: the `y`-column of a two-variable generating function.

## Main results

* `Jacobs.U3.matrixCoeff_kappaOp`: [Jacobs, Prop 2.6], true by construction.
* `Jacobs.U3.yCoeff_weightGenFun`: `yCoeff (weightGenFun γ) r = j_γ · w_γ^r` — the bridge
  identifying `weightGenFun` with the slash operator.
* `Jacobs.U3.kappaOp_apply`: the slash formula, read coefficientwise.
* `Jacobs.U3.mobius_mul`, `Jacobs.U3.compAn_mobius_mobius`: Möbius composition
  `w_δ ∘ w_γ = w_{δγ}`, formally and analytically.
* `Jacobs.U3.kappaCol_cocycle`, `Jacobs.U3.autFactor_cocycle`: the `κ`-cocycle
  `κ(lin (δγ)) = κ(lin γ) · (κ(lin δ) ∘ w_γ)` and its automorphy-factor form.
* `Jacobs.U3.kappaOp_one`, `Jacobs.U3.kappaOp_mul`: [Jacobs, Def 1.27]'s "easy check"
  made honest — `kappaOp` is a monoid homomorphism into the operators.

## Implementation notes

The composition law canNOT be proved by formal substitution: `PowerSeries.subst` requires
zero constant term, and `mobius γ` has constant term `b/d ≠ 0`.  It is proved instead with
the *analytic* substitution `PowerSeries.compAn` of `PhD/Jacobs/U3/Compose.lean`, which is
a ring homomorphism satisfying a chain rule; the `κ`-half then follows from a first-order
ODE plus the `p`-adic binomial theorem of `PhD/Jacobs/BinomialTheorem.lean`.
-/

open TateFredholm Jacobs
open scoped TateFredholm PowerSeries

/- See `Setting.lean`: pin the adic `Algebra ℚ K₃` path. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace Jacobs.U3

variable (t : K₃) (ht : ‖t‖ < 1)

/-- The Jacobs-form parameter matrix of a left-form `g`: the adjugate `(d −b; −c a)`,
read as the `2×2` array over `K₃` that `Jacobs.weightGenFun` consumes. -/
noncomputable def adjParams (g : Matrix (Fin 2) (Fin 2) K₃) : Matrix (Fin 2) (Fin 2) K₃ :=
  Matrix.adjugate g

/-- The valuation-to-norm dictionary in the direction the `Σ₁(9)` bounds need. -/
theorem norm_le_of_valued_le {x y : K₃} (hy : y ≠ 0) (h : Valued.v x ≤ Valued.v y) :
    ‖x‖ ≤ ‖y‖ := by
  have hy0 : Valued.v y ≠ 0 := by
    simpa using (Valuation.ne_zero_iff Valued.v).mpr hy
  have hdiv : Valued.v (x / y) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (lt_of_le_of_ne zero_le (Ne.symm hy0))]
    exact h
  have hn := Valued.toNormedField.norm_le_one_iff.mpr hdiv
  rw [norm_div, div_le_one (norm_pos_iff.mpr hy)] at hn
  exact hn

theorem norm_eq_one_of_valued_eq_one {x : K₃} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr (le_of_eq h)) ?_
  by_contra hc
  have hlt : ‖x‖ < 1 := not_le.mp hc
  have := Valued.toNormedField.norm_lt_one_iff.mp hlt
  rw [h] at this
  exact lt_irrefl 1 this

/-- Coefficientwise integrality: every coefficient has norm `≤ 1`.  This is the weight-`0`
analogue of `Jacobs.RowInt`; the `‖3‖^m` row decay of `RowInt` is FALSE for a general
`g ∈ Σ₁(9)` (`g = 1` gives `weightGenFun = 1/(1−xy)`, whose `(m,m)`-coefficient is `1`),
so the `Σ₁(9)`-uniform statement has to be this weaker one — recorded adversarial
finding, `decomposition.md` L5.2. -/
def CoeffInt (φ : MvPowerSeries (Fin 2) K₃) : Prop :=
  ∀ p : Fin 2 →₀ ℕ, ‖MvPowerSeries.coeff p φ‖ ≤ 1

theorem coeffInt_of_rowInt {φ : MvPowerSeries (Fin 2) K₃} (hφ : Jacobs.RowInt φ) :
    CoeffInt φ := fun p =>
  (hφ p).trans (pow_le_one₀ (norm_nonneg _) norm_three_lt_one.le)

theorem coeffInt_monomial {n : Fin 2 →₀ ℕ} {v : K₃} (hv : ‖v‖ ≤ 1) :
    CoeffInt (MvPowerSeries.monomial n v) := by
  intro p
  rw [MvPowerSeries.coeff_monomial]
  split_ifs with h
  · exact hv
  · simp

theorem coeffInt_add {φ ψ : MvPowerSeries (Fin 2) K₃} (hφ : CoeffInt φ) (hψ : CoeffInt ψ) :
    CoeffInt (φ + ψ) := fun p => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ p) (hψ p))

theorem coeffInt_neg {φ : MvPowerSeries (Fin 2) K₃} (hφ : CoeffInt φ) : CoeffInt (-φ) :=
  fun p => by rw [map_neg, norm_neg]; exact hφ p

theorem coeffInt_sub {φ ψ : MvPowerSeries (Fin 2) K₃} (hφ : CoeffInt φ) (hψ : CoeffInt ψ) :
    CoeffInt (φ - ψ) := by
  rw [sub_eq_add_neg]; exact coeffInt_add hφ (coeffInt_neg hψ)

theorem coeffInt_mul {φ ψ : MvPowerSeries (Fin 2) K₃} (hφ : CoeffInt φ) (hψ : CoeffInt ψ) :
    CoeffInt (φ * ψ) := by
  intro p
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hφ _) (norm_nonneg _) (hψ _)

/-- Coefficientwise integrality passes to inverses with unit constant coefficient. -/
theorem coeffInt_inv {φ : MvPowerSeries (Fin 2) K₃} (hφ : CoeffInt φ)
    (h1 : ‖MvPowerSeries.constantCoeff φ‖ = 1) : CoeffInt φ⁻¹ := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N →
      ‖MvPowerSeries.coeff p φ⁻¹‖ ≤ 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp
      rw [MvPowerSeries.coeff_inv]
      split_ifs with hp0
      · subst hp0
        simp [norm_inv, h1]
      · rw [norm_mul, norm_neg, norm_inv, h1, inv_one, one_mul]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
          fun x hx => ?_
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
            · exact absurd (Jacobs.fin2_eq_zero (by omega) (by omega)) hne
            · exact h
          rw [norm_mul]
          exact mul_le_one₀ (hφ _) (norm_nonneg _)
            (ih (x.2 0 + x.2 1) (by omega) x.2 rfl)
        · simp
  exact fun p => key (p 0 + p 1) p rfl

/-- Integrality of the weight generating function for `g ∈ Σ₁(9)` ([Jacobs, p. 29]:
"exp₃(t log(cx + d)) converges to an element of `𝒪₃[[x]]`", extended over the geometric
factor): every coefficient has norm `≤ 1`.

NOT the `‖3‖ ^ m` row decay: that stronger bound is false for general `g ∈ Σ₁(9)`
(`g = 1` gives `weightGenFun = 1/(1−xy)`, with `(m,m)`-coefficient `1`) and is special
to the `η`-composed block matrices ([Jacobs, Lemma 2.7] = `Jacobs.norm_coeff_h02_le` and
AG-W's `rowInt` family) — recorded adversarial finding, `decomposition.md` L5.2. -/
@[simp] theorem adjParams_apply (g : Matrix (Fin 2) (Fin 2) K₃) :
    adjParams g = Matrix.of ![![g 1 1, -g 0 1], ![-g 1 0, g 0 0]] :=
  Matrix.adjugate_fin_two g

/-- The **shifted** row bound `‖coeff p φ‖ ≤ ‖3‖ ^ (p 0 − p 1)` (truncated `ℕ`-subtraction).
Between `Jacobs.RowInt` (weight `‖3‖^(p 0)`, too strong on `Σ₁(9)`) and `CoeffInt`
(weight `1`, too weak to give column decay), this is exactly what `Σ₁(9)` supports and
exactly what `ofGenFun`'s column hypothesis needs: at a fixed column `r`, the bound is
`‖3‖^(m−r) → 0`. -/
def ShiftInt (φ : MvPowerSeries (Fin 2) K₃) : Prop :=
  ∀ p : Fin 2 →₀ ℕ, ‖MvPowerSeries.coeff p φ‖ ≤ ‖(3 : K₃)‖ ^ (p 0 - p 1)

theorem shiftInt_of_rowInt {φ : MvPowerSeries (Fin 2) K₃} (hφ : Jacobs.RowInt φ) :
    ShiftInt φ := fun p =>
  (hφ p).trans (pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le (Nat.sub_le _ _))

theorem shiftInt_monomial {n : Fin 2 →₀ ℕ} {v : K₃} (hv : ‖v‖ ≤ ‖(3 : K₃)‖ ^ (n 0 - n 1)) :
    ShiftInt (MvPowerSeries.monomial n v) := by
  intro p
  rw [MvPowerSeries.coeff_monomial]
  split_ifs with h
  · subst h; exact hv
  · simp [pow_nonneg (norm_nonneg (3 : K₃))]

theorem shiftInt_add {φ ψ : MvPowerSeries (Fin 2) K₃} (hφ : ShiftInt φ) (hψ : ShiftInt ψ) :
    ShiftInt (φ + ψ) := fun p => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ p) (hψ p))

theorem shiftInt_neg {φ : MvPowerSeries (Fin 2) K₃} (hφ : ShiftInt φ) : ShiftInt (-φ) :=
  fun p => by rw [map_neg, norm_neg]; exact hφ p

theorem shiftInt_sub {φ ψ : MvPowerSeries (Fin 2) K₃} (hφ : ShiftInt φ) (hψ : ShiftInt ψ) :
    ShiftInt (φ - ψ) := by
  rw [sub_eq_add_neg]; exact shiftInt_add hφ (shiftInt_neg hψ)

/-- The shift weight is superadditive along the antidiagonal:
`(a−b) + (c−d) ≥ (a+c) − (b+d)` in `ℕ`. -/
private theorem shift_mul_le {x y : Fin 2 →₀ ℕ} :
    ‖(3 : K₃)‖ ^ (x 0 - x 1) * ‖(3 : K₃)‖ ^ (y 0 - y 1)
      ≤ ‖(3 : K₃)‖ ^ ((x + y) 0 - (x + y) 1) := by
  rw [← pow_add]
  refine pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le ?_
  simp only [Finsupp.add_apply]
  omega

theorem shiftInt_mul {φ ψ : MvPowerSeries (Fin 2) K₃} (hφ : ShiftInt φ) (hψ : ShiftInt ψ) :
    ShiftInt (φ * ψ) := by
  intro p
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (pow_nonneg (norm_nonneg _) _) fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [norm_mul]
  refine le_trans (mul_le_mul (hφ _) (hψ _) (norm_nonneg _)
    (pow_nonneg (norm_nonneg _) _)) ?_
  rw [← hx]
  exact shift_mul_le

theorem shiftInt_inv {φ : MvPowerSeries (Fin 2) K₃} (hφ : ShiftInt φ)
    (h1 : ‖MvPowerSeries.constantCoeff φ‖ = 1) : ShiftInt φ⁻¹ := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N →
      ‖MvPowerSeries.coeff p φ⁻¹‖ ≤ ‖(3 : K₃)‖ ^ (p 0 - p 1) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp
      rw [MvPowerSeries.coeff_inv]
      split_ifs with hp0
      · subst hp0
        simp [norm_inv, h1]
      · rw [norm_mul, norm_neg, norm_inv, h1, inv_one, one_mul]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
          (pow_nonneg (norm_nonneg _) _) fun x hx => ?_
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
            · exact absurd (Jacobs.fin2_eq_zero (by omega) (by omega)) hne
            · exact h
          rw [norm_mul]
          refine le_trans (mul_le_mul (hφ _) (ih (x.2 0 + x.2 1) (by omega) x.2 rfl)
            (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) ?_
          rw [← pow_add]
          exact pow_le_pow_of_le_one (norm_nonneg _) norm_three_lt_one.le (by omega)
        · simp [pow_nonneg (norm_nonneg (3 : K₃))]
  exact fun p => key (p 0 + p 1) p rfl

include ht in
/-- The three factors of `weightGenFun` are coefficientwise integral for `g ∈ Σ₁(9)`. -/
theorem coeffInt_weightGenFun (g : Sigma1) :
    CoeffInt (weightGenFun t (adjParams g.1)) := by
  obtain ⟨⟨hint, hc, ha, -⟩, ha1⟩ := g.2
  have h3 : ‖(3 : K₃)‖ < 1 := norm_three_lt_one
  have h30 : (3 : K₃) ≠ 0 := three_ne_zero
  have h90 : (9 : K₃) ≠ 0 := by norm_num
  have hv3 : Valued.v (3 : K₃) ≤ 1 := Valued.toNormedField.norm_le_one_iff.mp h3.le
  have hn9 : ‖(9 : K₃)‖ = ‖(3 : K₃)‖ ^ 2 := by
    rw [show (9 : K₃) = 3 * 3 by norm_num, norm_mul, sq]
  have hγ9le3 : γ₉ ≤ Valued.v (3 : K₃) := by
    rw [← valued_nine_eq, show (9 : K₃) = 3 * 3 by norm_num, map_mul]
    exact le_trans (mul_le_mul' le_rfl hv3) (by rw [mul_one])
  have hna : ‖g.1 0 0‖ = 1 := norm_eq_one_of_valued_eq_one ha
  have hna1 : ‖g.1 0 0 - 1‖ ≤ ‖(3 : K₃)‖ :=
    norm_le_of_valued_le h30 (le_trans ha1 hγ9le3)
  have hnc : ‖g.1 1 0‖ ≤ ‖(3 : K₃)‖ ^ 2 := by
    rw [← hn9]
    exact norm_le_of_valued_le h90 (le_trans hc (le_of_eq valued_nine_eq.symm))
  have hnc1 : ‖g.1 1 0‖ ≤ 1 :=
    le_trans hnc (pow_le_one₀ (norm_nonneg _) h3.le)
  have hnint : ∀ i j, ‖g.1 i j‖ ≤ 1 := fun i j =>
    Valued.toNormedField.norm_le_one_iff.mpr (hint i j)
  -- the adjugate entries
  have hγ00 : adjParams g.1 0 0 = g.1 1 1 := by rw [adjParams_apply]; simp
  have hγ01 : adjParams g.1 0 1 = -g.1 0 1 := by rw [adjParams_apply]; simp
  have hγ10 : adjParams g.1 1 0 = -g.1 1 0 := by rw [adjParams_apply]; simp
  have hγ11 : adjParams g.1 1 1 = g.1 0 0 := by rw [adjParams_apply]; simp
  rw [weightGenFun]
  refine coeffInt_mul (coeffInt_mul ?_ ?_) ?_
  · refine coeffInt_of_rowInt (Jacobs.rowInt_kappaSeries₂ h3 ht ?_ ?_)
    · rw [hγ11]; exact hna1
    · rw [hγ10, hγ11, norm_div, norm_neg, hna, div_one]; exact hnc
  · refine coeffInt_inv ?_ ?_
    · rw [Jacobs.linSeries_eq]
      refine coeffInt_add (coeffInt_monomial ?_) (coeffInt_monomial ?_)
      · rw [hγ11, hna]
      · rw [hγ10, norm_neg]; exact hnc1
    · rw [Jacobs.constantCoeff_linSeries, hγ11, hna]
  · refine coeffInt_inv ?_ ?_
    · rw [Jacobs.quadSeries_eq]
      refine coeffInt_sub (coeffInt_sub (coeffInt_add (coeffInt_monomial ?_)
        (coeffInt_monomial ?_)) (coeffInt_monomial ?_)) (coeffInt_monomial ?_)
      · rw [hγ11, hna]
      · rw [hγ10, norm_neg]; exact hnc1
      · rw [hγ00]; exact hnint 1 1
      · rw [hγ01, norm_neg]; exact hnint 0 1
    · rw [Jacobs.constantCoeff_quadSeries, hγ11, hna]

include ht in
theorem norm_coeff_weightGenFun_le_one (g : Sigma1) (m r : ℕ) :
    ‖MvPowerSeries.coeff (idx m r) (weightGenFun t (adjParams g.1))‖ ≤ 1 :=
  coeffInt_weightGenFun t ht g _

include ht in
/-- The shifted bound holds on `Σ₁(9)`: `‖3‖^(m−r)` decay. -/
theorem shiftInt_weightGenFun (g : Sigma1) :
    ShiftInt (weightGenFun t (adjParams g.1)) := by
  obtain ⟨⟨hint, hc, ha, -⟩, ha1⟩ := g.2
  have h3 : ‖(3 : K₃)‖ < 1 := norm_three_lt_one
  have h30 : (3 : K₃) ≠ 0 := three_ne_zero
  have h90 : (9 : K₃) ≠ 0 := by norm_num
  have hv3 : Valued.v (3 : K₃) ≤ 1 := Valued.toNormedField.norm_le_one_iff.mp h3.le
  have hn9 : ‖(9 : K₃)‖ = ‖(3 : K₃)‖ ^ 2 := by
    rw [show (9 : K₃) = 3 * 3 by norm_num, norm_mul, sq]
  have hγ9le3 : γ₉ ≤ Valued.v (3 : K₃) := by
    rw [← valued_nine_eq, show (9 : K₃) = 3 * 3 by norm_num, map_mul]
    exact le_trans (mul_le_mul' le_rfl hv3) (by rw [mul_one])
  have hna : ‖g.1 0 0‖ = 1 := norm_eq_one_of_valued_eq_one ha
  have hna1 : ‖g.1 0 0 - 1‖ ≤ ‖(3 : K₃)‖ :=
    norm_le_of_valued_le h30 (le_trans ha1 hγ9le3)
  have hnc : ‖g.1 1 0‖ ≤ ‖(3 : K₃)‖ ^ 2 := by
    rw [← hn9]
    exact norm_le_of_valued_le h90 (le_trans hc (le_of_eq valued_nine_eq.symm))
  have hsq : ‖(3 : K₃)‖ ^ 2 ≤ ‖(3 : K₃)‖ := by
    simpa using pow_le_pow_of_le_one (norm_nonneg (3 : K₃)) h3.le (by norm_num : 1 ≤ 2)
  have hnc3 : ‖g.1 1 0‖ ≤ ‖(3 : K₃)‖ := le_trans hnc hsq
  have hnint : ∀ i j, ‖g.1 i j‖ ≤ 1 := fun i j =>
    Valued.toNormedField.norm_le_one_iff.mpr (hint i j)
  have hγ00 : adjParams g.1 0 0 = g.1 1 1 := by rw [adjParams_apply]; simp
  have hγ01 : adjParams g.1 0 1 = -g.1 0 1 := by rw [adjParams_apply]; simp
  have hγ10 : adjParams g.1 1 0 = -g.1 1 0 := by rw [adjParams_apply]; simp
  have hγ11 : adjParams g.1 1 1 = g.1 0 0 := by rw [adjParams_apply]; simp
  rw [weightGenFun]
  refine shiftInt_mul (shiftInt_mul ?_ ?_) ?_
  · refine shiftInt_of_rowInt (Jacobs.rowInt_kappaSeries₂ h3 ht ?_ ?_)
    · rw [hγ11]; exact hna1
    · rw [hγ10, hγ11, norm_div, norm_neg, hna, div_one]; exact hnc
  · refine shiftInt_of_rowInt (Jacobs.rowInt_inv (Jacobs.rowInt_linSeries ?_ ?_) ?_)
    · rw [hγ11, hna]
    · rw [hγ10, norm_neg]; exact hnc3
    · rw [Jacobs.constantCoeff_linSeries, hγ11, hna]
  · refine shiftInt_inv ?_ ?_
    · rw [Jacobs.quadSeries_eq]
      refine shiftInt_sub (shiftInt_sub (shiftInt_add (shiftInt_monomial ?_)
        (shiftInt_monomial ?_)) (shiftInt_monomial ?_)) (shiftInt_monomial ?_)
      · simpa [hγ11] using le_of_eq hna
      · simpa [hγ10] using hnc3
      · simpa [hγ00] using hnint 1 1
      · simpa [hγ01] using hnint 0 1
    · rw [Jacobs.constantCoeff_quadSeries, hγ11, hna]

include ht in
/-- Column decay: each column of the weight generating function is a Tate-algebra
element — the action of `g` sends `z^r` into `A₃` ([Jacobs, (2.1.3)]: "`= ∑ a_m^{(r)} z^m`
with `a_m^{(r)} ∈ ℂ₃`", coefficients tending to `0`).  Together with
`norm_coeff_weightGenFun_le_one` this is exactly the input pair of `Jacobs.ofGenFun`. -/
theorem tendsto_coeff_weightGenFun (g : Sigma1) (r : ℕ) :
    Filter.Tendsto (fun m => MvPowerSeries.coeff (idx m r) (weightGenFun t (adjParams g.1)))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm (fun m => ?_)
    (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (3 : K₃))
      norm_three_lt_one).comp (Filter.tendsto_sub_atTop_nat r)))
  simpa using shiftInt_weightGenFun t ht g (idx m r)

/-- The weight-`κ` action of a single `g ∈ Σ₁(9)` on the Tate algebra `c(ℕ, K₃)`:
`Jacobs.ofGenFun` of the weight generating function of the adjugate.
[Jacobs, Def 1.27 + (2.1.3): the operator whose `(m,r)` matrix entry is `a_m^{(r)}`.] -/
noncomputable def kappaOp (ht : ‖t‖ < 1) (g : Sigma1) : c(ℕ, K₃) →L[K₃] c(ℕ, K₃) :=
  ofGenFun (weightGenFun t (adjParams g.1))
    ⟨1, fun j i => norm_coeff_weightGenFun_le_one t ht g j i⟩
    (fun i => by
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_coeff_weightGenFun t ht g i)

/-- **[Jacobs, Proposition 2.6]** (by design): the matrix of `kappaOp g` is the
coefficient array of the generating function `κ(cx+d)/((cx+d)(cx+d−axy−by))` at the
Jacobs-form parameters of `g`. -/
theorem matrixCoeff_kappaOp (g : Sigma1) (j i : ℕ) :
    matrixCoeff (kappaOp t ht g) j i
      = MvPowerSeries.coeff (idx j i) (weightGenFun t (adjParams g.1)) :=
  matrixCoeff_ofGenFun _ _ _ j i

/-- The `y`-column of a two-variable generating function, as a one-variable series in `x`:
`yCoeff F r` is the `x`-series `∑ₙ (coeff xⁿyʳ F) xⁿ`, i.e. the `r`-th column of the
operator's matrix. -/
noncomputable def yCoeff (F : MvPowerSeries (Fin 2) K₃) (r : ℕ) : PowerSeries K₃ :=
  PowerSeries.mk fun n => MvPowerSeries.coeff (idx n r) F

@[simp] theorem coeff_yCoeff (F : MvPowerSeries (Fin 2) K₃) (r n : ℕ) :
    PowerSeries.coeff n (yCoeff F r) = MvPowerSeries.coeff (idx n r) F :=
  PowerSeries.coeff_mk _ _

/-- The linear factor `c·x + d` of `γ`, as a one-variable series. -/
noncomputable def linX (γ : Matrix (Fin 2) (Fin 2) K₃) : PowerSeries K₃ :=
  PowerSeries.C (γ 1 1) + PowerSeries.C (γ 1 0) * PowerSeries.X

/-- The numerator `a·x + b` of the Möbius map of `γ`. -/
noncomputable def numX (γ : Matrix (Fin 2) (Fin 2) K₃) : PowerSeries K₃ :=
  PowerSeries.C (γ 0 1) + PowerSeries.C (γ 0 0) * PowerSeries.X

/-- **The Möbius map of `γ` as a formal series**: `w_γ = (a·x + b)/(c·x + d)`.  Its constant
term is `b/d`, which is why the composition law of `kappaOp` canNOT be proved by formal
substitution (`PowerSeries.subst` needs zero constant term) — see ticket B13b. -/
noncomputable def mobius (γ : Matrix (Fin 2) (Fin 2) K₃) : PowerSeries K₃ :=
  numX γ * (linX γ)⁻¹

/-- **The automorphy factor** `j_γ = κ(c·x + d)/(c·x + d)²`, as a one-variable series. -/
noncomputable def autFactor (t : K₃) (γ : Matrix (Fin 2) (Fin 2) K₃) : PowerSeries K₃ :=
  yCoeff (Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1)) 0 * ((linX γ)⁻¹) ^ 2

/-- A two-variable multidegree is determined by its two components. -/
private theorem finsupp_fin2_ext {p q : Fin 2 →₀ ℕ} (h0 : p 0 = q 0) (h1 : p 1 = q 1) :
    p = q := by
  ext k
  fin_cases k <;> assumption

private theorem eq_idx (p : Fin 2 →₀ ℕ) : p = idx (p 0) (p 1) :=
  finsupp_fin2_ext (by simp) (by simp)

/-- Multiplying by a series concentrated in `y`-degree `0` acts on each `y`-column as a
one-variable convolution: the `y`-grading is respected. -/
theorem coeff_mul_of_yDeg0 {F G : MvPowerSeries (Fin 2) K₃}
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
theorem coeff_mul_of_yDeg1 {F H : MvPowerSeries (Fin 2) K₃}
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
theorem coeff_zero_mul_of_yDeg1 {F H : MvPowerSeries (Fin 2) K₃}
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
noncomputable def yNum (γ : Matrix (Fin 2) (Fin 2) K₃) : MvPowerSeries (Fin 2) K₃ :=
  MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) (γ 0 0)
    + MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) 1) (γ 0 1)

theorem quadSeries_eq_sub (γ : Matrix (Fin 2) (Fin 2) K₃) :
    Jacobs.quadSeries γ = Jacobs.linSeries γ - yNum γ := by
  rw [Jacobs.quadSeries_eq, Jacobs.linSeries_eq, yNum]
  abel

private theorem yDeg0_linSeries (γ : Matrix (Fin 2) (Fin 2) K₃) :
    ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p (Jacobs.linSeries γ) = 0 := by
  intro p hp
  rw [Jacobs.linSeries_eq, map_add, MvPowerSeries.coeff_monomial,
    MvPowerSeries.coeff_monomial, if_neg, if_neg, add_zero]
  · rintro rfl; simp at hp
  · rintro rfl; simp at hp

private theorem yDeg1_yNum (γ : Matrix (Fin 2) (Fin 2) K₃) :
    ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 1 → MvPowerSeries.coeff p (yNum γ) = 0 := by
  intro p hp
  rw [yNum, map_add, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial,
    if_neg, if_neg, add_zero]
  · rintro rfl; simp at hp
  · rintro rfl; simp at hp

@[simp] theorem yCoeff_linSeries (γ : Matrix (Fin 2) (Fin 2) K₃) :
    yCoeff (Jacobs.linSeries γ) 0 = linX γ := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, Jacobs.linSeries_eq, linX, map_add, map_add,
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

@[simp] theorem yCoeff_yNum (γ : Matrix (Fin 2) (Fin 2) K₃) :
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

theorem yCoeff_mul_yDeg0 {F G : MvPowerSeries (Fin 2) K₃}
    (hG : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G = 0) (r : ℕ) :
    yCoeff (F * G) r = yCoeff F r * yCoeff G 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, coeff_mul_of_yDeg0 hG, PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl fun ij _ => by rw [coeff_yCoeff, coeff_yCoeff]

theorem yCoeff_mul_yDeg1 {F H : MvPowerSeries (Fin 2) K₃}
    (hH : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 1 → MvPowerSeries.coeff p H = 0) (r : ℕ) :
    yCoeff (F * H) (r + 1) = yCoeff F r * yCoeff H 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, coeff_mul_of_yDeg1 hH, PowerSeries.coeff_mul]
  exact Finset.sum_congr rfl fun ij _ => by rw [coeff_yCoeff, coeff_yCoeff]

theorem yCoeff_zero_mul_yDeg1 {F H : MvPowerSeries (Fin 2) K₃}
    (hH : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 1 → MvPowerSeries.coeff p H = 0) :
    yCoeff (F * H) 0 = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, coeff_zero_mul_of_yDeg1 hH, map_zero]

/-- The inverse of a series concentrated in `y`-degree `0` is again concentrated there. -/
theorem yDeg0_inv {G : MvPowerSeries (Fin 2) K₃}
    (hG : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G = 0) :
    ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G⁻¹ = 0 := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N → p 1 ≠ 0 →
      MvPowerSeries.coeff p G⁻¹ = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp hp1
      rw [MvPowerSeries.coeff_inv, if_neg (fun hc => hp1 (by rw [hc]; simp)), mul_eq_zero]
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
            · exact absurd (Jacobs.fin2_eq_zero (by omega) (by omega)) hne
            · exact hh
          omega
        · rw [hG x.1 (by omega), zero_mul]
      · rfl
  exact fun p hp => key (p 0 + p 1) p rfl hp

@[simp] theorem yCoeff_sub (F G : MvPowerSeries (Fin 2) K₃) (r : ℕ) :
    yCoeff (F - G) r = yCoeff F r - yCoeff G r := by
  refine PowerSeries.ext fun n => ?_
  simp [coeff_yCoeff]

@[simp] theorem yCoeff_one_zero : yCoeff (1 : MvPowerSeries (Fin 2) K₃) 0 = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
  rcases n with _ | n
  · simp [idx]
  · rw [if_neg, if_neg]
    · exact Nat.succ_ne_zero n
    · intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp [idx] at this

private theorem yDeg0_kappaSeries₂ (c d : K₃) :
    ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p (Jacobs.kappaSeries₂ t c d) = 0 := by
  intro p hp
  rw [Jacobs.coeff_kappaSeries₂, if_neg hp]

@[simp] theorem constantCoeff_linX (γ : Matrix (Fin 2) (Fin 2) K₃) :
    PowerSeries.constantCoeff (linX γ) = γ 1 1 := by
  simp [linX]

/-- The `y`-column of `(linSeries γ)⁻¹` is `(linX γ)⁻¹`. -/
theorem yCoeff_linSeries_inv {γ : Matrix (Fin 2) (Fin 2) K₃} (hd : γ 1 1 ≠ 0) :
    yCoeff (Jacobs.linSeries γ)⁻¹ 0 = (linX γ)⁻¹ := by
  have hc : MvPowerSeries.constantCoeff (Jacobs.linSeries γ) ≠ 0 := by
    rw [Jacobs.constantCoeff_linSeries]; exact hd
  have h1 : Jacobs.linSeries γ * (Jacobs.linSeries γ)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ hc
  have h2 := congrArg (fun F => yCoeff F 0) h1
  simp only [yCoeff_mul_yDeg0 (yDeg0_inv (yDeg0_linSeries γ)) 0, yCoeff_linSeries,
    yCoeff_one_zero] at h2
  refine (PowerSeries.eq_inv_iff_mul_eq_one (k := K₃)
    (φ := yCoeff (Jacobs.linSeries γ)⁻¹ 0) (ψ := linX γ) ?_).mpr ?_
  · rw [constantCoeff_linX]; exact hd
  · rw [mul_comm]; exact h2

theorem yCoeff_eq_zero_of_yDeg0 {G : MvPowerSeries (Fin 2) K₃}
    (hG : ∀ p : Fin 2 →₀ ℕ, p 1 ≠ 0 → MvPowerSeries.coeff p G = 0) {r : ℕ} (hr : r ≠ 0) :
    yCoeff G r = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff, hG _ (by simpa using hr), map_zero]

/-- **B13a — the `y`-expansion of `weightGenFun`**: the `r`-th column of the operator is
`j_γ · w_γ^r`, i.e. the operator is the classical weight-`2` slash
`f ↦ j_γ · (f ∘ w_γ)`.  This is the bridge that turns the closed form back into the
Möbius action, and hence what makes the composition law (B13b) provable at all. -/
theorem yCoeff_weightGenFun {γ : Matrix (Fin 2) (Fin 2) K₃} (hd : γ 1 1 ≠ 0) (r : ℕ) :
    yCoeff (weightGenFun t γ) r = autFactor t γ * (mobius γ) ^ r := by
  have hlin0 : MvPowerSeries.constantCoeff (Jacobs.linSeries γ) ≠ 0 := by
    rw [Jacobs.constantCoeff_linSeries]; exact hd
  have hquad0 : MvPowerSeries.constantCoeff (Jacobs.quadSeries γ) ≠ 0 := by
    rw [Jacobs.constantCoeff_quadSeries]; exact hd
  have hlinX0 : PowerSeries.constantCoeff (linX γ) ≠ 0 := by
    rw [constantCoeff_linX]; exact hd
  have hinv : linX γ * (linX γ)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hlinX0
  have key : weightGenFun t γ * Jacobs.linSeries γ - weightGenFun t γ * yNum γ
      = Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1) * (Jacobs.linSeries γ)⁻¹ := by
    rw [← mul_sub, ← quadSeries_eq_sub, Jacobs.weightGenFun, mul_assoc,
      mul_comm (Jacobs.quadSeries γ)⁻¹ (Jacobs.quadSeries γ),
      MvPowerSeries.mul_inv_cancel _ hquad0, mul_one]
  have base : yCoeff (weightGenFun t γ) 0 = autFactor t γ := by
    have h := congrArg (fun G => yCoeff G 0) key
    simp only [yCoeff_sub, yCoeff_mul_yDeg0 (yDeg0_linSeries γ) 0,
      yCoeff_zero_mul_yDeg1 (yDeg1_yNum γ), yCoeff_linSeries, sub_zero,
      yCoeff_mul_yDeg0 (yDeg0_inv (yDeg0_linSeries γ)) 0, yCoeff_linSeries_inv hd] at h
    calc yCoeff (weightGenFun t γ) 0
        = yCoeff (weightGenFun t γ) 0 * (linX γ * (linX γ)⁻¹) := by rw [hinv, mul_one]
      _ = yCoeff (weightGenFun t γ) 0 * linX γ * (linX γ)⁻¹ := by ring
      _ = yCoeff (Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1)) 0 * (linX γ)⁻¹ * (linX γ)⁻¹ := by
          rw [h]
      _ = autFactor t γ := by rw [autFactor]; ring
  have step : ∀ k : ℕ, yCoeff (weightGenFun t γ) (k + 1)
      = yCoeff (weightGenFun t γ) k * mobius γ := by
    intro k
    have h := congrArg (fun G => yCoeff G (k + 1)) key
    simp only [yCoeff_sub, yCoeff_mul_yDeg0 (yDeg0_linSeries γ) (k + 1),
      yCoeff_mul_yDeg1 (yDeg1_yNum γ) k, yCoeff_linSeries, yCoeff_yNum,
      yCoeff_mul_yDeg0 (yDeg0_inv (yDeg0_linSeries γ)) (k + 1),
      yCoeff_eq_zero_of_yDeg0 (yDeg0_kappaSeries₂ t (γ 1 0) (γ 1 1)) (Nat.succ_ne_zero k),
      zero_mul] at h
    have h' : yCoeff (weightGenFun t γ) (k + 1) * linX γ
        = yCoeff (weightGenFun t γ) k * numX γ := by
      rw [sub_eq_zero] at h; exact h
    calc yCoeff (weightGenFun t γ) (k + 1)
        = yCoeff (weightGenFun t γ) (k + 1) * (linX γ * (linX γ)⁻¹) := by rw [hinv, mul_one]
      _ = yCoeff (weightGenFun t γ) (k + 1) * linX γ * (linX γ)⁻¹ := by ring
      _ = yCoeff (weightGenFun t γ) k * numX γ * (linX γ)⁻¹ := by rw [h']
      _ = yCoeff (weightGenFun t γ) k * mobius γ := by rw [mobius]; ring
  induction r with
  | zero => simpa using base
  | succ k ih => rw [step k, ih, pow_succ]; ring

/-- For `g ∈ Σ₁(9)` the `(1,1)` entry of `adjParams g` is `g₀₀`, a unit — in particular
nonzero, which is the standing hypothesis of `yCoeff_weightGenFun`. -/
theorem adjParams_lower_right_ne_zero (g : Sigma1) : adjParams g.1 1 1 ≠ 0 := by
  obtain ⟨⟨-, -, ha, -⟩, -⟩ := g.2
  rw [adjParams_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  intro hc
  rw [hc, map_zero] at ha
  exact zero_ne_one ha

include ht in
/-- The automorphy factor of a `Σ₁(9)` element has integral coefficients: it is the
`r = 0` column of `weightGenFun`, and `coeffInt_weightGenFun` bounds every column. -/
theorem norm_coeff_autFactor_le_one (g : Sigma1) (n : ℕ) :
    ‖PowerSeries.coeff n (autFactor t (adjParams g.1))‖ ≤ 1 := by
  have hd := adjParams_lower_right_ne_zero g
  have h := coeffInt_weightGenFun t ht g (idx n 0)
  rwa [← coeff_yCoeff, yCoeff_weightGenFun t hd 0, pow_zero, mul_one] at h

include ht in
/-- Every column of `weightGenFun` is integral, in `PowerSeries` form:
`‖coeff n (j_γ · w_γ^r)‖ ≤ 1`.  (The `r = 0` case is `norm_coeff_autFactor_le_one`.) -/
theorem norm_coeff_autFactor_mul_mobius_pow_le_one (g : Sigma1) (r n : ℕ) :
    ‖PowerSeries.coeff n (autFactor t (adjParams g.1) * (mobius (adjParams g.1)) ^ r)‖
      ≤ 1 := by
  have hd := adjParams_lower_right_ne_zero g
  have h := coeffInt_weightGenFun t ht g (idx n r)
  rwa [← coeff_yCoeff, yCoeff_weightGenFun t hd r] at h

include ht in
/-- The `‖3‖^(m−r)` decay, in `PowerSeries` form: the columns `j_γ · w_γ^r` decay in the
`x`-degree relative to `r`.  This is `shiftInt_weightGenFun` read through B13a, and is the
convergence input for the analytic composition law. -/
theorem norm_coeff_autFactor_mul_mobius_pow_le_shift (g : Sigma1) (r n : ℕ) :
    ‖PowerSeries.coeff n (autFactor t (adjParams g.1) * (mobius (adjParams g.1)) ^ r)‖
      ≤ ‖(3 : K₃)‖ ^ (n - r) := by
  have hd := adjParams_lower_right_ne_zero g
  have h := shiftInt_weightGenFun t ht g (idx n r)
  rw [← coeff_yCoeff, yCoeff_weightGenFun t hd r] at h
  simpa using h

include ht in
/-- **`kappaOp` acts by the slash formula.**  Combining `ofCoeffs_apply` with B13a's
column identity, `(kappaOp g f)_j = ∑ᵢ (coefficient of `xʲ` in `j_γ·w_γ^i`) · fᵢ` — i.e.
the operator is `f ↦ j_γ · (f ∘ w_γ)`, read coefficientwise.  This is the form in which
the composition law (`kappaOp_mul`) should be attacked: the remaining content is Möbius
composition plus the `κ`-cocycle, and the two convergence bounds are already available
(`norm_coeff_autFactor_mul_mobius_pow_le_one` / `_le_shift`). -/
theorem kappaOp_apply (g : Sigma1) (f : c(ℕ, K₃)) (j : ℕ) :
    kappaOp t ht g f j
      = ∑' i, PowerSeries.coeff j
          (autFactor t (adjParams g.1) * (mobius (adjParams g.1)) ^ i) * f i := by
  have hd := adjParams_lower_right_ne_zero g
  rw [kappaOp, ofGenFun, ofCoeffs_apply]
  refine tsum_congr fun i => ?_
  rw [← coeff_yCoeff, yCoeff_weightGenFun t hd i]

/-- **Möbius composition, in linear form.**  The denominator of `δ·γ` is the `δ`-linear
combination of the numerator and denominator of `γ`:
`lin(δγ) = δ₁₀ · num(γ) + δ₁₁ · lin(γ)`.  Together with `numX_mul` this is the Möbius
composition law `w_{δγ} = w_δ ∘ w_γ` written WITHOUT substitution — which is what makes it
provable formally, given that `w_γ` has nonzero constant term. -/
theorem linX_mul (γ δ : Matrix (Fin 2) (Fin 2) K₃) :
    linX (δ * γ) = PowerSeries.C (δ 1 0) * numX γ + PowerSeries.C (δ 1 1) * linX γ := by
  rw [linX, linX, numX, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  ring

/-- The numerator of `δ·γ`: `num(δγ) = δ₀₀ · num(γ) + δ₀₁ · lin(γ)`. -/
theorem numX_mul (γ δ : Matrix (Fin 2) (Fin 2) K₃) :
    numX (δ * γ) = PowerSeries.C (δ 0 0) * numX γ + PowerSeries.C (δ 0 1) * linX γ := by
  rw [numX, numX, linX, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  ring

/-- The denominator of `δ·γ` factors through `w_γ`:
`lin(δγ) = lin(γ) · (δ₁₀·w_γ + δ₁₁)`. -/
theorem linX_mul_eq (γ δ : Matrix (Fin 2) (Fin 2) K₃) (hγ : γ 1 1 ≠ 0) :
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

/-- The numerator of `δ·γ` factors the same way:
`num(δγ) = lin(γ) · (δ₀₀·w_γ + δ₀₁)`. -/
theorem numX_mul_eq (γ δ : Matrix (Fin 2) (Fin 2) K₃) (hγ : γ 1 1 ≠ 0) :
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

/-- **Möbius composition in closed form**: `w_{δγ} = (δ₀₀·w_γ + δ₀₁)/(δ₁₀·w_γ + δ₁₁)`,
i.e. `w_δ ∘ w_γ`, proved with no substitution at all — the `lin`/`num` factorisations do
all the work.  (`adjParams` is an anti-homomorphism, so `δ·γ` is the order corresponding
to `kappaOp (g * h)`.) -/
theorem mobius_mul (γ δ : Matrix (Fin 2) (Fin 2) K₃) (hγ : γ 1 1 ≠ 0)
    (hδγ : (δ * γ) 1 1 ≠ 0) :
    mobius (δ * γ)
      = (PowerSeries.C (δ 0 0) * mobius γ + PowerSeries.C (δ 0 1))
        * (PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1))⁻¹ := by
  have hlin : PowerSeries.constantCoeff (linX (δ * γ)) ≠ 0 := by
    rw [constantCoeff_linX]; exact hδγ
  have hfac := linX_mul_eq γ δ hγ
  have hden : (PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1))
      * ((PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1)))⁻¹ = 1 := by
    refine PowerSeries.mul_inv_cancel _ ?_
    intro hc
    apply hlin
    rw [hfac, map_mul, hc, mul_zero]
  have hlinγ : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hγ)
  rw [mobius, numX_mul_eq γ δ hγ, hfac, PowerSeries.mul_inv_rev]
  calc linX γ * (PowerSeries.C (δ 0 0) * mobius γ + PowerSeries.C (δ 0 1))
        * ((PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1))⁻¹ * (linX γ)⁻¹)
      = (linX γ * (linX γ)⁻¹)
        * ((PowerSeries.C (δ 0 0) * mobius γ + PowerSeries.C (δ 0 1))
          * (PowerSeries.C (δ 1 0) * mobius γ + PowerSeries.C (δ 1 1))⁻¹) := by ring
    _ = _ := by rw [hlinγ, one_mul]

section Compose

open PowerSeries (AbsSummable CoeffLeOne compAn absSummable_C absSummable_X
  absSummable_add absSummable_mul compAn_C compAn_X compAn_add compAn_mul compAn_inv
  compAn_ode derivative_compAn)

theorem absSummable_linX (δ : Matrix (Fin 2) (Fin 2) K₃) : AbsSummable (linX δ) := by
  rw [linX]
  exact absSummable_add (absSummable_C _) (absSummable_mul (absSummable_C _) absSummable_X)

theorem compAn_linX (δ : Matrix (Fin 2) (Fin 2) K₃) {w : PowerSeries K₃}
    (hw : CoeffLeOne w) :
    compAn (linX δ) w = PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w := by
  rw [linX, compAn_add (absSummable_C _) (absSummable_mul (absSummable_C _) absSummable_X) hw,
    compAn_mul (absSummable_C _) absSummable_X hw, compAn_C, compAn_C, compAn_X]

/-- The explicit geometric inverse of the linear factor `d + c·x`. -/
theorem linX_inv_eq {δ : Matrix (Fin 2) (Fin 2) K₃} (hd : δ 1 1 ≠ 0) :
    (linX δ)⁻¹ = PowerSeries.mk fun n => (-(δ 1 0)) ^ n / (δ 1 1) ^ (n + 1) := by
  refine ((PowerSeries.eq_inv_iff_mul_eq_one
    (by rw [constantCoeff_linX]; exact hd)).mpr ?_).symm
  refine PowerSeries.ext fun n => ?_
  rw [mul_comm, linX, add_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_mk, if_pos rfl]
    field_simp
    ring
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      if_neg (Nat.succ_ne_zero m)]
    field_simp
    ring

/-- The inverse of the linear factor is absolutely summable when `‖c‖ < ‖d‖` — a geometric
series with ratio `‖c‖/‖d‖`. -/
theorem absSummable_linX_inv {δ : Matrix (Fin 2) (Fin 2) K₃} (hd : δ 1 1 ≠ 0)
    (h : ‖δ 1 0‖ < ‖δ 1 1‖) : AbsSummable (linX δ)⁻¹ := by
  have hdpos : (0 : ℝ) < ‖δ 1 1‖ := norm_pos_iff.mpr hd
  have hr : ‖δ 1 0‖ / ‖δ 1 1‖ < 1 := (div_lt_one hdpos).mpr h
  have hgeo := (summable_geometric_of_lt_one (by positivity) hr).mul_right (1 / ‖δ 1 1‖)
  rw [AbsSummable, linX_inv_eq hd]
  refine hgeo.congr fun n => ?_
  rw [PowerSeries.coeff_mk, norm_div, norm_pow, norm_neg, norm_pow, div_pow]
  field_simp
  ring

theorem absSummable_numX (δ : Matrix (Fin 2) (Fin 2) K₃) : AbsSummable (numX δ) := by
  rw [numX]
  exact absSummable_add (absSummable_C _) (absSummable_mul (absSummable_C _) absSummable_X)

theorem compAn_numX (δ : Matrix (Fin 2) (Fin 2) K₃) {w : PowerSeries K₃}
    (hw : CoeffLeOne w) :
    compAn (numX δ) w = PowerSeries.C (δ 0 1) + PowerSeries.C (δ 0 0) * w := by
  rw [numX, compAn_add (absSummable_C _) (absSummable_mul (absSummable_C _) absSummable_X) hw,
    compAn_mul (absSummable_C _) absSummable_X hw, compAn_C, compAn_C, compAn_X]

theorem coeffLeOne_numX {δ : Matrix (Fin 2) (Fin 2) K₃} (h00 : ‖δ 0 0‖ ≤ 1)
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

theorem coeffLeOne_linX_inv {δ : Matrix (Fin 2) (Fin 2) K₃} (hd : ‖δ 1 1‖ = 1)
    (hc : ‖δ 1 0‖ ≤ 1) : CoeffLeOne (linX δ)⁻¹ := by
  have hd0 : δ 1 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
  intro n
  rw [linX_inv_eq hd0, PowerSeries.coeff_mk, norm_div, norm_pow, norm_neg, norm_pow, hd,
    one_pow, div_one]
  exact pow_le_one₀ (norm_nonneg _) hc

theorem coeffLeOne_mobius {δ : Matrix (Fin 2) (Fin 2) K₃} (h00 : ‖δ 0 0‖ ≤ 1)
    (h01 : ‖δ 0 1‖ ≤ 1) (hd : ‖δ 1 1‖ = 1) (hc : ‖δ 1 0‖ ≤ 1) : CoeffLeOne (mobius δ) := by
  rw [mobius]
  exact (coeffLeOne_numX h00 h01).mul (coeffLeOne_linX_inv hd hc)

theorem constantCoeff_compAn_linX_ne_zero {δ : Matrix (Fin 2) (Fin 2) K₃} (hd : ‖δ 1 1‖ = 1)
    (hc : ‖δ 1 0‖ < 1) {w : PowerSeries K₃} (hw : CoeffLeOne w) :
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

/-- **The Möbius map composes analytically**: `w_δ ∘ w = (δ₀₁ + δ₀₀·w)/(δ₁₁ + δ₁₀·w)`. -/
theorem compAn_mobius {δ : Matrix (Fin 2) (Fin 2) K₃} (hd : ‖δ 1 1‖ = 1)
    (hc : ‖δ 1 0‖ < 1) {w : PowerSeries K₃} (hw : CoeffLeOne w) :
    compAn (mobius δ) w
      = (PowerSeries.C (δ 0 1) + PowerSeries.C (δ 0 0) * w)
        * (PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w)⁻¹ := by
  have hd0 : δ 1 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
  have hlt : ‖δ 1 0‖ < ‖δ 1 1‖ := by rw [hd]; exact hc
  rw [mobius, compAn_mul (absSummable_numX δ) (absSummable_linX_inv hd0 hlt) hw,
    compAn_numX δ hw, compAn_inv (absSummable_linX δ) (absSummable_linX_inv hd0 hlt) hw
      (by rw [constantCoeff_linX]; exact hd0) (constantCoeff_compAn_linX_ne_zero hd hc hw),
    compAn_linX δ hw]

/-- **The composition law for Möbius maps**, analytic form: `w_δ ∘ w_γ = w_{δγ}`.  This is
the GEOMETRIC half of the `κ`-action law; `mobius_mul` supplies the closed form and
`compAn_mobius` identifies the substitution with it. -/
theorem compAn_mobius_mobius {γ δ : Matrix (Fin 2) (Fin 2) K₃} (hd : ‖δ 1 1‖ = 1)
    (hc : ‖δ 1 0‖ < 1) (hγ00 : ‖γ 0 0‖ ≤ 1) (hγ01 : ‖γ 0 1‖ ≤ 1) (hγd : ‖γ 1 1‖ = 1)
    (hγc : ‖γ 1 0‖ ≤ 1) (hδγ : (δ * γ) 1 1 ≠ 0) :
    compAn (mobius δ) (mobius γ) = mobius (δ * γ) := by
  have hγ0 : γ 1 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hγd; exact zero_ne_one hγd
  rw [compAn_mobius hd hc (coeffLeOne_mobius hγ00 hγ01 hγd hγc), mobius_mul γ δ hγ0 hδγ,
    add_comm (PowerSeries.C (δ 0 1)), add_comm (PowerSeries.C (δ 1 1))]

end Compose

/-- The `κ`-column in closed form: `κ(c·x + d)` has `xⁿ`-coefficient
`κ(d)·(t choose n)·(c/d)ⁿ`.  (The `y`-degree-`0` column of `kappaSeries₂`, which is where
all of its mass sits.) -/
@[simp] theorem coeff_yCoeff_kappaSeries₂ (c d : K₃) (n : ℕ) :
    PowerSeries.coeff n (yCoeff (Jacobs.kappaSeries₂ t c d) 0)
      = Jacobs.unitPow t d * (Jacobs.binomialCoeff t n * (c / d) ^ n) := by
  rw [coeff_yCoeff, Jacobs.coeff_kappaSeries₂, if_pos (by simp), idx_apply_zero]

/-- The constant term of the `κ`-column is `κ(d)` — in particular it is a unit for a
`1`-unit `d`, which is what makes `autFactor` invertible. -/
theorem constantCoeff_yCoeff_kappaSeries₂ (c d : K₃) :
    PowerSeries.constantCoeff (yCoeff (Jacobs.kappaSeries₂ t c d) 0)
      = Jacobs.unitPow t d := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_yCoeff_kappaSeries₂]
  simp

section Cocycle

open PowerSeries (AbsSummable CoeffLeOne compAn compAn_ode derivative_compAn
  constantCoeff_compAn absSummable_mul absSummable_pow compAn_mul compAn_pow compAn_inv
  coeff_mul_compAn)

/-- The `κ`-column `κ(c·x + d)` is the scaled binomial series
`κ(d) · B_t(c/d)`. -/
theorem yCoeff_kappaSeries₂_eq (c d : K₃) :
    yCoeff (Jacobs.kappaSeries₂ t c d) 0
      = PowerSeries.C (Jacobs.unitPow t d) * Jacobs.binomialSeries t (c / d) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_yCoeff_kappaSeries₂, PowerSeries.coeff_C_mul, coeff_binomialSeries]

/-- The linear factor is the scaled `1`-unit `d · (1 + (c/d)x)`. -/
theorem linX_eq_scaled {γ : Matrix (Fin 2) (Fin 2) K₃} (hd : γ 1 1 ≠ 0) :
    linX γ = PowerSeries.C (γ 1 1) * (1 + PowerSeries.C (γ 1 0 / γ 1 1) * PowerSeries.X) := by
  rw [linX, mul_add, mul_one, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ hd]

theorem derivative_linX (γ : Matrix (Fin 2) (Fin 2) K₃) :
    d⁄dX K₃ (linX γ) = PowerSeries.C (γ 1 0) := by
  rw [linX]; simp

/-- **The `κ`-column satisfies the first-order ODE** `lin γ · S′ = t · (lin γ)′ · S`.  This
is the ODE that `PowerSeries.eq_of_ode` uses to pin the cocycle. -/
theorem kappaCol_ode {γ : Matrix (Fin 2) (Fin 2) K₃} (hd : γ 1 1 ≠ 0) :
    linX γ * d⁄dX K₃ (yCoeff (Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1)) 0)
      = PowerSeries.C t * d⁄dX K₃ (linX γ)
        * yCoeff (Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1)) 0 := by
  set u := Jacobs.unitPow t (γ 1 1) with hu
  set e := γ 1 0 / γ 1 1 with he
  rw [yCoeff_kappaSeries₂_eq, derivative_linX, linX_eq_scaled hd]
  have hDer : d⁄dX K₃ (PowerSeries.C u * Jacobs.binomialSeries t e)
      = PowerSeries.C u * d⁄dX K₃ (Jacobs.binomialSeries t e) := by
    simp
  rw [hDer]
  have hkey : (1 + PowerSeries.C e * PowerSeries.X) * d⁄dX K₃ (Jacobs.binomialSeries t e)
      = PowerSeries.C (t * e) * Jacobs.binomialSeries t e := Jacobs.binomialSeries_ode t e
  have hscal : γ 1 1 * (u * (t * e)) = t * γ 1 0 * u := by
    rw [he]; field_simp
  calc PowerSeries.C (γ 1 1) * (1 + PowerSeries.C e * PowerSeries.X)
        * (PowerSeries.C u * d⁄dX K₃ (Jacobs.binomialSeries t e))
      = PowerSeries.C (γ 1 1) * PowerSeries.C u
        * ((1 + PowerSeries.C e * PowerSeries.X) * d⁄dX K₃ (Jacobs.binomialSeries t e)) := by
        ring
    _ = PowerSeries.C (γ 1 1) * PowerSeries.C u
        * (PowerSeries.C (t * e) * Jacobs.binomialSeries t e) := by rw [hkey]
    _ = PowerSeries.C (γ 1 1 * (u * (t * e))) * Jacobs.binomialSeries t e := by
        simp only [map_mul]; ring
    _ = PowerSeries.C (t * γ 1 0 * u) * Jacobs.binomialSeries t e := by rw [hscal]
    _ = PowerSeries.C t * PowerSeries.C (γ 1 0)
        * (PowerSeries.C u * Jacobs.binomialSeries t e) := by
        simp only [map_mul]; ring

theorem derivative_numX (γ : Matrix (Fin 2) (Fin 2) K₃) :
    d⁄dX K₃ (numX γ) = PowerSeries.C (γ 0 0) := by
  rw [numX]; simp

theorem derivative_mobius {γ : Matrix (Fin 2) (Fin 2) K₃} (hd : γ 1 1 ≠ 0) :
    d⁄dX K₃ (mobius γ)
      = PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) * ((linX γ)⁻¹) ^ 2 := by
  have hinv : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hd)
  rw [mobius, Derivation.leibniz, PowerSeries.derivative_inv', derivative_numX,
    derivative_linX]
  simp only [smul_eq_mul]
  have hlin : PowerSeries.C (γ 0 0) * linX γ - PowerSeries.C (γ 1 0) * numX γ
      = PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) := by
    rw [linX, numX, map_sub, map_mul, map_mul]
    ring
  have hL : (linX γ)⁻¹ = linX γ * ((linX γ)⁻¹) ^ 2 := by
    rw [pow_two, ← mul_assoc, hinv, one_mul]
  calc numX γ * (-(linX γ)⁻¹ ^ 2 * PowerSeries.C (γ 1 0))
        + (linX γ)⁻¹ * PowerSeries.C (γ 0 0)
      = numX γ * (-(linX γ)⁻¹ ^ 2 * PowerSeries.C (γ 1 0))
        + linX γ * ((linX γ)⁻¹) ^ 2 * PowerSeries.C (γ 0 0) := by rw [← hL]
    _ = (PowerSeries.C (γ 0 0) * linX γ - PowerSeries.C (γ 1 0) * numX γ)
        * ((linX γ)⁻¹) ^ 2 := by ring
    _ = PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) * ((linX γ)⁻¹) ^ 2 := by rw [hlin]

/-- The `x`-free identity behind the cocycle's `(1,0)`-entry:
`γ₁₀·num γ + det γ = γ₀₀·lin γ`. -/
theorem C_lower_left_mul_numX_add_det (γ : Matrix (Fin 2) (Fin 2) K₃) :
    PowerSeries.C (γ 1 0) * numX γ + PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0)
      = PowerSeries.C (γ 0 0) * linX γ := by
  rw [numX, linX]
  simp only [map_sub, map_mul]
  ring

/-- **The `(1,0)`-entry of the product matrix, read through the Möbius map.**  This is the
identity that makes the product `κ(lin γ)·(κ(lin δ) ∘ w_γ)` satisfy the `δγ`-ODE. -/
theorem lower_left_cocycle {γ δ : Matrix (Fin 2) (Fin 2) K₃} (hd : γ 1 1 ≠ 0) :
    PowerSeries.C (γ 1 0) * (PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * mobius γ)
        + PowerSeries.C (δ 1 0) * linX γ * d⁄dX K₃ (mobius γ)
      = PowerSeries.C ((δ * γ) 1 0) := by
  have hinv : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hd)
  have hL : linX γ * ((linX γ)⁻¹) ^ 2 = (linX γ)⁻¹ := by
    rw [pow_two, ← mul_assoc, hinv, one_mul]
  have hentry : (δ * γ) 1 0 = δ 1 0 * γ 0 0 + δ 1 1 * γ 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hterm : PowerSeries.C (δ 1 0) * linX γ
      * (PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) * ((linX γ)⁻¹) ^ 2)
      = PowerSeries.C (δ 1 0) * PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0)
        * (linX γ)⁻¹ := by
    calc PowerSeries.C (δ 1 0) * linX γ
          * (PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) * ((linX γ)⁻¹) ^ 2)
        = PowerSeries.C (δ 1 0) * PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0)
          * (linX γ * ((linX γ)⁻¹) ^ 2) := by ring
      _ = _ := by rw [hL]
  rw [derivative_mobius hd, mobius, hentry, map_add, map_mul, map_mul, hterm]
  calc PowerSeries.C (γ 1 0)
          * (PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * (numX γ * (linX γ)⁻¹))
        + PowerSeries.C (δ 1 0) * PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0)
          * (linX γ)⁻¹
      = PowerSeries.C (γ 1 0) * PowerSeries.C (δ 1 1)
        + PowerSeries.C (δ 1 0)
          * ((PowerSeries.C (γ 1 0) * numX γ
              + PowerSeries.C (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0)) * (linX γ)⁻¹) := by ring
    _ = PowerSeries.C (γ 1 0) * PowerSeries.C (δ 1 1)
        + PowerSeries.C (δ 1 0) * (PowerSeries.C (γ 0 0) * (linX γ * (linX γ)⁻¹)) := by
        rw [C_lower_left_mul_numX_add_det]; ring
    _ = PowerSeries.C (δ 1 0) * PowerSeries.C (γ 0 0)
        + PowerSeries.C (δ 1 1) * PowerSeries.C (γ 1 0) := by rw [hinv]; ring

/-- **The product `κ(lin γ)·(κ(lin δ) ∘ w_γ)` satisfies the `δγ`-ODE.** -/
theorem kappaCol_mul_compAn_ode {γ δ : Matrix (Fin 2) (Fin 2) K₃} (hγ : γ 1 1 ≠ 0)
    (hδ : AbsSummable (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0))
    (hδ0 : δ 1 1 ≠ 0) (hw : CoeffLeOne (mobius γ)) :
    linX (δ * γ) * d⁄dX K₃ (yCoeff (Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1)) 0
        * compAn (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0) (mobius γ))
      = PowerSeries.C t * d⁄dX K₃ (linX (δ * γ))
        * (yCoeff (Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1)) 0
          * compAn (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0) (mobius γ)) := by
  set S := yCoeff (Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1)) 0 with hSdef
  set T := compAn (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0) (mobius γ) with hTdef
  set w := mobius γ with hwdef
  have hS : linX γ * d⁄dX K₃ S = PowerSeries.C t * PowerSeries.C (γ 1 0) * S := by
    rw [hSdef, ← derivative_linX γ]
    exact kappaCol_ode t hγ
  have hLeq : compAn (linX δ) w = PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w :=
    compAn_linX δ hw
  have hdL : d⁄dX K₃ (compAn (linX δ) w) = PowerSeries.C (δ 1 0) * d⁄dX K₃ w := by
    rw [derivative_compAn (absSummable_linX δ) hw, derivative_linX, PowerSeries.compAn_C]
  have hT : compAn (linX δ) w * d⁄dX K₃ T
      = PowerSeries.C t * (PowerSeries.C (δ 1 0) * d⁄dX K₃ w) * T := by
    rw [← hdL]
    exact compAn_ode (absSummable_linX δ) hδ hw (kappaCol_ode t hδ0)
  have hfac : linX (δ * γ) = linX γ * (PowerSeries.C (δ 1 0) * w + PowerSeries.C (δ 1 1)) :=
    linX_mul_eq γ δ hγ
  have hcoc : PowerSeries.C (γ 1 0) * (PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w)
      + PowerSeries.C (δ 1 0) * linX γ * d⁄dX K₃ w = PowerSeries.C ((δ * γ) 1 0) :=
    lower_left_cocycle hγ
  rw [derivative_linX, Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [hfac]
  calc linX γ * (PowerSeries.C (δ 1 0) * w + PowerSeries.C (δ 1 1))
        * (S * d⁄dX K₃ T + T * d⁄dX K₃ S)
      = (linX γ * S) * ((PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w) * d⁄dX K₃ T)
        + ((PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w) * T) * (linX γ * d⁄dX K₃ S) := by
        ring
    _ = (linX γ * S) * (PowerSeries.C t * (PowerSeries.C (δ 1 0) * d⁄dX K₃ w) * T)
        + ((PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w) * T)
          * (PowerSeries.C t * PowerSeries.C (γ 1 0) * S) := by
        rw [← hLeq, hT, hS]
    _ = PowerSeries.C t * S * T
        * (PowerSeries.C (γ 1 0) * (PowerSeries.C (δ 1 1) + PowerSeries.C (δ 1 0) * w)
          + PowerSeries.C (δ 1 0) * linX γ * d⁄dX K₃ w) := by ring
    _ = PowerSeries.C t * PowerSeries.C ((δ * γ) 1 0) * (S * T) := by rw [hcoc]; ring

/-- **The constant term of the composed `κ`-column**: `κ(δ₁₁)·κ(1 + e_δ·w_{γ,0})`.  This is
where the `p`-adic binomial theorem enters. -/
theorem constantCoeff_compAn_kappaCol {γ δ : Matrix (Fin 2) (Fin 2) K₃} (ht : ‖t‖ ≤ 1)
    (hz : ‖δ 1 0 / δ 1 1 * PowerSeries.constantCoeff (mobius γ)‖ ≤ ‖(3 : K₃)‖ ^ 2) :
    PowerSeries.constantCoeff
        (compAn (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0) (mobius γ))
      = Jacobs.unitPow t (δ 1 1)
        * Jacobs.unitPow t
            (1 + δ 1 0 / δ 1 1 * PowerSeries.constantCoeff (mobius γ)) := by
  set z := PowerSeries.constantCoeff (mobius γ) with hzdef
  set e := δ 1 0 / δ 1 1 with hedef
  rw [constantCoeff_compAn, ← hzdef]
  have hterm : ∀ n : ℕ,
      PowerSeries.coeff n (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0) * z ^ n
        = Jacobs.unitPow t (δ 1 1) * (Jacobs.binomialCoeff t n * (e * z) ^ n) := by
    intro n
    rw [coeff_yCoeff_kappaSeries₂, ← hedef, mul_pow]
    ring
  rw [tsum_congr hterm, tsum_mul_left,
    Jacobs.tsum_binomialCoeff_eq_unitPow norm_three_lt_one ht hz
      (fun ε hε => exists_natCast_close ht hε)]

theorem constantCoeff_mobius (γ : Matrix (Fin 2) (Fin 2) K₃) :
    PowerSeries.constantCoeff (mobius γ) = γ 0 1 / γ 1 1 := by
  have hnum : PowerSeries.constantCoeff (numX γ) = γ 0 1 := by rw [numX]; simp
  rw [mobius, map_mul, PowerSeries.constantCoeff_inv, constantCoeff_linX, hnum,
    div_eq_mul_inv]

theorem lower_right_cocycle {γ δ : Matrix (Fin 2) (Fin 2) K₃} (hγ : γ 1 1 ≠ 0)
    (hδ : δ 1 1 ≠ 0) :
    (δ * γ) 1 1
      = γ 1 1 * (δ 1 1 * (1 + δ 1 0 / δ 1 1 * PowerSeries.constantCoeff (mobius γ))) := by
  rw [constantCoeff_mobius γ, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

/-- **The `κ`-cocycle**: `κ(lin (δγ)) = κ(lin γ) · (κ(lin δ) ∘ w_γ)`. -/
theorem kappaCol_cocycle {γ δ : Matrix (Fin 2) (Fin 2) K₃} (ht : ‖t‖ ≤ 1)
    (hγ0 : γ 1 1 ≠ 0) (hδ0 : δ 1 1 ≠ 0) (hδγ0 : (δ * γ) 1 1 ≠ 0)
    (hγ1 : ‖γ 1 1 - 1‖ ≤ ‖(3 : K₃)‖) (hδ1 : ‖δ 1 1 - 1‖ ≤ ‖(3 : K₃)‖)
    (hz : ‖δ 1 0 / δ 1 1 * PowerSeries.constantCoeff (mobius γ)‖ ≤ ‖(3 : K₃)‖ ^ 2)
    (hAS : AbsSummable (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0))
    (hw : CoeffLeOne (mobius γ)) :
    yCoeff (Jacobs.kappaSeries₂ t ((δ * γ) 1 0) ((δ * γ) 1 1)) 0
      = yCoeff (Jacobs.kappaSeries₂ t (γ 1 0) (γ 1 1)) 0
        * compAn (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0) (mobius γ) := by
  have h3lt : ‖(3 : K₃)‖ < 1 := norm_three_lt_one
  set z := δ 1 0 / δ 1 1 * PowerSeries.constantCoeff (mobius γ) with hzdef
  have hzs : ‖z‖ ≤ ‖(3 : K₃)‖ := hz.trans (by nlinarith [norm_nonneg (3 : K₃)])
  have hone : ‖(1 + z) - 1‖ ≤ ‖(3 : K₃)‖ := by rw [add_sub_cancel_left]; exact hzs
  have hδ11 : ‖δ 1 1‖ = 1 :=
    Jacobs.norm_eq_one_of_norm_sub_one_lt_one (hδ1.trans_lt h3lt)
  have hmid : ‖δ 1 1 * (1 + z) - 1‖ ≤ ‖(3 : K₃)‖ := by
    rw [show δ 1 1 * (1 + z) - 1 = (δ 1 1 - 1) + δ 1 1 * z from by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hδ1 ?_)
    rw [norm_mul, hδ11, one_mul]
    exact hzs
  refine PowerSeries.eq_of_ode (t := t) (A := linX (δ * γ))
    (by rw [constantCoeff_linX]; exact hδγ0) (kappaCol_ode t hδγ0)
    (kappaCol_mul_compAn_ode t hγ0 hAS hδ0 hw) ?_
  rw [constantCoeff_yCoeff_kappaSeries₂, map_mul, constantCoeff_yCoeff_kappaSeries₂,
    constantCoeff_compAn_kappaCol t ht hz, lower_right_cocycle hγ0 hδ0, ← hzdef,
    Jacobs.unitPow_mul h3lt ht hγ1 hmid, Jacobs.unitPow_mul h3lt ht hδ1 hone]

private theorem adjParams_entries (g : Sigma1) :
    adjParams g.1 0 0 = g.1 1 1 ∧ adjParams g.1 0 1 = -g.1 0 1
      ∧ adjParams g.1 1 0 = -g.1 1 0 ∧ adjParams g.1 1 1 = g.1 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> · rw [adjParams_apply]; simp

/-- Every entry of `adjParams g` is integral, for `g ∈ Σ₁(9)`. -/
theorem norm_adjParams_le_one (g : Sigma1) : ∀ i j : Fin 2, ‖adjParams g.1 i j‖ ≤ 1 := by
  obtain ⟨⟨hint, -, -, -⟩, -⟩ := g.2
  obtain ⟨h00, h01, h10, h11⟩ := adjParams_entries g
  have hn : ∀ a b, ‖g.1 a b‖ ≤ 1 := fun a b =>
    Valued.toNormedField.norm_le_one_iff.mpr (hint a b)
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩
  · rw [h00]; exact hn 1 1
  · rw [h01, norm_neg]; exact hn 0 1
  · rw [h10, norm_neg]; exact hn 1 0
  · rw [h11]; exact hn 0 0

/-- The `(1,1)`-entry of `adjParams g` is a `1`-unit, for `g ∈ Σ₁(9)`. -/
theorem norm_adjParams_lower_right_sub_one_le (g : Sigma1) :
    ‖adjParams g.1 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by
  obtain ⟨-, ha1⟩ := g.2
  obtain ⟨-, -, -, h11⟩ := adjParams_entries g
  have h30 : (3 : K₃) ≠ 0 := three_ne_zero
  have h90 : (9 : K₃) ≠ 0 := by norm_num
  have hv3 : Valued.v (3 : K₃) ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mp norm_three_lt_one.le
  have hγ9le3 : γ₉ ≤ Valued.v (3 : K₃) := by
    rw [← valued_nine_eq, show (9 : K₃) = 3 * 3 by norm_num, map_mul]
    exact le_trans (mul_le_mul' le_rfl hv3) (by rw [mul_one])
  rw [h11]
  exact norm_le_of_valued_le h30 (le_trans ha1 hγ9le3)

/-- The `(1,1)`-entry of `adjParams g` has norm one. -/
theorem norm_adjParams_lower_right (g : Sigma1) : ‖adjParams g.1 1 1‖ = 1 :=
  Jacobs.norm_eq_one_of_norm_sub_one_lt_one
    ((norm_adjParams_lower_right_sub_one_le g).trans_lt norm_three_lt_one)

/-- The `(1,0)`-entry of `adjParams g` is divisible by `9`, for `g ∈ Σ₁(9)`. -/
theorem norm_adjParams_lower_left_le (g : Sigma1) :
    ‖adjParams g.1 1 0‖ ≤ ‖(3 : K₃)‖ ^ 2 := by
  obtain ⟨⟨-, hc, -, -⟩, -⟩ := g.2
  obtain ⟨-, -, h10, -⟩ := adjParams_entries g
  have h90 : (9 : K₃) ≠ 0 := by norm_num
  have hn9 : ‖(9 : K₃)‖ = ‖(3 : K₃)‖ ^ 2 := by
    rw [show (9 : K₃) = 3 * 3 by norm_num, norm_mul, sq]
  rw [h10, norm_neg, ← hn9]
  exact norm_le_of_valued_le h90 (le_trans hc (le_of_eq valued_nine_eq.symm))

/-- The `κ`-column has geometrically decaying coefficients, hence is an admissible outer
series for `compAn`. -/
theorem absSummable_kappaCol {c d : K₃} (ht : ‖t‖ < 1) (hd : ‖d - 1‖ ≤ ‖(3 : K₃)‖)
    (hcd : ‖c / d‖ ≤ ‖(3 : K₃)‖ ^ 2) :
    AbsSummable (yCoeff (Jacobs.kappaSeries₂ t c d) 0) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg _) norm_three_lt_one)
  rw [coeff_yCoeff_kappaSeries₂, norm_mul]
  calc ‖Jacobs.unitPow t d‖ * ‖Jacobs.binomialCoeff t n * (c / d) ^ n‖
      ≤ 1 * ‖(3 : K₃)‖ ^ n :=
        mul_le_mul (Jacobs.norm_unitPow_le_one norm_three_lt_one ht hd)
          (Jacobs.norm_binomialCoeff_mul_pow_le norm_three_lt_one ht.le hcd n)
          (norm_nonneg _) zero_le_one
    _ = ‖(3 : K₃)‖ ^ n := one_mul _

/-- `‖c/d‖ ≤ ‖3‖²` for the `adjParams` of a `Σ₁(9)` element. -/
theorem norm_adjParams_ratio_le (g : Sigma1) :
    ‖adjParams g.1 1 0 / adjParams g.1 1 1‖ ≤ ‖(3 : K₃)‖ ^ 2 := by
  rw [norm_div, norm_adjParams_lower_right g, div_one]
  exact norm_adjParams_lower_left_le g

theorem coeffLeOne_mobius_adjParams (g : Sigma1) : CoeffLeOne (mobius (adjParams g.1)) :=
  coeffLeOne_mobius (norm_adjParams_le_one g 0 0) (norm_adjParams_le_one g 0 1)
    (norm_adjParams_lower_right g)
    ((norm_adjParams_lower_left_le g).trans
      (pow_le_one₀ (norm_nonneg _) norm_three_lt_one.le))

theorem absSummable_linX_inv_adjParams (g : Sigma1) :
    AbsSummable (linX (adjParams g.1))⁻¹ := by
  refine absSummable_linX_inv (adjParams_lower_right_ne_zero g) ?_
  rw [norm_adjParams_lower_right g]
  refine lt_of_le_of_lt (norm_adjParams_lower_left_le g) ?_
  exact pow_lt_one₀ (norm_nonneg _) norm_three_lt_one two_ne_zero

theorem absSummable_mobius_adjParams (g : Sigma1) : AbsSummable (mobius (adjParams g.1)) :=
  absSummable_mul (absSummable_numX _) (absSummable_linX_inv_adjParams g)

theorem absSummable_kappaCol_adjParams (ht : ‖t‖ < 1) (g : Sigma1) :
    AbsSummable (yCoeff (Jacobs.kappaSeries₂ t (adjParams g.1 1 0) (adjParams g.1 1 1)) 0) :=
  absSummable_kappaCol t ht (norm_adjParams_lower_right_sub_one_le g)
    (norm_adjParams_ratio_le g)

theorem absSummable_autFactor (ht : ‖t‖ < 1) (g : Sigma1) :
    AbsSummable (autFactor t (adjParams g.1)) :=
  absSummable_mul (absSummable_kappaCol_adjParams t ht g)
    (absSummable_pow (absSummable_linX_inv_adjParams g) 2)

/-- **The automorphy-factor cocycle**: `j_{δγ} = j_γ · (j_δ ∘ w_γ)`. -/
theorem autFactor_cocycle {g h : Sigma1} (ht : ‖t‖ < 1)
    (hδγ0 : (adjParams h.1 * adjParams g.1) 1 1 ≠ 0)
    (hz : ‖adjParams h.1 1 0 / adjParams h.1 1 1
        * PowerSeries.constantCoeff (mobius (adjParams g.1))‖ ≤ ‖(3 : K₃)‖ ^ 2)
    :
    autFactor t (adjParams h.1 * adjParams g.1)
      = autFactor t (adjParams g.1)
        * compAn (autFactor t (adjParams h.1)) (mobius (adjParams g.1)) := by
  set γ := adjParams g.1 with hγ
  set δ := adjParams h.1 with hδ
  set w := mobius γ with hw
  have hγ0 : γ 1 1 ≠ 0 := adjParams_lower_right_ne_zero g
  have hδ0 : δ 1 1 ≠ 0 := adjParams_lower_right_ne_zero h
  have hwc : CoeffLeOne w := coeffLeOne_mobius_adjParams g
  have hAS : AbsSummable (yCoeff (Jacobs.kappaSeries₂ t (δ 1 0) (δ 1 1)) 0) :=
    absSummable_kappaCol_adjParams t ht h
  have hAI : AbsSummable (linX δ)⁻¹ := absSummable_linX_inv_adjParams h
  have hlt : ‖δ 1 0‖ < ‖δ 1 1‖ := by
    rw [norm_adjParams_lower_right h]
    exact lt_of_le_of_lt (norm_adjParams_lower_left_le h)
      (pow_lt_one₀ (norm_nonneg _) norm_three_lt_one two_ne_zero)
  have hLinv : compAn ((linX δ)⁻¹) w = (compAn (linX δ) w)⁻¹ :=
    compAn_inv (absSummable_linX δ) hAI hwc
      (by rw [constantCoeff_linX]; exact hδ0)
      (constantCoeff_compAn_linX_ne_zero (norm_adjParams_lower_right h)
        (by rw [← norm_adjParams_lower_right h]; exact hlt) hwc)
  have hcoc := kappaCol_cocycle t ht.le hγ0 hδ0 hδγ0
    (norm_adjParams_lower_right_sub_one_le g) (norm_adjParams_lower_right_sub_one_le h)
    hz hAS hwc
  have hfac : linX (δ * γ) = linX γ * compAn (linX δ) w := by
    rw [compAn_linX δ hwc, linX_mul_eq γ δ hγ0, add_comm]
  rw [autFactor, autFactor, autFactor, hcoc, hfac, PowerSeries.mul_inv_rev,
    compAn_mul hAS (absSummable_pow hAI 2) hwc, compAn_pow hAI hwc 2, hLinv]
  ring

theorem adjParams_mul (g h : Matrix (Fin 2) (Fin 2) K₃) :
    adjParams (g * h) = adjParams h * adjParams g := by
  rw [adjParams, adjParams, adjParams, Matrix.adjugate_mul_distrib]

theorem absSummable_yCoeff_weightGenFun (ht : ‖t‖ < 1) (h : Sigma1) (r : ℕ) :
    PowerSeries.AbsSummable (yCoeff (Jacobs.weightGenFun t (adjParams h.1)) r) := by
  rw [yCoeff_weightGenFun t (adjParams_lower_right_ne_zero h) r]
  exact absSummable_mul (absSummable_autFactor t ht h)
    (absSummable_pow (absSummable_mobius_adjParams h) r)

/-- **The column cocycle**, the generating-function form of `kappaOp_mul`:
`yCoeff (weightGenFun (δγ)) r = j_γ · ((yCoeff (weightGenFun δ) r) ∘ w_γ)`. -/
theorem yCoeff_weightGenFun_mul {g h : Sigma1} (ht : ‖t‖ < 1)
    (hδγ0 : (adjParams h.1 * adjParams g.1) 1 1 ≠ 0)
    (hz : ‖adjParams h.1 1 0 / adjParams h.1 1 1
        * PowerSeries.constantCoeff (mobius (adjParams g.1))‖ ≤ ‖(3 : K₃)‖ ^ 2)
    (r : ℕ) :
    yCoeff (Jacobs.weightGenFun t (adjParams h.1 * adjParams g.1)) r
      = autFactor t (adjParams g.1)
        * compAn (yCoeff (Jacobs.weightGenFun t (adjParams h.1)) r)
            (mobius (adjParams g.1)) := by
  set γ := adjParams g.1 with hγd
  set δ := adjParams h.1 with hδd
  set w := mobius γ with hwd
  have hγ0 : γ 1 1 ≠ 0 := adjParams_lower_right_ne_zero g
  have hδ0 : δ 1 1 ≠ 0 := adjParams_lower_right_ne_zero h
  have hwc : CoeffLeOne w := coeffLeOne_mobius_adjParams g
  have hmob : compAn (mobius δ) w = mobius (δ * γ) := by
    refine compAn_mobius_mobius (norm_adjParams_lower_right h) ?_
      (norm_adjParams_le_one g 0 0) (norm_adjParams_le_one g 0 1)
      (norm_adjParams_lower_right g)
      ((norm_adjParams_lower_left_le g).trans
        (pow_le_one₀ (norm_nonneg _) norm_three_lt_one.le)) hδγ0
    exact lt_of_le_of_lt (norm_adjParams_lower_left_le h)
      (pow_lt_one₀ (norm_nonneg _) norm_three_lt_one two_ne_zero)
  rw [yCoeff_weightGenFun t hδγ0 r, yCoeff_weightGenFun t hδ0 r,
    compAn_mul (absSummable_autFactor t ht h)
      (PowerSeries.absSummable_pow (absSummable_mobius_adjParams h) r) hwc,
    compAn_pow (absSummable_mobius_adjParams h) hwc r, hmob,
    autFactor_cocycle t ht hδγ0 hz]
  ring

include ht in
/-- **The action law** ([Jacobs, Def 1.27]: "It is an easy check that … `|κ` is a
right-action of `Σ_ν` on `A_p`", left-composed form): `kappaOp` is multiplicative. -/
theorem kappaOp_mul (g h : Sigma1) :
    kappaOp t ht (g * h) = (kappaOp t ht g).comp (kappaOp t ht h) := by
  set γ := adjParams g.1 with hγd
  set δ := adjParams h.1 with hδd
  set w := mobius γ with hwd
  have hadj : adjParams ((g * h) : Sigma1).1 = δ * γ := by
    rw [hγd, hδd, ← adjParams_mul]
    rfl
  have hδγ0 : (δ * γ) 1 1 ≠ 0 := by
    rw [← hadj]; exact adjParams_lower_right_ne_zero (g * h)
  have hwc : CoeffLeOne w := coeffLeOne_mobius_adjParams g
  have hz : ‖δ 1 0 / δ 1 1 * PowerSeries.constantCoeff w‖ ≤ ‖(3 : K₃)‖ ^ 2 := by
    rw [norm_mul]
    refine le_trans (mul_le_mul (norm_adjParams_ratio_le h) ?_ (norm_nonneg _)
      (by positivity)) (by rw [mul_one])
    simpa using hwc 0
  refine ext_matrixCoeff fun j i => ?_
  rw [matrixCoeff_kappaOp, matrixCoeff_comp, hadj, ← coeff_yCoeff,
    yCoeff_weightGenFun_mul t ht hδγ0 hz i,
    coeff_mul_compAn (absSummable_yCoeff_weightGenFun t ht h i) hwc]
  refine tsum_congr fun k => ?_
  rw [matrixCoeff_kappaOp, matrixCoeff_kappaOp, ← coeff_yCoeff, ← coeff_yCoeff,
    yCoeff_weightGenFun t (adjParams_lower_right_ne_zero g) k, autFactor]

end Cocycle

/-- The diagonal series `∑ₘ xᵐyᵐ = (1 − xy)⁻¹`. -/
private noncomputable def diagSeries : MvPowerSeries (Fin 2) K₃ :=
  fun p => if p 0 = p 1 then 1 else 0

private theorem coeff_diagSeries (p : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff p diagSeries = if p 0 = p 1 then 1 else 0 := rfl

private theorem quadSeries_one :
    Jacobs.quadSeries (1 : Matrix (Fin 2) (Fin 2) K₃)
      = 1 - MvPowerSeries.X 0 * MvPowerSeries.X 1 := by
  rw [Jacobs.quadSeries]
  simp

private theorem linSeries_one :
    Jacobs.linSeries (1 : Matrix (Fin 2) (Fin 2) K₃) = 1 := by
  rw [Jacobs.linSeries]
  simp

private theorem kappaSeries₂_zero_one : Jacobs.kappaSeries₂ t 0 1 = 1 := by
  refine MvPowerSeries.ext fun p => ?_
  rw [Jacobs.coeff_kappaSeries₂]
  by_cases h1 : p 1 = 0
  · by_cases h0 : p 0 = 0
    · rw [if_pos h1, h0]
      simp [MvPowerSeries.coeff_one, Jacobs.fin2_eq_zero h0 h1]
    · rw [if_pos h1]
      have : (0 : K₃) / 1 = 0 := by norm_num
      rw [this, zero_pow h0, mul_zero, mul_zero]
      rw [MvPowerSeries.coeff_one, if_neg]
      intro hc
      exact h0 (by rw [hc]; simp)
  · rw [if_neg h1, MvPowerSeries.coeff_one, if_neg]
    intro hc
    exact h1 (by rw [hc]; simp)

include ht in
theorem kappaOp_one : kappaOp t ht 1 = ContinuousLinearMap.id K₃ c(ℕ, K₃) := by
  refine Jacobs.ext_matrixCoeff fun j i => ?_
  rw [matrixCoeff_kappaOp t ht 1 j i]
  have hadj : adjParams (1 : Sigma1).1 = 1 := by
    rw [adjParams]
    simp
  have hF : weightGenFun t (adjParams (1 : Sigma1).1) = diagSeries := by
    rw [hadj, Jacobs.weightGenFun, linSeries_one, quadSeries_one]
    have h11 : (1 : Matrix (Fin 2) (Fin 2) K₃) 1 0 = 0 := by simp
    have h1d : (1 : Matrix (Fin 2) (Fin 2) K₃) 1 1 = 1 := by simp
    rw [h11, h1d, kappaSeries₂_zero_one, one_mul, inv_one, one_mul]
    refine (MvPowerSeries.inv_eq_iff_mul_eq_one ?_).mpr ?_
    · simp
    · have hXX : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K₃)
          = MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) 1
              + Finsupp.single (1 : Fin 2) 1) 1 := by
        rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial,
          mul_one]
      refine MvPowerSeries.ext fun p => ?_
      rw [mul_sub, mul_one, map_sub, hXX, MvPowerSeries.coeff_mul_monomial,
        coeff_diagSeries, MvPowerSeries.coeff_one]
      set n : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1
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
                exact hp (Jacobs.fin2_eq_zero hz (hd ▸ hz)))
            · simpa [hn1] using Nat.one_le_iff_ne_zero.mpr (by
                intro hz
                exact hp (Jacobs.fin2_eq_zero (hd.symm ▸ hz) hz)))
  rw [hF, coeff_diagSeries]
  simp only [idx_apply_zero, idx_apply_one]
  rw [TateFredholm.matrixCoeff]
  show (if j = i then (1 : K₃) else 0) = (Pi.single i (1 : K₃) : ℕ → K₃) j
  rw [Pi.single_apply]

/-- The Tate algebra `c(ℕ, K₃)` as a distributive `Σ₁(9)`-module via `kappaOp`. -/
@[instance_reducible]
noncomputable def kappaModuleAction (t : K₃) (ht : ‖t‖ < 1) :
    DistribMulAction Sigma1 c(ℕ, K₃) where
  smul g f := kappaOp t ht g f
  one_smul f := by
    show kappaOp t ht 1 f = f
    rw [kappaOp_one t ht]
    rfl
  mul_smul g h f := by
    show kappaOp t ht (g * h) f = kappaOp t ht g (kappaOp t ht h f)
    rw [kappaOp_mul t ht g h]
    rfl
  smul_zero g := map_zero (kappaOp t ht g)
  smul_add g f₁ f₂ := map_add (kappaOp t ht g) f₁ f₂

end Jacobs.U3
