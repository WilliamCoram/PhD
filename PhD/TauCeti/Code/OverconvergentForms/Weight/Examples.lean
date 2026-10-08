/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import PhD.TauCeti.Code.OverconvergentForms.Weight.Classical
import PhD.TauCeti.Code.OverconvergentForms.Weight.Dictionary

/-!
# Acceptance examples for Layer 1

The examples of the roadmap's Layer 1 for `F = ℚ`, `L = K = ℚ_p` with the single embedding: the
algebraic weight `u ↦ u^k` at every level `ρ = ‖p‖` with `col(c, d) = (d + c z)^k`; the matrix of
`diag(1, d)`, `z^r ↦ d^{k−r} z^r`; the matrix of `((1 0), (c 1))`; a nebentypus of conductor `p`
loaded into `u^k ψ(u)` at level `p ∣ c`; the scalar `−1` acting by `(−1)^k`; and the adjugate of
`((3 0), (9t 1))`.

⚠ The example `u ↦ u^s = padicExp (s · padicLog u)` on `1 + pℤ_p` with its binomial expansion datum
is FLOOR-PENDING: it needs the `p`-adic-functional-analysis roadmap's §4.5 (`padicExp`, `padicLog`,
the binomial series), which the Tau Ceti chain does not yet contain (see `plan.md`).

Roadmap: Layer 1, Examples. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Weight/Examples.lean`.
-/

open MvPowerSeries MvPowerSeries.Restricted

namespace AutomorphicForm

/-- `‖p‖ < 1` in `ℚ_p`: the level `ρ = ‖p‖`. -/
theorem norm_natCast_prime_lt_one (p : ℕ) [Fact p.Prime] : ‖(p : ℚ_[p])‖ < 1 :=
  Padic.norm_p_lt_one

variable {p : ℕ} [Fact p.Prime]

/-- The algebraic weight `u ↦ u^k` has the expansion `col(c, d) = (d + c z)^k`. -/
example (k : ℕ) (c d : ℚ_[p]) :
    (Embeddings.self ℚ_[p]).algCol (fun _ : Unit => (k : ℤ)) c d =
      (C 1 d + C 1 c * X ℚ_[p] 1 ()) ^ k := by
  rw [(Embeddings.self ℚ_[p]).algCol_natCast (fun _ => k), Fintype.prod_unique]
  rfl

/-- The matrix of `diag(1, d)` on the weight `u ↦ u^k`: `z^r ↦ d^{k−r} z^r` for `r ≤ k`. -/
example (k r : ℕ) (hr : r ≤ k) {d : ℚ_[p]} (hd : ‖d‖ = 1) :
    ((Embeddings.self ℚ_[p]).algWeight
        (levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p))
        (fun _ : Unit => (k : ℤ)) 1 (by simp)).kappaSlash
      ⟨!![1, 0; 0, d], ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp [hd], by simp,
        by simpa using hd,
        by simpa [Matrix.det_fin_two_of] using norm_ne_zero_iff.mp (hd ▸ one_ne_zero)⟩⟩
        (monomial 1 (Finsupp.single () r) 1) =
      d ^ (k - r) • monomial 1 (Finsupp.single () r) 1 := by
  have hmono : monomial (1 : Unit → ℝ) (Finsupp.single () r) (1 : ℚ_[p]) = X ℚ_[p] 1 () ^ r := by
    rw [monomial_eq_C_mul_prod, map_one, one_mul,
      Finsupp.prod_single_index (h := fun i k => X ℚ_[p] (1 : Unit → ℝ) i ^ k) (pow_zero _)]
  refine (AnalyticWeight.kappaSlash_algWeight_monomial _ (fun _ => k) 1 (by simp) _ _
    fun _ => by simpa using hr).trans ?_
  rw [Fintype.prod_unique, hmono]
  simp [lin, num, Algebra.smul_def, MvPowerSeries.Restricted.algebraMap_apply,
    AnalyticWeight.detChar, Embeddings.self]

/-- The matrix of `((1 0), (c 1))` on the weight `u ↦ u^k`: `z^r ↦ (1 + c z)^{k−r} z^r` for
`r ≤ k`. -/
example (k r : ℕ) (hr : r ≤ k) {c : ℚ_[p]} (hc : ‖c‖ ≤ ‖(p : ℚ_[p])‖) :
    ((Embeddings.self ℚ_[p]).algWeight
        (levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p))
        (fun _ : Unit => (k : ℤ)) 1 (by simp)).kappaSlash
      ⟨!![1, 0; c, 1], ⟨fun i j => by
        fin_cases i <;> fin_cases j <;> simp [hc.trans (norm_natCast_prime_lt_one p).le],
        by simpa using hc, by simp, by simp [Matrix.det_fin_two_of]⟩⟩
        (monomial 1 (Finsupp.single () r) 1) =
      (1 + C 1 c * X ℚ_[p] 1 ()) ^ (k - r) * X ℚ_[p] 1 () ^ r := by
  refine (AnalyticWeight.kappaSlash_algWeight_monomial _ (fun _ => k) 1 (by simp) _ _
    fun _ => by simpa using hr).trans ?_
  rw [Fintype.prod_unique]
  simp [lin, num, AnalyticWeight.detChar, Embeddings.self]

/-- A nebentypus `ψ` of conductor `p` loaded into `u^k ψ(u)` at level `p ∣ c`: the automorphy
factor is `ψ(d̄) (d + c z)^k`. -/
example (k : ℕ)
    (ψ : (Subring.unitClosedBall ℚ_[p] ⧸ NormedRing.closedBallIdeal ℚ_[p]
      ⟨‖(p : ℚ_[p])‖, norm_nonneg _⟩)ˣ →* ℚ_[p]ˣ) (hψ : ∀ x, ‖(ψ x : ℚ_[p])‖ = 1)
    (γ : SigmaNorm ℚ_[p] ‖(p : ℚ_[p])‖ (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p)) :
    ((Embeddings.self ℚ_[p]).classicalShape
        (levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p))
        (fun _ : Unit => (k : ℤ)) 1 (by simp) ψ hψ).autFactor γ =
      (ψ ((levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p]))
          (norm_natCast_prime_lt_one p)).lowerRightResidue γ) : ℚ_[p]) •
        (C 1 ((γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1) +
          C 1 ((γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0) * X ℚ_[p] 1 ()) ^ k := by
  rw [Embeddings.autFactor_classicalShape]
  show ((ψ _ : ℚ_[p]) * (1 : ℚ_[p])) • _ = _
  rw [mul_one, (Embeddings.self ℚ_[p]).algCol_natCast (fun _ => k), Fintype.prod_unique]
  rfl

/-- The scalar `−1` acts on the weight `u ↦ u^k` by `(−1)^k`. -/
example (k : ℕ) (f : Restricted ℚ_[p] (1 : Unit → ℝ)) :
    ((Embeddings.self ℚ_[p]).algWeight
        (levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p))
        (fun _ : Unit => (k : ℤ)) 1 (by simp)).kappaSlash
      ⟨((-1 : (Subring.unitClosedBall ℚ_[p])ˣ) : Subring.unitClosedBall ℚ_[p]) • 1,
        smul_one_mem_sigmaNorm _ _ _⟩ f = (-1 : ℚ_[p]) ^ k • f := by
  refine (AnalyticWeight.kappaSlash_smul_one _ (-1) (smul_one_mem_sigmaNorm _ _ _) f).trans ?_
  congr 1
  show ((Embeddings.self ℚ_[p]).algChar (fun _ : Unit => (k : ℤ)) (-1) : ℚ_[p]) * (1 : ℚ_[p]) = _
  rw [mul_one, Embeddings.coe_algChar, Fintype.prod_unique]
  simp

/-- The adjugate of `((3 0), (9t 1))` is the left-handed `((1 0), (−9t 3))`. -/
example (t : ℚ_[3]) : (!![3, 0; 9 * t, 1] : Matrix (Fin 2) (Fin 2) ℚ_[3]).adjugate =
    !![1, 0; -(9 * t), 3] := by
  rw [Matrix.adjugate_fin_two_of, neg_zero]

end AutomorphicForm
