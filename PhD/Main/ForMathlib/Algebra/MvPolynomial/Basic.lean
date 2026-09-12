/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.MvPolynomial.Basic

/-! # Coefficientwise application of a zero-preserving map to a multivariate polynomial

Multivariate analogue of `Polynomial.coeff_finsetSum_monomial_apply`: for a zero-preserving
map `π : R → S` (any `ZeroHomClass`), the `k`-th coefficient of
`∑ n ∈ r.support, monomial n (π (r.coeff n))` — the polynomial `r` with `π` applied
coefficientwise — is `π (r.coeff k)`.
-/

namespace MvPolynomial

variable {F R S σ : Type*} [CommSemiring R] [CommSemiring S] [FunLike F R S]
  [ZeroHomClass F R S]

/-- The `k`-th coefficient of `∑ n ∈ r.support, monomial n (π (r.coeff n))` — the multivariate
polynomial `r` with the zero-preserving map `π` applied coefficientwise — is `π (r.coeff k)`. -/
lemma coeff_finsetSum_monomial_apply (π : F) (r : MvPolynomial σ R) (k : σ →₀ ℕ) :
    coeff k (∑ n ∈ r.support, monomial n (π (r.coeff n))) = π (r.coeff k) := by
  classical
  simp_rw [coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · grind

end MvPolynomial
