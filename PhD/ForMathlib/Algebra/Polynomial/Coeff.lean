/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs

/-! # Coefficientwise application of a zero-preserving map to a polynomial

For a zero-preserving map `π : R → S` (any `ZeroHomClass`, e.g. an additive, linear or ring
homomorphism), the polynomial `∑ n ∈ r.support, monomial n (π (r.coeff n))` is `r` with `π`
applied to each coefficient.  Its `k`-th coefficient is `π (r.coeff k)`
(`Polynomial.coeff_finsetSum_monomial_apply`) and its degree does not exceed that of `r`
(`Polynomial.degree_finsetSum_monomial_apply_lt`).

The multivariate analogue of the coefficient formula is
`MvPolynomial.coeff_finsetSum_monomial_apply`.
-/

namespace Polynomial

variable {F R S : Type*} [Semiring R] [Semiring S] [FunLike F R S] [ZeroHomClass F R S]

/-- The `k`-th coefficient of `∑ n ∈ r.support, monomial n (π (r.coeff n))` — the polynomial `r`
with the zero-preserving map `π` applied coefficientwise — is `π (r.coeff k)`. -/
lemma coeff_finsetSum_monomial_apply (π : F) (r : Polynomial R) (k : ℕ) :
    (∑ n ∈ r.support, monomial n (π (r.coeff n))).coeff k = π (r.coeff k) := by
  simp_rw [finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · grind

/-- Applying a zero-preserving map `π` coefficientwise does not raise the degree: if
`r.degree < s` then `(∑ n ∈ r.support, monomial n (π (r.coeff n))).degree < s`. -/
lemma degree_finsetSum_monomial_apply_lt (π : F) {r : Polynomial R} {s : ℕ} (hr : r.degree < s) :
    (∑ n ∈ r.support, monomial n (π (r.coeff n))).degree < s := by
  rw [degree_lt_iff_coeff_zero] at hr ⊢
  intro m hm
  rw [coeff_finsetSum_monomial_apply, hr m hm, map_zero]

end Polynomial
