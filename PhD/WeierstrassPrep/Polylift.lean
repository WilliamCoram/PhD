import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm
import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted

import PhD.WeierstrassPrep.Restricted_powerbounded_topnil
import PhD.WeierstrassPrep.EpsilonDense
import PhD.WeierstrassPrep.ResPoly
import PhD.WeierstrassPrep.ResC

section EuclideanLift

namespace Polynomial

variable {A : Type*} [CommRing A]

/-- Euclidean division by a monic polynomial, packaged as an existence statement. -/
lemma exists_div_by_monic [Nontrivial A] {g : A[X]} (hg : g.Monic) (f : A[X]) :
    ∃ q r : A[X], f = q * g + r ∧ r.degree < g.degree := by
  refine ⟨f /ₘ g, f %ₘ g, ?_, degree_modByMonic_lt f hg⟩
  have h := modByMonic_add_div f g
  linear_combination -h

variable (I : Ideal A)

/-- A set-theoretic section of `Polynomial.map (Ideal.Quotient.mk I)`: lift each coefficient via
`Quotient.out`. -/
noncomputable
def liftQuot (p : Polynomial (A ⧸ I)) : Polynomial A :=
  ∑ n ∈ p.support, monomial n (Quotient.out (p.coeff n))

@[simp] lemma liftQuot_coeff (p : Polynomial (A ⧸ I)) (n : ℕ) :
    (liftQuot I p).coeff n = if n ∈ p.support then Quotient.out (p.coeff n) else 0 := by
  simp only [liftQuot, finsetSum_coeff, coeff_monomial]
  split_ifs with hn
  · rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]
    · intros m _ hmn; exact if_neg hmn
    · intro h; exact absurd hn h
  · refine Finset.sum_eq_zero fun m hm => ?_
    have hne : m ≠ n := fun h => hn (h ▸ hm)
    exact if_neg hne

lemma liftQuot_map (p : Polynomial (A ⧸ I)) :
    (liftQuot I p).map (Ideal.Quotient.mk I) = p := by
  apply Polynomial.ext; intro n
  rw [coeff_map, liftQuot_coeff]
  by_cases hn : n ∈ p.support
  · rw [if_pos hn]; exact Quotient.out_eq (p.coeff n)
  · rw [if_neg hn, map_zero]
    rw [mem_support_iff, not_not] at hn; exact hn.symm

lemma degree_liftQuot_le (p : Polynomial (A ⧸ I)) : (liftQuot I p).degree ≤ p.degree := by
  refine (degree_sum_le _ _).trans (Finset.sup_le fun n hn => ?_)
  exact (degree_monomial_le n _).trans (le_degree_of_ne_zero (mem_support_iff.mp hn))

end Polynomial
end EuclideanLift
