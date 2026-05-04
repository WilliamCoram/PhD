import Mathlib.Algebra.Order.Antidiag.Prod

namespace Finset

lemma nonempty_antidiagonal {M : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] (a : M) :
    (Finset.antidiagonal a).Nonempty :=
  ⟨(0, a), by simp⟩
