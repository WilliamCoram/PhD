import PhD.ToPR.Restricted
import PhD.ToPR.MvRestricted

-- TODO: Move this section into Restricted and generalise the proofs into MvRestricted and
-- set these as corollaries

namespace Polynomial

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

@[simp] lemma toRestricted_zero (c : ℝ) :
    toRestricted c (0 : Polynomial S) = 0 :=
  Subtype.ext Polynomial.coe_zero

@[simp] lemma toRestricted_add (c : ℝ) (p q : Polynomial S) :
    toRestricted c (p + q) = toRestricted c p + toRestricted c q :=
  Subtype.ext (Polynomial.coe_add p q)

@[simp] lemma toRestricted_neg (c : ℝ) (p : Polynomial S) :
    toRestricted c (-p) = -toRestricted c p := by
  rfl

@[simp] lemma toRestricted_sub (c : ℝ) (p q : Polynomial S) :
    toRestricted c (p - q) = toRestricted c p - toRestricted c q := by
  rw [sub_eq_add_neg, toRestricted_add, toRestricted_neg, sub_eq_add_neg]

@[simp] lemma toRestricted_mul (c : ℝ) (p q : Polynomial S) :
    toRestricted c (p * q) = toRestricted c p * toRestricted c q :=
  Subtype.ext (coe_mul p q)

end Polynomial
