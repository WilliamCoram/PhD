import Mathlib
import PhD.NewtonPolygons.NPFinal

open Polynomial
open Padic

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable
abbrev f : (ℤ_[p])[X] := (C (1 : ℤ_[p])) + X^2 + (C (p^3 : ℤ_[p])) * X^5


instance : FunLike ((ℤ_[p]) → ℝ) (ℤ_[p]) (ℝ) :=
  {coe := fun a ↦ a, coe_injective' := by exact fun ⦃a₁ a₂⦄ a ↦ a}

lemma foo : StrictMonoOn (fun (i : ℕ) ↦ if i = 0 then (0 : ℝ)
    else if i = 1 then 2 else if i = 3 then 5 else 0) (Set.Ico 0 3) := by
  intro i hi j hj hij
  simp only

  sorry

lemma bar : (f p).support = {0,2,5} := by
  refine Finset.ext_iff.mpr ?_
  intro a
  constructor <;> intro ha
  ·
    sorry
  ·
    sorry

lemma check1 : LowerConvexHull.Poly_set (K := ℝ) (ℤ_[p]) ((ℤ_[p]) → ℝ)
    (Nat.cast ∘ PadicInt.valuation (p := p)) (f p) =
  {n := 3
   x := fun i => if i = 0 then 0 else -- maybe there is a better way to do this
                 if i = 1 then 2 else
                 if i = 3 then 5 else
                 0
   y := fun i => if i = 0 then 0 else
                 if i = 1 then 0 else
                 if i = 3 then 3 else
                 0
   increasing := foo
  } := by
  simp_rw [LowerConvexHull.Poly_set]
  simp only [ne_eq, List.getD_eq_getElem?_getD, LowerConvexHull.finset_Prod.mk.injEq]
  constructor
  ·
    sorry
  · constructor
    ·
      sorry
    ·
      sorry
