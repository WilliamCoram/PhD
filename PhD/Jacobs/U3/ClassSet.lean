/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3.Level

/-!
# Theorem 2.1: the class set of `U₁(9)`, and Lemma 2.2: trivial stabilisers

[Jacobs, Theorem 2.1 p. 23]:

> "D_f^× = D^× c₀ U₁(9) ⊔ D^× c₁ U₁(9) ⊔ D^× c₂ U₁(9), where c₀,p = 1 ∀p;
> c₁,p = 1 if p ≠ 3, (5 0; 0 2) if p = 3; c₂,p = 1 if p ≠ 3, (7 0; 0 4) if p = 3."

[Jacobs, Lemma 2.2 p. 24]:  "Γᵢ = {1} for all i = 0, 1, 2."

The proof route is the thesis's own chain [(1.4.5)–(1.4.12) pp. 16–18]: given (1.4.4)
(`HClassNumberOne`), the class set reduces to the orbit space of the 24-unit image
`𝓞_D^× → SL₂(ℤ/9)` acting on the 72 primitive vectors of `(ℤ/9)²`, a finite computation
("an unilluminating calculation shows that O_D^×\G·x consists of three elements").
Every statement below that mentions the class set takes `HClassNumberOne` as an explicit
hypothesis (discharged by `hClassNumberOne`).
-/

open Quaternion IsDedekindDomain NumberField QMF

namespace Jacobs.U3

/-! ## The representatives -/

/-- The adelic representative `cᵢ` [Jacobs, Thm 2.1]: trivial away from `3`, and the
diagonal matrix `θ₃⁻¹ (dᵢ 0; 0 eᵢ)` at `3`, for `(d,e) = (1,1), (5,2), (7,4)`.
(Constructed through the rigidification and the `v₃`-component splitting of
`PhD.QMF.UpiElement`; `det = dᵢeᵢ ∈ {1, 10, 28}` is a `3`-adic unit, so this is a unit
of the local order and defines an element of `D_f^×`.) -/
noncomputable def classRep : Fin 3 → Dfx ℚ D := sorry

/-- The `3`-component matrices of the representatives are the thesis's `(1 0; 0 1)`,
`(5 0; 0 2)`, `(7 0; 0 4)`. -/
theorem toMatrix_classRep (i : Fin 3) :
    toMatrix ℚ D v₃ (classRep i)
      = Matrix.of ![![((![1, 5, 7] : Fin 3 → ℤ) i : K₃), 0],
                    ![0, ((![1, 2, 4] : Fin 3 → ℤ) i : K₃)]] := sorry

/-! ## The mod-9 orbit computation

The finite substrate of Theorem 2.1: the image of the 24 Hurwitz units in `SL₂(ℤ/9)`
acting on the primitive vectors.  The unit images are *derived* from `θ₃` and the
congruence `ν₃ ≡ 4 mod 9` — the p. 23 table is recomputed, not transcribed. -/

/-- Reduction of the Hurwitz units to `GL₂(ℤ/9)` along `θ₃` and `𝓞₃ → ℤ/9`. -/
noncomputable def unitsMod9 : (hurwitzOrder)ˣ →* GL (Fin 2) (ZMod 9) := sorry

/-- The primitive vectors: pairs with at least one coordinate a unit ([Jacobs,
Prop 1.25]: "G·x = {(x₁, x₂) ∈ X : at least one of x₁, x₂ ∈ (ℤ/pⁿ)^×}"); there are
`72` of them. -/
def primitiveVectors : Finset ((ZMod 9) × (ZMod 9)) :=
  {v | IsUnit v.1 ∨ IsUnit v.2}

theorem card_primitiveVectors : primitiveVectors.card = 72 := sorry

/-- **The orbit computation** [Jacobs, Thm 2.1 proof, p. 24]: the `𝓞_D^×`-orbits of the
primitive vectors are exactly three, with representatives `(1,0), (5,0), (7,0)`.
Stated as a partition into three explicit orbits. -/
theorem orbits_unitsMod9 :
    ∀ x ∈ primitiveVectors, ∃! i : Fin 3,
      ∃ u : (hurwitzOrder)ˣ,
        (unitsMod9 u).1.mulVec ![((![1, 5, 7] : Fin 3 → ℤ) i : ZMod 9), 0] = ![x.1, x.2] := sorry

/-! ## Theorem 2.1 and Lemma 2.2 -/

/-- **[Jacobs, Theorem 2.1]**: under `HClassNumberOne`, the `classRep` family is a
complete system of representatives: every `g ∈ D_f^×` lies in `D^× · cᵢ · U₁(9)` for a
unique `i`. -/
theorem classRep_complete (hcn : HClassNumberOne) (g : Dfx ℚ D) :
    ∃! i : Fin 3, ∃ d ∈ globalUnits ℚ D, ∃ u ∈ U1_9, g = d * classRep i * u := sorry

/-- The double-coset section form used by `AutomorphicFunction.bijective_evalAtReps`:
each double-coset class contains exactly one `classRep`. -/
theorem exists_classRep_section (hcn : HClassNumberOne) :
    ∃ σ : DoubleCoset.Quotient ((globalUnits ℚ D : Subgroup (Dfx ℚ D)) : Set (Dfx ℚ D))
        (U1_9 : Set (Dfx ℚ D)) → Dfx ℚ D,
      (∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient _ _) = q) ∧
        ∀ q, ∃ i : Fin 3, σ q = classRep i := sorry

/-- **[Jacobs, Lemma 2.2]**: the stabilisers are trivial — `Γᵢ = cᵢ⁻¹ D^× cᵢ ∩ U₁(9) = 1`.
(In the framework's terms: `stabilizerAt (globalUnits) U1_9 (classRep i) = ⊥`; the proof
is the finite check that no nontrivial Hurwitz unit is `≡ (∗ ∗; 0 1) mod 9` after
conjugation by `cᵢ`.) -/
theorem stabilizerAt_classRep (i : Fin 3) :
    AutomorphicFunction.stabilizerAt (globalUnits ℚ D) U1_9 (classRep i) = ⊥ := sorry

end Jacobs.U3
