/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Hamilton.Factorisations
import PhD.TauCeti.Code.OverconvergentForms.Adelic.Norm

/-!
# Acceptance examples for Layer 0

The examples of the roadmap's Layer 0, each an instance of a theorem of this development: the
Hurwitz units, the compact open levels `U₀(1)` and `U₁(9)`, the two class sets, the splitting of
`Iw(3²) η Iw(3²)` into three right cosets, `diag(3, 1) ∈ M_t` not being a unit, and the norm class
of a global quaternion.

Roadmap: Layer 0, Examples. Tau Ceti home: `TauCeti/NumberTheory/AutomorphicForm/Examples.lean`.
-/

open scoped Quaternion TensorProduct Pointwise
open IsDedekindDomain NumberField AdelicAlgebra Quaternion QuaternionAlgebra LocalLevel Hamilton

open scoped AdelicAlgebra.RightAlgebra

noncomputable section

/-- The Hurwitz order has `24` units. -/
example : Nat.card (hurwitzOrder)ˣ = 24 := card_units_hurwitzOrder

/-- `U₀(1)` and `U₁(9)` are compact open. -/
example : IsCompact (Hamilton.U0 : Set (Dfx ℚ ℍ[ℚ])) ∧ IsOpen (Hamilton.U0 : Set (Dfx ℚ ℍ[ℚ])) :=
  ⟨Hamilton.isCompact_U0, Hamilton.isOpen_U0⟩

example : IsCompact (U1_9 : Set (Dfx ℚ ℍ[ℚ])) ∧ IsOpen (U1_9 : Set (Dfx ℚ ℍ[ℚ])) :=
  ⟨isCompact_U1_9, isOpen_U1_9⟩

/-- `D^× \ D_f^× / U₀(1)` is a point and `D^× \ D_f^× / U₁(9)` has three points. -/
example : Subsingleton (classSet ℚ ℍ[ℚ] Hamilton.U0) := subsingleton_classSet_U0

example : Nat.card (classSet ℚ ℍ[ℚ] U1_9) = 3 := card_classSet_U1_9

/-- `Iw(3²) η Iw(3²)` splits into three right cosets. -/
example :
    ((Quotient.mk'' : GL (Fin 2) K₃ →
        Quotient (QuotientGroup.rightRel (iwahori K₃ (Valued.v ((3 : ℚ) : K₃) ^ 2)))) ''
      (({etaGL ((3 : ℚ) : K₃) three_ne_zero'} : Set (GL (Fin 2) K₃)) *
        (iwahori K₃ (Valued.v ((3 : ℚ) : K₃) ^ 2) : Set (GL (Fin 2) K₃)))).ncard = 3 := by
  have hb := bijOn_etaRep three_ne_zero' valued_three_lt_one
    (fun _ hx => valued_le_valued_three hx) (t := 2) (by norm_num)
    ((iwahoriPrincipal_le_iwahoriOne _).trans (iwahoriOne_le_iwahori _)) le_rfl
    (fun t : Fin 3 => (((t : ℕ) : ℚ) : K₃))
    (fun t => by rw [Rat.cast_natCast]; exact natCast_mem (v₃.adicCompletionIntegers ℚ) _)
    (fun _ hx => existsUnique_fin_three hx)
  rw [← hb.image_eq, hb.injOn.ncard_image, Set.ncard_range_of_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  intro s t h
  exact etaRep3_injective (congrArg (unitAt ℚ ℍ[ℚ] v₃) h)

/-- `diag(3, 1) ∈ M_t` is not a unit of `M_t`. -/
example {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1) :
    (etaGL ((3 : ℚ) : K₃) three_ne_zero' : Matrix (Fin 2) (Fin 2) K₃) ∈ monoidM K₃ γ hγ ∧
      ((etaGL ((3 : ℚ) : K₃) three_ne_zero')⁻¹ : GL (Fin 2) K₃).1 ∉ monoidM K₃ γ hγ :=
  ⟨coe_etaGL_mem_monoidM hγ _ valued_three_lt_one.le, etaGL_not_unit hγ _ valued_three_lt_one⟩

/-- `|nrd(γ)|_f = nrd(γ)⁻¹` for `γ ∈ ℍ[ℚ]^×`. -/
example (x : (ℍ[ℚ])ˣ) :
    normClass ℚ (-1) (-1) (unitsIncl ℚ ℍ[ℚ] x) = ((nrd (x : ℍ[ℚ]) : ℚ) : ℝ)⁻¹ :=
  normClass_unitsIncl_rat isTotallyDefinite_hamilton x
