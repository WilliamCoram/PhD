/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.Padics.Complex
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Extension
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Padic

/-!
# The algebraic closure of `ℚ_p`, and `ℂ_p`

The valuation of `ℚ_p` is commensurable at `p`, so by `Extension.lean` so is the valuation of every
algebraic ultrametric normed `ℚ_p`-algebra field — in particular `PadicAlgCl p`, the algebraic
closure of `ℚ_p` with its spectral norm — and so is the valuation of the completion `ℂ_[p]` of that
closure. Hence `normAddValQ ℂ_[p] p : AddValuation ℂ_[p] (WithTop ℚ)` is defined, with
`normAddValQ ℂ_[p] p p = 1`; it restricts to `Padic.addValuation` on `ℚ_p`, satisfies
`‖x‖ = p ^ (-(normAddValQ ℂ_[p] p x))`, and takes every rational value: the value group of `ℂ_p`
is exactly `p^ℚ`.

This is the object roadmap convention 8 refers to: the valuation of a root of a polynomial over
`ℚ_p` is its `normAddValQ` value in `PadicAlgCl p`, a rational number.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §1.5.4–§1.5.5. Tau Ceti home:
`TauCeti/NumberTheory/Padics/Complex/AddVal.lean`.
-/

open scoped NNReal WithZero

variable {p : ℕ} [Fact p.Prime]

namespace NormedField

open Valuation

/-- Every algebraic ultrametric normed `ℚ_p`-algebra field is commensurable at `p`. -/
instance isCommensurable_natCast_prime {L : Type*} [NontriviallyNormedField L]
    [IsUltrametricDist L] [NormedAlgebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L] :
    (valuation (K := L)).IsCommensurable (p : L) := by
  have h := isCommensurable_algebraMap (K := ℚ_[p]) (L := L) (p : ℚ_[p])
  rwa [map_natCast] at h

end NormedField

namespace PadicAlgCl

open NormedField Valuation

/-- The valuation of the algebraic closure of `ℚ_p` is commensurable at `p`. -/
theorem isCommensurable_p : (valuation (K := PadicAlgCl p)).IsCommensurable (p : PadicAlgCl p) :=
  inferInstance

end PadicAlgCl

namespace PadicComplex

open NormedField Valuation WithZero

/-- The valuation of `ℂ_[p]` extended from the algebraic closure is the valuation read off the
norm. -/
theorem valuation_eq_nnnorm (x : ℂ_[p]) : Valued.v x = ‖x‖₊ := by
  rw [← NNReal.coe_inj, coe_nnnorm, PadicComplex.norm_eq_norm p x, Valuation.norm_def,
    PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]

theorem normedField_valuation_eq : (valuation (K := ℂ_[p])) = (PadicComplex.valued p).v :=
  Valuation.ext fun x ↦ by rw [NormedField.valuation_apply, valuation_eq_nnnorm]

/-- **The valuation of `ℂ_p` is commensurable at `p`**: the `ℚ`-valued additive valuation
`normAddValQ ℂ_[p] p` exists. -/
instance isCommensurable_p : (valuation (K := ℂ_[p])).IsCommensurable (p : ℂ_[p]) := by
  have h₀ : (Valued.v : Valuation (PadicAlgCl p) ℝ≥0).IsCommensurable (p : PadicAlgCl p) :=
    PadicAlgCl.isCommensurable_p
  have h₁ := Valued.isCommensurable_completion (K := PadicAlgCl p) (p : PadicAlgCl p)
  rw [normedField_valuation_eq]
  simpa only [PadicComplex.coe_natCast] using h₁

/-- The normalisation `normAddValQ ℂ_[p] p p = 1`. -/
theorem normAddValQ_p : normAddValQ ℂ_[p] p p = 1 := normAddValQ_self _ _

/-- On `ℚ_p`, the `ℚ`-valued additive valuation of `ℂ_p` normalised at `p` is `Padic.addValuation`
composed with `Int.cast`. -/
theorem normAddValQ_algebraMap_padic (x : ℚ_[p]) :
    normAddValQ ℂ_[p] p (algebraMap ℚ_[p] ℂ_[p] x)
      = WithTop.map (fun n : ℤ ↦ (n : ℚ)) (Padic.addValuation x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, normAddValQ_zero, AddValuation.map_zero, WithTop.map_top]
  rw [Padic.addValuation.apply hx, WithTop.map_coe]
  have hp : ‖(p : ℂ_[p])‖₊ = ‖(p : ℚ_[p])‖₊ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, nnnorm_algebraMap']
  have hxv : valuation (algebraMap ℚ_[p] ℂ_[p] x) ^ (1 : ℤ)
      = valuation (p : ℂ_[p]) ^ x.valuation := by
    rw [zpow_one, valuation_apply, valuation_apply, nnnorm_algebraMap', hp,
      Padic.nnnorm_p_zpow_valuation hx]
  rw [normAddValQ, addValQ_eq_of_zpow _ _
    ((Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hx)) one_pos hxv]
  norm_num

/-- **Norm recovery on `ℂ_p`**: `‖x‖ = p ^ (-(normAddValQ ℂ_[p] p x))`. -/
theorem norm_eq_rpow_neg_normAddValQ {x : ℂ_[p]} {q : ℚ}
    (hq : normAddValQ ℂ_[p] p x = (q : WithTop ℚ)) : ‖x‖ = (p : ℝ) ^ (-(q : ℝ)) := by
  rw [norm_eq_norm_rpow_normAddValQ _ _ hq]
  have hp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap', Padic.norm_p]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [hp, Real.inv_rpow hp0, ← Real.rpow_neg hp0]

/-- Every rational number is the additive valuation of a nonzero element of `ℂ_p`. -/
theorem exists_normAddValQ_eq (q : ℚ) :
    ∃ x : ℂ_[p], x ≠ 0 ∧ normAddValQ ℂ_[p] p x = (q : WithTop ℚ) := by
  have hb : 0 < q.den := q.den_pos
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p]) ^ q.num) hb
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hb.ne'] at hz
    exact zpow_ne_zero q.num hp0 hz.symm
  have hv : valuation z ^ (q.den : ℤ) = valuation (p : ℂ_[p]) ^ q.num := by
    rw [zpow_natCast, ← map_pow, hz, map_zpow₀]
  refine ⟨z, hz0, ?_⟩
  rw [normAddValQ, addValQ_eq_of_zpow _ _ ((Valuation.ne_zero_iff _).mpr hz0)
    (by exact_mod_cast hb) hv, Int.cast_natCast, Rat.num_div_den]

/-- **The value group of `ℂ_p` is exactly `p^ℚ`**: the additive valuation takes every rational
value and, apart from `⊤` at `0`, nothing else. -/
theorem range_normAddValQ :
    Set.range (normAddValQ ℂ_[p] p) = insert ⊤ (Set.range ((↑) : ℚ → WithTop ℚ)) := by
  ext y
  simp only [Set.mem_range, Set.mem_insert_iff]
  constructor
  · rintro ⟨x, rfl⟩
    rcases eq_or_ne x 0 with rfl | hx
    · left; exact normAddValQ_zero ℂ_[p] (p : ℂ_[p])
    · right
      obtain ⟨r, hr⟩ :=
        WithTop.ne_top_iff_exists.mp ((normAddValQ_eq_top ℂ_[p] (p : ℂ_[p])).not.mpr hx)
      exact ⟨r, hr⟩
  · rintro (rfl | ⟨r, rfl⟩)
    · exact ⟨0, normAddValQ_zero ℂ_[p] (p : ℂ_[p])⟩
    · obtain ⟨x, -, hx⟩ := exists_normAddValQ_eq (p := p) r
      exact ⟨x, hx⟩

end PadicComplex
