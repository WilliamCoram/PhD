/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Topology.Algebra.Valued.NormedValued
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Discrete
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ONable
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Rescale
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Residue

/-!
# Serre's theorem

Let `R` be a Banach–Tate ring with a pseudo-uniformiser `ϖ` such that `‖R ∖ {0}‖ = ‖ϖ‖ ^ ℤ`
(Bellaïche's Hypothesis II.1.11), `R̃ = R⁰/ϖR⁰` its residue ring, and `M` a Banach `R`-module whose
norm takes values in `‖ϖ‖ ^ ℤ ∪ {0}`. A family `e` of the unit ball of `M` is an orthonormal basis
if and only if its reduction is a basis of the `R̃`-module `M̃ = M⁰/ϖM⁰` (Bellaïche, Lemma II.1.12;
Colmez, Proposition 1.1.5): the "if" is the successive `ϖ`-adic approximation, the "only if" the
reduction of the sup-norm identity. Hence `M` is orthonormalisable if and only if `M̃` is free, and
every Banach `R`-module is potentially orthonormalisable when all `R̃`-modules are free, in
particular when `R̃` is a field — the rescaled norm of Layer 0 takes values in `‖ϖ‖ ^ ℤ`. Over a
discretely valued field this is Serre's theorem: every Banach space is potentially
orthonormalisable, and orthonormalisable on the nose exactly when its norm takes values in `‖K‖`
(Serre; Schneider, Proposition 10.1 and Remark 10.2; Bellaïche, Theorem II.1.13). Finally the index
set of `C₀(I, K)` is an invariant of the topological vector space (Schneider, Lemma 10.3).

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.3.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/Serre.lean`.

## Main declarations

* `NormedRing.PseudoUniformizer.residueFamily` — the reduction of a family of the unit ball.
* `NormedRing.PseudoUniformizer.isOrthonormalBasis_iff_residueFamily` — Bellaïche II.1.12.
* `NormedRing.PseudoUniformizer.isONable_iff_free_residueModule` — Serre's theorem, ring form.
* `Module.isPotentiallyONable_of_isRankOneDiscrete`, `Module.isONable_iff_forall_exists_norm_eq`
  — Serre's theorem, field form.
* `ZeroAtInftyContinuousMap.nonempty_continuousLinearEquiv_iff` — the index is an invariant.
-/

universe u v w

open Filter Topology Function Module
open scoped ZeroAtInfty
open ZeroAtInftyContinuousMap NormedRing

namespace NormedRing.PseudoUniformizer

variable {R : Type u} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  (ϖ : PseudoUniformizer R) {M : Type v} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [IsUltrametricDist M]

/-- The reduction `ẽ : I → M̃` of a family `e` of the unit ball of `M`. Source: Bellaïche, Lemma
II.1.12 ("let `(eᵢ)` be a family of elements of `M⁰` … their images `ẽᵢ` in `M̃`"). -/
noncomputable def residueFamily {I : Type w} (e : I → M) (he : ∀ i, ‖e i‖ ≤ 1) :
    I → ϖ.ResidueModule M :=
  fun i ↦ Submodule.Quotient.mk ⟨e i, Submodule.mem_unitClosedBall.2 (he i)⟩

section Residue

variable [CompleteSpace R] [CompleteSpace M] {I : Type w} {e : I → M}
  (hR : ∀ r : R, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : R)‖ ^ n)
  (hM : ∀ m : M, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖(ϖ : R)‖ ^ n)
include hR hM

/-- The reduction of an orthonormal family is linearly independent: a relation `∑ ãᵢ ẽᵢ = 0` lifts
to `‖∑ aᵢ eᵢ‖ < 1`, so every `‖aᵢ‖ < 1`, so every `ãᵢ = 0`. Source: Bellaïche, Lemma II.1.12 ("the
`ẽᵢ` are linearly independent over `R̃`"), roadmap §2.3.1 ("the 'only if' direction is the
reduction of the sup-norm identity"). -/
theorem linearIndependent_residueFamily_of_isOrthonormalFamily (he : IsOrthonormalFamily R e) :
    LinearIndependent ϖ.ResidueRing (ϖ.residueFamily e he.norm_le_one) := by
  sorry

/-- The reduction of an orthonormal basis spans `M̃`: expand a lift and keep the finitely many
coefficients of norm `1`. Source: Bellaïche, Lemma II.1.12 ("the `ẽᵢ` generate `M̃`"). -/
theorem span_residueFamily_eq_top_of_isOrthonormalBasis (he : IsOrthonormalBasis R e) :
    Submodule.span ϖ.ResidueRing (Set.range (ϖ.residueFamily e he.1.norm_le_one)) = ⊤ := by
  sorry

/-- A family of the unit ball whose reduction is linearly independent is orthonormal: scale a finite
combination by a power of `ϖ` so that the largest coefficient has norm `1`; the reduced combination
is then nonzero, so the combination has norm exactly `1`. Source: Bellaïche, Lemma II.1.12 ("if the
`ẽᵢ` are linearly independent, then `‖∑ aᵢ eᵢ‖ = sup ‖aᵢ‖`"); Schneider §10, Prop 10.1 ("we first
check that the norm of any finite linear combination of the vectors `v_x` satisfies
`‖a₁v_{x₁} + … + a_m v_{x_m}‖ = max(|a₁|, …, |a_m|)`"). -/
theorem isOrthonormalFamily_of_linearIndependent_residueFamily (he : ∀ i, ‖e i‖ ≤ 1)
    (hli : LinearIndependent ϖ.ResidueRing (ϖ.residueFamily e he)) : IsOrthonormalFamily R e := by
  sorry

/-- **Successive `ϖ`-adic approximation**: if the reduction of `e` spans `M̃`, every `m` is a
convergent sum `∑' aᵢ • eᵢ`. Source: roadmap §2.3.1 ("the successive `π`-adic approximation
`m = ∑ aᵢ eᵢ + π m₁`, iterated, with the coefficients converging by completeness of `R`");
Bellaïche, Lemma II.1.12; Colmez, Proposition 1.1.5. -/
theorem exists_hasSum_of_span_residueFamily_eq_top (he : ∀ i, ‖e i‖ ≤ 1)
    (hspan : Submodule.span ϖ.ResidueRing (Set.range (ϖ.residueFamily e he)) = ⊤) (m : M) :
    ∃ a : I → R, HasSum (fun i ↦ a i • e i) m := by
  sorry

/-- **Residue-basis lifting**, the "if" direction. Source: Bellaïche, Lemma II.1.12; roadmap
§2.3.1. -/
theorem isOrthonormalBasis_of_residueFamily (he : ∀ i, ‖e i‖ ≤ 1)
    (hli : LinearIndependent ϖ.ResidueRing (ϖ.residueFamily e he))
    (hspan : Submodule.span ϖ.ResidueRing (Set.range (ϖ.residueFamily e he)) = ⊤) :
    IsOrthonormalBasis R e := by
  sorry

/-- **Residue-basis lifting** (Bellaïche, Lemma II.1.12; Colmez, Proposition 1.1.5): a family of
the unit ball is an orthonormal basis if and only if its reduction is a basis of `M̃`. Source:
roadmap §2.3.1. -/
theorem isOrthonormalBasis_iff_residueFamily (he : ∀ i, ‖e i‖ ≤ 1) :
    IsOrthonormalBasis R e ↔ LinearIndependent ϖ.ResidueRing (ϖ.residueFamily e he) ∧
      Submodule.span ϖ.ResidueRing (Set.range (ϖ.residueFamily e he)) = ⊤ :=
  ⟨fun h ↦ ⟨ϖ.linearIndependent_residueFamily_of_isOrthonormalFamily hR hM h.1,
    ϖ.span_residueFamily_eq_top_of_isOrthonormalBasis hR hM h⟩,
    fun h ↦ ϖ.isOrthonormalBasis_of_residueFamily hR hM he h.1 h.2⟩

/-- **Serre's theorem, ring form**, "only if": an orthonormalisable module has a free residue
module. Source: roadmap §2.3.2 ("`M` is orthonormalisable if and only if `M̃` is a free
`R̃`-module"); Bellaïche, Theorem II.1.13. -/
theorem free_residueModule_of_isONable (h : IsONable R M) :
    Module.Free ϖ.ResidueRing (ϖ.ResidueModule M) := by
  sorry

/-- **Serre's theorem, ring form**, "if": lift a basis of the residue module. Source: roadmap
§2.3.2; Bellaïche, Theorem II.1.13 ("choose a basis `(ẽᵢ)` of `M̃` and lift it"). -/
theorem isONable_of_free_residueModule [Module.Free ϖ.ResidueRing (ϖ.ResidueModule M)] :
    IsONable R M := by
  sorry

/-- **Serre's theorem, ring form.** Source: roadmap §2.3.2. -/
theorem isONable_iff_free_residueModule :
    IsONable R M ↔ Module.Free ϖ.ResidueRing (ϖ.ResidueModule M) :=
  ⟨ϖ.free_residueModule_of_isONable hR hM, fun h ↦ by
    haveI := h
    exact ϖ.isONable_of_free_residueModule hR hM⟩

end Residue

section Potential

variable [CompleteSpace R] [CompleteSpace M]
  (hR : ∀ r : R, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : R)‖ ^ n)
include hR

/-- Every Banach `R`-module is potentially orthonormalisable when all `R̃`-modules are free: the
rescaled norm takes values in `‖ϖ‖ ^ ℤ`, and the rescaled module is orthonormalisable. Source:
roadmap §2.3.2 ("every Banach `R`-module is potentially orthonormalisable as soon as `R̃` has the
property that all its modules are free"); Bellaïche, Theorem II.1.13. -/
theorem isPotentiallyONable_of_forall_free
    (hfree : ∀ (N : Type v) [AddCommGroup N] [Module ϖ.ResidueRing N],
      Module.Free ϖ.ResidueRing N) : IsPotentiallyONable R M := by
  sorry

/-- Source: roadmap §2.3.2 ("in particular when `R̃` is a field"). -/
theorem isPotentiallyONable_of_isField_residueRing (hF : IsField ϖ.ResidueRing) :
    IsPotentiallyONable R M := by
  sorry

end Potential

end NormedRing.PseudoUniformizer

/-! ### Serre's theorem over a discretely valued field -/

section Field

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A discretely valued field has a pseudo-uniformiser whose norm generates the value group: a
uniformiser in the sense of `Valuation.IsUniformizer`. Source: roadmap §2.3.3 and convention 8;
Schneider, Lemma 1.4 ("`|K×| = r^ℤ` for some real number `0 < r < 1`"). -/
theorem NormedField.exists_pseudoUniformizer_forall_exists_norm_eq_zpow
    [Valuation.IsRankOneDiscrete (NormedField.valuation (K := K))] :
    ∃ ϖ : PseudoUniformizer K, ∀ r : K, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : K)‖ ^ n := by
  sorry

/-- The residue ring of a field at a uniformiser is a field: `ϖ.ideal` is the maximal ideal of the
valuation ring. Source: Schneider §10, Prop 10.1 ("Let `k := o/m` denote the residue class field
of `K`"); Layer 0, `NormedRing.maximalIdeal_unitClosedBall`. -/
theorem NormedRing.PseudoUniformizer.isField_residueRing (ϖ : PseudoUniformizer K)
    (hK : ∀ r : K, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : K)‖ ^ n) : IsField ϖ.ResidueRing := by
  sorry

variable {K} (M : Type v) [NormedAddCommGroup M] [NormedSpace K M] [IsUltrametricDist M]
  [CompleteSpace M] [Valuation.IsRankOneDiscrete (NormedField.valuation (K := K))]

/-- **Serre's theorem, field form**: every Banach space over a discretely valued nonarchimedean
field is potentially orthonormalisable. Source: roadmap §2.3.3; Serre, §1, Proposition 1;
Schneider, Proposition 10.1 ("every `K`-Banach space `V` is topologically isomorphic to a
`K`-Banach space `c₀(X)`"); Bellaïche, Theorem II.1.13. -/
theorem Module.isPotentiallyONable_of_isRankOneDiscrete : IsPotentiallyONable K M := by
  sorry

/-- **Serre's theorem, field form**, on the nose: a Banach space over a discretely valued field is
orthonormalisable if and only if its norm takes values in `‖K‖`. Source: roadmap §2.3.3 ("it is
orthonormalisable on the nose if and only if its norm takes values in `‖K‖`"); Schneider, Remark
10.2 ("every `K`-Banach space `(V, ‖‖)` such that `‖V‖ ⊆ |K|` is isometrically isomorphic to a
`K`-Banach space `(c₀(X), ‖‖_∞)`"). -/
theorem Module.isONable_iff_forall_exists_norm_eq : IsONable K M ↔ ∀ m : M, ∃ k : K, ‖m‖ = ‖k‖ := by
  sorry

end Field

/-! ### The index set is an invariant -/

namespace ZeroAtInftyContinuousMap

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {I J : Type w} [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J] [DiscreteTopology J]

/-- If `C₀(I, K) ≃L C₀(J, K)` with `I` finite then `J` is finite, since `C₀(J, K)` is then
finite-dimensional while the coordinate vectors are linearly independent. Source: Schneider,
Lemma 10.3 ("If one of the sets is finite then already for algebraic reasons the other set has to
be finite of the same cardinality"). -/
theorem finite_of_continuousLinearEquiv [Finite I] (e : C₀(I, K) ≃L[K] C₀(J, K)) : Finite J := by
  sorry

/-- If `C₀(I, K) ≃L C₀(J, K)` with `I` infinite then `|J| ≤ |I|`: every `j` lies in the countable
support of some `e (single i 1)`, since otherwise the image of `e` would lie in the closed
subspace of functions vanishing at `j`. Source: Schneider, Lemma 10.3 ("It follows that
`|Y| ≤ |⋃_{x ∈ X} Y_x| ≤ |ℕ| · |X| = |X|`"). -/
theorem cardinal_mk_le_of_continuousLinearEquiv [Infinite I] (e : C₀(I, K) ≃L[K] C₀(J, K)) :
    Cardinal.mk J ≤ Cardinal.mk I := by
  sorry

/-- **The index set is an invariant.** Source: roadmap §2.3.4; Schneider, Lemma 10.3 ("the
`K`-Banach spaces `c₀(X)` and `c₀(Y)` are topologically isomorphic if and only if the sets `X` and
`Y` have the same cardinality"). -/
theorem nonempty_equiv_of_continuousLinearEquiv (e : C₀(I, K) ≃L[K] C₀(J, K)) :
    Nonempty (I ≃ J) := by
  sorry

/-- Source: roadmap §2.3.4; Schneider, Lemma 10.3. -/
theorem nonempty_continuousLinearEquiv_iff :
    Nonempty (C₀(I, K) ≃L[K] C₀(J, K)) ↔ Nonempty (I ≃ J) :=
  ⟨fun ⟨e⟩ ↦ nonempty_equiv_of_continuousLinearEquiv e,
    fun ⟨σ⟩ ↦ ⟨(reindex (R := K) σ).toContinuousLinearEquiv⟩⟩

end ZeroAtInftyContinuousMap
