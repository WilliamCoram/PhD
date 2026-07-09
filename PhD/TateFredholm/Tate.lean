import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.Floor.Defs

/-!
# Compact operators and Fredholm determinants over Banach–Tate rings — the merged setting

The most general of this project's compact-operator developments, subsuming the three
blueprint files in `PhD/Test/`:

* `PhD.Test.CompactOperators` — Buzzard's *Eigenvarieties*: Banach algebra `A` over a
  nontrivially normed field `K` (Noetherian in the paper; dropped in our file);
* `PhD.Test.CompactOperatorsBellaiche` — Bellaïche's *Eigenbook* §3.1: Banach
  `ℚ_p`-algebra, **no Noetherian hypothesis**, proofs by coordinate truncation;
* `PhD.Test.CompactOperatorsJohanssonNewton` — [JN] §2.1: **Banach–Tate ring, no ground
  field**, Noetherian (inherited from Buzzard's proofs).

The three sources are maximal along two independent axes — base ring (field-algebra vs
Tate ring) and finiteness (Noetherian or not) — and the two improvements are orthogonal
and compatible.  This development records their common refinement:

> **Hypotheses**: a commutative nonarchimedean Banach–Tate ring `R` (`[IsTate R]`: there
> is a multiplicative pseudo-uniformizer `ϖ ∈ R^×`, `‖ϖ‖ < 1`) — no ground field, and
> **no Noetherian hypothesis** anywhere except the single isolated statement
> `finite_projective_of_one_sub_compact_nilpotent`.
>
> **Proof architecture**: Bellaïche's — coordinate truncations `π_S`, the quantitative
> Open Mapping Theorem, the Lipschitz bound for the determinant's coefficients, and the
> trace property `det(1 − Tφu) = det(1 − Tuφ)` as the primitive invariance statement.
> Every use Bellaïche makes of the ground field `ℚ_p` is a scaling argument, and the
> pseudo-uniformizer performs it verbatim ("Buzzard's `ρ`-trick with `ϖ` for `ρ`", as
> [JN] put it).

## Module map

* `Tate.lean` (this file) — the index type, Banach–Tate rings, the bridge from Banach
  algebras over fields
* `OperatorNorm.lean` — the operator norm on `Hom_R(M, N)`, boundedness, completeness,
  the Open Mapping Theorem
* `Compact.lean` — finite-rank and completely continuous operators
* `ModelSpace.lean` — the model space `c(I, R)`, ON-able / potentially ON-able / (Pr)
* `Matrix.lean` — matrix coefficients, truncations, the compactness criterion
* `Fredholm.lean` — the Fredholm determinant `det(1 − Tu)` and its invariances
* `Pr.lean` — the lifting property, projectivity, the one Noetherian statement
* `Residue.lean` — residue machinery for Serre's theorem
* `BaseChange.lean` — norm comparison, equivalent-norm invariance, bounded base change,
  and the classical (field) specialisations

## How the three blueprints are recovered

* **Buzzard / Bellaïche files**: the bridge lemma `isTate_of_normedAlgebra` (proved below,
  not sorried) shows every norm-unital Banach algebra over a nontrivially normed field is
  Banach–Tate, with `ϖ = λ·1` for any scalar `0 < ‖λ‖ < 1`.  Instantiating this
  development's statements along the bridge yields the field-based statements (up to the
  definitional equivalences: we define ON-able by isometry to the model space, as [JN]
  do; the `ONBasis`-structure formulation and its equivalence `isONable_iff` live in the
  Bellaïche file).
* **[JN] file**: every statement of `CompactOperatorsJohanssonNewton` reappears here with
  its `[IsNoetherianRing R]` hypothesis **deleted** — a strict improvement over the
  published statements of [JN, §2.1], licensed by Bellaïche's Noetherian-free proofs.
  [JN] describe a Banach–Tate ring as exactly a Banach algebra with `|A^m| ≠ 1` in
  Coleman's sense, so this merged setting is, in a slogan, *Coleman minus Noetherian*.

Three statements resist the merge and are recorded accordingly:
* Serre's theorem (every Banach space over a *discretely valued field* is potentially
  ON-able) is intrinsically a field statement — kept in the "classical specialisations"
  section of `BaseChange.lean`, phrased over a field via the bridge, with its residue
  machinery in `Residue.lean`;
* Bellaïche's Proposition II.1.21 (compact `u`, `1 − u` nilpotent ⟹ finite projective)
  genuinely needs `[IsNoetherianRing R]` and keeps it, isolated;
* [JN]'s norm-comparison Lemmas 2.1.6–2.1.7 are Tate-specific and hold here as stated —
  they never made sense in the field-only files.

## References

As in the three parent files: [Bel] Bellaïche, *The Eigenbook*, §3.1 (draft §II.1);
[JN] Johansson–Newton, *Extended eigenvarieties for overconvergent cohomology*,
arXiv:1604.07739v4, §2.1; [Buzzard] *Eigenvarieties*, §2; [Serre] IHÉS 12 (1962);
[Col97] Coleman; [Hub94] Huber (open mapping theorem for Tate rings); [Som] the Essen
seminar programme.  Citations give the statement's *origin*; the hypotheses here are the
merged ones.

## Dictionary (merged Lean name ↔ sources)

| Lean                                     | [Bel]        | [JN]        | blueprint |
| ---------------------------------------- | ------------ | ----------- | --------- |
| `IsMultiplicative`, `PseudoUniformizer`, `IsTate` | —    | Def 2.1.1–2 | —         |
| `isTate_of_normedAlgebra` (the bridge)   | —            | —           | —         |
| `PseudoUniformizer.val`                  | —            | Def 2.1.2   | ch. 5     |
| `instNorm`, `le_opNorm`, `norm_add_le`   | II.1.1       | Def 2.1.4   | 6.8–6.10  |
| `exists_preimage_norm_le` (OMT)          | II.1.1       | Def 2.1.4   | —         |
| `IsFiniteRank`, `IsCompletelyContinuous` | Def II.1.3   | Def 2.1.5   | 6.13      |
| `IsFiniteRank/IsCompletelyContinuous.comp_left/right` | Lem II.1.4 | — | —     |
| `cSpace` (`c(I, R)`), `single`           | Ex II.1.7    | Def 2.1.5   | 6.3–6.5   |
| `IsONable`, `IsPotentiallyONable`, `HasPr` | Def II.1.5–6, §II.1.6 | Def 2.1.5 | 6.6 |
| `matrixCoeff`, `norm_eq_iSup_matrixCoeff`, `exists_coeffEquiv` | §II.1.3 | p.65 | 6.11 |
| `truncation`, `exists_truncation_near`   | Lem II.1.8   | —           | —         |
| `isCompletelyContinuous_iff_rowNorm` (**no Noetherian**) | Prop II.1.9 | Def 2.1.5 | 6.14 |
| `tendsto_truncation_comp`                | Schol II.1.10| —           | —         |
| `minor`, `summable_minor`, `charCoeff`, `charPowerSeries` | §II.1.5 | p.67 recipe | 6.16–6.17 |
| `IsEntire`, `charPowerSeries_isEntire`   | Lem II.1.14  | `R{{T}}`    | 6.16(2)   |
| `norm_charCoeff_sub_le` (quantitative)   | Lem II.1.15  | —           | 6.16(3)   |
| `charCoeff_eq_det_coeff`                 | (II.1.2)     | —           | —         |
| `charPowerSeries_comm` (trace property)  | Prop II.1.17 | —           | —         |
| `charPowerSeries_conj`, `_extendZero`    | Cor II.1.18  | 2.5/2.6, pp.72–73 | —  |
| `HasPr.exists_lift`, `HasPr.projective`  | Ex II.1.19, Prop II.1.20 | — | —      |
| `finite_projective_of_one_sub_compact_nilpotent` (**Noetherian**) | Prop II.1.21 | — | — |
| `norm_le_pow_of_equiv`, `norm_comparison_of_common_uniformizer` | — | Lem 2.1.6–7 | — |
| `isCompletelyContinuous_map_equiv`, `charPowerSeries_map_equiv` | — | Prop 2.1.8 | — |
| `charCoeff_baseChange` etc. (bounded `ψ`)| Lem II.1.23 (matrix-wise) | Buz 2.9/2.10 | — |
| `isPotentiallyONable_of_uniformizer` (field case) | Thm II.1.13 | — | 6.7 |

## TODO

Riesz theory and slope factorizations/decompositions ([Bel] §II.2, [JN] §2.2) in this
merged setting — the convergence point of all three parent blueprints and the natural
consumer of this project's `NewtonPolygon` and `DivValueGroup` work; completed tensor
products and the `⊗̂`-form of base change; spectral varieties ([JN] §2.3).
-/

open Filter Topology

-- Blueprint development: hypotheses are stated at final generality even where a
-- particular `sorry`ed statement does not yet use them.
set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

/-! ## The index type -/

/-- `Ix I` is `I` regarded as a discrete topological space (the index set of an orthonormal
basis). -/
def Ix (I : Type*) : Type _ := I

instance {I : Type*} : TopologicalSpace (Ix I) := ⊥
instance {I : Type*} : DiscreteTopology (Ix I) := ⟨rfl⟩
instance {I : Type*} [DecidableEq I] : DecidableEq (Ix I) := inferInstanceAs (DecidableEq I)

/-! ## Banach–Tate rings and the bridge from Banach algebras
([JN] Definitions 2.1.1–2.1.2) -/

section Tate

variable {A : Type*} [NormedRing A]

/-- An element `a` of a normed ring is *multiplicative* if `‖ax‖ = ‖a‖‖x‖` for all `x`
([JN] Definition 2.1.1). -/
def IsMultiplicative (a : A) : Prop :=
  ∀ x : A, ‖a * x‖ = ‖a‖ * ‖x‖

/-- A *multiplicative pseudo-uniformizer*: a multiplicative unit `ϖ` with `‖ϖ‖ < 1`
([JN] Definition 2.1.2).  The scaling element that replaces the ground field of the
Buzzard/Bellaïche settings. -/
structure PseudoUniformizer (A : Type*) [NormedRing A] where
  /-- the underlying unit -/
  unit : Aˣ
  /-- topological nilpotence: `‖ϖ‖ < 1` -/
  norm_lt_one : ‖(unit : A)‖ < 1
  /-- multiplicativity: `‖ϖ x‖ = ‖ϖ‖ ‖x‖` -/
  isMultiplicative : IsMultiplicative (unit : A)

instance : CoeHead (PseudoUniformizer A) A := ⟨fun ϖ => ϖ.unit⟩

/-- The coercion of a pseudo-uniformizer is its underlying unit. -/
@[simp] theorem PseudoUniformizer.coe_eq (ϖ : PseudoUniformizer A) :
    (ϖ : A) = ϖ.unit := rfl

/-- A pseudo-uniformizer has positive norm.  (`[Nontrivial A]` is necessary: in the
trivial ring the unit `0 = 1` is a pseudo-uniformizer of norm `0`; [JN]'s Def 2.1.1
bakes nontriviality in via the axiom `‖1‖ = 1`.) -/
theorem PseudoUniformizer.norm_pos [Nontrivial A] (ϖ : PseudoUniformizer A) :
    0 < ‖(ϖ : A)‖ := by
  rw [PseudoUniformizer.coe_eq, norm_pos_iff]
  intro h
  apply one_ne_zero (α := A)
  calc (1 : A) = ↑ϖ.unit⁻¹ * ↑ϖ.unit := ϖ.unit.inv_mul.symm
  _ = ↑ϖ.unit⁻¹ * 0 := by rw [h]
  _ = 0 := mul_zero _

/-- The norm of the inverse of a pseudo-uniformizer: `‖ϖ⁻¹‖ = ‖ϖ‖⁻¹` ([JN], remark
after Definition 2.1.2 — the characterisation of multiplicative units). -/
theorem PseudoUniformizer.norm_inv [NormOneClass A] (ϖ : PseudoUniformizer A) :
    ‖((ϖ.unit⁻¹ : Aˣ) : A)‖ = ‖(ϖ : A)‖⁻¹ := by
  rw [PseudoUniformizer.coe_eq]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← ϖ.isMultiplicative ((ϖ.unit⁻¹ : Aˣ) : A), Units.mul_inv, norm_one]

/-- **[JN] Definition 2.1.2.**  A normed ring is *Tate* if it admits a multiplicative
pseudo-uniformizer; complete + Tate = *Banach–Tate*.  The standing hypothesis of this
development, replacing `[NormedAlgebra K R]` of the field-based blueprints. -/
class IsTate (A : Type*) [NormedRing A] : Prop where
  nonempty_pseudoUniformizer : Nonempty (PseudoUniformizer A)

/-- The additive valuation `v_ϖ(r) = −log_a ‖r‖`, `a = ‖ϖ‖⁻¹`, normalised so
`v_ϖ(ϖ) = 1` ([JN] Definition 2.1.2) — the bridge to Newton polygons and slopes. -/
def PseudoUniformizer.val (ϖ : PseudoUniformizer A) (r : A) : ℝ :=
  -(Real.log ‖r‖ / Real.log ‖(ϖ : A)‖⁻¹)

/-- The valuation is normalised so that `v_ϖ(ϖ) = 1`. -/
@[simp] theorem PseudoUniformizer.val_self [Nontrivial A] (ϖ : PseudoUniformizer A) :
    ϖ.val (ϖ : A) = 1 := by
  have hlog : Real.log ‖(ϖ : A)‖ < 0 :=
    Real.log_neg ϖ.norm_pos (by rw [PseudoUniformizer.coe_eq]; exact ϖ.norm_lt_one)
  show -(Real.log ‖(ϖ : A)‖ / Real.log ‖(ϖ : A)‖⁻¹) = 1
  rw [Real.log_inv, div_neg, div_self hlog.ne, neg_neg]

end Tate

/-- **The bridge lemma.**  Every norm-unital Banach algebra over a nontrivially normed
field is Tate: `ϖ = λ·1` for any scalar `0 < ‖λ‖ < 1` is a multiplicative
pseudo-uniformizer.  This is what makes the present development subsume the Buzzard and
Bellaïche blueprints: instantiate their `(K, A)` here via this instance-producing lemma
and specialise. -/
theorem isTate_of_normedAlgebra (K : Type*) [NontriviallyNormedField K]
    (A : Type*) [NormedRing A] [NormedAlgebra K A] [NormOneClass A] : IsTate A := by
  obtain ⟨lam, hlam0, hlam1⟩ := NormedField.exists_norm_lt_one K
  have hlamne : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlam0
    exact lt_irrefl _ hlam0
  have hnorm : ∀ x : A, ‖algebraMap K A lam * x‖ = ‖lam‖ * ‖x‖ := fun x => by
    rw [← Algebra.smul_def, norm_smul]
  have h1 : ‖algebraMap K A lam‖ = ‖lam‖ := by
    simpa using hnorm 1
  refine ⟨⟨⟨⟨algebraMap K A lam, algebraMap K A lam⁻¹, ?_, ?_⟩, ?_, ?_⟩⟩⟩
  · rw [← map_mul, mul_inv_cancel₀ hlamne, map_one]
  · rw [← map_mul, inv_mul_cancel₀ hlamne, map_one]
  · show ‖algebraMap K A lam‖ < 1
    rw [h1]; exact hlam1
  · intro x
    show ‖algebraMap K A lam * x‖ = ‖algebraMap K A lam‖ * ‖x‖
    rw [hnorm x, h1]

end TateFredholm

end
