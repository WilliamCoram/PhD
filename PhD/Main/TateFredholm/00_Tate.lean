/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.Analysis.Normed.Ring.NegLogNorm
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Compact operators and Fredholm determinants over Banach–Tate rings — the merged setting

The most general of this project's compact-operator developments, subsuming the three
blueprint files in `PhD/Main/Test/`:

* `PhD.Main.Test.CompactOperators` — Buzzard's *Eigenvarieties*: Banach algebra `A` over a
  nontrivially normed field `K` (Noetherian in the paper; dropped in our file);
* `PhD.Main.Test.CompactOperatorsBellaiche` — Bellaïche's *Eigenbook* §3.1: Banach
  `ℚ_p`-algebra, **no Noetherian hypothesis**, proofs by coordinate truncation;
* `PhD.Main.Test.CompactOperatorsJohanssonNewton` — [JN] §2.1: **Banach–Tate ring, no ground
  field**, Noetherian (inherited from Buzzard's proofs).

The three sources are maximal along two independent axes — base ring (field-algebra vs
Tate ring) and finiteness (Noetherian or not) — and the two improvements are orthogonal
and compatible.  This development records their common refinement:

> **Hypotheses**: a commutative nonarchimedean Banach–Tate ring `R` (`[IsTate R]`: there
> is a multiplicative pseudo-uniformizer `ϖ ∈ R^×`, `‖ϖ‖ < 1`) — no ground field, and
> **no Noetherian hypothesis** anywhere except `05_Noetherian.lean` (the closedness of
> finitely generated submodules, the bridge `IsCompletelyContinuous.isCompactoid`, and
> the recovered criterion `isCompletelyContinuous_iff_rowNorm`).  The determinant theory
> itself runs on `IsCompactoid` (cofinite row decay) and is Noetherian-free, and so is
> [Bel] Proposition II.1.21 (`finite_projective_of_one_sub_compact_nilpotent`), whose proof
> only ever used the Neumann inverse.
>
> **Proof architecture**: Bellaïche's — coordinate truncations `π_S`, the quantitative
> Open Mapping Theorem, the Lipschitz bound for the determinant's coefficients, and the
> trace property `det(1 − Tφu) = det(1 − Tuφ)` as the primitive invariance statement.
> Every use Bellaïche makes of the ground field `ℚ_p` is a scaling argument, and the
> pseudo-uniformizer performs it verbatim ("Buzzard's `ρ`-trick with `ϖ` for `ρ`", as
> [JN] put it).

## Module map

* `00_Tate.lean` (this file) — the index type, Banach–Tate rings, the bridge from Banach
  algebras over fields
* `01_OperatorNorm.lean` — the operator norm on `Hom_R(M, N)`, boundedness, completeness,
  the Open Mapping Theorem
* `02_Compact.lean` — finite-rank and completely continuous operators
* `03_ModelSpace.lean` — the model space `c(I, R)`, ON-able / potentially ON-able / (Pr)
* `04_Matrix.lean` — matrix coefficients, truncations, the compactness criterion
* `05_Fredholm.lean` — the Fredholm determinant `det(1 − Tu)` and its invariances
* `06_Pr.lean` — the lifting property, projectivity, [Bel] Proposition II.1.21 (Noetherian-free)
* `10_Entire.lean` — entire power series, Euclidean division by a polynomial with unit leading
  coefficient, `IsEntireCoprime`, good zeros
* `00_Resultant.lean` — `Res(charpoly A, g) = det g(A)`
* `11_Coleman.lean` — Coleman's `D(B, P)` and the spectral mapping `det(1 − T·B(u))`
* `00_Charpoly.lean` — `charpolyRev` under base change; Sylvester; unipotent matrices over a field
* `12_RieszColeman.lean` — [JN] Theorem 2.2.2: the Riesz–Coleman decomposition for a coprime
  factorisation `det(1 − Tu) = QS`
* `11_SlopeFactor.lean` — the vertex (slope) factorisation of an entire series ([Bel] II.3.6)
* `07_Residue.lean` — residue machinery for Serre's theorem
* `08_BaseChange.lean` — norm comparison, equivalent-norm invariance, bounded base change,
  and the classical (field) specialisations
* `05_Noetherian.lean` — closedness of finitely generated submodules over Noetherian bases
  ([FvdP] 1.2.3, [Buz07] Lemma 2.3) and the bridge from `IsCompletelyContinuous` to
  `IsCompactoid`
* `01_AddVal.lean` — the seam between `v_ϖ` and `ForMathlib`'s additive-valuation API: over an
  ultrametric normed field the two agree up to the normalisation `-log ‖ϖ‖`

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
  section of `08_BaseChange.lean`, phrased over a field via the bridge, with its residue
  machinery in `07_Residue.lean`;
* Bellaïche's Proposition II.1.21 (compact `u`, `1 − u` nilpotent ⟹ finite projective) was
  proved Noetherian-free in 2026-09-06 (`06_Pr.lean`, `finite_of_one_sub_compact_nilpotent`);
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
| `negLogNorm` (`ForMathlib`)              | —            | —           | —         |
| `PseudoUniformizer.val` (`WithTop ℝ`, `v_ϖ`) | —        | Def 2.1.2   | ch. 5     |
| `PseudoUniformizer.val_eq_map_normAddVal` (`01_AddVal.lean`) | — | —      | —         |
| `instNorm`, `le_opNorm`, `norm_add_le`   | II.1.1       | Def 2.1.4   | 6.8–6.10  |
| `exists_preimage_norm_le` (OMT)          | II.1.1       | Def 2.1.4   | —         |
| `IsFiniteRank`, `IsCompletelyContinuous` | Def II.1.3   | Def 2.1.5   | 6.13      |
| `IsFiniteRank/IsCompletelyContinuous.comp_left/right` | Lem II.1.4 | — | —     |
| `cSpace` (`c(I, R)`), `single`           | Ex II.1.7    | Def 2.1.5   | 6.3–6.5   |
| `IsONable`, `IsPotentiallyONable`, `HasPr` | Def II.1.5–6, §II.1.6 | Def 2.1.5 | 6.6 |
| `matrixCoeff`, `norm_eq_iSup_matrixCoeff`, `exists_coeffEquiv` | §II.1.3 | p.65 | 6.11 |
| `truncation`, `exists_truncation_near` (+ `IsClosed` = Hyp 3.1.8) | Lem 3.1.12 / II.1.8 | — | — |
| `IsCompactoid` (row decay; the working notion, **no Noetherian**) | — | §2.2 usage | 6.14 |
| `IsCompactoid.isCompletelyContinuous` (**no Noetherian**) | Prop II.1.9 ⇐ | — | — |
| `IsCompletelyContinuous.isCompactoid`, `isCompletelyContinuous_iff_rowNorm` (**Noetherian**, `05_Noetherian.lean`) | Prop II.1.9 ⇒ | Def 2.1.5 | 6.14 |
| `tendsto_truncation_comp`, `IsCompactoid.comp_left/right` | Schol II.1.10, Lem II.1.4 | — | — |
| `isClosed_of_finite`, `isClosed_of_fg` (`05_Noetherian.lean`) | — | p. 7 remark | — |
| `minor`, `summable_minor`, `charCoeff`, `charPowerSeries` | §II.1.5 | p.67 recipe | 6.16–6.17 |
| `charPowerSeries_isEntire` (`PowerSeries.IsRestricted` at every radius) | Lem II.1.14 | `R{{T}}` | 6.16(2) |
| `norm_charCoeff_sub_le` (quantitative)   | Lem II.1.15  | —           | 6.16(3)   |
| `charCoeff_eq_det_coeff`                 | (II.1.2)     | —           | —         |
| `charPowerSeries_comm` (trace property)  | Prop II.1.17 | —           | —         |
| `charPowerSeries_conj`, `_extendZero`    | Cor II.1.18  | 2.5/2.6, pp.72–73 | —  |
| `HasPr.exists_lift`, `HasPr.projective`  | Ex II.1.19, Prop II.1.20 | — | —      |
| `finite_projective_of_one_sub_compact_nilpotent` (Noetherian-free) | Prop II.1.21 | — | — |
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

noncomputable section

namespace TateFredholm

/-- A copy of `I` equipped with the discrete topology (the index set of an orthonormal basis). -/
def Ix (I : Type*) := I

instance {I : Type*} : TopologicalSpace (Ix I) := ⊥
instance {I : Type*} : DiscreteTopology (Ix I) := ⟨rfl⟩
instance {I : Type*} [h : DecidableEq I] : DecidableEq (Ix I) := h

section Tate

/-- An element `a` is *multiplicative* if `‖ax‖ = ‖a‖‖x‖` for all `x` — the single-element
form of `NormMulClass` ([JN] Definition 2.1.1). -/
def IsMultiplicative {A : Type*} [Norm A] [Mul A] (a : A) : Prop := ∀ x : A, ‖a * x‖ = ‖a‖ * ‖x‖

/-- Products of multiplicative elements are multiplicative. -/
theorem IsMultiplicative.mul {A : Type*} [Norm A] [Semigroup A] {a b : A}
    (ha : IsMultiplicative a) (hb : IsMultiplicative b) : IsMultiplicative (a * b) := fun x ↦ by
  rw [mul_assoc, ha, hb, ha, mul_assoc]

/-- Powers of a multiplicative element scale norms by the corresponding power. -/
theorem IsMultiplicative.norm_pow_mul {A : Type*} [Norm A] [Monoid A] {a : A}
    (ha : IsMultiplicative a) (n : ℕ) (x : A) : ‖a ^ n * x‖ = ‖a‖ ^ n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ha, ih, pow_succ', mul_assoc]

/-- Powers of a multiplicative element are multiplicative. -/
theorem IsMultiplicative.pow {A : Type*} [SeminormedRing A] [NormOneClass A] {a : A}
    (ha : IsMultiplicative a) (n : ℕ) : IsMultiplicative (a ^ n) := fun x ↦ by
  have h1 : ‖a ^ n‖ = ‖a‖ ^ n := by simpa using ha.norm_pow_mul n 1
  rw [ha.norm_pow_mul n x, h1]

variable {A : Type*} [NormedRing A]

/-- A *multiplicative pseudo-uniformizer*: a multiplicative unit `ϖ` with `‖ϖ‖ < 1`
([JN] Definition 2.1.2).  The scaling element that replaces the ground field of the
Buzzard/Bellaïche settings. -/
structure PseudoUniformizer (A : Type*) [Norm A] [Monoid A] where
  /-- the underlying unit -/
  unit : Aˣ
  /-- topological nilpotence: `‖ϖ‖ < 1` -/
  norm_lt_one : ‖(unit : A)‖ < 1
  /-- multiplicativity: `‖ϖ x‖ = ‖ϖ‖ ‖x‖` -/
  isMultiplicative : IsMultiplicative (unit : A)

omit [NormedRing A] in
instance [Norm A] [Monoid A] : CoeHead (PseudoUniformizer A) A := ⟨fun ϖ ↦ ϖ.unit⟩

omit [NormedRing A] in
/-- The coercion of a pseudo-uniformizer is its underlying unit. -/
@[simp] theorem PseudoUniformizer.coe_eq [Norm A] [Monoid A] (ϖ : PseudoUniformizer A) :
    (ϖ : A) = ϖ.unit := rfl

/-- A pseudo-uniformizer has positive norm.  (`[Nontrivial A]` is necessary: in the
trivial ring the unit `0 = 1` is a pseudo-uniformizer of norm `0`; [JN]'s Def 2.1.1
bakes nontriviality in via the axiom `‖1‖ = 1`.) -/
theorem PseudoUniformizer.norm_pos [Nontrivial A] (ϖ : PseudoUniformizer A) : 0 < ‖(ϖ : A)‖ :=
  ϖ.unit.norm_pos

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

/-- In a normed division ring every nonzero element of norm `< 1` is a pseudo-uniformizer:
`Units.mk0` supplies the unit and multiplicativity of the norm is automatic.

Reach for this whenever the scaling element is a *specific* element of the field rather than
an abstract parameter.  It turns the pseudo-uniformizer from a hypothesis into a definition,
so the normalisation of `PseudoUniformizer.val` is a choice made once instead of a
`(ϖ : PseudoUniformizer K) (hϖ : (ϖ : K) = …)` pair threaded through every statement. -/
def PseudoUniformizer.ofNormLtOne {K : Type*} [NormedDivisionRing K] {x : K} (hx : x ≠ 0)
    (h : ‖x‖ < 1) : PseudoUniformizer K where
  unit := Units.mk0 x hx
  norm_lt_one := h
  isMultiplicative _ := norm_mul _ _

@[simp] theorem PseudoUniformizer.coe_ofNormLtOne {K : Type*} [NormedDivisionRing K] {x : K}
    (hx : x ≠ 0) (h : ‖x‖ < 1) :
    ((PseudoUniformizer.ofNormLtOne hx h : PseudoUniformizer K) : K) = x := rfl

/-- Every nontrivially normed field is Tate: an element of norm in `(0, 1)` is a unit, and
multiplicativity of the field norm makes it a pseudo-uniformizer.  This is the instance
that exhibits the Banach–Tate results as generalisations of their Mathlib counterparts —
see `TateFredholm.exists_preimage_norm_le`. -/
instance (K : Type*) [NontriviallyNormedField K] : IsTate K :=
  let ⟨x, hx_pos, hx_lt⟩ := NormedField.exists_norm_lt_one K
  ⟨⟨PseudoUniformizer.ofNormLtOne (by simpa using hx_pos.ne') hx_lt⟩⟩

/-- The logarithm of `‖ϖ‖` is negative — the normalising constant of `PseudoUniformizer.val`. -/
theorem PseudoUniformizer.log_norm_neg [Nontrivial A] (ϖ : PseudoUniformizer A) :
    Real.log ‖(ϖ : A)‖ < 0 :=
  Real.log_neg ϖ.norm_pos (by rw [PseudoUniformizer.coe_eq]; exact ϖ.norm_lt_one)

/-- The additive valuation `v_ϖ(r) = −log_a ‖r‖`, `a = ‖ϖ‖⁻¹`, normalised so `v_ϖ(ϖ) = 1`
([JN] Definition 2.1.2) — the bridge to Newton polygons and slopes.

Valued in `WithTop ℝ = ℝ ∪ {∞}` with `∞` at `0`.  Both halves of that matter: it is the shape
`ForMathlib.NumberTheory.NewtonPolygon` consumes (`v : ℕ → WithTop Γ`), and the `∞` is what
makes a vanishing coefficient drop out of the lower convex hull instead of sitting at height
`0` — the generic situation for `charPowerSeries` of a finite-rank operator.

**This is not an `AddValuation`.**  The norm of a Banach–Tate ring is only submultiplicative,
so `v_ϖ` is only *super*additive on products (`val_mul_le`), with equality exactly under
`[NormMulClass A]` (`val_mul`).  Over an ultrametric normed field it is
`NormedField.normAddVal` rescaled by `-log ‖ϖ‖`; see `PhD/Main/TateFredholm/01_AddVal.lean`. -/
def PseudoUniformizer.val (ϖ : PseudoUniformizer A) (r : A) : WithTop ℝ :=
  (AddMonoidHom.mulRight (-Real.log ‖(ϖ : A)‖)⁻¹).withTopMap (negLogNorm r)

namespace PseudoUniformizer

variable (ϖ : PseudoUniformizer A) {r s : A}

theorem val_def (r : A) :
    ϖ.val r = WithTop.map (· * (-Real.log ‖(ϖ : A)‖)⁻¹) (negLogNorm r) := rfl

theorem val_strictMono [Nontrivial A] :
    StrictMono (WithTop.map (· * (-Real.log ‖(ϖ : A)‖)⁻¹)) :=
  StrictMono.withTop_map fun _ _ h ↦
    mul_lt_mul_of_pos_right h (inv_pos.mpr (neg_pos.mpr ϖ.log_norm_neg))

theorem val_monotone [Nontrivial A] :
    Monotone (WithTop.map (· * (-Real.log ‖(ϖ : A)‖)⁻¹)) :=
  ϖ.val_strictMono.monotone

@[simp] theorem val_zero : ϖ.val 0 = ⊤ := by rw [val_def, negLogNorm_zero, WithTop.map_top]

theorem val_of_ne_zero (h : r ≠ 0) :
    ϖ.val r = ((Real.log ‖r‖ / Real.log ‖(ϖ : A)‖ : ℝ) : WithTop ℝ) := by
  rw [val_def, negLogNorm_of_ne_zero h, WithTop.map_coe]
  rw [show ∀ a b : ℝ, -a * (-b)⁻¹ = a / b from fun a b ↦ by
    rw [← neg_inv, neg_mul_neg, div_eq_mul_inv]]

@[simp] theorem val_eq_top : ϖ.val r = ⊤ ↔ r = 0 := by
  rcases eq_or_ne r 0 with rfl | h
  · simp
  · simp [val_of_ne_zero ϖ h, h]

theorem val_ne_top (h : r ≠ 0) : ϖ.val r ≠ ⊤ := by simpa using h

/-- **The normalisation**: `v_ϖ(ϖ) = 1`. -/
@[simp] theorem val_self [Nontrivial A] : ϖ.val (ϖ : A) = 1 := by
  rw [val_of_ne_zero ϖ (norm_ne_zero_iff.mp ϖ.norm_pos.ne'), div_self ϖ.log_norm_neg.ne,
    WithTop.coe_one]

@[simp] theorem val_one [NormOneClass A] : ϖ.val (1 : A) = 0 := by
  rw [val, negLogNorm_one A, map_zero]

/-- **The order reversal.**  Larger norm means smaller valuation; valid at `0` with no side
condition.  The workhorse of every slope comparison. -/
theorem val_le_val_iff [Nontrivial A] : ϖ.val r ≤ ϖ.val s ↔ ‖s‖ ≤ ‖r‖ := by
  rw [val_def, val_def, ϖ.val_strictMono.le_iff_le, negLogNorm_le_negLogNorm]

theorem val_lt_val_iff [Nontrivial A] : ϖ.val r < ϖ.val s ↔ ‖s‖ < ‖r‖ :=
  lt_iff_lt_of_le_iff_le ϖ.val_le_val_iff

/-- **Submultiplicativity, additively.**  Only an inequality; see `val_mul`. -/
theorem val_mul_le [Nontrivial A] (r s : A) : ϖ.val r + ϖ.val s ≤ ϖ.val (r * s) := by
  rw [val, val, val, ← map_add]
  exact ϖ.val_monotone add_negLogNorm_le_negLogNorm_mul

/-- When the norm is multiplicative, `v_ϖ` is an honest additive valuation. -/
theorem val_mul [NormMulClass A] (r s : A) : ϖ.val (r * s) = ϖ.val r + ϖ.val s := by
  rw [val, val, val, negLogNorm_mul, map_add]

/-- **The ultrametric bound.** -/
theorem le_val_add [IsUltrametricDist A] [Nontrivial A] (r s : A) :
    min (ϖ.val r) (ϖ.val s) ≤ ϖ.val (r + s) := by
  rw [val_def, val_def, val_def, ← ϖ.val_monotone.map_min]
  exact ϖ.val_monotone le_negLogNorm_add

/-- The valuation is nonnegative exactly on the elements of norm at most one. -/
theorem val_nonneg_iff [NormOneClass A] [Nontrivial A] : 0 ≤ ϖ.val r ↔ ‖r‖ ≤ 1 := by
  rw [← ϖ.val_one, ϖ.val_le_val_iff, norm_one]

/-- Inverse scaling: `‖ϖ⁻¹ r‖ = ‖ϖ‖⁻¹‖r‖`. -/
theorem norm_inv_mul [NormOneClass A] [Nontrivial A] (r : A) :
    ‖((ϖ.unit⁻¹ : Aˣ) : A) * r‖ = ‖(ϖ : A)‖⁻¹ * ‖r‖ := by
  have h := ϖ.isMultiplicative (((ϖ.unit⁻¹ : Aˣ) : A) * r)
  rw [← mul_assoc, PseudoUniformizer.coe_eq, Units.mul_inv, one_mul] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ ϖ.norm_pos.ne', one_mul]

/-- Integer powers of `ϖ` scale the norm exactly: `‖ϖⁿ‖ = ‖ϖ‖ⁿ`. -/
theorem norm_zpow [NormOneClass A] [Nontrivial A] (n : ℤ) :
    ‖((ϖ.unit ^ n : Aˣ) : A)‖ = ‖(ϖ : A)‖ ^ n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      rw [add_comm (k : ℤ) 1, zpow_one_add, Units.val_mul, ← PseudoUniformizer.coe_eq,
        ϖ.isMultiplicative, ih, zpow_one_add₀ ϖ.norm_pos.ne']
  | pred k ih =>
      rw [show (-(k : ℤ) - 1) = -1 + -(k : ℤ) by ring, zpow_add, zpow_neg, zpow_one,
        Units.val_mul, ϖ.norm_inv_mul, ih, zpow_add₀ ϖ.norm_pos.ne']
      simp

/-- **`v_ϖ` attains every integer**, on the integer powers of `ϖ`.  This is what makes the value
set unbounded in both directions, and is the source of the vertices of a Newton polygon. -/
@[simp] theorem val_zpow_self [NormOneClass A] [Nontrivial A] (n : ℤ) :
    ϖ.val ((ϖ.unit ^ n : Aˣ) : A) = (n : ℝ) := by
  rw [val_of_ne_zero ϖ (Units.ne_zero _), ϖ.norm_zpow, Real.log_zpow,
    mul_div_assoc, div_self ϖ.log_norm_neg.ne, mul_one]

/-- **`‖r‖ = ‖ϖ‖ ^ q`.**  The inverse dictionary: the norm is `‖ϖ‖` raised to the valuation.
Mirrors `NormedField.norm_eq_norm_rpow_normAddValQ`. -/
theorem norm_eq_rpow_val [Nontrivial A] {q : ℝ} (h : ϖ.val r = (q : WithTop ℝ)) :
    ‖r‖ = ‖(ϖ : A)‖ ^ q := by
  have hr : r ≠ 0 := fun hr ↦ by simp [hr] at h
  have hrpos : (0 : ℝ) < ‖r‖ := (norm_nonneg r).lt_of_ne' (norm_ne_zero_iff.mpr hr)
  rw [val_of_ne_zero ϖ hr, WithTop.coe_inj] at h
  rw [Real.rpow_def_of_pos ϖ.norm_pos, ← h, mul_div_cancel₀ _ ϖ.log_norm_neg.ne,
    Real.exp_log hrpos]

end PseudoUniformizer

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
    simp
  refine ⟨⟨⟨⟨algebraMap K A lam, algebraMap K A lam⁻¹, ?_, ?_⟩, ?_, ?_⟩⟩⟩
  · rw [← map_mul, mul_inv_cancel₀ hlamne, map_one]
  · rw [← map_mul, inv_mul_cancel₀ hlamne, map_one]
  · show ‖algebraMap K A lam‖ < 1
    rw [h1]; exact hlam1
  · intro x
    show ‖algebraMap K A lam * x‖ = ‖algebraMap K A lam‖ * ‖x‖
    rw [hnorm x, h1]

section UltrametricSummability

open Filter

variable {ι E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]
  {f : ι → E}

/-- In a complete ultrametric group, a family tending to `0` along the cofinite filter is
summable ([Bel] §II.1.5 footnote) — the convergence principle behind every `tsum` in this
development.  Not in Mathlib; a candidate for upstreaming. -/
theorem summable_of_tendsto_cofinite (hf : Tendsto f cofinite (𝓝 0)) : Summable f := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hev : ∀ᶠ i in cofinite, ‖f i‖ < ε := by
    have := Metric.tendsto_nhds.1 hf ε hε
    simpa [dist_zero_right] using this
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun t ht => ?_⟩
  rcases t.eq_empty_or_nonempty with rfl | hne
  · simpa using hε
  · refine lt_of_le_of_lt (hne.norm_sum_le_sup'_norm f) ?_
    rw [Finset.sup'_lt_iff]
    intro i hi
    have hi' : i ∉ (Filter.eventually_cofinite.1 hev).toFinset :=
      Finset.disjoint_left.1 ht hi
    rw [Set.Finite.mem_toFinset] at hi'
    exact not_not.1 hi'

omit [IsUltrametricDist E] [CompleteSpace E] in
/-- A cofinitely-vanishing family has bounded norms. -/
theorem bddAbove_range_norm_of_tendsto_cofinite (hf : Tendsto f cofinite (𝓝 0)) :
    BddAbove (Set.range fun i => ‖f i‖) := by
  have hev : ∀ᶠ i in cofinite, ‖f i‖ < 1 := by
    have := Metric.tendsto_nhds.1 hf 1 zero_lt_one
    simpa [dist_zero_right] using this
  set s := (Filter.eventually_cofinite.1 hev).toFinset with hs
  have hout : ∀ i, i ∉ s → ‖f i‖ < 1 := by
    intro i hi
    rw [hs, Set.Finite.mem_toFinset] at hi
    exact not_not.1 hi
  rcases s.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, ?_⟩
    rintro y ⟨i, rfl⟩
    exact (hout i (hemp ▸ Finset.notMem_empty i)).le
  · refine ⟨max 1 (s.sup' hne (‖f ·‖)), ?_⟩
    rintro y ⟨i, rfl⟩
    by_cases hi : i ∈ s
    · exact le_max_of_le_right (Finset.le_sup' (fun i => ‖f i‖) hi)
    · exact le_max_of_le_left (hout i hi).le

/-- The ultrametric bound on infinite sums: `‖∑' f‖ ≤ ⨆ ‖f i‖`. -/
theorem norm_tsum_le_iSup (hf : Tendsto f cofinite (𝓝 0)) :
    ‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [tsum_eq_sum (s := (∅ : Finset ι)) fun i _ => (IsEmpty.false i).elim]
    simp [Real.iSup_of_isEmpty]
  · have hbdd := bddAbove_range_norm_of_tendsto_cofinite hf
    refine le_of_tendsto (summable_of_tendsto_cofinite hf).hasSum.norm
      (Filter.Eventually.of_forall fun S => ?_)
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simpa using (norm_nonneg (f hι.some)).trans (le_ciSup hbdd hι.some)
    · exact (hS.norm_sum_le_sup'_norm f).trans
        (Finset.sup'_le hS _ fun i _ => le_ciSup hbdd i)

end UltrametricSummability

end TateFredholm

end
