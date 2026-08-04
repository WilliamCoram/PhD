import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.MulAction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Blueprint: compact operators on nonarchimedean Banach modules

This file is a Lean *blueprint* for Chapter 6 ("Compact Operators") of the project blueprint,
in the **full generality of Buzzard's eigenvarieties machine**: Banach modules over a
commutative nonarchimedean Banach `K`-algebra `A`, rather than Banach spaces over a `p`-adic
field.  The blueprint's Chapter 6 is recovered as the special case `A = K` (see §5 for the
one genuinely field-specific statement).  Statements are given in full; proofs that still
need to be formalised are `sorry`ed, each with a proof sketch and a reference.

## References

* [Buzzard] K. Buzzard, *Eigenvarieties*, in: L-functions and Galois representations,
  LMS Lecture Note Series **320** (2007), 59–120.  Part I, §2 is the main reference: Banach
  `A`-modules, ONable / potentially ONable modules, property (Pr), compact operators and
  their characteristic power series, and base change.  It in turn follows:
* [Serre] J-P. Serre, *Endomorphismes complètement continus des espaces de Banach
  p-adiques*, Publ. Math. IHÉS **12** (1962), 69–85 (the case `A = K`).
* [Coleman] R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math.
  **127** (1997) — the intermediate generality that Buzzard axiomatises.

Blueprint/[Buzzard, §2] ↔ Lean dictionary (this file):

| Source                            | Lean                                              |
| --------------------------------- | ------------------------------------------------- |
| Banach `A`-module                 | instance package, see "Standing hypotheses" below |
| Def 6.3, `c_A(I)`                 | `CompactOperators.cSpace` (= `C₀(Ix I, A)`)       |
| Lemma 6.5                         | Mathlib instances + `instIsUltrametricDist`       |
| Def 6.6 / [Buzzard] "ONable"      | `ONBasis`, `IsONable`                             |
| [Buzzard] "potentially ONable"    | `IsPotentiallyONable`                             |
| [Buzzard] property (Pr)           | `HasPr`                                           |
| Lemma 6.7 ([Serre] Prop. 1)       | `exists_onBasis` (the classical case `A = K`)     |
| Def 6.8–L. 6.10 (operator norm)   | `instNorm` on `M →L[A] N` (NOT in Mathlib!)       |
| Prop 6.11 ([Serre] Prop. 3)       | `matrixCoeff`, `exists_coeffEquiv`                |
| Def 6.13 (finite rank, compact)   | `IsFiniteRank`, `IsCompletelyContinuous`          |
| Lemma 6.14 ([Serre] Prop. 6)      | `isCompletelyContinuous_iff_rowNorm`              |
| Cor 6.15 (`D(1/p)` criterion)     | `isCompletelyContinuous_of_matrix_le_pow`         |
| Prop 6.16 (1) ([Serre] Prop. 7a)  | `charCoeff`, `charCoeff_eq_sum_perm`              |
| Prop 6.16 (2) ([Serre] Prop. 7b)  | `charCoeff_entire`                                |
| Prop 6.16 (3) ([Serre] Prop. 7c)  | `charCoeff_continuousAt`                          |
| Def 6.17                          | `charPowerSeries`                                 |
| [Buzzard, §2] basis independence  | `charPowerSeries_conj` (any continuous iso)       |
| [Buzzard, §2] direct sums / (Pr)  | `charPowerSeries_extendZero`                      |
| [Buzzard, §2] base change         | `charCoeff_baseChange`, `charPowerSeries_baseChange` |

## Standing hypotheses

* `K` — a complete nonarchimedean nontrivially normed field:
  `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`.
* `A` — a commutative nonarchimedean Banach `K`-algebra with `‖1‖ = 1`:
  `[NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  [NormOneClass A]`.
  Buzzard also assumes `A` **Noetherian**; up to the characteristic power series this is
  never used, so we omit `[IsNoetherianRing A]` here — it becomes essential for the Riesz
  theory (see the TODO section).
* A **Banach `A`-module** `M` is the instance package
  `[NormedAddCommGroup M] [Module A M] [IsBoundedSMul A M] [IsUltrametricDist M]
  [CompleteSpace M]`, i.e. a complete nonarchimedean normed group with `‖a • m‖ ≤ ‖a‖ ‖m‖`.
  Where boundedness arguments need the ground field (they all do — see below) we further
  assume `[NormedSpace K M] [IsScalarTower K A M]`, exactly Buzzard's "Banach module over a
  Banach `K`-algebra".

## Design decisions forced by the generalisation

* **The operator norm is not in Mathlib.**  Mathlib develops `opNorm` only over
  `NontriviallyNormedField`, so `M →L[A] N` has *no* norm instance.  We define
  `‖u‖ = sInf {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c ‖x‖}` (the same formula as Mathlib's `opNorm`;
  the definition is `K`-free).  Beware: over a general normed ring, a *continuous* `A`-linear
  map need not be *bounded* — there is no scaling trick.  It is the `K`-vector-space
  structure that rescues boundedness (`norm_restrictScalars`, `le_opNorm`), which is exactly
  why Buzzard's `A` is an algebra over a nontrivially valued field.
* **No normed-group instance on `M →L[A] N`.**  Mathlib already endows `M →L[A] N` with the
  strong topology; registering a `NormedAddCommGroup` instance would create a topology
  diamond.  We therefore register only a `Norm` instance and phrase "closure of the
  finite-rank operators" *metrically*: `IsCompletelyContinuous u ↔ ∀ ε > 0, ∃ v` finite rank
  with `‖u - v‖ < ε`.  (Over `A = K` this is literally membership in the closure.)
* **Finite rank over a ring.**  `u` has finite rank if its range is contained in a finitely
  *generated* `A`-submodule ([Buzzard, §2]) — over a ring this is the right notion; when
  `A = K` it coincides with "finite-dimensional range" (blueprint Definition 6.13).
* **ONable / potentially ONable / (Pr) without universe quantification.**  The basis vectors
  of an orthonormal basis are distinct elements of `M`, so index sets may be taken to be
  subsets `s : Set M`; property (Pr) ("`M ⊕ N` is potentially ONable for some `N`") is
  equivalent to "`M` is a continuous direct summand of some `c_A(I)`", which is how `HasPr`
  is stated.
* **Base change without completed tensor products.**  Buzzard's base-change lemma
  (`c_A(I) ⊗̂_A B = c_B(I)`) is stated *matrix-wise*: a contractive ring homomorphism
  `φ : A → B` applied to the matrix of `u` yields an operator whose characteristic series is
  `PowerSeries.map φ` of that of `u`.  This captures the content while the completed tensor
  product is not yet available.

## TODO / not in this file

Everything after the characteristic power series: the characteristic series of a compact
endomorphism of an abstract module with property (Pr) (via `u ⊕ 0` on a complement,
well-defined by `charPowerSeries_conj` + `charPowerSeries_extendZero`); multiplicativity;
resultants and the Riesz decomposition ([Buzzard, §2–3] — **here the Noetherian hypothesis
on `A` enters**); links to the Newton polygon of `det(1 - Tu)` (blueprint Chapter 5); and
the completed tensor product refinement of base change.
-/

open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction

-- Blueprint file: hypotheses are stated at final generality even where a particular
-- `sorry`ed statement does not yet use them.
set_option linter.unusedSectionVars false

noncomputable section

namespace CompactOperators

/-! ## §0  The index type -/

/-- `Ix I` is `I` regarded as a discrete topological space (the index set of an orthonormal
basis). -/
def Ix (I : Type*) : Type _ := I

instance {I : Type*} : TopologicalSpace (Ix I) := ⊥
instance {I : Type*} : DiscreteTopology (Ix I) := ⟨rfl⟩
instance {I : Type*} [DecidableEq I] : DecidableEq (Ix I) := inferInstanceAs (DecidableEq I)

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (A : Type*) [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
  [CompleteSpace A] [NormOneClass A]

/-! ## §1  The model Banach module `c_A(I)`  (blueprint Definition 6.3, Lemma 6.5)

`c_A(I)` is the module of families `(a_i)_{i ∈ I}` in `A` tending to `0` along the cofinite
filter, with norm `‖a‖ = sup_i ‖a_i‖`; realised as `C₀(Ix I, A)`.  Mathlib supplies the
normed group, `A`-module, `K`-normed-space and completeness instances; the ultrametric and
bounded-action facts are recorded below.  [Buzzard, §2; Serre, §1]. -/

/-- **Blueprint Definition 6.3, over `A`.**  `cSpace A I` (notation: `c(I, A)`) is the Banach
`A`-module of families `(a_i)_{i ∈ I}` in `A` tending to `0` in the cofinite filter, with the
sup norm.  [Buzzard, §2]. -/
def cSpace (I : Type*) : Type _ := C₀(Ix I, A)

@[inherit_doc] scoped notation "c(" I ", " A ")" => cSpace A I

namespace cSpace

variable {K A}
variable {I J : Type*}

instance : NormedAddCommGroup c(I, A) :=
  inferInstanceAs (NormedAddCommGroup C₀(Ix I, A))

instance : Module A c(I, A) :=
  inferInstanceAs (Module A C₀(Ix I, A))

instance : NormedSpace K c(I, A) :=
  inferInstanceAs (NormedSpace K C₀(Ix I, A))

/-- **Blueprint Lemma 6.5** (completeness): `c_A(I)` is a Banach module.  Supplied by
Mathlib. -/
instance : CompleteSpace c(I, A) :=
  inferInstanceAs (CompleteSpace C₀(Ix I, A))

instance : FunLike c(I, A) I A :=
  inferInstanceAs (FunLike C₀(Ix I, A) (Ix I) A)

/-- The `A`-action on `c_A(I)` is bounded: `‖a • f‖ ≤ ‖a‖ ‖f‖`.

*Proof sketch.*  Pointwise from `norm_mul_le` and the sup-norm description
(`norm_eq_iSup`). -/
instance : IsBoundedSMul A c(I, A) :=
  .of_norm_smul_le fun _ _ => by sorry

/-- The two scalar actions are compatible, making `c_A(I)` a Banach module over the Banach
`K`-algebra `A` in Buzzard's sense.

*Proof sketch.*  Pointwise `smul_assoc`. -/
instance : IsScalarTower K A c(I, A) := ⟨by sorry⟩

/-- Membership in `c_A(I)` is exactly the blueprint condition: the family tends to `0` along
the cofinite filter (blueprint Definition 6.3 / Remark 2.2). -/
theorem tendsto_cofinite (f : c(I, A)) : Tendsto (f : I → A) cofinite (𝓝 0) := by
  have h := (f : C₀(Ix I, A)).zero_at_infty'
  rwa [Filter.cocompact_eq_cofinite] at h

/-- The sup-norm formula of Definition 6.3: `‖f‖ = ⨆ i, ‖f i‖`.

*Proof sketch.*  Unfold the `BoundedContinuousFunction` norm; the sup is attained cofinitely
close, cf. the "gauss norm is attained" argument in the restricted-power-series chapter. -/
theorem norm_eq_iSup (f : c(I, A)) : ‖f‖ = ⨆ i : I, ‖f i‖ := by
  sorry

/-- The ultrametric inequality for the sup norm, making `c_A(I)` a nonarchimedean Banach
module in the sense of blueprint Definition 6.1.

*Proof sketch.*  Pointwise from `IsUltrametricDist A` and `norm_eq_iSup`, exactly as in
Lemma 3.6 (the nonarchimedean property of the Gauss norm). -/
instance : IsUltrametricDist c(I, A) := by
  sorry

section single

variable [DecidableEq I]

/-- The standard basis vector `e i` scaled by `a`: the family which is `a` in coordinate `i`
and `0` elsewhere.  (Used with `a = 1` as the canonical orthonormal basis of `c_A(I)`.) -/
def single (i : I) (a : A) : c(I, A) :=
  ⟨⟨Pi.single (i : Ix I) a, continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_cofinite_ne (i : Ix I)] with j hj
    exact (Pi.single_eq_of_ne (M := fun _ : Ix I => A) hj a).symm⟩

@[simp] theorem single_apply_self (i : I) (a : A) : single i a i = a :=
  show Pi.single (M := fun _ : Ix I => A) i a i = a from Pi.single_eq_same _ _

theorem single_apply_of_ne {i j : I} (h : j ≠ i) (a : A) : single i a j = 0 :=
  show Pi.single (M := fun _ : Ix I => A) i a j = 0 from Pi.single_eq_of_ne h _

/-- `‖e i‖ = 1`: the standard basis is orthonormal (here `‖(1 : A)‖ = 1` is the
`NormOneClass` hypothesis on the Banach algebra).

*Proof sketch.*  By `norm_eq_iSup` the norm is `⨆ j, ‖single i 1 j‖`, a sup of `0`s and a
single `1`. -/
@[simp] theorem norm_single_one (i : I) : ‖single i (1 : A)‖ = 1 := by
  sorry

end single

/-- **Blueprint Remark 6.4.**  For finite `I` every family tends to `0`, so `c_A(I) ≃ A^I`
with the sup norm; we phrase the target as the bounded functions `Ix I →ᵇ A`.

*Proof sketch.*  `ZeroAtInftyContinuousMap.toBCF` is an isometric embedding; for finite `I`
it is surjective since the cofinite filter is trivial. -/
theorem nonempty_isoOfFinite [Finite I] :
    Nonempty (c(I, A) ≃ₗᵢ[A] (Ix I →ᵇ A)) := by
  sorry

end cSpace

/-! ## §2  ONable, potentially ONable, property (Pr)
(blueprint Definition 6.6; [Buzzard, §2])

Buzzard's hierarchy of "has a good basis" conditions.  Note the index-set trick: the vectors
of an orthonormal basis are necessarily distinct and nonzero, so index sets can always be
taken to be *subsets of `M`*; this keeps all three definitions inside `Prop` with no
quantification over types. -/

section ONable

variable (I : Type*) (M : Type*) [NormedAddCommGroup M] [Module A M] [IsBoundedSMul A M]

/-- **Blueprint Definition 6.6, over `A`.**  An *orthonormal basis* of a Banach `A`-module
`M`, indexed by `I`, is a family `e : I → M` such that every `x ∈ M` has a unique expansion
`x = ∑ᵢ aᵢ • e i` with coefficients `a ∈ c_A(I)`, and moreover `‖x‖ = ‖a‖ = supᵢ ‖aᵢ‖`.
[Buzzard, §2 "ONable"; Serre, §1]. -/
structure ONBasis where
  /-- the basis vectors -/
  elem : I → M
  /-- every vector has a `c_A(I)`-expansion -/
  exists_expansion : ∀ x : M, ∃ a : c(I, A), HasSum (fun i => a i • elem i) x
  /-- the expansion is unique -/
  expansion_unique : ∀ (a b : c(I, A)) (x : M),
    HasSum (fun i => a i • elem i) x → HasSum (fun i => b i • elem i) x → a = b
  /-- the norm of a vector is the sup norm of its coefficients -/
  norm_expansion : ∀ (a : c(I, A)) (x : M), HasSum (fun i => a i • elem i) x → ‖x‖ = ‖a‖

variable {I}

/-- **[Buzzard, §2].**  `M` is *ONable* if it admits an orthonormal basis.  (Indexing by a
subset of `M` loses no generality: distinct basis vectors are distinct elements of `M`.) -/
def IsONable : Prop :=
  ∃ s : Set M, Nonempty (ONBasis A s M)

/-- **[Buzzard, §2].**  `M` is *potentially ONable* if it becomes ONable after replacing the
norm by an equivalent one — equivalently, if `M` is isomorphic *as a topological `A`-module*
(not necessarily isometrically) to some `c_A(I)`. -/
def IsPotentiallyONable : Prop :=
  ∃ s : Set M, Nonempty (M ≃L[A] c(s, A))

/-- **[Buzzard, §2], property (Pr).**  Buzzard: `M` has property (Pr) if there is a Banach
module `N` such that `M ⊕ N` is potentially ONable.  Equivalently (take `N := ker π`): `M`
is a continuous direct summand of some `c_A(I)` — the formulation used here, which avoids
quantifying over the complement `N`. -/
def HasPr : Prop :=
  ∃ (s : Set M) (ι : M →L[A] c(s, A)) (π : c(s, A) →L[A] M),
    π.comp ι = ContinuousLinearMap.id A M

variable {A M}

/-- ONable modules are potentially ONable (isometric isos are in particular topological).

*Proof sketch.*  From an `ONBasis` build the coefficient map `M ≃ c_A(s)`; it is an isometry
by `norm_expansion`, in particular a homeomorphism. -/
theorem IsONable.isPotentiallyONable (h : IsONable A M) : IsPotentiallyONable A M := by
  sorry

/-- Potentially ONable modules have property (Pr): an isomorphism onto `c_A(s)` exhibits `M`
as a (trivial) direct summand. -/
theorem IsPotentiallyONable.hasPr (h : IsPotentiallyONable A M) : HasPr A M := by
  obtain ⟨s, ⟨e⟩⟩ := h
  refine ⟨s, (e : M →L[A] c(s, A)), (e.symm : c(s, A) →L[A] M), ?_⟩
  ext x
  simp

/-- ONable ⟺ isometrically isomorphic to a model space `c_A(I)` ([Buzzard, §2]).

*Proof sketch.*  (⇒) the coefficient map of an `ONBasis` is an isometric `A`-linear
equivalence by definition.  (⇐) transport the standard basis `standardONBasis` along the
isomorphism. -/
theorem isONable_iff :
    IsONable A M ↔ ∃ s : Set M, Nonempty (M ≃ₗᵢ[A] c(s, A)) := by
  sorry

/-- The standard basis vectors `(e i)ᵢ` form an orthonormal basis of `c_A(I)` itself: model
spaces are ONable.

*Proof sketch.*  Expansion: `f = ∑ᵢ f i • e i` converges because `f i → 0` cofinitely and
the norm is ultrametric (partial sums are Cauchy).  Uniqueness: evaluate at each coordinate.
Norm condition: `cSpace.norm_eq_iSup`. -/
def cSpace.standardONBasis (I : Type*) [DecidableEq I] : ONBasis A I c(I, A) where
  elem i := cSpace.single i 1
  exists_expansion := by sorry
  expansion_unique := by sorry
  norm_expansion := by sorry

end ONable

/-! ### The classical case `A = K`  (blueprint Lemma 6.7)

For a general Banach algebra `A` there is no reason for a Banach module to be ONable — this
is precisely why Buzzard introduces potentially ONable and (Pr).  Over the *field* `K`
itself, with a discrete valuation, Serre proved every reasonable Banach space is ONable. -/

section ClassicalCase

/-- **Blueprint Lemma 6.7** (Serre, Proposition 1 and Lemme 1).  If the valuation on `K` is
**discrete** (hypothesis `hπ`) and every vector norm in `E` is realised by a scalar
(hypothesis `hE`, i.e. `‖E‖ ⊆ ‖K‖`), then a Banach *space* `E` over `A = K` admits an
orthonormal basis.

*Proof sketch* (Serre).  Reduce mod the maximal ideal of `𝒪_K`: `E⁰/E⁻` is a vector space
over the residue field; lift a basis and check, using discreteness of the valuation, that
the lifts expand everything (successive approximation, completeness) with the right norms.
Without discreteness this fails in general — for `K` with dense valuation one only gets
*potential* ONability results, which is Buzzard's motivation for the weaker notions
above. -/
theorem exists_onBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    [IsUltrametricDist E] [CompleteSpace E]
    (hπ : ∃ π : K, 1 < ‖π‖ ∧ ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n)
    (hE : ∀ x : E, ∃ c : K, ‖x‖ = ‖c‖) :
    IsONable K E := by
  sorry

end ClassicalCase

/-! ## §3  The operator norm on `ℒ_A(M, N)`  (blueprint Def 6.8 – Lemma 6.10)

Over the field `K`, Mathlib provides everything (`ContinuousLinearMap.hasOpNorm`,
completeness).  Over the Banach algebra `A` **none of this exists in Mathlib**: the operator
norm is developed only for `NontriviallyNormedField` scalars.  We register the norm by the
same `sInf` formula.  Two warnings:

1. Over a general normed ring, continuity of an `A`-linear map does **not** imply
   boundedness.  It is restriction of scalars to `K` (`u.restrictScalars K`, Mathlib) that
   provides bounds — this is where "Banach algebra **over `K`**" earns its keep, and why the
   `K`-module hypotheses appear below.
2. We deliberately do **not** register a `NormedAddCommGroup` instance on `M →L[A] N`:
   Mathlib already puts the strong topology on this type and a second, metric, topology
   would create an instance diamond.  Consequences of the norm axioms (triangle inequality
   etc.) are stated as standalone lemmas instead. -/

section OperatorNorm

variable {K A}
variable {M N : Type*}
  [NormedAddCommGroup M] [Module A M] [IsBoundedSMul A M]
  [NormedAddCommGroup N] [Module A N] [IsBoundedSMul A N]

/-- **Blueprint Definition 6.8/Lemma 6.10, over `A`.**  The operator norm on `ℒ_A(M, N)`,
by the usual formula.  (`K`-free as a definition; see the section comment.) -/
instance instNorm : Norm (M →L[A] N) :=
  ⟨fun u => sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}⟩

theorem norm_def (u : M →L[A] N) :
    ‖u‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖} := rfl

variable [NormedSpace K M] [IsScalarTower K A M] [NormedSpace K N] [IsScalarTower K A N]

/-- The `A`-linear operator norm agrees with the Mathlib operator norm of the underlying
`K`-linear map.

*Proof sketch.*  Both sides are `sInf` of the same set of bounds (the coercions of `u` and
`u.restrictScalars K` are the same function) — morally `rfl`. -/
theorem norm_restrictScalars (u : M →L[A] N) : ‖u‖ = ‖u.restrictScalars K‖ := by
  sorry

/-- Fundamental estimate `‖u x‖ ≤ ‖u‖ ‖x‖`.

*Proof sketch.*  Via `norm_restrictScalars` this is Mathlib's
`ContinuousLinearMap.le_opNorm` for the `K`-linear restriction; the nontrivially valued `K`
provides the scaling argument unavailable over `A`. -/
theorem le_opNorm (u : M →L[A] N) (x : M) : ‖u x‖ ≤ ‖u‖ * ‖x‖ := by
  sorry

/-- The operator norm is subadditive.  (Stated as a lemma since `M →L[A] N` carries no
`SeminormedAddCommGroup` instance — see the section comment.)

*Proof sketch.*  Transport along `norm_restrictScalars`; `restrictScalars` is additive. -/
theorem norm_add_le (u v : M →L[A] N) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  sorry

/-- `ℒ_A(M, N)` is complete for the operator norm, phrased metrically: every sequence that
is Cauchy in the operator norm converges in the operator norm (blueprint Lemma 6.10;
Mathlib's `ContinuousLinearMap.completeSpace` gives this for the `K`-restriction).

*Proof sketch.*  A Cauchy sequence for `‖·‖` restricts to a Cauchy sequence in
`ℒ_K(M, N)`, which converges to some `K`-linear `v`; `A`-linearity of the limit follows
pointwise from `A`-linearity of the terms, and `‖uₙ - v‖ → 0` transfers back along
`norm_restrictScalars`. -/
theorem exists_lim_of_cauchySeq (u : ℕ → M →L[A] N)
    (hu : ∀ ε > 0, ∃ M₀, ∀ m n, M₀ ≤ m → M₀ ≤ n → ‖u m - u n‖ < ε) :
    ∃ v : M →L[A] N, Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
  sorry

end OperatorNorm

/-! ## §4  Matrices  (blueprint Prop 6.11; [Buzzard, §2]) -/

section Matrix

variable {K A}
variable {I J : Type*} [DecidableEq I]

/-- The matrix coefficient `n_{ji}` of an operator `u : c_A(I) → c_A(J)` with respect to the
standard bases: `n_{ji} = (u e_i)_j`  (blueprint, discussion before Proposition 6.11). -/
def matrixCoeff (u : c(I, A) →L[A] c(J, A)) (j : J) (i : I) : A :=
  u (cSpace.single i 1) j

/-- Matrix coefficients are bounded by the operator norm: `‖n_{ji}‖ ≤ ‖u‖`.

*Proof sketch.*  `‖(u e_i)_j‖ ≤ ‖u e_i‖ ≤ ‖u‖ ‖e_i‖ = ‖u‖` using `le_opNorm`,
`norm_single_one`, and that coordinate evaluation is norm-nonincreasing
(`norm_eq_iSup`). -/
theorem norm_matrixCoeff_le (u : c(I, A) →L[A] c(J, A)) (j : J) (i : I) :
    ‖matrixCoeff u j i‖ ≤ ‖u‖ := by
  sorry

/-- Each *column* of the matrix of `u` tends to `0`: for fixed `i`, `n_{ji} → 0` cofinitely
in `j` (since `u e_i ∈ c_A(J)`). -/
theorem tendsto_matrixCoeff_column (u : c(I, A) →L[A] c(J, A)) (i : I) :
    Tendsto (fun j => matrixCoeff u j i) cofinite (𝓝 0) :=
  cSpace.tendsto_cofinite (u (cSpace.single i 1))

/-- The operator norm is the sup of the matrix coefficients: `‖u‖ = sup_{i,j} ‖n_{ji}‖`
(blueprint, after Proposition 6.11).

*Proof sketch.*  `≥` is `norm_matrixCoeff_le`.  For `≤`: expand `f = ∑ f i • e_i` and use
the ultrametric inequality on `u f = ∑ f i • u e_i` coordinatewise, with
`‖f i • (u e_i)_j‖ ≤ ‖f i‖ ‖n_{ji}‖` from `IsBoundedSMul`. -/
theorem norm_eq_iSup_matrixCoeff (u : c(I, A) →L[A] c(J, A)) :
    ‖u‖ = ⨆ j : J, ⨆ i : I, ‖matrixCoeff u j i‖ := by
  sorry

/-- **Blueprint Proposition 6.11** (Serre, Proposition 3; [Buzzard, §2]).  `u ↦ (u e_i)_i`
is an `A`-linear, norm-preserving bijection from `ℒ_A(c_A(I), N)` onto the space of
*bounded* families in `N`, i.e. the bounded functions `Ix I →ᵇ N` with the sup norm.
("Giving a continuous map out of `c_A(I)` is giving a bounded family.")

*Proof sketch.*  Injectivity: the `e_i` span a dense submodule.  Surjectivity: a bounded
family `(f_i)` defines `u f := ∑ᵢ f i • f_i`, convergent since `f i → 0` and `(f_i)` is
bounded (ultrametric).  Norm-preservation: same computation as
`norm_eq_iSup_matrixCoeff`. -/
theorem exists_coeffEquiv (N : Type*) [NormedAddCommGroup N] [Module A N]
    [IsBoundedSMul A N] [IsUltrametricDist N] [CompleteSpace N] :
    ∃ φ : (c(I, A) →L[A] N) ≃ₗ[A] (Ix I →ᵇ N), ∀ u, ‖φ u‖ = ‖u‖ := by
  sorry

end Matrix

/-! ## §5  Finite-rank and completely continuous (compact) operators
(blueprint Definition 6.13, Lemma 6.14, Corollary 6.15; [Buzzard, §2]) -/

section Compact

variable {K A}
variable {M N : Type*}
  [NormedAddCommGroup M] [Module A M] [IsBoundedSMul A M]
  [NormedAddCommGroup N] [Module A N] [IsBoundedSMul A N]

/-- **[Buzzard, §2].**  An operator has *finite rank* if its range is contained in a
finitely **generated** `A`-submodule.  When `A = K` this is the blueprint's Definition 6.13
("finite-dimensional range"); over a general ring "contained in f.g." is the robust
notion. -/
def IsFiniteRank (u : M →L[A] N) : Prop :=
  ∃ P : Submodule A N, P.FG ∧ LinearMap.range (u : M →ₗ[A] N) ≤ P

/-- **Blueprint Definition 6.13 / [Buzzard, §2].**  `u` is *completely continuous* (Serre;
= *compact* in the blueprint and in Buzzard) if it is an operator-norm limit of finite-rank
operators.  Phrased metrically (`∀ ε …`) because `M →L[A] N` carries no metric-space
instance — over `A = K` this is literally membership in the closure of `ℱ(M, N)`.

Warning: this is **not** Mathlib's `IsCompactOperator` — over a non-locally-compact `K`
(e.g. `ℂ_p`) no nonzero operator maps a neighbourhood to a relatively compact set.  The two
notions agree for `A = K` a finite extension of `ℚ_p`. -/
def IsCompletelyContinuous (u : M →L[A] N) : Prop :=
  ∀ ε > 0, ∃ v : M →L[A] N, IsFiniteRank v ∧ ‖u - v‖ < ε

theorem IsFiniteRank.isCompletelyContinuous {u : M →L[A] N} (hu : IsFiniteRank u) :
    IsCompletelyContinuous u := by
  intro ε hε
  refine ⟨u, hu, ?_⟩
  sorry -- `‖u - u‖ = ‖0‖ = 0 < ε`: needs `norm_zero` for the operator norm (via `sub_self`).

/-- Completely continuous operators are stable under operator-norm limits ("𝒞 is closed",
Serre §4).

*Proof sketch.*  `ε/2`-argument, using the triangle inequality `norm_add_le`. -/
theorem isCompletelyContinuous_of_tendsto (u : ℕ → M →L[A] N) (v : M →L[A] N)
    (hu : ∀ n, IsCompletelyContinuous (u n))
    (huv : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)) :
    IsCompletelyContinuous v := by
  sorry

/-- Finite-rank operators are stable under sums and scalars ("ℱ is a submodule"; with the
previous lemma, 𝒞 is a closed submodule).

*Proof sketch.*  `range (u + v) ≤ range u ⊔ range v` and `FG` is stable under `⊔`;
`range (a • u) ≤ range u`. -/
theorem IsFiniteRank.add {u v : M →L[A] N} (hu : IsFiniteRank u) (hv : IsFiniteRank v) :
    IsFiniteRank (u + v) := by
  sorry

variable {I J : Type*} [DecidableEq I]

/-- The row sup `r_j(u) = sup_i ‖n_{ji}‖` (blueprint Lemma 6.14). -/
def rowNorm (u : c(I, A) →L[A] c(J, A)) (j : J) : ℝ :=
  ⨆ i : I, ‖matrixCoeff u j i‖

/-- **Blueprint Lemma 6.14** (Serre, Proposition 6; [Buzzard, §2] in matrix form).  An
operator between model modules is completely continuous iff its row sups tend to `0`:

  `u` compact  ⟺  `r_j(u) → 0` cofinitely in `j`.

*Proof sketch.*  (⇐)  Truncate: for `S : Finset J` let `u_S` keep only the rows in `S`;
its range lies in the `A`-span of `{e_j : j ∈ S}` (finitely generated!), and
`‖u - u_S‖ = sup_{j ∉ S} r_j(u) → 0` by `norm_eq_iSup_matrixCoeff`.
(⇒)  A finite-rank `v` has `r_j(v) → 0` (a f.g. submodule of `c_A(J)` is spanned by finitely
many decaying families), and `|r_j(u) - r_j(v)| ≤ ‖u - v‖`, so the property passes to
limits. -/
theorem isCompletelyContinuous_iff_rowNorm (u : c(I, A) →L[A] c(J, A)) :
    IsCompletelyContinuous u ↔ Tendsto (rowNorm u) cofinite (𝓝 0) := by
  sorry

/-- **Blueprint Corollary 6.15** (the `D(1/p)` criterion, for a general scalar `a` with
`‖a‖ < 1` in place of `1/p`).  If the matrix of `u : c_A(ℕ) → c_A(ℕ)` satisfies
`‖n_{ji}‖ ≤ ‖a‖ ^ j` — all entries integral and still integral after multiplying row `j` by
`a^{-j}` — then `u` is completely continuous.

*Proof sketch.*  `r_j(u) ≤ ‖a‖ ^ j → 0`; apply `isCompletelyContinuous_iff_rowNorm`
(`Nat.cofinite_eq_atTop`). -/
theorem isCompletelyContinuous_of_matrix_le_pow (u : c(ℕ, A) →L[A] c(ℕ, A)) (a : A)
    (ha : ‖a‖ < 1) (h : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖a‖ ^ j) :
    IsCompletelyContinuous u := by
  sorry

end Compact

/-! ## §6  The characteristic power series  (blueprint Prop 6.16, Def 6.17; [Buzzard, §2])

For `u : c_A(I) → c_A(I)` completely continuous with matrix `(n_{ji})`, the Fredholm
determinant

  `det(1 - Tu) = ∑ₘ cₘ Tᵐ ∈ A⟦T⟧`,
  `cₘ = (-1)ᵐ ∑_{S ⊆ I, |S| = m} ∑_{σ ∈ Sym(S)} sgn(σ) ∏_{i ∈ S} n_{σ(i) i}`.

The inner double sum is the determinant of the finite submatrix `(n_{ji})_{j,i ∈ S}`, so we
*define* `cₘ` as a `tsum` of principal minors (now with entries in the commutative ring `A`)
and recover the permutation formula as a lemma.  Note the Noetherian hypothesis on `A` is
still not needed — convergence is pure ultrametric analysis. -/

section CharPowerSeries

variable {K A}
variable {I : Type*} [DecidableEq I]

/-- The principal `S × S` minor of the matrix of `u`, for `S` a finite subset of `I`. -/
def minor (u : c(I, A) →L[A] c(I, A)) (S : Finset I) : A :=
  Matrix.det (Matrix.of fun j i : S => matrixCoeff u j i)

/-- Summability of the degree-`m` minors of a completely continuous operator — the
convergence underlying Proposition 6.16 (1).

*Proof sketch* (Serre, proof of Prop. 7; [Buzzard, §2]).  By
`isCompletelyContinuous_iff_rowNorm`, `r_j(u) → 0`; the ultrametric Hadamard bound gives
`‖minor u S‖ ≤ ∏_{j ∈ S} r_j(u)` (expand the determinant, every monomial picks one entry
per row), and for any `ε > 0` only finitely many `S` of size `m` avoid a factor small
enough.  Summability in complete ultrametric `A` is "terms → 0 cofinitely". -/
theorem summable_minor (u : c(I, A) →L[A] c(I, A)) (hu : IsCompletelyContinuous u) (m : ℕ) :
    Summable fun S : {S : Finset I // S.card = m} => minor u (S : Finset I) := by
  sorry

/-- **Blueprint Proposition 6.16 (1) / Definition 6.17, over `A`** — the `m`-th coefficient
of the characteristic power series `det(1 - Tu)`:

  `cₘ = (-1)ᵐ ∑_{|S| = m} det (n_{ji})_{j,i ∈ S}`.

(For non-compact `u` the `tsum` silently takes the junk value `0`; all theorems below assume
`IsCompletelyContinuous u`.) -/
def charCoeff (u : c(I, A) →L[A] c(I, A)) (m : ℕ) : A :=
  (-1 : A) ^ m * ∑' S : {S : Finset I // S.card = m}, minor u (S : Finset I)

/-- **Blueprint Definition 6.17 / [Buzzard, §2].**  The characteristic power series
`det(1 - Tu) = ∑ₘ cₘ Tᵐ ∈ A⟦T⟧` of a compact operator `u` (the Fredholm determinant of the
matrix `(n_{ji})`). -/
def charPowerSeries (u : c(I, A) →L[A] c(I, A)) : PowerSeries A :=
  PowerSeries.mk (charCoeff u)

@[simp] theorem charPowerSeries_coeff (u : c(I, A) →L[A] c(I, A)) (m : ℕ) :
    PowerSeries.coeff m (charPowerSeries u) = charCoeff u m :=
  PowerSeries.coeff_mk m _

/-- `c₀ = 1`: the characteristic series has constant term `1`.

*Proof sketch.*  The only `S` with `S.card = 0` is `∅`, whose minor is the empty determinant
`1`; the `tsum` over a `Unique` index is the single term. -/
@[simp] theorem charCoeff_zero (u : c(I, A) →L[A] c(I, A)) : charCoeff u 0 = 1 := by
  sorry

/-- **Blueprint Proposition 6.16 (1)**, in the literal permutation form:

  `cₘ = (-1)ᵐ ∑_{S, |S| = m} ∑_{σ ∈ Sym(S)} sgn(σ) ∏_{i ∈ S} n_{σ(i) i}`.

*Proof sketch.*  Expand each `minor` by `Matrix.det_apply`. -/
theorem charCoeff_eq_sum_perm (u : c(I, A) →L[A] c(I, A)) (m : ℕ) :
    charCoeff u m = (-1 : A) ^ m * ∑' S : {S : Finset I // S.card = m},
      ∑ σ : Equiv.Perm (S : Finset I),
        ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : (S : Finset I), matrixCoeff u (σ i) i := by
  sorry

/-- **Blueprint Proposition 6.16 (2)** (Serre, Proposition 7 (b); [Buzzard, §2]):
`det(1 - Tu)` is *entire* — `‖cₘ‖ rᵐ → 0` for every radius `r ≥ 0`.  Equivalently
(chapter 2 of the blueprint): the characteristic series is a restricted power series over
`A` for **every** parameter, i.e. its radius of convergence is infinite.

*Proof sketch.*  With `r_j = r_j(u) → 0`, the Hadamard bound gives
`‖cₘ‖ ≤ ρ₁ ⋯ ρₘ` where `ρ₁ ≥ ρ₂ ≥ ⋯` is the decreasing rearrangement of `(r_j)`; since
`ρₘ → 0` the tail beats any geometric growth `r^m`. -/
theorem charCoeff_entire (u : c(I, A) →L[A] c(I, A)) (hu : IsCompletelyContinuous u)
    (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun m => ‖charCoeff u m‖ * r ^ m) atTop (𝓝 0) := by
  sorry

/-- **Blueprint Proposition 6.16 (3)** (Serre, Proposition 7 (c)): continuity of the
Fredholm determinant.  If compact operators `uₙ → u` in operator norm (stated metrically)
then each coefficient of `det(1 - T uₙ)` converges to the corresponding coefficient of
`det(1 - T u)`.

(Serre proves more: convergence uniform in `m` after weighting by any radius; that stronger
statement makes `det(1 - Tu)` continuous into entire series and can be added once a topology
on entire series over `A` is fixed — cf. the Gauss-norm chapter.)

*Proof sketch.*  `cₘ` is a uniformly convergent sum of polynomials in the entries `n_{ji}`,
each norm-controlled by `‖u‖` (`norm_matrixCoeff_le`); dominate the tail uniformly in `n`
with the Hadamard bound. -/
theorem charCoeff_continuousAt (u : ℕ → c(I, A) →L[A] c(I, A)) (v : c(I, A) →L[A] c(I, A))
    (hu : ∀ n, IsCompletelyContinuous (u n))
    (huv : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)) (m : ℕ) :
    Tendsto (fun n => charCoeff (u n) m) atTop (𝓝 (charCoeff v m)) := by
  sorry

/-- **[Buzzard, §2], basis independence.**  Conjugating `u` by *any* continuous `A`-linear
isomorphism `φ : c_A(I) ≃ c_A(J)` — not necessarily isometric! — does not change
`det(1 - Tu)`.  This strengthening (Buzzard) over the isometric case (Serre) is exactly what
makes the characteristic series well-defined on *potentially* ONable modules, hence on
modules with property (Pr); that extension is the first TODO after this file.

*Proof sketch.*  Both sides are limits of characteristic polynomials of finite truncations
(by 6.16 (3), noting conjugation preserves complete continuity); for finite matrices this
is `det(1 - TPAP⁻¹) = det(1 - TA)`. -/
theorem charPowerSeries_conj {J : Type*} [DecidableEq J]
    (φ : c(I, A) ≃L[A] c(J, A)) (u : c(I, A) →L[A] c(I, A))
    (hu : IsCompletelyContinuous u) :
    charPowerSeries (((φ : c(I, A) →L[A] c(J, A)).comp u).comp
        (φ.symm : c(J, A) →L[A] c(I, A)))
      = charPowerSeries u := by
  sorry

/-- **[Buzzard, §2], extension by zero.**  If `v` acts on `c_A(I ⊕ J)` as `u ⊕ 0` — matrix
`u` on the `I`-block, zero elsewhere — then `det(1 - Tv) = det(1 - Tu)`.  Together with
`charPowerSeries_conj` this is what makes the characteristic series of a compact
endomorphism of a module with property (Pr) independent of the chosen complement.

*Proof sketch.*  Every minor of `v` meeting the `J`-block has a zero row, so only
`S ⊆ inl(I)` contribute, and those minors equal the corresponding minors of `u`. -/
theorem charPowerSeries_extendZero {J : Type*} [DecidableEq J]
    (u : c(I, A) →L[A] c(I, A)) (hu : IsCompletelyContinuous u)
    (v : c(I ⊕ J, A) →L[A] c(I ⊕ J, A))
    (hII : ∀ j i, matrixCoeff v (Sum.inl j) (Sum.inl i) = matrixCoeff u j i)
    (hJrow : ∀ j q, matrixCoeff v (Sum.inr j) q = 0)
    (hJcol : ∀ p j, matrixCoeff v p (Sum.inr j) = 0) :
    charPowerSeries v = charPowerSeries u := by
  sorry

end CharPowerSeries

/-! ## §7  Base change  ([Buzzard, §2])

For a contractive homomorphism `φ : A → B` of Banach algebras, Buzzard's base-change lemma
says `c_A(I) ⊗̂_A B = c_B(I)`, a compact `u` base-changes to a compact `u ⊗ 1`, and
`det(1 - T(u ⊗ 1)) = φ(det(1 - Tu))`.  Pending completed tensor products in Mathlib, we
state this *matrix-wise*: the base-changed operator is any operator on `c_B(I)` whose matrix
is `φ` of the matrix of `u`. -/

section BaseChange

variable {K A}
variable (B : Type*) [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
  [CompleteSpace B] [NormOneClass B]
variable {I : Type*} [DecidableEq I]

/-- Base change preserves complete continuity ([Buzzard, §2]): if `v` on `c_B(I)` has matrix
`φ(n_{ji})` for a contractive `φ`, and `u` is compact, then `v` is compact.

*Proof sketch.*  `r_j(v) ≤ r_j(u) → 0` by contractivity; apply
`isCompletelyContinuous_iff_rowNorm` twice. -/
theorem isCompletelyContinuous_baseChange (φ : A →+* B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (u : c(I, A) →L[A] c(I, A)) (hu : IsCompletelyContinuous u)
    (v : c(I, B) →L[B] c(I, B))
    (hv : ∀ j i, matrixCoeff v j i = φ (matrixCoeff u j i)) :
    IsCompletelyContinuous v := by
  sorry

/-- **[Buzzard, §2], base change, coefficientwise.**  `cₘ(v) = φ(cₘ(u))` when the matrix of
`v` is `φ` of the matrix of `u`.

*Proof sketch.*  `φ` commutes with the finite determinants (`RingHom.map_det`) and, being
contractive hence continuous, with the `tsum` (`Summable.map`, using `summable_minor` for
`u`). -/
theorem charCoeff_baseChange (φ : A →+* B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (u : c(I, A) →L[A] c(I, A)) (hu : IsCompletelyContinuous u)
    (v : c(I, B) →L[B] c(I, B))
    (hv : ∀ j i, matrixCoeff v j i = φ (matrixCoeff u j i)) (m : ℕ) :
    charCoeff v m = φ (charCoeff u m) := by
  sorry

/-- **[Buzzard, §2], base change.**  `det(1 - Tv) = φ(det(1 - Tu))` as power series:
the characteristic series commutes with base change along contractive homomorphisms of
Banach algebras.  Immediate from `charCoeff_baseChange` and extensionality of power
series. -/
theorem charPowerSeries_baseChange (φ : A →+* B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (u : c(I, A) →L[A] c(I, A)) (hu : IsCompletelyContinuous u)
    (v : c(I, B) →L[B] c(I, B))
    (hv : ∀ j i, matrixCoeff v j i = φ (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map φ (charPowerSeries u) := by
  ext m
  simp [charCoeff_baseChange B φ hφ u hu v hv m, PowerSeries.coeff_map]

end BaseChange

end CompactOperators

end
