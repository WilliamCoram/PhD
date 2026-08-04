import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.MulAction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Polynomial.Basic

/-!
# Blueprint: compact operators and Fredholm determinants, after Bellaïche's *Eigenbook*

A **self-contained** Lean blueprint for the non-archimedean Fredholm theory of
**[Bellaïche, The Eigenbook, Chapter 3, §3.1]** (§II.1 in the numbering of the draft on the
author's webpage, which we use below; `II.1.x` = `3.1.x` of the published edition): Banach
modules over a Banach algebra, orthonormalizable and potentially orthonormalizable modules,
compact operators, the Fredholm determinant `det(1 − Tu)`, property (Pr), and extension of
scalars.  Statements are given in full; proofs still to be formalised are `sorry`ed, each
with a proof sketch and a reference.

This file is deliberately **independent** of `PhD.Test.CompactOperators` (the parallel
blueprint following Buzzard's *Eigenvarieties*): everything is developed from the ground
up in the `Eigenbook` namespace, so that each blueprint can be read, built, and eventually
proved against its own source.  The price is some duplication (`Ix`, the model space, the
operator norm); the payoff is that the two treatments' *differing definitions* are each
recorded faithfully.  See "Differences from the Buzzard blueprint" below.

## References

* [Bel] J. Bellaïche, *The Eigenbook — Eigenvarieties, families of Galois representations,
  p-adic L-functions*, Pathways in Mathematics, Birkhäuser (2021).  Chapter 3, §3.1; cited
  below by the draft numbering §II.1.1–II.1.7
  (https://people.brandeis.edu/~jbellaic/preprint/Eigenbook.pdf).
* [Som] P. Sommaruga, *Babyseminar: Eigenvarieties*, seminar programme, Universität
  Duisburg–Essen, Summer Semester 2025 — a reading guide to [Bel] Chapters 2–3 and the
  eigenvariety machine; Talk 4 covers exactly the material of this file
  (https://www.esaga.uni-due.de/f/paolo.sommaruga/eigenprogram/Proposal_for_babyseminar__Eigenvarieties-2.pdf).
* [Serre] J-P. Serre, *Endomorphismes complètement continus des espaces de Banach
  p-adiques*, Publ. Math. IHÉS **12** (1962), 69–85.
* [Buzzard] K. Buzzard, *Eigenvarieties*, LMS Lecture Note Series **320** (2007), 59–120.
  [Bel] §II.1 is a self-contained rewrite of [Serre] and [Buzzard, §2] "getting rid of the
  noetherian hypothesis".

## Standing hypotheses

[Bel] works over a commutative Banach algebra `R` over `ℚ_p`, with (nonarchimedean,
submultiplicative) norm extending the `p`-adic absolute value.  We keep one notch more
generality, as elsewhere in this project: a complete nonarchimedean nontrivially normed
field `K` in place of `ℚ_p`, and

* `R` — a commutative nonarchimedean Banach `K`-algebra:
  `[NormedCommRing R] [NormedAlgebra K R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]`.  For [Bel] the axiom `‖λ·1_R‖ = ‖λ‖` makes `‖1‖ = 1` automatic; in
  our setting it is the explicit `NormOneClass` hypothesis.
* A **Banach `R`-module** `M` is the instance package
  `[NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]
  [CompleteSpace M]`; where an argument needs the ground field (Open Mapping Theorem,
  boundedness of linear maps) we further assume `[NormedSpace K M] [IsScalarTower K R M]`.
* **No Noetherian hypothesis**: [Bel]'s stated goal.  The single statement using it
  (Proposition II.1.21) carries an isolated `[IsNoetherianRing R]`.

## Differences from the Buzzard blueprint (`PhD.Test.CompactOperators`)

The two files develop the *same* objects ground-up under *different* source assumptions;
where the sources agree the definitions below coincide verbatim with the Buzzard file's
(with `A` renamed `R`).  The genuine divergences, all traceable to differing assumptions
or primitives in the sources:

1. **Ground ring.**  [Buzzard]: a Noetherian Banach algebra `A` over any complete
   nonarchimedean `K`.  [Bel]: a not-necessarily-Noetherian Banach algebra over `ℚ_p`.
   Both files use a general `K`; this one flags the two `ℚ_p`-sensitive spots (discreteness
   of the valuation in Theorem II.1.13, `NormOneClass` above) instead of inheriting them
   silently.
2. **Orthonormal bases.**  [Bel] Definition II.1.5 *requires* `‖eᵢ‖ = 1`; in the Buzzard
   file it is a derived lemma.  Accordingly `Eigenbook.ONBasis` has a `norm_elem` field and
   is a *different structure* from `CompactOperators.ONBasis` (same expansion, uniqueness
   and norm axioms).
3. **Property (Pr).**  [Bel] defines: `∃ Q`, `P ⊕ Q` potentially orthonormalizable.  We
   state the equivalent "continuous direct summand of a model space" form (`HasPr`), as in
   the Buzzard file, to avoid quantifying over the complement — but here (Pr) is
   additionally characterised by [Bel]'s **lifting property** (Exercise II.1.19), the
   Banach analogue of projectivity, which has no counterpart in the Buzzard file.
4. **The determinant's primitives are inverted.**  Both files define the coefficients of
   `det(1 − Tu)` by the same convergent sum of principal minors.  The Buzzard file then
   takes conjugation-invariance as the primitive invariance statement; here, following
   [Bel], the primitive is the **trace property** `det(1 − Tφu) = det(1 − Tuφ)` for `φ`
   compact and `u` merely continuous (Prop II.1.17), proven by **coordinate truncation**
   (`truncation`, Lemma II.1.8 via the Open Mapping Theorem, Scholium II.1.10) plus a
   **quantitative Lipschitz bound** (Lemma II.1.15) reducing everything to finite linear
   algebra ((II.1.2)/(II.1.3)); invariance under change of basis, of norm, and conjugation
   are then formal corollaries.
5. **Continuity of `u ↦ det(1 − Tu)`.**  Quantitative here (Lemma II.1.15:
   `‖cₙ(u) − cₙ(v)‖ ≤ max(‖u‖,‖v‖)^{n−1}‖u − v‖`), qualitative in the Buzzard file.
6. **Operator norm.**  Same `sInf` definition on `M →L[R] N` in both files — over a normed
   *ring* Mathlib has none, and continuity does not imply boundedness without the field
   `K`.  Here the instance is **`scoped`** (active under `open scoped Eigenbook`), so that
   importing both blueprints never produces two competing global `Norm` instances.
7. **Matrix conventions.**  `matrixCoeff u j i = (u eᵢ)_j` in both files; this is [Bel]'s
   `a_{i,j}` (he writes `φ(eᵢ) = ∑_j a_{i,j} f_j`), and his "rows `(a_{i,j})_j` tend to `0`
   uniformly in `i`" is our `rowNorm u · → 0` (cofinitely).

## Dictionary ([Bel] §II.1 ↔ Lean, this file)

| [Bel]                                 | Lean                                       |
| ------------------------------------- | ------------------------------------------ |
| II.1.1 norms, `Hom_R(M,N)`, OMT       | `instNorm`, `norm_add_le`, `exists_lim_of_cauchySeq`, `exists_preimage_norm_le` |
| Def II.1.3 (finite rank, compact)     | `IsFiniteRank`, `IsCompletelyContinuous`   |
| Lemma II.1.4 (two-sided ideal)        | `IsFiniteRank.comp_left/comp_right`, `IsCompletelyContinuous.comp_left/comp_right` |
| Def II.1.5 (ON basis, with `‖eᵢ‖=1`)  | `ONBasis` (field `norm_elem`)              |
| Def II.1.6 (pot. orthonormalizable)   | `IsONable`, `IsPotentiallyONable`          |
| Ex II.1.7 (`c_I(R)`, canonical basis) | `cSpace` (`c(I, R)`), `cSpace.standardONBasis`, `isONable_iff` |
| matrix description, `‖φ‖ = sup‖a‖`    | `matrixCoeff`, `norm_eq_iSup_matrixCoeff`, `exists_coeffEquiv` |
| Lemma II.1.8 (truncation approx.)     | `truncation`, `exists_truncation_near`     |
| Prop II.1.9 (compact ⟺ rows → 0)      | `isCompletelyContinuous_iff_rowNorm`       |
| Scholium II.1.10                      | `tendsto_truncation_comp`                  |
| Hyp II.1.11, Thm II.1.13 (Serre)      | `HasUniformizer`, `isPotentiallyONable_of_hasUniformizer` |
| (II.1.1) estimate, `c_n`              | `summable_minor`, `charCoeff`, `charPowerSeries` |
| Def II.1.16, Lemma II.1.14            | `IsEntire`, `charPowerSeries_isEntire`     |
| Lemma II.1.15 (quantitative cont.)    | `norm_charCoeff_sub_le`                    |
| (II.1.2) algebraic determinant        | `charCoeff_eq_det_coeff`                   |
| Prop II.1.17 (trace property)         | `charPowerSeries_comm`                     |
| Cor II.1.18 (independence)            | `charPowerSeries_conj`                     |
| §II.1.6 property (Pr)                 | `HasPr`, `HasPr.exists_lift`, `HasPr.projective` |
| Prop II.1.21 (the Noetherian one)     | `finite_projective_of_one_sub_compact_nilpotent` |
| §II.1.7 extension of scalars          | `charCoeff_baseChange` (matrix-wise); `⊗̂` TODO |

## TODO / not in this file

* Lemma II.1.12 (an `(eᵢ)` in the unit ball is an ON basis iff the residues `(ẽᵢ)` are an
  `R̃`-basis of `M̃ = M⁰/πM⁰`): needs the reduction functor `M ↦ M̃`; it is the proof engine
  for Theorem II.1.13 and is noted in its sketch.
* §II.1.7 in full: the completed tensor product `M ⊗̂_R R'` (universal property,
  Lemma II.1.22 `c_I(R) ⊗̂ R' ≅ c_I(R')`, Lemma II.1.23, and Serre's Lemma II.1.24
  `𝒞(M,N) = M' ⊗̂ N`) — pending `⊗̂` in Mathlib; the matrix-wise substitute is §7 below.
* §II.2 (Riesz theory: `ν`-dominant polynomials, good zeros, resultants) and §II.3–II.4
  (adapted pairs, submodules of slope `≤ ν`, [Som] Talks 5 and 7) — the next chapter of
  this blueprint and the payoff of the Fredholm theory recorded here.
-/

open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction

-- Blueprint file: hypotheses are stated at final generality even where a particular
-- `sorry`ed statement does not yet use them.
set_option linter.unusedSectionVars false

noncomputable section

namespace Eigenbook

/-! ## §0  The index type -/

/-- `Ix I` is `I` regarded as a discrete topological space (the index set of an orthonormal
basis). -/
def Ix (I : Type*) : Type _ := I

instance {I : Type*} : TopologicalSpace (Ix I) := ⊥
instance {I : Type*} : DiscreteTopology (Ix I) := ⟨rfl⟩
instance {I : Type*} [DecidableEq I] : DecidableEq (Ix I) := inferInstanceAs (DecidableEq I)

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (R : Type*) [NormedCommRing R] [NormedAlgebra K R] [IsUltrametricDist R]
  [CompleteSpace R] [NormOneClass R]

/-! ## §1  General notions  ([Bel] II.1.1)

Banach `R`-modules are the instance package fixed above.  `Hom_R(M,N)` is `M →L[R] N`;
[Bel] norms it by "the smallest `C` with `‖φ(m)‖ ≤ C‖m‖`", which is the `sInf` below.  Two
warnings, both stemming from `R` being a mere ring:

* Mathlib's operator norm exists only over `NontriviallyNormedField` scalars, so this
  instance is genuinely new — and it is `scoped` (see difference 6 in the module
  docstring).
* Over a normed ring, a continuous `R`-linear map need not be bounded; [Bel]'s
  "continuous ⟺ bounded" holds because `ℚ_p ⊂ R`, and correspondingly our proofs go
  through restriction of scalars to `K`. -/

section GeneralNotions

variable {K R}
variable {M N : Type*}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- **[Bel] II.1.1.**  The operator norm on `Hom_R(M, N)`: the least bound `C` in
`‖φ(m)‖ ≤ C‖m‖`, as an `sInf`.  Scoped instance; `K`-free as a definition. -/
scoped instance instNorm : Norm (M →L[R] N) :=
  ⟨fun u => sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}⟩

theorem norm_def (u : M →L[R] N) :
    ‖u‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖} := rfl

variable [NormedSpace K M] [IsScalarTower K R M] [NormedSpace K N] [IsScalarTower K R N]

/-- The operator norm agrees with Mathlib's for the underlying `K`-linear map.

*Proof sketch.*  Both sides are `sInf` of the same set of bounds. -/
theorem norm_restrictScalars (u : M →L[R] N) : ‖u‖ = ‖u.restrictScalars K‖ := by
  sorry

/-- Fundamental estimate `‖u x‖ ≤ ‖u‖ ‖x‖` — via the `K`-structure ([Bel] II.1.1;
"continuous ⟺ bounded" needs scalars from a nontrivially valued field).

*Proof sketch.*  `norm_restrictScalars` and Mathlib's `ContinuousLinearMap.le_opNorm`. -/
theorem le_opNorm (u : M →L[R] N) (x : M) : ‖u x‖ ≤ ‖u‖ * ‖x‖ := by
  sorry

/-- Subadditivity of the operator norm (stated as a lemma: `M →L[R] N` carries no
`SeminormedAddCommGroup` instance, deliberately — see the section comment).

*Proof sketch.*  Transport along `norm_restrictScalars`. -/
theorem norm_add_le (u v : M →L[R] N) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  sorry

/-- **[Bel] II.1.1**: `Hom_R(M, N)` is a Banach `R`-module — completeness, phrased
metrically.

*Proof sketch.*  A `‖·‖`-Cauchy sequence restricts to a Cauchy sequence in `ℒ_K(M, N)`
(complete by Mathlib); the limit is `R`-linear pointwise, and the convergence transfers
back along `norm_restrictScalars`. -/
theorem exists_lim_of_cauchySeq (u : ℕ → M →L[R] N) [CompleteSpace N]
    (hu : ∀ ε > 0, ∃ M₀, ∀ m n, M₀ ≤ m → M₀ ≤ n → ‖u m - u n‖ < ε) :
    ∃ v : M →L[R] N, Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
  sorry

/-- **Quantitative Open Mapping Theorem** ([Bel] II.1.1, last paragraph): a continuous
surjection of Banach `R`-modules admits norm-controlled preimages.  [Bel] uses this at
every approximation step of the Fredholm theory (Lemma II.1.8 below).

*Proof sketch.*  Restrict scalars to `K` and apply Mathlib's Banach open mapping theorem
(`ContinuousLinearMap.exists_preimage_norm_le`). -/
theorem exists_preimage_norm_le [CompleteSpace M] [CompleteSpace N]
    (f : M →L[R] N) (hf : Function.Surjective f) :
    ∃ C > 0, ∀ n : N, ∃ m : M, f m = n ∧ ‖m‖ ≤ C * ‖n‖ := by
  sorry

end GeneralNotions

/-! ## §2  Compact operators  ([Bel] Definition II.1.3, Lemma II.1.4) -/

section Compact

variable {K R}
variable {M N P : Type*}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- **[Bel] Definition II.1.3 (first half).**  A morphism has *finite rank* if its image is
contained in a finite (= finitely generated) submodule. -/
def IsFiniteRank (u : M →L[R] N) : Prop :=
  ∃ Q : Submodule R N, Q.FG ∧ LinearMap.range (u : M →ₗ[R] N) ≤ Q

/-- **[Bel] Definition II.1.3 (second half).**  A continuous morphism is *compact* (or
*completely continuous*) if it lies in the closure of the finite-rank morphisms in
`Hom_R(M, N)`.  Phrased metrically since `M →L[R] N` carries only a `Norm`.

Warning (as in the Buzzard file): this is **not** Mathlib's `IsCompactOperator` — over a
non-locally-compact base no nonzero operator maps a neighbourhood to a relatively compact
set. -/
def IsCompletelyContinuous (u : M →L[R] N) : Prop :=
  ∀ ε > 0, ∃ v : M →L[R] N, IsFiniteRank v ∧ ‖u - v‖ < ε

theorem IsFiniteRank.isCompletelyContinuous {u : M →L[R] N} (hu : IsFiniteRank u) :
    IsCompletelyContinuous u := by
  intro ε hε
  refine ⟨u, hu, ?_⟩
  sorry -- `‖u - u‖ = ‖0‖ = 0 < ε`: needs `norm_zero` for the operator norm.

/-- "The set of compact morphisms is a closed submodule" ([Bel], after Definition II.1.3) —
the closedness half, phrased as stability under operator-norm limits.

*Proof sketch.*  `ε/2`-argument with `norm_add_le`. -/
theorem isCompletelyContinuous_of_tendsto (u : ℕ → M →L[R] N) (v : M →L[R] N)
    (hu : ∀ n, IsCompletelyContinuous (u n))
    (huv : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)) :
    IsCompletelyContinuous v := by
  sorry

/-- The submodule half of the same statement: finite-rank morphisms are stable under sums
(hence, with `isCompletelyContinuous_of_tendsto`, so are compact ones).

*Proof sketch.*  `range (u + v) ≤ range u ⊔ range v` and `FG` is stable under `⊔`. -/
theorem IsFiniteRank.add {u v : M →L[R] N} (hu : IsFiniteRank u) (hv : IsFiniteRank v) :
    IsFiniteRank (u + v) := by
  sorry

/-- **[Bel] Lemma II.1.4, finite-rank half, post-composition**: the image of `f ∘ u` lands
in the image of a finitely generated submodule. -/
theorem IsFiniteRank.comp_left {u : M →L[R] N} (hu : IsFiniteRank u) (f : N →L[R] P) :
    IsFiniteRank (f.comp u) := by
  obtain ⟨Q, hQ, hle⟩ := hu
  refine ⟨Q.map (f : N →ₗ[R] P), hQ.map _, ?_⟩
  rintro x ⟨m, rfl⟩
  exact Submodule.mem_map_of_mem (hle ⟨m, rfl⟩)

/-- **[Bel] Lemma II.1.4, finite-rank half, pre-composition**: the range of `u ∘ f` is
contained in the range of `u`. -/
theorem IsFiniteRank.comp_right {u : M →L[R] N} (hu : IsFiniteRank u) (f : P →L[R] M) :
    IsFiniteRank (u.comp f) := by
  obtain ⟨Q, hQ, hle⟩ := hu
  refine ⟨Q, hQ, ?_⟩
  rintro x ⟨m, rfl⟩
  exact hle ⟨f m, rfl⟩

/-- **[Bel] Lemma II.1.4** (compact half): post-composition by a continuous map preserves
complete continuity.

*Proof sketch.*  If `‖u − v‖ < ε/‖f‖` with `v` finite rank, then `f ∘ v` is finite rank
(`IsFiniteRank.comp_left`) and `‖f∘u − f∘v‖ ≤ ‖f‖‖u − v‖ < ε` (submultiplicativity of the
operator norm, via `le_opNorm`). -/
theorem IsCompletelyContinuous.comp_left {u : M →L[R] N}
    (hu : IsCompletelyContinuous u) (f : N →L[R] P) :
    IsCompletelyContinuous (f.comp u) := by
  sorry

/-- **[Bel] Lemma II.1.4** (compact half): pre-composition by a continuous map preserves
complete continuity. -/
theorem IsCompletelyContinuous.comp_right {u : M →L[R] N}
    (hu : IsCompletelyContinuous u) (f : P →L[R] M) :
    IsCompletelyContinuous (u.comp f) := by
  sorry

end Compact

/-! ## §3  Orthonormalizable modules, the model space, truncations
([Bel] II.1.3: Definitions II.1.5–II.1.6, Example II.1.7, Lemma II.1.8,
Proposition II.1.9, Scholium II.1.10) -/

section ONable

variable (I : Type*) (M : Type*) [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- **[Bel] Definition II.1.5.**  An *orthonormal basis* of a Banach `R`-module `M`,
indexed by `I`, is a family `e : I → M` with `‖e i‖ = 1` such that every `m ∈ M` has a
unique expansion `m = ∑ᵢ aᵢ • e i` with coefficients `(aᵢ)` tending to `0`, and
`‖m‖ = supᵢ ‖aᵢ‖`.

Note the difference from the Buzzard blueprint: there `‖e i‖ = 1` is a derived lemma;
[Bel] puts it in the definition, so here it is the field `norm_elem`.  (The coefficient
space is `c(I, R)`, defined just below; to keep the structure first we phrase the
coefficients as bare families with a decay hypothesis.) -/
structure ONBasis where
  /-- the basis vectors -/
  elem : I → M
  /-- [Bel]'s normalisation `‖eᵢ‖ = 1`, part of the definition -/
  norm_elem : ∀ i, ‖elem i‖ = 1
  /-- every vector has an expansion with coefficients tending to `0` cofinitely -/
  exists_expansion : ∀ x : M, ∃ a : I → R,
    Tendsto a cofinite (𝓝 0) ∧ HasSum (fun i => a i • elem i) x
  /-- the expansion is unique -/
  expansion_unique : ∀ (a b : I → R) (x : M),
    Tendsto a cofinite (𝓝 0) → Tendsto b cofinite (𝓝 0) →
    HasSum (fun i => a i • elem i) x → HasSum (fun i => b i • elem i) x → a = b
  /-- the norm of a vector is the sup norm of its coefficients -/
  norm_expansion : ∀ (a : I → R) (x : M), Tendsto a cofinite (𝓝 0) →
    HasSum (fun i => a i • elem i) x → ‖x‖ = ⨆ i, ‖a i‖

variable {I}

/-- **[Bel] Definition II.1.6 (first half).**  `M` is *orthonormalizable* if it has an
orthonormal basis.  (Indexing by a subset of `M` loses no generality: uniqueness of
expansions forces the basis vectors to be distinct.) -/
def IsONable : Prop :=
  ∃ s : Set M, Nonempty (ONBasis R s M)

end ONable

/-! ### The model space `c_I(R)`  ([Bel] Example II.1.7)

The Banach `R`-module of families `(rᵢ)_{i ∈ I}` converging to `0`, with the sup norm —
realised, as in the Buzzard blueprint, as Mathlib's `C₀(Ix I, R)` for the discrete index
`Ix I` (zero-at-infinity = zero along the cofinite filter), which yields the normed group,
module, and completeness instances for free. -/

/-- **[Bel] Example II.1.7.**  `cSpace R I` (notation: `c(I, R)`) is the Banach `R`-module
`c_I(R)` of families in `R` tending to `0` in the cofinite filter, with the sup norm. -/
def cSpace (I : Type*) : Type _ := C₀(Ix I, R)

@[inherit_doc] scoped notation "c(" I ", " R ")" => cSpace R I

namespace cSpace

variable {K R}
variable {I J : Type*}

instance : NormedAddCommGroup c(I, R) :=
  inferInstanceAs (NormedAddCommGroup C₀(Ix I, R))

instance : Module R c(I, R) :=
  inferInstanceAs (Module R C₀(Ix I, R))

instance : NormedSpace K c(I, R) :=
  inferInstanceAs (NormedSpace K C₀(Ix I, R))

instance : CompleteSpace c(I, R) :=
  inferInstanceAs (CompleteSpace C₀(Ix I, R))

instance : FunLike c(I, R) I R :=
  inferInstanceAs (FunLike C₀(Ix I, R) (Ix I) R)

/-- The `R`-action on `c_I(R)` is bounded: `‖r • f‖ ≤ ‖r‖ ‖f‖`.

*Proof sketch.*  Pointwise from `norm_mul_le` and `norm_eq_iSup`. -/
instance : IsBoundedSMul R c(I, R) :=
  .of_norm_smul_le fun _ _ => by sorry

/-- Compatibility of the `K`- and `R`-actions.

*Proof sketch.*  Pointwise `smul_assoc`. -/
instance : IsScalarTower K R c(I, R) := ⟨by sorry⟩

/-- Membership in `c_I(R)` is exactly [Bel]'s condition: the family tends to `0` along the
cofinite filter. -/
theorem tendsto_cofinite (f : c(I, R)) : Tendsto (f : I → R) cofinite (𝓝 0) := by
  have h := (f : C₀(Ix I, R)).zero_at_infty'
  rwa [Filter.cocompact_eq_cofinite] at h

/-- The sup-norm formula: `‖f‖ = ⨆ i, ‖f i‖`.

*Proof sketch.*  Unfold the `BoundedContinuousFunction` norm; the sup over a decaying
family is attained cofinitely close. -/
theorem norm_eq_iSup (f : c(I, R)) : ‖f‖ = ⨆ i : I, ‖f i‖ := by
  sorry

/-- The ultrametric inequality for the sup norm.

*Proof sketch.*  Pointwise from `IsUltrametricDist R` and `norm_eq_iSup`. -/
instance : IsUltrametricDist c(I, R) := by
  sorry

section single

variable [DecidableEq I]

/-- The canonical basis vector `e i` scaled by `r` ([Bel] Example II.1.7: "the sequence
whose `i`-th term is `1` and all others `0`", with `r = 1`). -/
def single (i : I) (r : R) : c(I, R) :=
  ⟨⟨Pi.single (i : Ix I) r, continuous_of_discreteTopology⟩, by
    rw [Filter.cocompact_eq_cofinite]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_cofinite_ne (i : Ix I)] with j hj
    exact (Pi.single_eq_of_ne (M := fun _ : Ix I => R) hj r).symm⟩

@[simp] theorem single_apply_self (i : I) (r : R) : single i r i = r :=
  show Pi.single (M := fun _ : Ix I => R) i r i = r from Pi.single_eq_same _ _

theorem single_apply_of_ne {i j : I} (h : j ≠ i) (r : R) : single i r j = 0 :=
  show Pi.single (M := fun _ : Ix I => R) i r j = 0 from Pi.single_eq_of_ne h _

/-- `‖e i‖ = 1` — [Bel]'s normalisation `norm_elem` for the canonical basis.  Uses
`‖(1 : R)‖ = 1`, automatic in [Bel] (`‖λ1‖ = ‖λ‖`), a `NormOneClass` hypothesis here.

*Proof sketch.*  By `norm_eq_iSup`, a sup of `0`s and a single `1`. -/
@[simp] theorem norm_single_one (i : I) : ‖single i (1 : R)‖ = 1 := by
  sorry

/-- **[Bel] Example II.1.7.**  The canonical basis `(e i)` is an orthonormal basis of
`c_I(R)`: model spaces are orthonormalizable.

*Proof sketch.*  Expansion: `f = ∑ᵢ f i • e i`, convergent since `f i → 0` and the norm is
ultrametric.  Uniqueness: evaluate coordinates.  Norm: `norm_eq_iSup`. -/
def standardONBasis : ONBasis R I c(I, R) where
  elem i := single i 1
  norm_elem i := norm_single_one i
  exists_expansion := by sorry
  expansion_unique := by sorry
  norm_expansion := by sorry

end single

end cSpace

/-! ### Potential orthonormalizability -/

section PotONable

variable {K}
variable (M : Type*) [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- **[Bel] Definition II.1.6 (second half).**  `M` is *potentially orthonormalizable* if
some equivalent norm makes it orthonormalizable — equivalently ([Bel] Example II.1.7),
if `M` is isomorphic *as a topological `R`-module* (not necessarily isometrically) to some
`c_I(R)`.  We take the latter as the definition. -/
def IsPotentiallyONable : Prop :=
  ∃ s : Set M, Nonempty (M ≃L[R] c(s, R))

/-- **[Bel] Example II.1.7**, the isometric half: `M` is orthonormalizable iff it is
*isometrically* isomorphic to a model space.

*Proof sketch.*  (⇒) the coefficient map of an `ONBasis` is an isometric equivalence by
`norm_expansion`.  (⇐) transport `standardONBasis`. -/
theorem isONable_iff :
    IsONable R M ↔ ∃ s : Set M, Nonempty (M ≃ₗᵢ[R] c(s, R)) := by
  sorry

/-- Orthonormalizable modules are potentially orthonormalizable. -/
theorem IsONable.isPotentiallyONable (h : IsONable R M) : IsPotentiallyONable R M := by
  sorry

end PotONable

/-! ### Matrices, truncations, and the compactness criterion -/

section Matrix

variable {K R}
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- The matrix coefficient of `u : c_R(I) → c_R(J)` in the canonical bases:
`matrixCoeff u j i = (u eᵢ)_j`.  This is [Bel]'s `a_{i,j}` (he writes
`φ(eᵢ) = ∑_j a_{i,j} fⱼ`, [Bel] §II.1.3). -/
def matrixCoeff (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) : R :=
  u (cSpace.single i 1) j

/-- Each column of the matrix tends to `0`: for fixed `i`, `(u eᵢ)_j → 0` cofinitely in `j`
(it is a coordinate family of an element of `c_J(R)`) — [Bel]'s "whose rows go to zero for
every `i`" (his rows are indexed by our `j`). -/
theorem tendsto_matrixCoeff_column (u : c(I, R) →L[R] c(J, R)) (i : I) :
    Tendsto (fun j => matrixCoeff u j i) cofinite (𝓝 0) :=
  cSpace.tendsto_cofinite (u (cSpace.single i 1))

/-- **[Bel] §II.1.3**: "It is clear that `‖φ‖ = sup_{i,j} ‖a_{i,j}‖`."

*Proof sketch.*  `≥` from `le_opNorm` and `norm_single_one`; `≤` by expanding along the
canonical basis and estimating ultrametrically. -/
theorem norm_eq_iSup_matrixCoeff (u : c(I, R) →L[R] c(J, R)) :
    ‖u‖ = ⨆ j : J, ⨆ i : I, ‖matrixCoeff u j i‖ := by
  sorry

/-- **[Bel] §II.1.3**: "conversely, every matrix … whose rows go to zero for every `i` and
whose coefficients are bounded defines an element of `Hom_R(M, N)`" — packaged, together
with injectivity and the norm formula, as a norm-preserving `R`-linear bijection onto the
bounded families (`Ix I →ᵇ N` on the discrete index).

*Proof sketch.*  Injectivity: the `eᵢ` span densely.  Surjectivity: `f ↦ ∑ᵢ f i • (data i)`
converges by the ultrametric estimate.  Norm: previous lemma. -/
theorem exists_coeffEquiv (N : Type*) [NormedAddCommGroup N] [Module R N]
    [IsBoundedSMul R N] [IsUltrametricDist N] [CompleteSpace N] :
    ∃ φ : (c(I, R) →L[R] N) ≃ₗ[R] (Ix I →ᵇ N), ∀ u, ‖φ u‖ = ‖u‖ := by
  sorry

/-- The coordinate truncation `π_S : c_R(I) → c_R(I)`, keeping the coordinates in the
finite set `S` and killing the others ([Bel] §II.1.3, the projection `π_S`).  The workhorse
of [Bel]'s whole treatment: every determinant statement is proven by truncating to finite
rank and passing to the limit. -/
def truncation (S : Finset I) : c(I, R) →L[R] c(I, R) :=
  ⟨⟨⟨fun f => (⟨⟨fun i : I => if i ∈ S then f i else 0, continuous_of_discreteTopology⟩,
      by sorry⟩ : c(I, R)),
    by sorry⟩, by sorry⟩, by sorry⟩

@[simp] theorem truncation_apply (S : Finset I) (f : c(I, R)) (i : I) :
    truncation S f i = if i ∈ S then f i else 0 := rfl

/-- Truncations are contractions: `‖π_S f‖ ≤ ‖f‖`.

*Proof sketch.*  Coordinatewise from `cSpace.norm_eq_iSup`. -/
theorem norm_truncation_apply_le (S : Finset I) (f : c(I, R)) :
    ‖truncation S f‖ ≤ ‖f‖ := by
  sorry

/-- Truncations have finite rank: the image lies in the span of `{eᵢ : i ∈ S}`. -/
theorem isFiniteRank_truncation (S : Finset I) :
    IsFiniteRank (truncation (R := R) S) := by
  sorry

/-- **[Bel] Lemma II.1.8.**  A finitely generated submodule `P` of `c_R(I)` is uniformly
approximated by coordinate truncations: for every `ε > 0` there is a finite `S ⊆ I` with
`‖π_S p − p‖ ≤ ε ‖p‖` for **all** `p ∈ P` simultaneously.

*Proof sketch.*  Pick a continuous surjection `π : Rʳ → P`; the quantitative Open Mapping
Theorem (`exists_preimage_norm_le`) gives `c > 0` with norm-controlled preimages.  Choose
`S` so that `‖π_S(π(eₖ)) − π(eₖ)‖ ≤ ε/c` for the `r` generators, and estimate any
`p = π(m)` ultrametrically.  This is the only place the ground field `K` (through the OMT)
enters the construction of the Fredholm determinant.

**Warning (found while formalising, 2026-07-10).**  As stated in [Bel] the lemma needs
`P` **closed**: the OMT step requires the target complete, and completeness of f.g.
submodules is exactly the Noetherian input ([JN, p. 7]).  Over a general Banach–Tate
base there is a counterexample (`R = ℚₚ ⊕ c(ℕ, ℚₚ)` pointwise, `P = R·(pʲeⱼ)ⱼ`, whose
unit vectors `p⁻ⁿeₙ • g` concentrate at coordinate `n`).  In this file's Banach-algebra
setting the statement should carry an `IsClosed (P : Set c(I, R))` hypothesis unless `R`
is Noetherian or a field.  The merged development (`PhD.TateFredholm.Matrix`) states it
with the explicit hypothesis; see the b2 log there for the full analysis. -/
theorem exists_truncation_near (P : Submodule R c(I, R)) (hP : P.FG) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset I, ∀ p ∈ P, ‖truncation S p - p‖ ≤ ε * ‖p‖ := by
  sorry

/-- The row sup `r_j(u) = sup_i ‖(u eᵢ)_j‖` — the quantity whose decay characterises
compactness. -/
def rowNorm (u : c(I, R) →L[R] c(J, R)) (j : J) : ℝ :=
  ⨆ i : I, ‖matrixCoeff u j i‖

/-- **[Bel] Proposition II.1.9.**  An operator between model modules is compact iff its
rows tend to `0` *uniformly in the column index*: `sup_i ‖a_{i,j}‖ → 0` cofinitely in `j`.

*Proof sketch* ([Bel]).  (⇐) `π_S ∘ u → u` directly.  (⇒) given ε, take finite-rank `v`
with `‖u − v‖ < ε`; Lemma II.1.8 gives a truncation `π_S` with `‖π_S∘v − v‖ < ε`, whence
`‖π_S∘u − u‖ ≤ ε` ultrametrically and the rows off `S` have sup `≤ ε`. -/
theorem isCompletelyContinuous_iff_rowNorm (u : c(I, R) →L[R] c(J, R)) :
    IsCompletelyContinuous u ↔ Tendsto (rowNorm u) cofinite (𝓝 0) := by
  sorry

/-- **[Bel] Scholium II.1.10.**  For compact `u`, the truncations `π_S ∘ u` converge to `u`
in operator norm along the directed family of finite sets `S` — the approximating sequence
in "compact = limit of finite rank" can be taken to be the canonical truncations.

*Proof sketch.*  Contained in the proof of Proposition II.1.9, as [Bel] notes. -/
theorem tendsto_truncation_comp (u : c(I, R) →L[R] c(J, R))
    (hu : IsCompletelyContinuous u) :
    Tendsto (fun S : Finset J => ‖(truncation S).comp u - u‖) atTop (𝓝 0) := by
  sorry

end Matrix

/-! ## §4  Serre's sufficient condition for orthonormalizability
([Bel] II.1.4: Hypothesis II.1.11, Lemma II.1.12, Theorem II.1.13)

[Bel] proves: **every Banach `ℚ_p`-module is potentially orthonormalizable**
(Theorem II.1.13).  The mechanism is reduction modulo a uniformiser: under
Hypothesis II.1.11 (the norms `< 1` attain a maximum at a *multiplicative* element `π` —
i.e. the valuation is discrete), a family `(eᵢ)` in the unit ball `M⁰` is an orthonormal
basis iff the residues `(ẽᵢ)` form an algebraic basis of `M̃ = M⁰/πM⁰` over `R̃ = R⁰/πR⁰`
(Lemma II.1.12, successive approximation).  Over a *field* the residue module is a vector
space, hence free, hence — after rescaling the norm into `‖K^×‖`, which is what
"potentially" buys — every Banach space is orthonormalizable.

Lemma II.1.12 needs the reduction functor `M ↦ M̃` and is a TODO (module docstring); we
record the hypothesis and the theorem, in the `K`-generality the argument supports. -/

section Serre

/-- **[Bel] Hypothesis II.1.11.**  Among the elements of norm `< 1` there is one of largest
norm which is moreover multiplicative (`‖πx‖ = ‖π‖‖x‖` for all `x`).  For a nontrivially
normed field this says exactly that the valuation is **discrete** with uniformiser `π`;
`ℚ_p` satisfies it with `π = p`. -/
def HasUniformizer (F : Type*) [NormedRing F] : Prop :=
  ∃ π : F, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ (∀ x : F, ‖π * x‖ = ‖π‖ * ‖x‖) ∧
    ∀ r : F, ‖r‖ < 1 → ‖r‖ ≤ ‖π‖

variable {K}

/-- **[Bel] Theorem II.1.13**, in `K`-generality: if the ground field is discretely valued
(Hypothesis II.1.11) then *every* Banach `K`-space is potentially orthonormalizable.
[Bel] states this for `K = ℚ_p`; the proof only uses discreteness of the valuation — this
is one of the two `ℚ_p`-sensitive points flagged in the module docstring.

*Proof sketch.*  Replace `‖·‖` by the equivalent norm `‖m‖' = inf {‖c‖ : c ∈ K, ‖c‖ ≥ ‖m‖}`
whose values lie in `‖K‖`; then Hypothesis II.1.11 applies to `(E, ‖·‖')` and by
Lemma II.1.12 (TODO) orthonormalizability reduces to freeness of the residue module
`Ẽ = E⁰/πE⁰` over the residue *field* — automatic.  So `(E, ‖·‖')` is orthonormalizable,
i.e. `E` is potentially orthonormalizable. -/
theorem isPotentiallyONable_of_hasUniformizer (hK : HasUniformizer K)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    [CompleteSpace E] :
    IsPotentiallyONable K E := by
  sorry

end Serre

/-! ## §5  The Fredholm determinant
([Bel] II.1.5: estimate (II.1.1), Lemmas II.1.14–II.1.15, Definition II.1.16,
(II.1.2)–(II.1.3), Proposition II.1.17, Corollary II.1.18)

For a compact `φ` with matrix `(a_{i,j})`, [Bel] sets `c_S = ∑_σ ε(σ) ∏_{i∈S} a_{i,σ(i)}`
(the determinant of the `S × S` principal submatrix), shows `∑_{|S| = n} c_S` converges via
the row-decay estimate (II.1.1), and defines `det(1 − Tφ) = ∑ₙ cₙ Tⁿ`.  We define `c_S` as
`Matrix.det` of the minor — the same element of `R` — and the `cₙ` by a `tsum`. -/

section Fredholm

variable {K R}
variable {I : Type*} [DecidableEq I]

/-- The principal `S × S` minor `c_S` of the matrix of `u` ([Bel] §II.1.5, defined there by
the permutation sum; `Matrix.det` is that sum). -/
def minor (u : c(I, R) →L[R] c(I, R)) (S : Finset I) : R :=
  Matrix.det (Matrix.of fun j i : S => matrixCoeff u j i)

/-- Summability of the degree-`n` minors — [Bel]'s convergence of `∑_{|S| = n} c_S`, via
the estimate **(II.1.1)**: `‖c_S‖ ≤ ‖u‖^{|S∩I₀|} ε^{|S∖I₀|}` where the rows outside a
finite `I₀` have sup `< ε` (each monomial of the determinant picks one entry per row).

*Proof sketch.*  By Proposition II.1.9 pick `I₀`; only finitely many `S` of size `n` sit
inside `I₀`, and every other `S` picks up a factor `< ε`; conclude with "summable ⟺ terms
→ 0 cofinitely" in the complete ultrametric `R`. -/
theorem summable_minor (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u) (n : ℕ) :
    Summable fun S : {S : Finset I // S.card = n} => minor u (S : Finset I) := by
  sorry

/-- **[Bel] §II.1.5.**  The `n`-th coefficient `cₙ = ∑_{|S| = n} c_S` of the Fredholm
determinant (with `c₀ = 1`; for non-compact `u` the `tsum` silently takes the junk value
`0` when `n ≥ 1`). -/
def charCoeff (u : c(I, R) →L[R] c(I, R)) (n : ℕ) : R :=
  (-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)

/-- **[Bel] §II.1.5.**  The *Fredholm determinant* `det(1 − Tu) = ∑ₙ cₙ Tⁿ ∈ R⟦T⟧` of a
compact operator.  (Sign convention: [Bel]'s expansion of `det(1 − Tφ)` carries the
`(−1)ⁿ` inside his `cₙ`; we keep it explicit, matching the blueprint's Chapter 6.) -/
def charPowerSeries (u : c(I, R) →L[R] c(I, R)) : PowerSeries R :=
  PowerSeries.mk (charCoeff u)

@[simp] theorem charPowerSeries_coeff (u : c(I, R) →L[R] c(I, R)) (n : ℕ) :
    PowerSeries.coeff n (charPowerSeries u) = charCoeff u n :=
  PowerSeries.coeff_mk n _

/-- `c₀ = 1` ([Bel] §II.1.5, "and `c₀ = 1`").

*Proof sketch.*  The unique `S` with `S.card = 0` is `∅`, whose minor is the empty
determinant `1`. -/
@[simp] theorem charCoeff_zero (u : c(I, R) →L[R] c(I, R)) : charCoeff u 0 = 1 := by
  sorry

/-- **[Bel] Definition II.1.16.**  A power series lies in `R{{T}}` — is *everywhere
convergent*, equivalently entire — if `‖aₙ‖ Cⁿ → 0` for every `C > 0`.  This is the
blueprint's "restricted for every parameter" (Chapter 2). -/
def IsEntire (F : PowerSeries R) : Prop :=
  ∀ C : ℝ, 0 < C → Tendsto (fun n => ‖PowerSeries.coeff n F‖ * C ^ n) atTop (𝓝 0)

/-- **[Bel] Lemma II.1.14.**  The Fredholm determinant of a compact operator is everywhere
convergent: `det(1 − Tu) ∈ R{{T}}`.

*Proof sketch.*  With `ε = min(1/(2C), 1)` and `I₀` from (II.1.1),
`‖cₙ‖Cⁿ ≤ Cⁿ max(1,‖u‖)^{|I₀|} ε^{n−|I₀|} ≤ D/2ⁿ` for `n > |I₀|`. -/
theorem charPowerSeries_isEntire (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) : IsEntire (charPowerSeries u) := by
  sorry

/-- **[Bel] Lemma II.1.15** — the *quantitative* continuity of the Fredholm determinant,
coefficient by coefficient:

  `‖cₙ(u) − cₙ(v)‖ ≤ max(‖u‖, ‖v‖)^{n−1} · ‖u − v‖`   (n ≥ 1).

"The assignment `φ ↦ det(1 − Tφ)` is continuous" for the sup-of-coefficients norm on
`R{{T}}`, with an explicit modulus — the estimate that powers every limit argument below.
(The Buzzard blueprint only records the qualitative statement.)

*Proof sketch.*  `‖a_{S,σ}(u) − a_{S,σ}(v)‖ ≤ max(‖u‖,‖v‖)^{|S|−1}‖u − v‖` by telescoping
the difference of products and bounding ultrametrically; sum over `σ` and `S`
(ultrametrically again). -/
theorem norm_charCoeff_sub_le (u v : c(I, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) (hv : IsCompletelyContinuous v)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖charCoeff u n - charCoeff v n‖ ≤ max ‖u‖ ‖v‖ ^ (n - 1) * ‖u - v‖ := by
  sorry

/-- **[Bel] (II.1.2)** — compatibility with the algebraic determinant.  If the rows of `u`
are supported on a finite set `S` (image in the span of `{eⱼ : j ∈ S}`), the Fredholm
determinant *is* the determinant of the finite matrix: coefficientwise,

  `cₙ(u) = coeff_n det(1 − T·(a)_{j,i ∈ S})`,

the determinant taken in `Matrix S S (Polynomial R)`.  (No compactness needed: every minor
meeting the complement of `S` has a zero row, so the `tsum` is a finite sum.)

*Proof sketch.*  Expand both determinants by permutations and match terms. -/
theorem charCoeff_eq_det_coeff (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (n : ℕ) :
    charCoeff u n =
      (Matrix.det (1 - (Polynomial.X : Polynomial R) •
        Matrix.of fun j i : S => Polynomial.C (matrixCoeff u j i))).coeff n := by
  sorry

/-- **[Bel] Proposition II.1.17 — the trace property, the central theorem of this file.**
For `u : c_R(I) → c_R(J)` **compact** and `v : c_R(J) → c_R(I)` merely **continuous**,

  `det(1 − T·(u ∘ v)) = det(1 − T·(v ∘ u))`.

*Proof sketch* (the [Bel] pattern in full).  (1) Both composites are compact
(`IsCompletelyContinuous.comp_left/comp_right`).  (2) By Scholium II.1.10 truncate:
`π_S ∘ u → u`, and by the quantitative Lemma II.1.15 both sides are continuous in the
operator, so reduce to `u` finite-rank of truncated form.  (3) Truncate `v` likewise.
(4) For finite-rank operators both sides are algebraic determinants by (II.1.2), where the
identity is classical for finite matrices ((II.1.3): `det(1 − AB) = det(1 − BA)`). -/
theorem charPowerSeries_comm {J : Type*} [DecidableEq J]
    (u : c(I, R) →L[R] c(J, R)) (v : c(J, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) :
    charPowerSeries (u.comp v) = charPowerSeries (v.comp u) := by
  sorry

/-- **[Bel] Corollary II.1.18.**  The Fredholm determinant depends only on the compact
operator and the *topological* module — not on the orthonormal basis, nor on the choice of
norm within its equivalence class.  Stated as invariance under conjugation by an arbitrary
continuous isomorphism; a **formal consequence** of the trace property
`charPowerSeries_comm` (apply it to `φ ∘ u` and `φ⁻¹`).  This is what justifies extending
`det(1 − Tu)` to compact endomorphisms of *potentially* orthonormalizable modules — the
"potentially" costs nothing. -/
theorem charPowerSeries_conj {J : Type*} [DecidableEq J]
    (φ : c(I, R) ≃L[R] c(J, R)) (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) :
    charPowerSeries (((φ : c(I, R) →L[R] c(J, R)).comp u).comp
        (φ.symm : c(J, R) →L[R] c(I, R)))
      = charPowerSeries u := by
  sorry

end Fredholm

/-! ## §6  Property (Pr)  ([Bel] II.1.6: Exercise II.1.19, Propositions II.1.20–II.1.21)

[Bel]: `P` has property (Pr) if there is a Banach module `Q` such that `P ⊕ Q` is
potentially orthonormalizable.  We state the equivalent "continuous direct summand of a
model space" form — given [Bel]'s definition, compose `P ⊕ Q ≅ c_I(R)` with the
inclusion/projection of the summand; conversely take `Q := ker π`.  This avoids
quantifying over the complement `Q` (a universe issue in Lean).

The Fredholm determinant of a compact endomorphism of a (Pr) module is defined by
extension by zero to `P ⊕ Q`; independence of `Q` is a formal consequence of the trace
property `charPowerSeries_comm` ([Bel], discussion after Exercise II.1.19) — the matrix
side of that argument is a direct analogue of the extension-by-zero lemma of the Buzzard
blueprint, and formalising it here is part of the §II.2 TODO. -/

section Pr

variable {K}

/-- **[Bel] §II.1.6, property (Pr)** in direct-summand form: `P` is a continuous direct
summand of some model space `c_R(I)` (equivalently, of a potentially orthonormalizable
module — [Bel]'s `P ⊕ Q`). -/
def HasPr (P : Type*) [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P] : Prop :=
  ∃ (s : Set P) (ι : P →L[R] c(s, R)) (π : c(s, R) →L[R] P),
    π.comp ι = ContinuousLinearMap.id R P

variable {P : Type*} [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- Potentially orthonormalizable modules have property (Pr): an isomorphism onto a model
space exhibits `P` as a (trivial) direct summand. -/
theorem IsPotentiallyONable.hasPr (h : IsPotentiallyONable R P) : HasPr R P := by
  obtain ⟨s, ⟨e⟩⟩ := h
  refine ⟨s, (e : P →L[R] c(s, R)), (e.symm : c(s, R) →L[R] P), ?_⟩
  ext x
  simp

/-- **[Bel] Exercise II.1.19, forward direction** — property (Pr) as a lifting property:
a (Pr) module lifts continuous maps through continuous surjections of Banach `R`-modules.
(The Banach analogue of the defining property of projective modules; the converse
direction of [Bel]'s exercise needs "every Banach module is a quotient of some `c_R(I)`" —
TODO.)

*Proof sketch.*  A direct summand inherits the lifting property, so reduce to
`P = c_R(I)`: lift each basis vector — `α(eᵢ)` has a preimage of controlled norm by the
quantitative OMT (`exists_preimage_norm_le`) — and the resulting bounded family defines
`β` by `exists_coeffEquiv`. -/
theorem HasPr.exists_lift [IsUltrametricDist P] [CompleteSpace P] (hP : HasPr R P)
    {M N : Type*}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]
    [CompleteSpace M] [NormedSpace K M] [IsScalarTower K R M]
    [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [IsUltrametricDist N]
    [CompleteSpace N] [NormedSpace K N] [IsScalarTower K R N]
    (f : M →L[R] N) (hf : Function.Surjective f) (α : P →L[R] N) :
    ∃ β : P →L[R] M, f.comp β = α := by
  sorry

/-- **[Bel] Proposition II.1.20.**  A *finitely generated* module with property (Pr) is
projective.  ("(Pr) : Banach modules = projective : modules", made literal in the finite
case.)

*Proof sketch.*  Apply the lifting property to a surjection `Rʳ → P` and `α = id_P`: the
lift splits the surjection, exhibiting `P` as a direct summand of `Rʳ`. -/
theorem HasPr.projective [IsUltrametricDist P] [CompleteSpace P]
    (hP : HasPr R P) [Module.Finite R P] :
    Module.Projective R P := by
  sorry

/-- **[Bel] Proposition II.1.21 — the only statement in the whole Fredholm theory that
needs `R` Noetherian.**  If `P` has property (Pr) and carries a compact operator `u` with
`1 − u` nilpotent, then `P` is finitely generated and projective.  (The germ of the Riesz
decomposition of §II.2: generalized eigenspaces of compact operators are finite
projective.)

*Proof sketch.*  Expanding `(1 − u)ⁿ = 0` shows the *identity* of `P` is compact.  Embed
`P` as a direct summand of a model space `M`, extend `id_P` by zero to a compact `ũ` on
`M`, and truncate (Scholium II.1.10): a finite-rank projector approximates `ũ` within
`1/‖p‖`, forcing `P` to inject into a finitely generated module — Noetherianity makes `P`
itself finitely generated; projectivity follows from Proposition II.1.20. -/
theorem finite_projective_of_one_sub_compact_nilpotent [IsNoetherianRing R]
    [IsUltrametricDist P] [CompleteSpace P]
    (hP : HasPr R P) (u : P →L[R] P) (hu : IsCompletelyContinuous u)
    (hnil : ∃ n : ℕ, (ContinuousLinearMap.id R P - u) ^ n = 0) :
    Module.Finite R P ∧ Module.Projective R P := by
  sorry

end Pr

/-! ## §7  Extension of scalars, matrix-wise  ([Bel] II.1.7)

[Bel] §II.1.7 constructs the completed tensor product `M ⊗̂_R R'` and proves:
`c_I(R) ⊗̂_R R'` is `c_I(R')` up to equivalent norm (Lemma II.1.22); potential
orthonormalizability and (Pr) are stable under base change; and for `φ` compact on a (Pr)
module, `φ ⊗ 1` is compact with `det(1 − T(φ⊗1)) = ` the image of `det(1 − Tφ)` in
`R'{{T}}` (Lemma II.1.23) — the proof being simply that *the matrices agree*.  Serre's
Lemma II.1.24 (`𝒞(M, N) = M' ⊗̂ N` over a field) closes the section.

Pending `⊗̂` in Mathlib we state the matrix-wise content of Lemma II.1.23, which is what
the eigenvariety machine actually consumes: the base-changed operator is any operator over
`R'` whose matrix is `ψ` of the matrix of `u`. -/

section BaseChange

variable {K R}
variable (R' : Type*) [NormedCommRing R'] [NormedAlgebra K R'] [IsUltrametricDist R']
  [CompleteSpace R'] [NormOneClass R']
variable {I : Type*} [DecidableEq I]

/-- **[Bel] Lemma II.1.23, compactness half, matrix-wise**: if `v` over `R'` has matrix
`ψ(a_{i,j})` for a contractive ring homomorphism `ψ`, and `u` is compact, then `v` is
compact.

*Proof sketch.*  `r_j(v) ≤ r_j(u) → 0` by contractivity; apply Proposition II.1.9 twice. -/
theorem isCompletelyContinuous_baseChange (ψ : R →+* R') (hψ : ∀ r, ‖ψ r‖ ≤ ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, R') →L[R'] c(I, R'))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) :
    IsCompletelyContinuous v := by
  sorry

/-- **[Bel] Lemma II.1.23, determinant half, matrix-wise**: `cₙ(v) = ψ(cₙ(u))` when the
matrix of `v` is `ψ` of the matrix of `u`.

*Proof sketch.*  `ψ` commutes with the finite determinants (`RingHom.map_det`) and — being
contractive, hence continuous — with the `tsum` (`summable_minor` for `u`). -/
theorem charCoeff_baseChange (ψ : R →+* R') (hψ : ∀ r, ‖ψ r‖ ≤ ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, R') →L[R'] c(I, R'))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) (n : ℕ) :
    charCoeff v n = ψ (charCoeff u n) := by
  sorry

/-- **[Bel] Lemma II.1.23**, assembled: the Fredholm determinant commutes with base change
along contractive homomorphisms of Banach algebras, `det(1 − Tv) = ψ(det(1 − Tu))` in
`R'⟦T⟧`. -/
theorem charPowerSeries_baseChange (ψ : R →+* R') (hψ : ∀ r, ‖ψ r‖ ≤ ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, R') →L[R'] c(I, R'))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map ψ (charPowerSeries u) := by
  ext n
  simp [charCoeff_baseChange R' ψ hψ u hu v hv n, PowerSeries.coeff_map]

end BaseChange

end Eigenbook

end
