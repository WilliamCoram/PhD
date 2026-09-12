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

/-!
# Blueprint: compact operators over Banach–Tate rings, after Johansson–Newton

A **self-contained** Lean blueprint for the non-archimedean Fredholm theory of
**[JN, §2.1 "Fredholm determinants over Banach–Tate rings"]** — the third treatment of
compact operators in this project, alongside `PhD.Main.Test.CompactOperators` (Buzzard) and
`PhD.Main.Test.CompactOperatorsBellaiche` (Bellaïche's Eigenbook).  Statements are given in
full; proofs still to be formalised are `sorry`ed, each with a proof sketch and reference.

The point of [JN]'s setting: to extend eigenvarieties over the **boundary of weight
space**, the coefficient rings arising from affinoid opens of the adic weight space are
complete Tate rings of characteristic `p` or mixed characteristic — they need **not be
algebras over any nontrivially normed field**.  The rôle the ground field `K` (Buzzard) or
`ℚ_p` (Bellaïche) played — providing a scaling element for boundedness arguments — is
taken over by a **multiplicative pseudo-uniformizer `ϖ ∈ R` itself**: a multiplicative
*unit* of norm `< 1`.  [JN] describe their generality as "intermediate between [Buz07] and
[Col97]", and note that "the proofs in [Buz07] go through with little to no change".

## References

* [JN] C. Johansson, J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739v4 (Oct 2020; corrected version of the published paper — the correction
  concerns precisely Lemma 2.1.6 below).  §2.1 is the source for this file; §2.2–2.3
  (Riesz theory, slope decompositions, spectral varieties) are the TODO.
* [Buz07] K. Buzzard, *Eigenvarieties* — [JN] inherit its proofs, "using a multiplicative
  pseudo-uniformizer `ϖ` for what Buzzard calls `ρ`".
* [Col97] R. Coleman, *p-adic Banach spaces and families of modular forms* — a Banach–Tate
  ring is exactly a Banach algebra `A` with `|A^m| ≠ 1` in Coleman's sense
  ([JN, Remark 2.1.3(2)]).
* [AIP] F. Andreatta, A. Iovita, V. Pilloni, *Le halo spectral* (Annexe B) — the spectral
  variety input for [JN, §2.3].
* [AS] A. Ash, G. Stevens, unpublished — source of the slope-decomposition formalism of
  [JN, §2.2].
* [Hub93/94] R. Huber — Tate rings, and the open mapping theorem in this generality
  ([Hub94, Lemma 2.4(i)]).
* [KL15] K. Kedlaya, R. Liu — a multiplicative pseudo-uniformizer is a *uniform unit* in
  their sense ([JN, Remark 2.1.3]).

## Standing hypotheses

* `R` — a commutative nonarchimedean Banach ring:
  `[NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]`.
  Note `‖1‖ = 1` is **axiom (1) of [JN]'s Definition 2.1.1** of a seminorm, so
  `NormOneClass` is part of the definition here (not a convenience, not a consequence).
* **There is no ground field.**  Where the other two blueprints assume
  `[NormedAlgebra K A]`-style structure, this file assumes `[IsTate R]` — the existence of
  a multiplicative pseudo-uniformizer (`PseudoUniformizer`, Definition 2.1.2) — precisely
  where a scaling element is needed (boundedness, open mapping, the compactness
  criterion).
* **Noetherian hypotheses return**: [JN] inherit Buzzard's proofs, so the compactness
  criterion and the Fredholm-determinant theory carry `[IsNoetherianRing R]`
  (Definition 2.1.5 ff., Proposition 2.1.8).
* A **Banach `R`-module** `M` is the usual package `[NormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]`
  ([JN, Definition 2.1.4]).

## Differences from the other two blueprints

1. **No ground field anywhere.**  The typeclass signature contains no `K`; every statement
   that previously needed `[NormedSpace K M] [IsScalarTower K A M]` here needs `[IsTate R]`
   instead.  Boundedness of continuous maps ([JN, Def 2.1.4]: "continuity of an `R`-linear
   map is equivalent to boundedness" *for `R` Tate*) and the open mapping theorem (via
   [Hub94], not via a Banach field) are powered by `ϖ`-scaling — Buzzard's `ρ`-trick with
   `ϖ` for `ρ`.
2. **`‖1‖ = 1` is definitional** ([JN, Def 2.1.1(1)]); in the Buzzard file it was a
   convenience hypothesis, in the Bellaïche file a consequence of the `ℚ_p`-structure.
3. **Noetherian is back** (contrast Bellaïche, who removes it; the Buzzard file dropped it
   as unused up to the characteristic series): [JN] reuse Buzzard's proofs verbatim, so
   `isCompletelyContinuous_iff_rowNorm` and everything downstream of it carries
   `[IsNoetherianRing R]` here.
4. **ON-able is *defined* by isometry to the model space** ([JN, Def 2.1.5]): no `ONBasis`
   structure — the basis is the *derived* notion (the preimage of the canonical basis
   under the isometry).  This inverts Bellaïche, who defines the basis and proves the
   characterisation; the blueprint's Definition 6.6-style structure is absent here.
5. **Property (Pr) is verbatim "a direct summand of a potentially ON-able module"**
   ([JN, Def 2.1.5]) — of the three sources this is the closest to the
   direct-summand-of-model-space formulation all three files use in Lean.
6. **The norm-change theory is new material** with no analogue in the other two files:
   the distinction *equivalent* vs *bounded-equivalent* norms ([JN, Def 2.1.1]), the
   power-type comparison of equivalent Tate norms (Lemmas 2.1.6–2.1.7 — the subject of
   [JN]'s published-version erratum), and the invariance of (Pr), compactness and the
   Fredholm determinant under equivalent norm changes (Proposition 2.1.8).  A consequence
   worth noting: a bicontinuous ring isomorphism of Banach–Tate rings is in general only
   *power*-equivalent, not bounded — so the determinant's invariance under it
   (`charPowerSeries_map_equiv`) is a *topological* statement (summability transfer), not
   a special case of bounded base change.
7. **No truncation machinery and no lifting property**: the coordinate projections `π_S`
   and the (Pr)-as-projectivity results are Bellaïche's tools; [JN] simply defer to
   Buzzard's proofs.
8. **The valuation `v_ϖ`** attached to a pseudo-uniformizer ([JN, Def 2.1.2]) is recorded
   here (`PseudoUniformizer.val`): it is the bridge to Newton polygons and slopes in
   [JN, §2.2] — and hence to this project's `PhD/ToPR/NewtonPolygon.lean` and
   `DivValueGroup` API, which are the natural consumers of the TODO below.

## Dictionary ([JN] §2.1 ↔ Lean, this file)

| [JN]                                   | Lean                                        |
| --------------------------------------- | ------------------------------------------- |
| Def 2.1.1 (norms, bounded, mult. elts)  | standing instances; `IsMultiplicative`, `IsBoundedEquiv` |
| Def 2.1.2 (Banach–Tate, `v_ϖ`)          | `PseudoUniformizer`, `IsTate`, `PseudoUniformizer.val` |
| Def 2.1.4 (modules, Hom, opnorm, OMT)   | `instNorm`, `le_opNorm`, `norm_add_le`, `exists_lim_of_cauchySeq`, `exists_preimage_norm_le` |
| Noetherian ⟺ ideals closed (BGR §3.7.2) | `isNoetherianRing_iff_isClosed_ideal`       |
| Def 2.1.5 (`c_R(I)`, ON-able, (Pr))     | `cSpace` (`c(I, R)`), `IsONable`, `IsPotentiallyONable`, `HasPr` |
| Def 2.1.5 (finite rank, compact)        | `IsFiniteRank`, `IsCompletelyContinuous`    |
| [Buz07 2.3/2.4] criterion (Noetherian)  | `isCompletelyContinuous_iff_rowNorm`        |
| Lemma 2.1.6 (equivalent Tate norms)     | `norm_le_pow_of_equiv`                      |
| Lemma 2.1.7 (common uniformizer)        | `norm_comparison_of_common_uniformizer`     |
| Fredholm det ([Buz07 p.67] recipe)      | `minor`, `summable_minor`, `charCoeff`, `charPowerSeries` |
| `det(1−Tφ) ∈ R{{T}}`                    | `IsEntire`, `charPowerSeries_isEntire`      |
| [Buz07 2.5/2.6] (potential ON-bases)    | `charPowerSeries_conj`                      |
| [Buz07 pp.72–73] ((Pr) extension)       | `charPowerSeries_extendZero`                |
| Prop 2.1.8 (norm-invariance summary)    | `isCompletelyContinuous_map_equiv`, `charPowerSeries_map_equiv` |
| [Buz07 2.9/2.10] (base change)          | `isCompletelyContinuous_baseChange`, `charCoeff_baseChange`, `charPowerSeries_baseChange` |

## TODO / not in this file

* **[JN, §2.2] Riesz theory and slopes**: Fredholm series, multiplicative polynomials,
  relative primality via Coleman's resultant (Lemma 2.2.7), the Riesz decomposition
  (Theorem 2.2.2), the link lemma (Lemma 2.2.3), Newton polygons of Fredholm series w.r.t.
  `v_ϖ` and specialisation at Gelfand points (Def 2.2.4), slope-`≤ h` factorizations
  (Def 2.2.5), Ash–Stevens slope-`≤ h` decompositions of abstract modules
  (Defs 2.2.8–2.2.10) and their equivalence with factorizations (Theorem 2.2.13,
  Corollary 2.2.14).  The Newton-polygon side should be phrased against this project's
  `PhD/ToPR/NewtonPolygon.lean`; note also that [JN, §6]'s numerical slope estimates for
  controlling operators are of the same flavour as the arithmetic-progression slope
  statements of Jacobs' thesis that this project targets.
* **[JN, §2.3] spectral varieties**: Fredholm hypersurfaces `Z(F) ⊆ 𝔸¹_X` over adic
  spectra, slope data `(U, h)` — needs adic-space machinery far beyond this file.
* **[JN, Appendix A]**: the class of Tate rings appearing as local pieces of the extended
  eigenvarieties (Noetherian rings of definition, spectral seminorms, quasinilpotents).
* The `⊗̂`-form of base change, as in the other two blueprints.
-/

open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction

-- Blueprint file: hypotheses are stated at final generality even where a particular
-- `sorry`ed statement does not yet use them.
set_option linter.unusedSectionVars false

noncomputable section

namespace JohanssonNewton

/-! ## §0  The index type -/

/-- `Ix I` is `I` regarded as a discrete topological space (the index set of an orthonormal
basis). -/
def Ix (I : Type*) : Type _ := I

instance {I : Type*} : TopologicalSpace (Ix I) := ⊥
instance {I : Type*} : DiscreteTopology (Ix I) := ⟨rfl⟩
instance {I : Type*} [DecidableEq I] : DecidableEq (Ix I) := inferInstanceAs (DecidableEq I)

/-! ## §1  Banach–Tate rings  ([JN] Definitions 2.1.1–2.1.2, Remark 2.1.3)

[JN] Definition 2.1.1 (seminorm on a ring: `‖0‖ = 0`, `‖1‖ = 1`, ultrametric,
submultiplicative; norm if definite; Banach if complete) is our standing instance package.
The genuinely new definitions are multiplicativity, pseudo-uniformizers and the Tate
condition — the structure that replaces the ground field of the other two blueprints. -/

section Tate

variable {A : Type*} [NormedRing A]

/-- **[JN] Definition 2.1.1.**  An element `a` of a normed ring is *multiplicative* if
`‖ax‖ = ‖a‖‖x‖` for all `x`.  (E.g. every element of `ℚ_p^×` is multiplicative in a
`ℚ_p`-Banach algebra — which is how the other two blueprints secretly used this notion.) -/
def IsMultiplicative (a : A) : Prop :=
  ∀ x : A, ‖a * x‖ = ‖a‖ * ‖x‖

/-- **[JN] Definition 2.1.2.**  A *multiplicative pseudo-uniformizer* of a normed ring: a
multiplicative **unit** `ϖ` with `‖ϖ‖ < 1`.  This is a *uniform unit* in the sense of
Kedlaya–Liu ([JN, Remark 2.1.3]); it is the scaling element that replaces the ground
field. -/
structure PseudoUniformizer (A : Type*) [NormedRing A] where
  /-- the underlying unit -/
  unit : Aˣ
  /-- topological nilpotence: `‖ϖ‖ < 1` -/
  norm_lt_one : ‖(unit : A)‖ < 1
  /-- multiplicativity: `‖ϖ x‖ = ‖ϖ‖ ‖x‖` -/
  isMultiplicative : IsMultiplicative (unit : A)

instance : CoeHead (PseudoUniformizer A) A := ⟨fun ϖ => ϖ.unit⟩

/-- A pseudo-uniformizer has positive norm (it is a unit, hence nonzero, and the norm is
definite; nontriviality of `A` comes from `‖1‖ = 1 ≠ 0`). -/
theorem PseudoUniformizer.norm_pos (ϖ : PseudoUniformizer A) : 0 < ‖(ϖ : A)‖ := by
  sorry

/-- **[JN, after Definition 2.1.2].**  A unit `ϖ` is multiplicative if and only if
`‖ϖ⁻¹‖ = ‖ϖ‖⁻¹`.

*Proof sketch.*  (⇒) apply multiplicativity to `x = ϖ⁻¹` and use `‖1‖ = 1`; (⇐) sandwich
`‖x‖ = ‖ϖ⁻¹(ϖx)‖ ≤ ‖ϖ‖⁻¹‖ϖx‖` against submultiplicativity. -/
theorem isMultiplicative_unit_iff (u : Aˣ) :
    IsMultiplicative (u : A) ↔ ‖((u⁻¹ : Aˣ) : A)‖ = ‖(u : A)‖⁻¹ := by
  sorry

/-- **[JN] Definition 2.1.2.**  A normed ring is *Tate* if it admits a multiplicative
pseudo-uniformizer.  Complete + Tate = **Banach–Tate**.  This `Prop`-class is the standing
hypothesis that replaces `[NormedAlgebra K R]` of the other two blueprints. -/
class IsTate (A : Type*) [NormedRing A] : Prop where
  nonempty_pseudoUniformizer : Nonempty (PseudoUniformizer A)

/-- **[JN] Definition 2.1.2.**  The additive valuation `v_ϖ(r) = −log_a ‖r‖` (where
`a = ‖ϖ⁻¹‖ = ‖ϖ‖⁻¹`) attached to a pseudo-uniformizer, normalised so that `v_ϖ(ϖ) = 1`.
This is the bridge to the Newton-polygon and slope theory of [JN, §2.2] — cf. this
project's `DivValueGroup` and `NewtonPolygon` files, which develop exactly this
multiplicative ⇔ additive dictionary over a field. -/
def PseudoUniformizer.val (ϖ : PseudoUniformizer A) (r : A) : ℝ :=
  -(Real.log ‖r‖ / Real.log ‖(ϖ : A)‖⁻¹)

/-- Normalisation: `v_ϖ(ϖ) = 1`. -/
@[simp] theorem PseudoUniformizer.val_self (ϖ : PseudoUniformizer A) :
    ϖ.val (ϖ : A) = 1 := by
  sorry

/-- **[JN] Definition 2.1.1.**  Two norms are *bounded-equivalent* if each linearly bounds
the other — phrased here for a ring isomorphism onto a second normed ring carrying the
other norm.  This is **strictly stronger** than topological equivalence (cf.
Lemma 2.1.6 = `norm_le_pow_of_equiv`: equivalent Tate norms are in general only
*power*-comparable). -/
def IsBoundedEquiv {B : Type*} [NormedRing B] (e : A ≃+* B) : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ ∀ a : A, C₁ * ‖a‖ ≤ ‖e a‖ ∧ ‖e a‖ ≤ C₂ * ‖a‖

end Tate

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

/-! ## §2  Banach modules and `Hom_R(M, N)`  ([JN] Definition 2.1.4)

[JN] Definition 2.1.4 (normed `R`-module: ultrametric, `‖rm‖ ≤ ‖r‖‖m‖`) is our standing
package; note their remark that `‖rm‖ = ‖r‖‖m‖` when `r` is a multiplicative unit — the
`ϖ`-scaling identity powering everything below.  For `R` **Tate**, continuity of an
`R`-linear map is equivalent to boundedness, `Hom_{R,cts}(M,N)` is a normed (Banach)
`R`-module for the operator norm, and the open mapping theorem holds ([Hub94,
Lemma 2.4(i)]).  Mathlib has none of this over a normed ring (its operator norm and OMT
require `NontriviallyNormedField` scalars) — a genuine gap this section records. -/

section Modules

variable {R}
variable {M N : Type*}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- **[JN] Definition 2.1.4, remark.**  Multiplicative units scale norms exactly:
`‖ϖ • m‖ = ‖ϖ‖ ‖m‖`.

*Proof sketch.*  `‖m‖ = ‖ϖ⁻¹ • ϖ • m‖ ≤ ‖ϖ⁻¹‖‖ϖ • m‖` and `‖ϖ⁻¹‖ = ‖ϖ‖⁻¹`
(`isMultiplicative_unit_iff`). -/
theorem norm_pseudoUniformizer_smul (ϖ : PseudoUniformizer R) (m : M) :
    ‖(ϖ : R) • m‖ = ‖(ϖ : R)‖ * ‖m‖ := by
  sorry

/-- **[JN] Definition 2.1.4.**  The operator norm on `Hom_{R,cts}(M, N)`:
`|φ| = sup_{m ≠ 0} ‖φ(m)‖/‖m‖`, realised as the usual `sInf` of bounds.  Scoped instance,
as in the other blueprints, to avoid competing global `Norm` instances. -/
scoped instance instNorm : Norm (M →L[R] N) :=
  ⟨fun u => sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}⟩

theorem norm_def (u : M →L[R] N) :
    ‖u‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖} := rfl

variable [IsTate R]

/-- **[JN] Definition 2.1.4**: over a Tate ring, continuous `R`-linear maps are bounded,
with the fundamental estimate `‖u x‖ ≤ ‖u‖ ‖x‖`.  This is where `[IsTate R]` replaces the
ground field of the other two blueprints.

*Proof sketch* (Buzzard's `ρ`-trick with `ϖ` for `ρ`).  By continuity at `0` pick `δ` with
`‖y‖ ≤ δ → ‖u y‖ ≤ 1`; given `x ≠ 0` choose `n : ℤ` with `δ‖ϖ‖ < ‖ϖ^n x‖ ≤ δ` (possible
since `‖ϖ^n x‖ = ‖ϖ‖^n ‖x‖` by `norm_pseudoUniformizer_smul` and `‖ϖ‖ < 1`), so
`‖u x‖ = ‖ϖ‖^{-n}‖u(ϖ^n x)‖ ≤ ‖ϖ‖^{-n} ≤ (δ‖ϖ‖)⁻¹ ‖x‖`. -/
theorem le_opNorm (u : M →L[R] N) (x : M) : ‖u x‖ ≤ ‖u‖ * ‖x‖ := by
  sorry

/-- Subadditivity of the operator norm.

*Proof sketch.*  From `le_opNorm` and the `sInf` description. -/
theorem norm_add_le (u v : M →L[R] N) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  sorry

/-- **[JN] Definition 2.1.4**: `Hom_{R,cts}(M, N)` is a Banach `R`-module for the operator
norm — completeness, phrased metrically.

*Proof sketch.*  Operator-norm Cauchy ⇒ pointwise Cauchy (`le_opNorm`) ⇒ pointwise limit,
which is `R`-linear and bounded; convergence in operator norm by the usual `ε/3`. -/
theorem exists_lim_of_cauchySeq [CompleteSpace N] (u : ℕ → M →L[R] N)
    (hu : ∀ ε > 0, ∃ M₀, ∀ m n, M₀ ≤ m → M₀ ≤ n → ‖u m - u n‖ < ε) :
    ∃ v : M →L[R] N, Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
  sorry

/-- **Quantitative Open Mapping Theorem over a Banach–Tate ring** ([JN] Definition 2.1.4:
"The open mapping theorem holds in this context; see [Hub94, Lemma 2.4(i)]").  Note the
contrast with the other two blueprints, where this came from Mathlib's Banach theorem over
the ground field: here it must be proven from Baire + `ϖ`-scaling — a genuine Mathlib
gap. -/
theorem exists_preimage_norm_le [CompleteSpace M] [CompleteSpace N]
    (f : M →L[R] N) (hf : Function.Surjective f) :
    ∃ C > 0, ∀ n : N, ∃ m : M, f m = n ∧ ‖m‖ ≤ C * ‖n‖ := by
  sorry

end Modules

/-- **[JN, after Definition 2.1.4]** (BGR §3.7.2 over Banach–Tate rings): a Banach–Tate
ring is Noetherian if and only if all its ideals are closed.  ([JN] use the Noetherian
theory of BGR §3.7.2–3.7.3 — canonical topologies on finite modules, automatic continuity
— "with the same proofs, thanks to the open mapping theorem".)

*Proof sketch.*  (⇒) an ideal of a Noetherian Banach–Tate ring is the image of a
continuous surjection `Rⁿ → I ⊆ R`, and OMT-type arguments show it is strict, hence
closed.  (⇐) BGR's argument. -/
theorem isNoetherianRing_iff_isClosed_ideal [IsTate R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, IsClosed (I : Set R) := by
  sorry

/-! ## §3  The model space, ON-able modules, property (Pr)  ([JN] Definition 2.1.5)

[JN] *define* (potentially) ON-able by (isometric) isomorphism to `c_R(I)` — the basis is
the derived notion (the preimage of `{eᵢ}`).  Property (Pr) is verbatim "a direct summand
of a potentially ON-able Banach `R`-module"; as in the other blueprints we realise the
ambient module as a model space to avoid quantifying over it. -/

/-- **[JN] Definition 2.1.5.**  `cSpace R I` (notation: `c(I, R)`) is the Banach
`R`-module `c_R(I)` of families `(rᵢ)_{i ∈ I}` tending to `0` along the cofinite filter,
with the sup norm — realised as Mathlib's `C₀(Ix I, R)` on the discrete index. -/
def cSpace (I : Type*) : Type _ := C₀(Ix I, R)

@[inherit_doc] scoped notation "c(" I ", " R ")" => cSpace R I

namespace cSpace

variable {R}
variable {I J : Type*}

instance : NormedAddCommGroup c(I, R) :=
  inferInstanceAs (NormedAddCommGroup C₀(Ix I, R))

instance : Module R c(I, R) :=
  inferInstanceAs (Module R C₀(Ix I, R))

instance : CompleteSpace c(I, R) :=
  inferInstanceAs (CompleteSpace C₀(Ix I, R))

instance : FunLike c(I, R) I R :=
  inferInstanceAs (FunLike C₀(Ix I, R) (Ix I) R)

/-- The `R`-action on `c_R(I)` is bounded.

*Proof sketch.*  Pointwise from `norm_mul_le` and `norm_eq_iSup`. -/
instance : IsBoundedSMul R c(I, R) :=
  .of_norm_smul_le fun _ _ => by sorry

/-- Membership in `c_R(I)`: the family tends to `0` along the cofinite filter
("the filter of subsets of `I` with finite complement", [JN] Definition 2.1.5). -/
theorem tendsto_cofinite (f : c(I, R)) : Tendsto (f : I → R) cofinite (𝓝 0) := by
  have h := (f : C₀(Ix I, R)).zero_at_infty'
  rwa [Filter.cocompact_eq_cofinite] at h

/-- The sup-norm formula `‖f‖ = ⨆ i, ‖f i‖` ([JN] Definition 2.1.5).

*Proof sketch.*  Unfold the `BoundedContinuousFunction` norm. -/
theorem norm_eq_iSup (f : c(I, R)) : ‖f‖ = ⨆ i : I, ‖f i‖ := by
  sorry

/-- The ultrametric inequality for the sup norm.

*Proof sketch.*  Pointwise from `IsUltrametricDist R` and `norm_eq_iSup`. -/
instance : IsUltrametricDist c(I, R) := by
  sorry

section single

variable [DecidableEq I]

/-- The canonical basis vector `eᵢ = (δᵢⱼ)ⱼ` scaled by `r` ([JN] Definition 2.1.5). -/
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

/-- `‖eᵢ‖ = 1` — here a direct consequence of [JN]'s axiom `‖1‖ = 1` (Def 2.1.1(1)).

*Proof sketch.*  By `norm_eq_iSup`, a sup of `0`s and a single `1`. -/
@[simp] theorem norm_single_one (i : I) : ‖single i (1 : R)‖ = 1 := by
  sorry

end single

end cSpace

section ONable

variable (M : Type*) [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- **[JN] Definition 2.1.5.**  `M` is *orthonormalisable* (ON-able) if it is `R`-linearly
**isometric** to some `c_R(I)`.  Note this is the *definition* here — the ON-basis (the
preimage of `{eᵢ}` under such an isometry) is the derived notion, inverting the order of
the Bellaïche blueprint.  (Index sets may be taken to be subsets of `M`: the basis vectors
are distinct.) -/
def IsONable : Prop :=
  ∃ s : Set M, Nonempty (M ≃ₗᵢ[R] c(s, R))

/-- **[JN] Definition 2.1.5.**  `M` is *potentially ON-able* if it is `R`-linearly
**homeomorphic** to some `c_R(I)` (isomorphic as topological modules — "merely
`R`-linearly homeomorphic"). -/
def IsPotentiallyONable : Prop :=
  ∃ s : Set M, Nonempty (M ≃L[R] c(s, R))

/-- **[JN] Definition 2.1.5.**  `M` has *property (Pr)* if it is a direct summand of a
potentially ON-able Banach `R`-module — realised, as in the other blueprints, as a
continuous direct summand of a model space (compose with the potential ON-structure of
the ambient module; conversely take the kernel of the projector as the complement). -/
def HasPr : Prop :=
  ∃ (s : Set M) (ι : M →L[R] c(s, R)) (π : c(s, R) →L[R] M),
    π.comp ι = ContinuousLinearMap.id R M

variable {R M}

/-- ON-able modules are potentially ON-able (an isometry is in particular a
homeomorphism). -/
theorem IsONable.isPotentiallyONable (h : IsONable R M) : IsPotentiallyONable R M := by
  obtain ⟨s, ⟨e⟩⟩ := h
  exact ⟨s, ⟨e.toContinuousLinearEquiv⟩⟩

/-- Potentially ON-able modules have property (Pr) (a direct summand of themselves). -/
theorem IsPotentiallyONable.hasPr (h : IsPotentiallyONable R M) : HasPr R M := by
  obtain ⟨s, ⟨e⟩⟩ := h
  refine ⟨s, (e : M →L[R] c(s, R)), (e.symm : c(s, R) →L[R] M), ?_⟩
  ext x
  simp

/-- The model space is ON-able ([JN] Definition 2.1.5, implicitly: the identity is an
isometry).  The content is re-indexing `I` by the subset `{eᵢ} ⊆ c_R(I)`.

*Proof sketch.*  `i ↦ single i 1` is injective (`1 ≠ 0` since `‖1‖ = 1`), and re-indexing
a `C₀`-space along a bijection of discrete index sets is an isometric equivalence. -/
theorem isONable_cSpace {I : Type*} [DecidableEq I] : IsONable R c(I, R) := by
  sorry

end ONable

/-! ### Matrices  ([JN] Definition 2.1.5, citing [Buz07, p. 65]) -/

section Matrix

variable {R}
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- The matrix coefficient of `u : c_R(I) → c_R(J)` in the canonical bases:
`matrixCoeff u j i = (u eᵢ)_j` — [JN]'s `a_{ij}` (matrix "as on [Buz07, p. 65]"). -/
def matrixCoeff (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) : R :=
  u (cSpace.single i 1) j

/-- Columns decay: for fixed `i`, `(u eᵢ)_j → 0` cofinitely in `j`. -/
theorem tendsto_matrixCoeff_column (u : c(I, R) →L[R] c(J, R)) (i : I) :
    Tendsto (fun j => matrixCoeff u j i) cofinite (𝓝 0) :=
  cSpace.tendsto_cofinite (u (cSpace.single i 1))

/-- `‖u‖ = sup_{i,j} ‖a_{ij}‖` ([Buz07, p. 65], valid over Banach–Tate rings per [JN]).

*Proof sketch.*  `≥` from `le_opNorm` and `norm_single_one`; `≤` by expanding along the
canonical basis and estimating ultrametrically. -/
theorem norm_eq_iSup_matrixCoeff [IsTate R] (u : c(I, R) →L[R] c(J, R)) :
    ‖u‖ = ⨆ j : J, ⨆ i : I, ‖matrixCoeff u j i‖ := by
  sorry

/-- The row sup `r_j(u) = sup_i ‖a_{ij}‖`, whose decay characterises compactness. -/
def rowNorm (u : c(I, R) →L[R] c(J, R)) (j : J) : ℝ :=
  ⨆ i : I, ‖matrixCoeff u j i‖

end Matrix

/-! ## §4  Finite rank and compact operators  ([JN] Definition 2.1.5) -/

section Compact

variable {R}
variable {M N P : Type*}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- **[JN] Definition 2.1.5.**  `φ` has *finite rank* if its image is contained in a
finitely generated submodule. -/
def IsFiniteRank (u : M →L[R] N) : Prop :=
  ∃ Q : Submodule R N, Q.FG ∧ LinearMap.range (u : M →ₗ[R] N) ≤ Q

/-- **[JN] Definition 2.1.5.**  `φ` is *compact* (*completely continuous*) if it is a
limit of finite-rank operators in `Hom_{R,cts}(M, N)` — phrased metrically, as in the
other blueprints. -/
def IsCompletelyContinuous (u : M →L[R] N) : Prop :=
  ∀ ε > 0, ∃ v : M →L[R] N, IsFiniteRank v ∧ ‖u - v‖ < ε

theorem IsFiniteRank.isCompletelyContinuous {u : M →L[R] N} (hu : IsFiniteRank u) :
    IsCompletelyContinuous u := by
  intro ε hε
  refine ⟨u, hu, ?_⟩
  sorry -- `‖u - u‖ = ‖0‖ = 0 < ε`.

/-- Post-composition preserves finite rank (image lands in the image of a f.g.
submodule). -/
theorem IsFiniteRank.comp_left {u : M →L[R] N} (hu : IsFiniteRank u) (f : N →L[R] P) :
    IsFiniteRank (f.comp u) := by
  obtain ⟨Q, hQ, hle⟩ := hu
  refine ⟨Q.map (f : N →ₗ[R] P), hQ.map _, ?_⟩
  rintro x ⟨m, rfl⟩
  exact Submodule.mem_map_of_mem (hle ⟨m, rfl⟩)

/-- Pre-composition preserves finite rank (range shrinks). -/
theorem IsFiniteRank.comp_right {u : M →L[R] N} (hu : IsFiniteRank u) (f : P →L[R] M) :
    IsFiniteRank (u.comp f) := by
  obtain ⟨Q, hQ, hle⟩ := hu
  refine ⟨Q, hQ, ?_⟩
  rintro x ⟨m, rfl⟩
  exact hle ⟨f m, rfl⟩

/-- Compacts are a two-sided ideal, post-composition half ([JN] inherit this from
[Buz07]).

*Proof sketch.*  `‖f∘u − f∘v‖ ≤ ‖f‖‖u − v‖` via `le_opNorm` (whence `[IsTate R]`). -/
theorem IsCompletelyContinuous.comp_left [IsTate R] {u : M →L[R] N}
    (hu : IsCompletelyContinuous u) (f : N →L[R] P) :
    IsCompletelyContinuous (f.comp u) := by
  sorry

/-- Compacts are a two-sided ideal, pre-composition half. -/
theorem IsCompletelyContinuous.comp_right [IsTate R] {u : M →L[R] N}
    (hu : IsCompletelyContinuous u) (f : P →L[R] M) :
    IsCompletelyContinuous (u.comp f) := by
  sorry

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- **[JN] Definition 2.1.5, the compactness criterion** ([Buz07, Lemma 2.3, Prop 2.4]
"go through with the same proofs, using a multiplicative pseudo-uniformizer `ϖ` for what
Buzzard calls `ρ`"): for **`R` Noetherian** Banach–Tate, an operator between model modules
is compact iff `lim_j sup_i ‖a_{ij}‖ = 0`.

Note both hypotheses: `[IsTate R]` powers the scaling in Buzzard's proof, and
`[IsNoetherianRing R]` is where [JN] genuinely restrict — contrast the Bellaïche
blueprint, where the Noetherian hypothesis is eliminated (via the truncation/OMT route). -/
theorem isCompletelyContinuous_iff_rowNorm [IsTate R] [IsNoetherianRing R]
    (u : c(I, R) →L[R] c(J, R)) :
    IsCompletelyContinuous u ↔ Tendsto (rowNorm u) cofinite (𝓝 0) := by
  sorry

end Compact

/-! ## §5  Changing the norm  ([JN] Lemmas 2.1.6–2.1.7)

New material relative to the other two blueprints.  [JN] need to know their theory is
insensitive to the choice of norm inducing the intrinsic topology of a complete Tate ring
— but two equivalent Tate norms need **not** be bounded-equivalent: the honest comparison
is of *power type*, `‖a‖' ≍ ‖a‖^s`.  (Lemma 2.1.6 is the statement corrected in [JN]'s
erratum to the published version.)  We phrase "two norms on the same ring" as a ring
isomorphism `e : R ≃+* S` that is a homeomorphism, `‖·‖` and `‖e ·‖` being the two
norms. -/

section NormChange

variable {R}
variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [NormOneClass S]

/-- **[JN] Lemma 2.1.6.**  Let `‖·‖_ϖ` and `‖·‖_π` be two equivalent norms on a complete
Tate ring, with pseudo-uniformizers `ϖ` (for the first) and `π` (for the second).  Then
there are `C₁, C₂, s > 0` such that `‖a‖_ϖ ≤ C₁` whenever `‖a‖_π < 1`, and
`‖a‖_ϖ ≤ C₂ ‖a‖_π^s` whenever `‖a‖_π ≥ 1`.

*Proof sketch* ([JN]).  Equivalence gives `D₁ < 1` with `‖a‖_π ≤ D₁ → ‖a‖_ϖ ≤ 1`; pick
`m` with `‖ϖ^m‖_π ≤ D₁` and set `C₁ = ‖ϖ‖_ϖ^{-m}`; for the second bound scale `a` by the
power `n ≈ log‖a‖_π / log‖ϖ^m‖_π^{-1}` of `ϖ^m` into the unit ball and use
multiplicativity of `ϖ` for `‖·‖_ϖ`. -/
theorem norm_le_pow_of_equiv (e : R ≃+* S) (he : Continuous (e : R → S))
    (he' : Continuous (e.symm : S → R))
    (ϖ : PseudoUniformizer R) (π : PseudoUniformizer S) :
    ∃ C₁ C₂ s : ℝ, 0 < s ∧ (∀ a : R, ‖e a‖ < 1 → ‖a‖ ≤ C₁) ∧
      ∀ a : R, 1 ≤ ‖e a‖ → ‖a‖ ≤ C₂ * ‖e a‖ ^ s := by
  sorry

/-- **[JN] Lemma 2.1.7.**  If moreover the *same* pseudo-uniformizer is multiplicative for
both norms (i.e. `e ϖ` is a multiplicative pseudo-uniformizer for the second norm), the
comparison is two-sided of pure power type:
`C₁ ‖a‖^s ≤ ‖e a‖ ≤ C₂ ‖a‖^s`, with `s` pinned down by `‖e ϖ‖ = ‖ϖ‖^s`.  (In particular,
if additionally `‖e ϖ‖ = ‖ϖ‖` then `s = 1` and the norms are bounded-equivalent.)

*Proof sketch* ([JN]).  Same scaling argument in both directions. -/
theorem norm_comparison_of_common_uniformizer (e : R ≃+* S)
    (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (ϖ : PseudoUniformizer R)
    (hmul : IsMultiplicative (e (ϖ : R)))
    (hlt : ‖e (ϖ : R)‖ < 1) :
    ∃ C₁ C₂ s : ℝ, 0 < C₁ ∧ 0 < s ∧
      ∀ a : R, C₁ * ‖a‖ ^ s ≤ ‖e a‖ ∧ ‖e a‖ ≤ C₂ * ‖a‖ ^ s := by
  sorry

end NormChange

/-! ## §6  The Fredholm determinant
([JN] Definition 2.1.5 ff.: the recipe of [Buz07, p. 67], `R{{T}}`, [Buz07, Lemma
2.5–Corollary 2.10] over Noetherian Banach–Tate rings, Proposition 2.1.8)

The coefficients are the usual convergent sums of principal minors of the matrix
`(a_{ij})`.  Per [JN], the whole §6 stands under the standing hypotheses
**`[IsTate R]` and `[IsNoetherianRing R]`** — the second is genuinely used (via the
compactness criterion) in [JN]'s citations of Buzzard's proofs. -/

section Fredholm

variable {R}
variable {I : Type*} [DecidableEq I]

/-- The principal `S × S` minor of the matrix of `u`. -/
def minor (u : c(I, R) →L[R] c(I, R)) (S : Finset I) : R :=
  Matrix.det (Matrix.of fun j i : S => matrixCoeff u j i)

/-- Summability of the degree-`n` minors of a compact operator ([Buz07, p. 67] recipe,
valid over Noetherian Banach–Tate rings per [JN]).

*Proof sketch.*  Row decay from `isCompletelyContinuous_iff_rowNorm` (whence the two
standing hypotheses) plus the ultrametric Hadamard bound `‖minor u S‖ ≤ ∏_{j∈S} r_j(u)`. -/
theorem summable_minor [IsTate R] [IsNoetherianRing R]
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u) (n : ℕ) :
    Summable fun S : {S : Finset I // S.card = n} => minor u (S : Finset I) := by
  sorry

/-- The `n`-th coefficient of the Fredholm determinant, `cₙ = (−1)ⁿ ∑_{|S| = n} det`
of the principal minors ([Buz07, p. 67]). -/
def charCoeff (u : c(I, R) →L[R] c(I, R)) (n : ℕ) : R :=
  (-1 : R) ^ n * ∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)

/-- **[JN] Definition 2.1.5 ff.**  The *characteristic power series*, or *Fredholm
determinant*, `det(1 − Tφ) ∈ R⟦T⟧` of a compact operator on a model module. -/
def charPowerSeries (u : c(I, R) →L[R] c(I, R)) : PowerSeries R :=
  PowerSeries.mk (charCoeff u)

@[simp] theorem charPowerSeries_coeff (u : c(I, R) →L[R] c(I, R)) (n : ℕ) :
    PowerSeries.coeff n (charPowerSeries u) = charCoeff u n :=
  PowerSeries.coeff_mk n _

/-- `c₀ = 1`: the Fredholm determinant is a *Fredholm series* in the sense of
[JN, Definition 2.2.1] (constant term `1`). -/
@[simp] theorem charCoeff_zero (u : c(I, R) →L[R] c(I, R)) : charCoeff u 0 = 1 := by
  sorry

/-- **[JN]**: `R{{T}} = {∑ aₙTⁿ ∈ R⟦T⟧ : ‖aₙ‖Mⁿ → 0 ∀ M ∈ ℝ_{≥0}}`, the ring of entire
power series. -/
def IsEntire (F : PowerSeries R) : Prop :=
  ∀ C : ℝ, 0 < C → Tendsto (fun n => ‖PowerSeries.coeff n F‖ * C ^ n) atTop (𝓝 0)

/-- **[JN]**: "one sees that `det(1 − Tu) ∈ R{{T}}`" — the Fredholm determinant is
entire. -/
theorem charPowerSeries_isEntire [IsTate R] [IsNoetherianRing R]
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u) :
    IsEntire (charPowerSeries u) := by
  sorry

/-- **[JN]** (citing [Buz07, Lemma 2.5, Corollary 2.6], valid over Noetherian Banach–Tate
rings): the Fredholm determinant is insensitive to conjugation by a continuous `R`-linear
isomorphism — hence "the notion extends to compact operators on potentially ON-able `M`,
and may be computed using a potential ON-basis". -/
theorem charPowerSeries_conj [IsTate R] [IsNoetherianRing R] {J : Type*} [DecidableEq J]
    (φ : c(I, R) ≃L[R] c(J, R)) (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompletelyContinuous u) :
    charPowerSeries (((φ : c(I, R) →L[R] c(J, R)).comp u).comp
        (φ.symm : c(J, R) →L[R] c(I, R)))
      = charPowerSeries u := by
  sorry

/-- **[JN]** (citing [Buz07, pp. 72–73]): extension by zero does not change the Fredholm
determinant — the matrix-wise ingredient (with `charPowerSeries_conj`) for the
well-definedness of `det(1 − Tφ)` on modules with property (Pr), i.e. for
Proposition 2.1.8. -/
theorem charPowerSeries_extendZero [IsTate R] [IsNoetherianRing R]
    {J : Type*} [DecidableEq J]
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I ⊕ J, R) →L[R] c(I ⊕ J, R))
    (hII : ∀ j i, matrixCoeff v (Sum.inl j) (Sum.inl i) = matrixCoeff u j i)
    (hJrow : ∀ j q, matrixCoeff v (Sum.inr j) q = 0)
    (hJcol : ∀ p j, matrixCoeff v p (Sum.inr j) = 0) :
    charPowerSeries v = charPowerSeries u := by
  sorry

end Fredholm

/-! ### Invariance under equivalent norms, and base change
([JN] Proposition 2.1.8; [Buz07, Corollaries 2.9, 2.10])

Proposition 2.1.8 summarises: over a Noetherian Banach–Tate ring, a compact `φ` on a (Pr)
module has a well-defined Fredholm determinant, **unchanged if the norms on `(R, M)` are
replaced by equivalent ones**.  Matrix-wise, the norm-invariance is the statement
`charPowerSeries_map_equiv` below for a bicontinuous ring isomorphism `e`.  Note the
subtlety from §5: `e` is in general only *power*-comparable (Lemma 2.1.6), **not**
bounded — so this is *not* a special case of the bounded base change
(`charPowerSeries_baseChange`); its proof is topological (summability is a topological
notion, and the minors match termwise). -/

section BaseChange

variable {R}
variable (S : Type*) [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [NormOneClass S]
variable {I : Type*} [DecidableEq I]

/-- Norm-invariance of compactness ([JN] Proposition 2.1.8): if `e : R ≃+* S` is a
bicontinuous ring isomorphism (two equivalent norms on one Tate ring) and `v` has matrix
`e(a_{ij})`, then `v` is compact when `u` is.

*Proof sketch.*  Row decay is topological: `e` maps null families to null families. -/
theorem isCompletelyContinuous_map_equiv [IsTate R] [IsNoetherianRing R] [IsTate S]
    (e : R ≃+* S) (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = e (matrixCoeff u j i)) :
    IsCompletelyContinuous v := by
  sorry

/-- Norm-invariance of the Fredholm determinant ([JN] Proposition 2.1.8):
`det(1 − Tv) = e(det(1 − Tu))` for a bicontinuous ring isomorphism `e` relating the
matrices.

*Proof sketch.*  `e` commutes with the finite determinants and — being a homeomorphism —
with the `tsum` (`summable_minor` for `u`, transported topologically; the power-type
bounds of Lemma 2.1.6 are what guarantee `e` interacts with entireness). -/
theorem charPowerSeries_map_equiv [IsTate R] [IsNoetherianRing R] [IsTate S]
    (e : R ≃+* S) (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = e (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map (e : R →+* S) (charPowerSeries u) := by
  sorry

/-- Base change along a **bounded** homomorphism ([JN, Definition 2.1.1]; [Buz07,
Corollary 2.9] "holds over Noetherian Banach–Tate rings"), compactness half: if
`ψ : R → S` is bounded (`‖ψ r‖ ≤ C‖r‖`) and `v` has matrix `ψ(a_{ij})`, then `v` is
compact when `u` is.

*Proof sketch.*  `r_j(v) ≤ C · r_j(u) → 0`. -/
theorem isCompletelyContinuous_baseChange [IsTate R] [IsNoetherianRing R] [IsTate S]
    [IsNoetherianRing S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) :
    IsCompletelyContinuous v := by
  sorry

/-- Base change along a bounded homomorphism ([Buz07, Corollary 2.10] over Noetherian
Banach–Tate rings), coefficientwise: `cₙ(v) = ψ(cₙ(u))`.

*Proof sketch.*  `ψ` commutes with finite determinants (`RingHom.map_det`) and, being
bounded hence continuous, with the `tsum`. -/
theorem charCoeff_baseChange [IsTate R] [IsNoetherianRing R] [IsTate S]
    [IsNoetherianRing S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) (n : ℕ) :
    charCoeff v n = ψ (charCoeff u n) := by
  sorry

/-- Base change along a bounded homomorphism, assembled:
`det(1 − Tv) = ψ(det(1 − Tu))` in `S⟦T⟧`. -/
theorem charPowerSeries_baseChange [IsTate R] [IsNoetherianRing R] [IsTate S]
    [IsNoetherianRing S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map ψ (charPowerSeries u) := by
  ext n
  simp [charCoeff_baseChange S ψ C hψ u hu v hv n, PowerSeries.coeff_map]

end BaseChange

end JohanssonNewton

end
