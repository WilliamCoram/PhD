# Roadmap: Newton polygons of polynomials and power series

This roadmap develops the Newton polygon of a polynomial or a power series over a nonarchimedean
field: the lower convex hull of the points `(i, v aᵢ)` cut out by the additive valuations of the
coefficients, the slopes that hull carries, and what those slopes say about roots, zeros and
convergence. Three results are the headline milestones.

```text
slope multiset of f  =  multiset of  -(valuation of a root of f),  with multiplicity
Newton polygon of f·g  =  Minkowski sum of the Newton polygons of f and g
radius of convergence of f  =  b ^ (sup of the slopes of f)
```

where `b` is the base of the norm, `‖x‖ = b ^ (-(v x))`: `b = p` for `ℚ_p` with `v p = 1`.

The first layer is discrete convexity and has no arithmetic content: it is the theory of convex
minorants of a sequence, and it is where the polygon is defined, constructed and shown unique. The
second layer is the additive valuation itself — the `ℤ`-valued, `ℚ`-valued and `ℝ`-valued additive
valuations attached to a valuation or a norm, with the normalisation `v π = 1` at a chosen
element — because the polygon is only as good as the valuation feeding it: with `v p = 1` on `ℚ_p`
the slopes of a polynomial are honest rational numbers, and a statement such as "the slopes are
`j + ½`" is literally true rather than true up to a factor of `log p`. The remaining layers are the
arithmetic: the polygon of a polynomial and of a power series, the Weierstrass factorisation that
splits a series at a vertex of its polygon, the root and zero counts that the slopes compute, the
product formula, and the discretely valued specialisation, where the polygon becomes an
irreducibility criterion.

## Scope

The roadmap includes the following material.

- Convex sequences and their increments; convex minorants of a point sequence; the Newton polygon
  of an arbitrary sequence `v : ℕ → WithTop ℝ` as the greatest convex minorant, with its
  construction, its uniqueness, and the exact hypothesis under which it exists.
- Slopes, vertices, segments, lengths and the slope multiset; supporting lines, chords, and faces;
  the two counting functions that a face determines; the Minkowski sum (min-convolution) of two
  polygons.
- Additive valuations of a nonarchimedean field: the real additive valuation of a rank-one
  valuation, the `ℤ`-valued additive valuation of a discrete one, the `ℚ`-valued additive valuation
  of a valuation of rational rank one normalised at an element, the compatibility squares
  `ℤ → ℚ → ℝ` between them, the recovery of the norm from each, the instances read off the norm of
  an ultrametric normed field, and their agreement with `Padic.addValuation` on `ℚ_p` and with the
  convention `v p = 1` on `ℂ_p`.
- The Newton polygon of a polynomial and of a power series with respect to such a valuation; the
  integrality of its vertices and the rationality of its slopes; the dictionary relating it to
  `Polynomial.gaussNorm` and `PowerSeries.gaussNorm`; purity, first breaks, and distinguished
  polynomials.
- Weierstrass division at an arbitrary radius, and the factorisation of a series at a vertex of its
  polygon into a polynomial carrying the slopes up to that vertex times a unit of the disc algebra.
- Root counting for polynomials: the number of roots of each valuation, with multiplicity, and the
  identification of a face with the number of roots in a closed or open ball.
- Zeros of a power series in a disc, the radius of convergence, purity criteria, and the
  factorisation of an entire series into linear factors.
- The product formula: the polygon of `f·g` is the Minkowski sum, slope multisets and
  multiplicities add, and the Gauss norm of a product of power series is the product of the Gauss
  norms.
- The discretely valued specialisation: denominators and ramification, the irreducibility criteria
  that generalise Eisenstein, and the reading of the `μ` and `λ` invariants of a power series over
  a complete discrete valuation ring off its polygon.

The roadmap does not include the following.

- ⚠ **The Newton polygon of an `F`-crystal, a Dieudonné module, or an abelian variety over a finite
  field** — the Frobenius slope polygon, Newton strata, and the Newton-above-Hodge inequality. That
  is a different object with the same name, and nothing here touches it.
- ⚠ **Newton polytopes** of multivariable polynomials, mixed volumes, Bernstein's theorem, and
  tropical geometry. Multivariable coefficient supports are outside the scope; see the analytic
  toric geometry roadmap.
- Newton–Puiseux expansions at a singular point of a plane curve, Puiseux series, and the
  Ore–Montes algorithms for factoring polynomials over local fields.
- Valuation theory beyond rank one: higher-rank value groups, the general theory of extensions of
  valuations, and ramification theory. Layer 1 handles rank one only, and Layer 6 uses the
  ramification index of a finite extension of a discretely valued field as an input cited from the
  local-fields-and-ramification roadmap.
- Restricted power series, Tate algebras, and Weierstrass division over general Tate or Huber
  rings. Layer 0 of the adic-spaces roadmap owns that material, and this roadmap cites it; the only
  thing built here is the strengthening to an arbitrary radius recorded in §3.1.
- Berkovich spaces, rigid analytic geometry, the Gauss point, and the Shilov boundary.
- `p`-adic differential operators, their Newton polygons, and irregularity.
- Fredholm determinants of compact operators, their slopes, and eigenvalue counting. Those consume
  this roadmap and are not part of it.

The convexity material of §0.1 belongs under `TauCeti/Analysis/Convex/`. The additive valuations
of Layer 1 belong under `TauCeti/RingTheory/Valuation/AddValuation/`, mirroring Mathlib's directory
of that name, with the normed-field instances under `TauCeti/Topology/Algebra/Valued/` and the `ℚ_p`
and `ℂ_p` instances under `TauCeti/NumberTheory/Padics/`. Everything else belongs under
`TauCeti/NumberTheory/NewtonPolygon/`.

## Conventions and coordination with Mathlib

The following Mathlib pull requests are relevant to this roadmap.

- mathlib4#43578 identifies `Mᵐ⁰ = WithZero (Multiplicative M)` with `WithTop M`, through
  `WithZero.negLog` and the order-and-additive isomorphism `WithZero.orderAddIsoWithTop`.
- mathlib4#43580 attaches to a valuation with values in `Mᵐ⁰` an additive valuation with values in
  `WithTop M` (`Valuation.addVal`, `Valuation.addValValueGroup`, `Valuation.addVal_map`). It builds
  on #43578.
- mathlib4#40013 defines bounded subsets of topological rings and power-bounded elements. The
  adic-spaces roadmap coordinates with it as well.
- mathlib4#42867 makes restricted multivariate power series a type of their own, and mathlib4#42871
  extends the multivariate Gauss-norm API. Either may change the shape of `IsRestricted` and
  `gaussNorm` that §2.1 and §2.3 consume.

The Tau Ceti API should agree with the final Mathlib API. ⚠ **None of these is a blocker, and
nothing in this roadmap waits on Mathlib.** §1.1 builds the dictionary of #43578 and #43580 here,
named and shaped as those pull requests name and shape it, so that if they land the Tau Ceti copy is
deleted in favour of an import rather than rewritten.

These conventions are binding. Several of them are corrections to the obvious first design, and the
reasons are given because an implementor who does not know them will reintroduce the problem.

1. **A Newton polygon *is* its height function.** The polygon of a sequence is a function
   `h : ℕ → WithTop ℝ`, namely the height of the hull above each integer abscissa, and slopes,
   vertices, segments and lengths are *derived* from it. Do not make the primary object a structure
   bundling a slope sequence, a length sequence and a support bound.

   The reason is uniqueness. A segment of the hull may be presented as one segment or as two
   collinear segments, so the segment-decorated data is **not** determined by the sequence, and
   uniqueness can then only be stated as equality of heights. With the height function primary,
   uniqueness is literal equality of the object, the `⊥` bookkeeping needed to mark a degenerate
   zero-width segment disappears, and convexity is the single statement that the increment sequence
   is monotone.

2. **The input is an additive valuation, not `-log ‖·‖`.** The points of the polygon of `f` are
   `(i, v (coeff i f))` for an additive valuation `v : AddValuation K (WithTop Γ)`, where `Γ` is a
   linearly ordered additive commutative group equipped with a strictly monotone additive map
   `e : Γ →+ ℝ` — the rank-one hypothesis, in additive form. The three instances that matter, from
   most to least specific, are

   - `Γ = ℤ`, the `ℤ`-valued valuation of a discretely valued field with `v π = 1` at a uniformiser
     (`ℚ_p` with `v p = 1`);
   - `Γ = ℚ`, the `ℚ`-valued valuation of a field of rational rank one, normalised at a chosen
     element `π` by `v π = 1` (`ℂ_p` with `π = p`, and every algebraic extension of `ℚ_p` with
     the valuation normalised at `p`);
   - `Γ = ℝ`, the unnormalised valuation `x ↦ -log ‖x‖` of any ultrametric normed field.

   The first two are the point of the convention: over `ℚ_p` the points of the polygon have
   integer heights and the slopes of a polynomial are rational numbers, so that "the slopes are
   `j + ½`" is an equality in `ℚ` and not an equality in `ℝ` carrying a factor of `log p`. The third
   is the fallback when no normalisation is available, and is the one the existing code uses
   throughout; in this roadmap it is an instance, never the definition.

3. **Normalisation is carried by an element, never by hidden data.** The `ℚ`-valued additive
   valuation is `addValQ v π`, indexed by the element `π` at which it is normalised, and the
   hypothesis that makes it well defined is the Prop class `IsCommensurable v π`: `0 < v π < 1` and
   every value of `v` is commensurable with `v π`. There is no data-carrying class recording an
   embedding of the value group into `ℚ`.

   The reason: an embedding of a dense subgroup of `ℚ` into `ℚ` is unique only up to a positive
   rational scalar, so a data class would hide a normalisation, and two such instances on the same
   field would disagree by a scalar — a mathematically meaningful diamond. A discrete value group
   has a canonical generator, which is why `IsRankOneDiscrete` can be a Prop and its `ℤ`-valued
   valuation needs no element; a dense one does not, so the element is part of the name.

4. **The polygon is real-valued even when the points are integer-valued.** The points live in
   `WithTop Γ`, pushed into `WithTop ℝ` along `e`; the polygon `h` takes values in `WithTop ℝ`.
   Integrality and rationality are theorems, not part of the type: a vertex of the polygon is a
   point of the sequence, so its height lies in the image of `e`, and a polynomial's slopes are
   quotients of differences of such heights by positive integers, hence rational when `Γ = ℤ`.

   The codomain cannot be narrowed to `ℚ` because it is false for power series. Over `ℚ_p`, the
   series with coefficient valuations `v (coeff k f) = ⌈k√2⌉` has as Newton polygon the ray of
   slope `√2` through the origin: the slopes `⌈k√2⌉/k` from the origin tend to `√2` from above and
   never attain it. For a polynomial, or any polygon with finitely many segments, everything is
   rational, and §2.2 states exactly that.

5. **`⊤` is the only junk value.** The set `{k | h k ≠ ⊤}` is an interval of `ℕ`: it is
   `[i₀, i₁]` for a polynomial, where `i₀` is the first index with `aᵢ ≠ 0`, and `[i₀, ∞)` for a
   series with infinitely many nonzero coefficients. Convexity is required on that interval.
   There is no `⊥`, and no `WithBotTop`: a one-sided polygon never needs a value below the
   bottom of its range.

6. **Slopes increase from left to right; slope `m` means roots of valuation `-m`.** The `j`-th
   increment `h (j+1) - h j` is the `j`-th unit slope, the unit slopes are monotone, and the slope
   multiset is the multiset of unit slopes. A polynomial of degree `d` anchored at `0` has exactly
   `d` unit slopes. A segment of slope `m` corresponds to roots `x` with `v x = -m`, and, when the
   norm is `‖x‖ = b ^ (-(v x))`, to roots of absolute value `b ^ m`; a radius `c` corresponds to
   the slope `log c / log b`. Larger slope means larger root. This orientation is fixed throughout
   and the mirrored convention is not used anywhere. Every statement about a radius is accompanied
   by its slope form, and vice versa, rather than silently preferring one.

7. **Multiplicities are multisets.** Root counts are `Multiset.card` of a `Multiset.filter` of
   `Polynomial.roots`, and the slope multiset is a `Multiset ℝ`. Do not phrase a count with
   multiplicity as a `Finset.card`, and do not introduce a bespoke multiplicity function.

8. **Roots are measured by the spectral norm, and their valuations by the valuation it induces.**
   For `K` complete, roots live in `AlgebraicClosure K`, normed by Mathlib's
   `spectralNorm K (AlgebraicClosure K)`, which is multiplicative, nonarchimedean and extends the
   norm of `K`; the additive valuation on the closure is the one Layer 1 attaches to that norm,
   normalised at the same `π` as on `K`. Do **not** take a valuation on the algebraic closure
   together with a hypothesis that it extends the valuation of `K` as the interface of a root
   count: that hypothesis is a theorem (§1.5.2), and the statement should use the canonical object.
   Where a result genuinely holds for an arbitrary extension, say so and take the extension as data.

9. **Zeros of a series need a complete extension.** `AlgebraicClosure K` is not complete, so a
   power series cannot be evaluated there, and the zero-counting statements of §4.3 are phrased
   over a complete ultrametric field extending `K` isometrically, with `HasSum` for convergence.
   Mathlib's `ℂ_[p]` is the model case and every zero-counting milestone must be instantiated at
   it. The root counts of §4.1 are statements about polynomials and do not need completeness of the
   extension, only of `K`.

10. **Names.** The polygon of a sequence is `newtonPolygon v`; the polygon of a polynomial or a
    series with respect to an additive valuation `v` is `Polynomial.newtonPolygon v f` and
    `PowerSeries.newtonPolygon v f`, with the valuation explicit, and the slope multiset of a
    polynomial is `Polynomial.newtonSlopes v f`. Derived notions live in the `NewtonPolygon`
    namespace (`NewtonPolygon.unitSlope`, `NewtonPolygon.IsPure`, `NewtonPolygon.face`). The
    additive valuations of Layer 1 live in the `Valuation` namespace where they are built from a
    valuation (`Valuation.addValQ`, `Valuation.IsRankOneDiscrete.addValZ`) and in the
    `NormedField` namespace where they are read off a norm (`NormedField.normAddValZ`,
    `NormedField.normAddValQ`, `NormedField.normAddVal`). Nothing from this roadmap is placed in
    the root namespace.

11. **Coordinate with the Gauss-norm files.** `Polynomial.gaussNorm`, `PowerSeries.gaussNorm` and
    `MvPowerSeries.gaussNorm` are Mathlib's vocabulary for `sup_i v(aᵢ) cⁱ`, with `HasGaussNorm` for
    boundedness of the family. Every statement about the supporting value of a polygon at a radius
    is phrased with them; no parallel definition of a Gauss norm is introduced. ⚠ The two
    definitions are not literally the same shape — `Polynomial.gaussNorm` is a `Finset.sup'` over
    the support and `PowerSeries.gaussNorm` is an `iSup` — and `Polynomial.gaussNorm_coe_powerSeries`
    is the bridge. ⚠ They also disagree on how `v` is taken: `Polynomial.gaussNorm` takes a bundle
    `v : F` with `[FunLike F R ℝ]`, while `PowerSeries.gaussNorm` takes a bare function `R → ℝ`, so
    `norm` can be passed directly to the second but not to the first. Decide once how a statement
    quantifying over both is phrased, and record it here.

12. **Defer to Mathlib on the multiplicative side.** Valuations are Mathlib's `Valuation R Γ₀`,
    rank one is `Valuation.RankOne` with its `hom : Γ₀ →*₀ ℝ≥0`, discreteness is
    `Valuation.IsRankOneDiscrete` with `IsUniformizer` and `generator`, the valuation of a normed
    field is `NormedField.valuation`, and the bijection between valuations and additive valuations
    is `Valuation.toAddValuation`. Layer 1 reads that bijection into a usable target (§1.1), adds
    the `ℤ`- and `ℚ`-valued refinements, and proves the norm-recovery theorems; it does not
    re-found the multiplicative theory.

## Existing Mathlib used by the roadmap

- `AddValuation`, `Valuation.toAddValuation` and `Valuation.ofValuation`: the bijections
  `Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ` and
  `Valuation R (Multiplicative Γ₀ᵒᵈ) ≃ AddValuation R Γ₀`. ⚠ Their codomains are type synonyms for
  `Γ₀` itself rather than a type of the shape `M ∪ {∞}`, which is why §1.1 composes
  `toAddValuation` with an isomorphism onto `WithTop M` instead of using it directly. The
  `WithZero.exp` / `WithZero.log` API on `Mᵐ⁰` and `MonoidWithZeroHom.valueGroup` are inputs;
  `WithZero.negLog` and `Valuation.addVal` are **not** — they are mathlib4#43578 and
  mathlib4#43580, and §1.1 builds them.
- `Valuation.RankOne` and `Valuation.RankLeOne`, with `Valuation.RankOne.hom : Γ₀ →*₀ ℝ≥0` and
  its strict monotonicity; `Valuation.IsNontrivial`; `MonoidWithZeroHom.valueGroup`.
- `Valuation.IsRankOneDiscrete`, `Valuation.IsRankOneDiscrete.generator`, `Valuation.IsUniformizer`,
  and `Valuation.Uniformizer`.
- `Valued`, `NormedField.valuation`, `NormedField.toValued`, and `NormedField.v_eq_valuation`.
- `Padic.valuation : ℚ_[p] → ℤ` and `Padic.addValuation : AddValuation ℚ_[p] (WithTop ℤ)`.
  ⚠ These are defined directly for `ℚ_p`, not as instances of a general construction; §1.3 builds
  the general `ℤ`-valued valuation and proves it agrees with them.
- `PadicAlgCl p = AlgebraicClosure ℚ_[p]` and `ℂ_[p] = PadicComplex p`, each with `NormedField`,
  `IsUltrametricDist`, `Valued _ ℝ≥0`, `RankOne`, and `valuation_p : Valued.v p = 1 / p`;
  `IsAlgClosed ℂ_[p]`; the valuation subring `𝓞_ℂ_[p]`.
- `spectralNorm`, `spectralAlgNorm`, `isNonarchimedean_spectralNorm`, `spectralAlgNorm_mul`, and
  `spectralNorm.normedField`, which makes an algebraic extension of a complete nonarchimedean field
  a normed field; `PadicAlgCl.spectralNorm_eq`.
- `Polynomial.gaussNorm`, `PowerSeries.gaussNorm`, `MvPowerSeries.gaussNorm`, `HasGaussNorm`, and
  `Polynomial.gaussNorm_coe_powerSeries`. ⚠ Mathlib has `Polynomial.gaussNorm_mul` — the Gauss
  norm of a product of *polynomials* is the product, for a nonarchimedean absolute value and
  `c > 0` — but for power series only the inequality `MvPowerSeries.gaussNorm_mul_le`. The
  equality for power series is a milestone here (§5.4), not an input.
- `PowerSeries.IsRestricted` and `MvPowerSeries.IsRestricted`: the normed decay condition
  `‖aₖ‖ cᵏ → 0`, available both along `cofinite` (`isRestricted_iff`) and along `atTop`
  (`isRestricted_iff'`); the univariate predicate is the `σ = Unit` case of the multivariate one.
  ⚠ This is genuinely different from adic
  restrictedness, and from the `I`-adic completeness hypotheses of
  `Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`; §6.3 is where the two are
  compared, and nowhere else may they be conflated.
- `IsUltrametricDist`, `NontriviallyNormedField`, `IsNonarchimedean`, and the strong triangle
  inequality in the form `norm_add_le_max`.
- `AlgebraicClosure`, `minpoly`, `Polynomial.roots` as a `Multiset`, `Polynomial.Splits`, and
  `Polynomial.roots_map`.
- `Polynomial.IsEisensteinAt` and its irreducibility consequence, and
  `Mathlib/RingTheory/Polynomial/Eisenstein/Distinguished.lean`.
- `Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean` (Weierstrass division,
  factorization and preparation for a ring adic-complete with respect to an ideal) — consumed in
  §6.3 for the comparison, and not used as the normed Weierstrass theorem.
- `ConvexOn`, `Mathlib/Analysis/Convex/Slope.lean`, and `Mathlib/Analysis/Convex/Jensen.lean`.
  ⚠ These are about functions on a real convex set. The `ℕ`-indexed theory of §0.1 is **not** a
  corollary of them and is built here; the bridge to `ConvexOn` of the piecewise-linear
  interpolation is a milestone of §0.1, in the direction "discrete convexity implies `ConvexOn`".
- `WithTop` with its order, addition, `WithTop.map` and `untop₀`. ⚠ `WithTop ℝ` has no subtraction
  and is not a complete lattice, so neither "the increment `h (j+1) - h j`" nor an infimum over all
  of `ℕ` is literally available: fix a convention for the increment sequence in §0.1 (a
  `WithTop ℝ`-valued slope defined by cases, or a function defined only on the finiteness
  interval), take finite infima with `Finset.inf`, and use both everywhere.
- `Multiset` and its `filter`, `card`, `map` and `sum`.
- `HasSum`, `tsum`, `CompleteSpace`, and `UniformSpace.Completion`.

⚠ Mathlib has **no** Newton polygon, in any sense, and **no** lower convex hull of a discrete point
set. `Mathlib/Analysis/Convex/Hull.lean` is the convex hull of a set in a real vector space and is
not usable as the definition here: the hull wanted is the greatest convex minorant of a sequence,
which is a function, not a set.

⚠ Mathlib has **no** additive valuation with values in a type of the shape `M ∪ {∞}`, no `ℤ`- or
`ℚ`-valued additive valuation attached to a norm or to an abstract rank-one valuation, no notion of
rational rank one normalised at an element, and no norm-recovery theorem of the shape
`‖x‖ = ‖π‖ ^ (v x)`. All of that is Layer 1, §1.1 coordinated with mathlib4#43578 and
mathlib4#43580 as described above.

---

## Layer 0: convex minorants and the polygon of a sequence

No arithmetic. Everything in this layer is about a sequence of extended reals, and all of it should
be usable by anyone who needs a discrete convex hull. The points are `v : ℕ → WithTop ℝ`; Layer 2
supplies them from an additive valuation by pushing `WithTop Γ` into `WithTop ℝ`.

### 0.1 Convex sequences

Develop the basic theory of convexity for a function `h : ℕ → WithTop ℝ` whose finiteness set is an
interval.

1. Define the increment (unit slope) sequence and fix the convention for its value outside the
   finiteness interval. Define `IsConvexSeq h` to say that the increments are monotone on that
   interval.
2. The chord inequality (discrete Jensen): a convex sequence lies on or below the chord joining any
   two of its points, and on or above every extension of one of its increments. State both as
   comparisons of `h` with an affine function of the index.
3. A convex sequence is determined by its value at one point together with its increments. The
   pointwise maximum of two convex sequences is convex, and so is the pointwise supremum of any
   family of convex sequences that is bounded above at each index; the pointwise *minimum* of two
   convex sequences is **not** convex in general, and the counterexample is to be recorded. The
   supremum statement is what makes the greatest convex minorant of §0.2 exist, and it is the
   backbone of the maximality half of §0.3.
4. The bridge to Mathlib: a convex sequence that is finite everywhere is the restriction to `ℕ` of a
   function `ConvexOn ℝ (Set.Ici 0)`, and conversely the restriction of a `ConvexOn` function to the
   integers is a convex sequence.
5. Affine sequences are convex; a convex sequence with a bounded increment sequence has a limiting
   slope; a convex sequence is eventually monotone.

### 0.2 The Newton polygon of a sequence

Fix `v : ℕ → WithTop ℝ`, thought of as the point set `{(i, v i) | v i ≠ ⊤}`.

1. Define `IsNewtonPolygonOf v h`: `h` is convex in the sense of §0.1, is anchored at the first
   index where `v` is finite (with the same value there), satisfies `h ≤ v` pointwise, and is the
   greatest such function. Make the anchoring condition and the greatest-minorant condition separate
   fields, so that each can be used alone.
2. **Uniqueness.** Two functions satisfying `IsNewtonPolygonOf v` are equal. This is where
   convention 1 pays: the statement is equality, not equality of a derived height.
3. **Admissibility.** Define `IsAdmissible v`, the condition that some line through the anchor lies
   on or below every point — equivalently, that the slopes from the anchor to the later points are
   bounded below. Prove that it is exactly the condition for a minorant to exist:
   `IsNewtonPolygonOf v h` for some `h` implies `IsAdmissible v`, and the converse is §0.3. Record
   the failing example `v k = -k²`, for which the hull is vertical and no convex minorant anchored
   at `0` exists.
4. Define `newtonPolygon v` as a total function returning the polygon when `v` is admissible and has
   a finite value, with a documented junk value otherwise, and prove
   `IsNewtonPolygonOf v (newtonPolygon v)` under those hypotheses. Every statement in the later
   layers is phrased with `newtonPolygon` and its characterisation, never with the construction of
   §0.3.
5. Monotonicity and invariance: `newtonPolygon` is unchanged by adding a constant to `v`, is
   translated by an affine shear `v i ↦ v i + m·i`, and is monotone in `v` pointwise.

### 0.3 Existence by construction

1. Construct the polygon by the vertex walk: from the current vertex take the infimum of the slopes
   to all later points, and move to the furthest point achieving it. Prove the walk is well defined
   under `IsAdmissible`, that each step's slope is at least the previous one, and that the resulting
   function satisfies `IsNewtonPolygonOf`.
2. Handle the two ways the walk can fail to reach a next vertex: the sequence has no further finite
   value (the polygon stops, and `h` is `⊤` beyond the last point), and the infimum of the slopes is
   not attained (the polygon ends in a ray of that slope, of infinite length). Prove that in the
   second case the limiting slope is the supremum of the unit slopes.
3. For a finitely supported `v` the polygon has finitely many segments and its last vertex is the
   last finite index.
4. Prove the minorant half ("the polygon lies below the points") and the maximality half
   separately, since they have different hypotheses: maximality is the chord argument of §0.1 and
   needs a competitor, and on a final ray it needs an approximation along slopes tending to the
   infimum.

### 0.4 Slopes, vertices, segments and the slope multiset

1. Define the unit slope sequence of a polygon, the vertex set (the indices where the unit slope
   strictly increases, together with the anchor), the segments as maximal runs of equal unit slope,
   and the length of a segment. Prove the unit slopes are monotone and that the vertices are points
   of the sequence, i.e. `h k = v k` at a vertex.
2. Define the slope multiset of a polygon with finitely many unit slopes, as a `Multiset ℝ`, and
   prove that its cardinality is the length of the polygon and its sum is the total height gain.
   For a polynomial this will be the multiset of the negatives of the root valuations.
3. Define `IsPure h m`: the polygon is a single segment of slope `m`, equivalently every unit slope
   equals `m`. Prove `IsPure` is equivalent to the slope multiset being a constant multiset.
4. Define the first break of a polygon: the first slope together with the length of the first
   segment, and characterise it by an inequality on the points — `v k ≥ v i₀ + m(k - i₀)` for all
   `k`, with equality at the end of the segment.
5. Prove that the polygon of the restriction of `v` to `[0, n]` agrees with the polygon of `v` up to
   the last vertex at or before `n`, and that the polygon of `v` determines and is determined by its
   unit slope sequence.

### 0.5 Supporting lines, faces, and the competitor lemma

1. **Supporting lines.** For every real `σ` and every index `n`, the affine function of slope `σ`
   through `(n, h n)` lies on or below `h` if and only if `σ` lies between the unit slopes adjacent
   to `n`; and any affine function lying below all the points lies below the polygon. The second
   statement is the workhorse used throughout the arithmetic layers and should be stated as such.
2. **The competitor lemma.** A two-slope broken line lying on or below every point lies on or below
   the polygon. This is the instance of maximality that the arithmetic layers actually consume, and
   the one-slope case is the statement above.
3. **Faces.** For a real `σ`, define `faceLeft h σ` as the number of unit slopes strictly less than
   `σ` and `faceRight h σ` as the number of unit slopes at most `σ`; these are the endpoints of the
   face on which a supporting line of slope `σ` touches the polygon, counted from the anchor. Prove
   the polygon is affine of slope `σ` on `[faceLeft σ, faceRight σ]`, is strictly above the
   supporting line outside it, and that `faceLeft σ ≤ faceRight σ` with equality exactly when `σ` is
   not a slope.
4. Prove both face endpoints are finite exactly when the unit slopes are unbounded, define
   `SlopesUnbounded` for that condition, and prove it holds when `v` is finitely supported and when
   `v k / k → ∞`. ⚠ This hypothesis is not cosmetic: it is exactly what the product formula of
   Layer 5 needs, and §5.1 records the counterexample without it.
5. Prove the multiplicity of `σ` in the slope multiset is `faceRight σ - faceLeft σ`, and that
   `faceRight` is the right-continuous counting function of the slope multiset.

### 0.6 Minkowski sums

1. For polygons `h₁, h₂` anchored at `0`, define the Minkowski sum
   `minkowski h₁ h₂ n = min_{i+j=n} (h₁ i + h₂ j)` (the min-convolution, a finite `Finset.inf`), and
   prove it is convex, symmetric, associative, and anchored at `h₁ 0 + h₂ 0`.
2. Prove the subgradient property: for every `n` there is a slope `σ` and a split `i + j = n`
   realising the minimum such that supporting lines of slope `σ` to `h₁` at `i` and to `h₂` at `j`
   sum to a supporting line of the Minkowski sum at `n`.
3. Prove the unit slope multiset of the Minkowski sum is the sum of the two slope multisets, and
   hence `faceRight (minkowski h₁ h₂) σ = faceRight h₁ σ + faceRight h₂ σ`, and likewise for
   `faceLeft`. Both halves need `SlopesUnbounded` for the factors.
4. Prove the minimising split is unique at the endpoints of a face, which is the fact that turns the
   ultrametric inequality into an equality in §5.1.

### Examples

Compute the polygon, the slope multiset and both face counting functions for: a sequence with one
finite value; the affine sequence `v i = a + m·i`; `v i = i²`; the sequence
`v = (0, 1, 0, 1, 0, …)`, whose polygon is the zero function; a finitely supported sequence whose
hull has a genuinely collinear middle point, demonstrating that the vertex set is a strict subset of
the set of points lying on the polygon; and `v k = ⌈k√2⌉`, whose polygon is the ray of slope `√2`
and whose slopes from the anchor are all rational.

### Dependencies

Mathlib only.

---

## Layer 1: additive valuations of a nonarchimedean field

The valuation the polygon consumes. Mathlib's `Valuation` takes values in a linearly ordered
commutative group with zero, while an additive valuation is written with values in `M ∪ {∞}`; §1.1
builds that dictionary, and §§1.2–1.4 build the three concrete members of the family — real, integer
and rational — with their normalisations, the compatibility squares between them, and the recovery of
the norm from each. §1.5 carries them to algebraic extensions, to `ℚ_p`'s algebraic closure and to
`ℂ_p`. Nothing in this layer mentions polygons, and all of it is reusable by anyone working with
nonarchimedean valuations in additive form.

### 1.1 Additive valuations with a usable target

Mathlib's `Valuation.toAddValuation` lands in a type synonym for the value group, not in a type of
the shape `M ∪ {∞}`. This section fixes that, and everything else in Layer 1 is stated against the
result. Name and shape it exactly as mathlib4#43578 and mathlib4#43580 do.

1. Define `WithZero.negLog : Mᵐ⁰ → WithTop M`, sending `0 ↦ ⊤` and `exp m ↦ -m`: the `WithZero.log`
   of Mathlib's `Mᵐ⁰` API in its additive-valuation reading, recording `0` as a genuine `⊤` instead
   of the junk value `log 0 = 0`, and negated so that the reversed order on `Mᵐ⁰` becomes the usual
   order on `WithTop M`. Prove it underlies an order-and-additive isomorphism
   `WithZero.orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M`, and prove `negLog_mul`,
   `negLog_one`, `negLog_eq_top`, `negLog_le_negLog`, and the characterisation
   `negLog x = m ↔ x = exp (-m)`.
2. Define the functoriality `WithZero.mapAddHom' : (M →+ N) → (Mᵐ⁰ →*₀ Nᵐ⁰)`, prove it is strictly
   monotone when the hom is, and prove `negLog` is natural along it.
3. Define `Valuation.addVal : Valuation R Mᵐ⁰ → AddValuation R (WithTop M)` as `x ↦ negLog (v x)`,
   by composing `Valuation.toAddValuation` with the isomorphism of clause 1. Prove
   `addVal_eq_top : v.addVal x = ⊤ ↔ v x = 0` and
   `addVal_eq_coe : v.addVal x = m ↔ v x = exp (-m)`. ⚠ The second is the lemma the rest of Layer 1
   runs on: every norm-recovery theorem below reduces to it, and without it each one re-derives the
   same `WithZero.unzero` bookkeeping.
4. Define `Valuation.addValValueGroup`, the tautological additive valuation of an arbitrary
   valuation, with values in `WithTop` of its own value group written additively. Prove
   `Valuation.addVal_map`: pushing `v` along `mapAddHom' f` pushes `v.addVal` along `f`. This is
   what gives the compatibility squares `WithTop ℤ → WithTop ℚ → WithTop ℝ` of §1.4.5, and every
   concrete additive valuation of §§1.2–1.4 is `addValValueGroup` pushed along a hom out of the
   value group.
5. ⚠ **Pin the architecture.** Do not build the `ℤ`-, `ℚ`- and `ℝ`-valued valuations by
   constructing additive homs *out of* `Additive (valueGroup v)` and pushing the tautological
   valuation along each. Compose multiplicative homs *into* `Mᵐ⁰` and convert once, at the end, with
   `addVal`. The first shape forces `WithZero.unzero` gymnastics into every downstream theorem; the
   second confines it to clause 3. Each specialisation below is then literally
   `(v.restrict.map φ _).addVal` for a hom `φ` into `ℤᵐ⁰`, `ℚᵐ⁰` or `ℝᵐ⁰`.

### 1.2 The real additive valuation of a rank-one valuation

1. For `v : Valuation R Γ₀` with `[v.RankOne]`, define `Valuation.RankOne.realValuation v`, the
   `ℝᵐ⁰`-valued valuation obtained by pushing `v` along `RankOne.hom`, and
   `Valuation.RankOne.addVal v : AddValuation R (WithTop ℝ)` as its `addVal`. Prove
   `RankOne.addVal v x = -log (hom (v x))` for `v x ≠ 0`, that it is `⊤` exactly at `v x = 0`, and
   that it is unchanged when `v` is replaced by an equivalent valuation with the matching `hom`.
2. For an ultrametric normed field, define `NormedField.normAddVal K : AddValuation K (WithTop ℝ)`
   from `NormedField.valuation`, and prove `normAddVal K x = -log ‖x‖` for `x ≠ 0`. This is the
   unnormalised member of the family: it takes no element and `normAddVal K π` is `-log ‖π‖`, not
   `1`.
3. Prove the defining equivalence `‖x‖ = exp (-(normAddVal K x))` for `x ≠ 0`, and that
   `normAddVal K` is the unique additive valuation into `WithTop ℝ` satisfying it.

### 1.3 Discrete rank one: the `ℤ`-valued additive valuation

For `v : Valuation R Γ₀` with `[v.IsRankOneDiscrete]`, so that the value group is infinite cyclic
with `generator v < 1`.

1. Define `Valuation.IsRankOneDiscrete.addValZ v : AddValuation R (WithTop ℤ)` and prove its
   characterisation: `addValZ v x = k ↔ v x = generator v ^ k`, with `⊤` exactly at `v x = 0`.
2. Prove `addValZ v π = 1` for every uniformiser `π`, and `addValZ v x = k ↔ v x = v π ^ k` for such
   a `π`.
3. **Norm recovery.** If `[v.RankOne]` as well and `hom v (generator v) = e⁻¹` for a real `e > 1`,
   then `hom v (v x) = e ^ (-(addValZ v x))` for `v x ≠ 0`. Prove that on a discrete valuation the
   single scalar `e` determines `hom`, because a monoid-with-zero hom out of an infinite cyclic group
   is determined by its value on the generator.
4. For an ultrametric normed field whose valuation is discrete, define
   `NormedField.normAddValZ K : AddValuation K (WithTop ℤ)` and prove `‖x‖ = e ^ (-(normAddValZ K x))`
   when a uniformiser has norm `e⁻¹`.
5. **`ℚ_p`.** Prove that `NormedField.valuation` on `ℚ_[p]` is `IsRankOneDiscrete`, with value group
   generated by `‖p‖₊ = p⁻¹`, that `normAddValZ ℚ_[p] = Padic.addValuation` as additive valuations,
   and that `‖x‖ = p ^ (-(normAddValZ ℚ_[p] x))`. Prove the same for the Laurent-series field
   `𝔽_q⸨t⸩` at the uniformiser `t`.
6. **Finite extensions.** For `L/K` a finite extension of a complete discretely valued field, with
   `L` discretely valued under the spectral norm and ramification index `e(L/K)` — both cited from
   the local-fields-and-ramification roadmap — prove `normAddValZ L x = e(L/K) · normAddValZ K x`
   for `x ∈ K`, and identify `normAddValZ L` with `e(L/K)` times the `ℚ`-valued valuation of §1.4
   normalised at a uniformiser of `K`.

### 1.4 Rational rank one, normalised at an element

The density analogue of discreteness, for fields such as `ℂ_p` whose value group is `p^ℚ`.

1. Define the Prop class `Valuation.IsCommensurable v π`: `0 < v π`, `v π < 1`, and for every `x`
   with `v x ≠ 0` there are integers `m` and `n > 0` with `v x ^ n = v π ^ m`. Prove it implies
   `v.IsNontrivial`, and that `IsRankOneDiscrete` implies `IsCommensurable` at every uniformiser.
2. Define `Valuation.ratLog v π`, the unique additive hom from the additively written value group to
   `ℚ` sending `v π` to `-1`, and prove it strictly monotone. Define
   `Valuation.addValQ v π : AddValuation R (WithTop ℚ)` by pushing the tautological
   `addValValueGroup` along it, and prove `addValQ v π π = 1`.
3. **The workhorse.** `v x ^ n = v π ^ m` with `n > 0` implies `addValQ v π x = m / n`. Everything
   else in this section reduces to it.
4. **Uniqueness.** Any additive valuation `w : AddValuation R (WithTop ℚ)` inducing the same order
   on values as `v` (`w x ≤ w y ↔ v y ≤ v x`) and satisfying `w π = 1` equals `addValQ v π`. This is
   the statement that justifies convention 3: the element pins the valuation.
5. **From rational rank one to rank one.** For every real `e > 1`, build `RankOne v` with
   `hom v (v π) = e⁻¹`, and prove the compatibility squares: `RankOne.addVal v` is
   `(-log (hom v (v π)))` times `addValQ v π`, and on a discrete valuation `addValQ v π` is
   `addValZ v` composed with `Int.cast` at a uniformiser `π`.
6. **Norm recovery.** For an ultrametric normed field, define `NormedField.normAddValQ K π` and prove
   `‖x‖ = ‖π‖ ^ (normAddValQ K π x)` for `x ≠ 0`. ⚠ There is no exponential base and no
   factorisation hypothesis in this statement: normalising at `π` pins the base to `‖π‖⁻¹`.

### 1.5 Algebraic extensions, `ℂ_p`, and the valuation of the algebraic closure

1. For `L/K` an algebraic extension of a complete ultrametric normed field, normed by
   `spectralNorm.normedField`, prove `IsUltrametricDist L` and that the spectral norm extends the
   norm of `K`. Prove that `normAddVal L` restricts to `normAddVal K`.
2. **Commensurability is inherited.** If `NormedField.valuation` on `K` is `IsCommensurable` at `π`,
   so is the valuation of `L` at `algebraMap K L π`, and `normAddValQ L π` restricts to
   `normAddValQ K π`. The proof is from the definition of the spectral norm as a spectral value:
   `spectralNorm x ^ (n - i) = ‖aᵢ‖` for the index `i` realising the maximum over the coefficients
   of the minimal polynomial, so every value of `L` is commensurable with a value of `K`.
3. **Completion preserves the value group.** For a rank-one valued field, the value group of the
   completion is the value group of the field, so `IsCommensurable` at `π` passes to the completion,
   and `normAddValQ` of the completion restricts to `normAddValQ` of the field.
4. **The algebraic closure of `ℚ_p`, and `ℂ_p`.** Prove `IsCommensurable` at `p` for
   `PadicAlgCl p` and for `ℂ_[p]`, so that `normAddValQ ℂ_[p] p : AddValuation ℂ_[p] (WithTop ℚ)`
   is defined with `normAddValQ ℂ_[p] p p = 1`, restricts to `Padic.addValuation` on `ℚ_p`, and
   satisfies `‖x‖ = p ^ (-(normAddValQ ℂ_[p] p x))`. This is the object convention 8 refers to: the
   valuation of a root of a polynomial over `ℚ_p` is its `normAddValQ` value in
   `AlgebraicClosure ℚ_[p]`, a rational number.
5. Prove the value group of `ℂ_[p]` is exactly `p^ℚ`: every rational occurs as a valuation, and
   nothing else does.

### Examples

`ℚ_p`: `normAddValZ p = 1`, `normAddValZ (1/p²) = -2`, `‖x‖ = p ^ (-v x)`, and `normAddVal ℚ_[p]`
is `log p` times `normAddValZ`. `ℚ_p(√p)`: `normAddValZ` of the extension gives `√p ↦ 1` and
`p ↦ 2`, while `normAddValQ` normalised at `p` gives `√p ↦ 1/2`. `ℂ_p` at `π = p`: `p^{1/3} ↦ 1/3`.
`𝔽_q⸨t⸩` at `t`: `normAddValZ` is the order of vanishing at `t`.

### Dependencies

Mathlib. The discreteness of a finite extension and the ramification index in §1.3.6 are cited from
the local-fields-and-ramification roadmap.

---

## Layer 2: the polygon of a polynomial and of a power series

`K` is a nonarchimedean normed field throughout: `NontriviallyNormedField K` with
`IsUltrametricDist K`. It carries a **normed additive valuation**: an additive valuation
`v : AddValuation K (WithTop Γ)`, a strictly monotone additive map `e : Γ →+ ℝ`, and a base `b > 1`
with `‖x‖ = b ^ (-(e (v x)))` for `x ≠ 0`. Prove that the three members of Layer 1's family are
instances: `(normAddValZ K, Int.cast, ‖π‖⁻¹)` for a discretely valued `K` with uniformiser `π`,
`(normAddValQ K π, Rat.cast, ‖π‖⁻¹)` in the commensurable case, and `(normAddVal K, id, exp 1)`
always. Completeness is **not** assumed in this layer and is introduced in Layer 3 where it is
needed.

### 2.1 Coefficient valuations

1. Define the coefficient valuation sequence of a power series, `i ↦ WithTop.map e (v (coeff i f))`,
   and the corresponding notion for a polynomial. Prove the value is `⊤` exactly at a vanishing
   coefficient, and that the sequence of a polynomial is finitely supported.
2. Prove the dictionary between Gauss-norm terms and polygon heights: for a slope `m` and the radius
   `c = b ^ m`, the term `‖aₖ‖ cᵏ` is at most `1` exactly when the point `(k, e (v aₖ))` lies on or
   above the line of slope `m` through the origin, and similarly for `<`, `=`, and for comparison
   against another term rather than against `1`. State the whole dictionary; the later layers use
   every direction of it.
3. Prove that the coefficient valuation sequence of a polynomial is admissible, and that the
   sequence of a power series is admissible exactly when `f` is restricted at some positive radius;
   in particular `PowerSeries.IsRestricted c f` for some `c > 0` implies admissibility.

### 2.2 The polygon of a polynomial and of a power series

1. Define `Polynomial.newtonPolygon v f` and `PowerSeries.newtonPolygon v f` by applying
   `newtonPolygon` to the coefficient valuation sequence, and prove the specification holds: they
   satisfy `IsNewtonPolygonOf` under the hypotheses of §2.1.3.
2. For a polynomial: the polygon is anchored at the order of vanishing at `0`, its last vertex is at
   the degree, it has exactly `natDegree f - order f` unit slopes, and `SlopesUnbounded` holds.
   Define `Polynomial.newtonSlopes v f : Multiset ℝ` and prove its cardinality is
   `natDegree f - order f`.
3. **Integrality and rationality.** The height of the polygon at a vertex lies in the image of `e`.
   Every unit slope of the polygon of a polynomial is `(e γ) / l` for some `γ : Γ` and some segment
   length `l ≥ 1`; for `Γ = ℤ` every slope is a rational number whose denominator divides the length
   of its segment. ⚠ This is false for power series — the example `v (coeff k f) = ⌈k√2⌉` of
   convention 4 — and the statement is to be made for polygons with finitely many segments, not for
   polynomials only.
4. For a power series restricted at every positive radius ("entire"), prove `SlopesUnbounded` holds
   and the unit slopes tend to `+∞`. For a series restricted at some radius, prove the unit slopes
   are bounded above; the sharp bound, `log_b` of the radius of convergence, is §4.4.
5. Prove the polygon of a polynomial, viewed as a power series, is the polygon of the polynomial,
   and that the coercion is compatible with everything in §2.1.
6. Prove the normalisation: if `coeff 0 f = 1` the polygon is anchored at `(0, 0)`, and every series
   with `coeff 0 f ≠ 0` becomes so after dividing by `coeff 0 f`, with the polygon translated by a
   constant. The later layers assume `coeff 0 f = 1`; this is the lemma that makes that harmless.
7. Prove the elementary operations: the polygon of `f (cX)` is sheared by `e (v c)`, the polygon of
   `X^n · f` is translated right by `n`, the polygon is unchanged under an isometric scalar extension
   `L/K` carrying a compatible normed additive valuation, and the polygon of `Polynomial.reverse f`
   is the reflection `i ↦ h (d - i)` of the polygon of `f`, where `d = natDegree f`. ⚠ The
   reflection is what relates this roadmap's `coeff 0 = 1` normalisation to the monic normalisation
   used for Eisenstein polynomials, and §6.2 depends on it; it is a milestone, not a remark.
8. Prove the polygon does not depend on the choice of normed additive valuation beyond a rescaling:
   the polygons of `f` for `(v, e, b)` and for `(v', e', b')` on the same normed field differ by
   the positive scalar `log b' / log b` in height, because both `e (v x)` and `e' (v' x)` equal
   `-log ‖x‖` up to that scalar. In particular the polygon for `normAddValZ` on `ℚ_p` is the polygon
   for `normAddVal` divided by `log p`.

### 2.3 The Gauss norm as the supporting value

1. Prove that for the radius `c = b ^ m`, `gaussNorm norm c f = b ^ (-(the supporting value of the
   polygon at slope m))`, where the supporting value is the infimum over `k` of `h k - k·m`;
   equivalently the Gauss norm is the Legendre transform of the polygon. State it in the
   `gaussNorm` form, in the infimum form, and in the attained form "the Gauss norm is the term at
   the right endpoint of the face of slope `m`", which is the one the later layers use. ⚠ Check the
   sign against a worked example before building on it: for `1 - pX` over `ℚ_p` with `v p = 1`, at
   `c = p²` (so `m = 2`) the Gauss norm is `p`, and `h 1 - 1·2 = -1`, giving `p ^ 1`.
2. Prove `HasGaussNorm norm c f` is equivalent to the supporting value being finite, and relate it to
   `PowerSeries.IsRestricted c f`. ⚠ These are not the same condition: restrictedness is decay and
   is strictly stronger than boundedness. Prove the implication that holds and give the example
   separating them.
3. Prove the Gauss norm is attained at an index exactly when the polygon has a vertex on the
   supporting line, and that for a polynomial it is always attained.
4. Prove `m ↦ -log_b (gaussNorm norm (b ^ m) f)` is concave and piecewise affine with the unit slopes
   as its breakpoints — the polygon and the Gauss norm function determine each other.

### 2.4 Purity, first breaks, and distinguished polynomials

1. Define `IsPureSeries v f m` as purity of the polygon of `f`, and prove it is equivalent to: every
   Gauss-norm term at radius `b ^ m` is dominated by the leading one, with equality only at the two
   ends. Prove a pure polynomial of slope `m` has all its coefficients controlled by the line.
2. Define the first break of `f` and prove the line bounds it gives: `e (v aₖ) ≥ m·k` for all `k`,
   with equality at the break index, and strict inequality strictly between `0` and the break index
   when the break has length greater than one.
3. Prove that a polynomial whose first break is at index `i` with slope `m` is distinguished at
   radius `c = b ^ m` of degree `i`, in the sense that its Gauss norm at `c` is attained at `i` and
   nowhere later. Pin the name: reuse the predicate of the adic-spaces roadmap's §0.5 material if
   one is adopted there, and otherwise define `IsDistinguishedAt f c i` here and state that it is
   the normed analogue of `Polynomial.IsWeaklyEisensteinAt`.
4. Prove a polynomial that is irreducible over `K` and has `coeff 0 = 1` is pure, and that a pure
   polynomial of slope `m` has all its roots of valuation `-m` — the second half after Layer 4,
   cross-referenced from here.

### Examples

Over `ℚ_p` with `v p = 1`, compute the polygon and the slope multiset of: `1 - X` (slope `0`) and
`1 - pX` (slope `1`); `1 + pX + p³X²` (slopes `1, 2`); `1 + pX + p²X² + ⋯` (a pure series of slope
`1`); `∑ pⁱ² Xⁱ`, an entire series with unit slopes `1, 3, 5, …`; `1 + 3^{2j+1} X²` over `ℚ_3`, pure
of slope `j + ½`; a polynomial with a collinear interior point; `Φ_p(X + 1) / p`, where `Φ_p` is the
`p`-th cyclotomic polynomial, pure of slope `-1/(p-1)`, against `Φ_p` itself, whose polygon is flat
at height `0`.

### Dependencies

Layers 0 and 1; Mathlib's Gauss-norm and `IsRestricted` files.

---

## Layer 3: Weierstrass factorisation along the polygon

`K` is complete from here on. The content of this layer is that each vertex of the polygon splits
the series. Radii are written `c = b ^ m` so that the slope form is always at hand.

### 3.1 Weierstrass division at an arbitrary radius

The adic-spaces roadmap's §0.5 asks for Weierstrass division and preparation over a complete
rank-one nonarchimedean field, for the Tate algebra `K⟨X⟩`, i.e. at radius `1`. This roadmap needs
it at an arbitrary radius `c > 0`, and that is **not** a corollary by rescaling: the substitution
`X ↦ cX` leaves `K⟨X⟩` only when `c` is a value of the norm, so the general case is a genuine
strengthening when the value group is neither divisible nor dense.

1. State and prove Weierstrass division at radius `c`: for `f` restricted at `c` and `g` restricted
   at `c` and distinguished at `c` of degree `i`, there are a unique restricted `q` and a unique
   polynomial `r` of degree less than `i` with `f = g·q + r`, together with the Gauss-norm bounds on
   `q` and `r`.
2. Deduce Weierstrass preparation at radius `c`: a series distinguished at `c` of degree `i`
   factors as a polynomial of degree `i` times a unit of the ring of series restricted at `c`, with
   the unit congruent to a constant.
3. Prove the units of the ring of series restricted at `c = b ^ m` are exactly the series whose
   polygon has no unit slope at most `m`, equivalently whose Gauss norm at `c` is attained only at
   index `0`.
4. If the implementation of the adic-spaces roadmap's §0.5 already delivers the arbitrary-radius
   form, this section consumes it and proves nothing. State the dependency that way round and do not
   duplicate.

### 3.2 Factorisation at the first break

Let `f` be restricted at `b ^ m` with `coeff 0 f = 1`, and suppose the first break of its polygon is
at index `i` with slope `m`.

1. `f = g · h` with `g` a polynomial of degree `i` with `g 0 = 1` whose polygon is the first segment
   (so `g` is pure of slope `m`), and `h` restricted at `b ^ m` with no unit slope at most `m`.
2. The Gauss norm of `f` at `b ^ m` is attained, `gaussNorm norm (b ^ m) (f - g) < gaussNorm norm (b ^ m) f`,
   and `gaussNorm norm (b ^ m) (h - 1) < 1`.
3. `h` has no zero in the closed ball of radius `b ^ m` in any valued extension of `K`, and is a
   unit of the ring of series restricted at `b ^ m`.
4. The factorisation is unique subject to `deg g = i` and `g 0 = 1`.

### 3.3 Factorisation at an arbitrary vertex

Generalise §3.2 from the first vertex to the `k`-th. Let the `k`-th segment of the polygon of `f`
have slope `m` and end at abscissa `j₀`, and let `f` be restricted at `b ^ m`.

1. `f = g · h` with `g` a polynomial of degree `j₀` with `g 0 = 1`, `h` restricted at `b ^ m` with
   `gaussNorm norm (b ^ m) (h - 1) < 1`, and `gaussNorm norm (b ^ m) (f - g) < gaussNorm norm (b ^ m) f`.
2. The polygon of `g` agrees with the polygon of `f` on `[0, j₀]`: same unit slopes at every index
   below `j₀`. ⚠ Do not state the bound on `f - g` as `< 1`; that is correct only on the first
   segment, where the Gauss norm of `f` is `1`. The scale-correct form is the one above.
3. The factorisation is unique subject to `deg g = j₀` and `g 0 = 1`, and is compatible with
   passing from the `k`-th vertex to the `(k+1)`-st: the degree-`j₀` factor divides the next one.

### 3.4 Slope factorisation

1. A polynomial with `coeff 0 = 1` factors as a product over the distinct slopes of its polygon of
   pure polynomials, one for each slope, of degree the multiplicity of that slope, and the
   factorisation is unique up to order. This is §3.3 iterated over the vertices.
2. An entire power series with `coeff 0 f = 1` and unbounded slopes factors, for every `c > 0`, as a
   polynomial carrying exactly the unit slopes at most `log_b c` times a unit of the ring of series
   restricted at `c`.
3. The factors are coprime, and the decomposition is compatible with a larger radius.

### Examples

Factor `1 + pX + p³X²` over `ℚ_p` at each of its two slopes; exhibit the two factors of
`1 - X²/p` and check their polygons; carry out §3.3 at the second vertex of a polynomial with three
segments and check clause 2 on the nose.

### Dependencies

Layer 2; the adic-spaces roadmap §0.5 (see §3.1); `CompleteSpace K`.

---

## Layer 4: roots, zeros, and convergence

This is the layer the name "Newton polygon" is for: the slopes are the negatives of the valuations
of the roots.

### 4.1 Roots of a polynomial

`K` is complete; roots are taken in `AlgebraicClosure K`, normed by the spectral norm, with the
additive valuation of §1.5 extending `v` (convention 8); write `v̄` for it. Let `f` be a polynomial
with `coeff 0 f = 1`.

1. **The root count on a sphere.** If the `k`-th segment of the polygon of `f` has slope `m` and
   length `l`, then `f` has exactly `l` roots of valuation `-m`, counted with multiplicity.
2. **The root count in a ball.** The number of roots of valuation at least `-σ` (the closed ball of
   radius `b ^ σ`) is `faceRight σ`, and of valuation strictly greater than `-σ` (the open ball) is
   `faceLeft σ`. Deduce clause 1 from these two by subtraction, and prove both from the
   supporting-line and chord inequalities of §0.5 together with the factorisation of §3.3.
3. **The slope multiset is the root valuation multiset.** `Polynomial.newtonSlopes v f` equals the
   image of `Polynomial.roots (f.map (algebraMap K (AlgebraicClosure K)))` under `x ↦ -(e (v̄ x))`,
   as multisets. This is the clean form of clauses 1 and 2 and should be the statement other
   developments cite. For `K = ℚ_p` with `v = normAddValZ` it reads: the slopes of `f` are the
   negatives of the `p`-adic valuations of its roots, as rational numbers.
4. Prove the three statements with the roots taken in an arbitrary complete valued extension in which
   `f` splits, carrying a normed additive valuation compatible with `(v, e, b)`, with the canonical
   form as the instance, and prove the transport to `K` itself when `K` is algebraically closed.
5. Prove the converse realisability statement: over an algebraically closed complete `K`, every
   finite convex polygon anchored at the origin whose slopes are negatives of values of `v̄` is the
   polygon of a polynomial, namely `∏ (1 - X/aᵢ)` for roots `aᵢ` of the prescribed valuations.

### 4.2 Purity and irreducibility over a complete field

1. `f` is pure of slope `m` if and only if all its roots have valuation `-m`.
2. An irreducible polynomial with `coeff 0 = 1` is pure. Deduce that the Newton polygon of the
   minimal polynomial of an algebraic element `x` is a single segment of slope `-(e (v̄ x))`.
3. The Newton polygon of `f` refines the factorisation of `f`: distinct slopes force distinct
   irreducible factors, so a polygon with `r` distinct slopes forces at least `r` irreducible
   factors. With §3.4 this gives the slope decomposition of `f` into pure factors.

### 4.3 Zeros of a power series in a disc

`L` is a complete ultrametric field extending `K` isometrically and carrying a compatible normed
additive valuation; `ℂ_[p]` over `ℚ_[p]` with `normAddValQ ℂ_[p] p` is the model case and every
statement here must be instantiated at it.

1. Define convergence of `f` at a point of `L` by `HasSum`, and prove that `f` restricted at `c`
   converges at every point of the closed ball of radius `c`, with the sum bounded by the Gauss norm.
   Prove the converse when `c` is the norm of an element of `L`, and give the example showing that
   without such an element convergence on the whole closed ball does not imply restrictedness at `c`.
2. **The zeros in a ball are the roots of the polynomial factor.** For `f` restricted at `b ^ m` with
   `coeff 0 f = 1` and the factorisation `f = g·h` of §3.3 at a vertex ending at `j₀`, a point of the
   closed ball of radius `b ^ m` is a zero of `f` if and only if it is a root of `g`. Deduce that `f`
   has exactly `faceRight m` zeros in that ball, with multiplicity, and exactly `l` zeros of
   valuation `-m` when `m` is a slope of multiplicity `l`.
3. Every zero of `f` in the closed ball of radius `b ^ m` has valuation `-μ` for some unit slope
   `μ ≤ m`: no zeros off the spheres cut out by the slopes.
4. The multiplicity of a zero of `f` is its multiplicity as a root of `g`, so multiplicities are
   finite and the zero set in a closed ball is finite.

### 4.4 The radius of convergence

1. Define the radius of convergence of `f` relative to `L` as the supremum of `‖x‖` over points of
   `L` at which `f` converges. ⚠ This is relative to `L` of necessity: over `ℚ_[p]` the attainable
   norms are only powers of `p`, so the supremum can undershoot the analytic radius. Statements
   needing points of prescribed norm carry a density hypothesis on the norms of `L`, and that
   hypothesis must be stated, not assumed away. Prove it holds for `ℂ_[p]`.
2. **The radius of convergence is `b ^ (sup of the slopes)`**, as two inequalities: the lower bound
   needs the density hypothesis, the upper bound does not. Prove each from the per-radius statement
   relating restrictedness at `b ^ m` to the slopes being at least `m`.
3. ⚠ Sharpness needs infinitely many nonzero coefficients: for a polynomial the radius is infinite
   while the slopes are bounded. State the polynomial case separately rather than carrying a
   hypothesis that hides it.
4. `f` is entire (restricted at every radius) if and only if its unit slopes tend to `+∞`.

### 4.5 Entire series and their zeros

1. An entire series with `coeff 0 f = 1` has, for each `c`, finitely many zeros in the closed ball of
   radius `c`, and its zero multiset is countable with valuations tending to `-∞`.
2. **The Weierstrass product.** An entire series with `coeff 0 f = 1` over a complete algebraically
   closed `L` is the limit of its polynomial factors, and is determined by its zero multiset: two
   entire series with `coeff 0 = 1` and the same zeros with multiplicity are equal. Prove the product
   `∏ (1 - X/aᵢ)` converges for any multiset of nonzero `aᵢ` with `‖aᵢ‖ → ∞` and has exactly those
   zeros.
3. Deduce that an entire series with no zeros and `coeff 0 f = 1` is `1`, and that an entire function
   with finitely many zeros is a polynomial times a unit.

### Examples

Over `ℚ_p` and `ℂ_p` with `v p = 1`: the zeros of `1 - X` and `1 - pX`; `Φ_p(X + 1) / p` has all
roots of valuation `1/(p-1)`; `∑ Xⁱ/i!` has radius of convergence `p^{-1/(p-1)}` and no zero inside
it; `∑ pⁱ² Xⁱ` is entire with one zero of valuation `-(2i+1)` for each `i`; a series whose polygon
ends in a ray of slope `m` has radius exactly `b ^ m` and no zero of valuation `-m`.

### Dependencies

Layers 2 and 3; `spectralNorm`; `ℂ_[p]`; `Polynomial.roots`.

---

## Layer 5: products

### 5.1 The polygon of a product is the Minkowski sum

Let `f, g` be power series with `coeff 0 = 1` whose polygons have unbounded slopes — polynomials, or
entire series.

1. The ultrametric inequality puts the points of `f·g` on or above the Minkowski sum:
   `e (v (coeff n (f·g))) ≥ min_{i+j=n} (e (v (coeff i f)) + e (v (coeff j g)))`.
2. At the endpoints of a face the minimising split is unique (§0.6.4), so the inequality is an
   equality there.
3. Therefore the polygon of `f·g` is the Minkowski sum of the polygons of `f` and `g`, by the two
   inequalities: the subgradient property of §0.6.2 with the supporting-line lemma gives one, and
   every abscissa lying on a face whose endpoints are points of `f·g` gives the other via the chord
   inequality.
4. ⚠ `SlopesUnbounded` cannot be dropped: `(1 - X)·∑ Xⁱ = 1`, whose polygon is a single point while
   the Minkowski sum is the horizontal ray. Record this as a counterexample, not as a remark.

### 5.2 Slope multisets and multiplicities add

1. `Polynomial.newtonSlopes v (f * g) = Polynomial.newtonSlopes v f + Polynomial.newtonSlopes v g`
   as multisets.
2. `faceRight σ` and `faceLeft σ` are additive, so the multiplicity of each slope adds.
3. With §4.1.3 this is the multiset statement that the roots of a product are the roots of the
   factors; prove that the two routes agree.

### 5.3 Initial segments

If every unit slope of `g` among the first `n` is at most every unit slope of `f`, the polygon of
`f·g` agrees with that of `g` up to abscissa `n`, raised by the height of `f` at `0`. This is the
form in which a finite factor supplies the first slopes of a product, and it is the statement the
slope-theoretic applications of a Fredholm determinant consume.

### 5.4 The Gauss norm of a product

1. For power series restricted at `c > 0` over a nonarchimedean field,
   `gaussNorm norm c (f * g) = gaussNorm norm c f * gaussNorm norm c g`. Mathlib has this for
   polynomials (`Polynomial.gaussNorm_mul`) and only the inequality for power series, so this is the
   milestone. Prove it from §5.1 by evaluating both sides as supporting values, and separately by a
   direct argument if that is shorter.
2. Deduce that the ring of series restricted at `c` is a domain, that the Gauss norm at `c` is a
   multiplicative norm on it, and that it is a nonarchimedean absolute value in Mathlib's sense.
3. Deduce the sum statement: the polygon of `f + g` lies on or above the pointwise minimum of the two
   polygons, with equality at every abscissa where the two heights differ.

### Examples

`(1 - X)(1 - pX)` over `ℚ_p`; a product of two pure polynomials of different slopes; the product
counterexample of §5.1.4; multiplicativity of the Gauss norm at a radius where neither factor attains
its norm at index `0`.

### Dependencies

Layers 0 (§0.6), 2, 4.

---

## Layer 6: discretely valued fields

The specialisation in which `Γ = ℤ` and the polygon becomes a tool for irreducibility and
ramification. `K` is complete and discretely valued, `v = normAddValZ K` with `v π = 1` at a
uniformiser `π`, and `b = ‖π‖⁻¹`; `ℚ_[p]` with `v p = 1` and `b = p` is the model case.

### 6.1 Denominators and ramification

1. The unit slopes of a polynomial over `K` are rational, with denominators dividing the length of
   their segment (§2.2.3). State the sharp form: a segment from `(i₀, y₀)` to `(i₁, y₁)` with
   `y₀, y₁ ∈ ℤ` has slope `(y₁ - y₀)/(i₁ - i₀)`.
2. A root of a pure polynomial of slope `a/l` in lowest terms has valuation `-a/l`, so the
   `ℤ`-valued valuation of any finite extension `L` containing it, normalised at a uniformiser of
   `L`, takes the value `-a · e(L/K)/l` there, and `l` divides the ramification index `e(L/K)`. The
   ramification index and the discreteness of `L` are cited from the local-fields-and-ramification
   roadmap, as in §1.3.6.
3. The polygon of the minimal polynomial of an algebraic element computes the element's valuation and
   bounds the ramification of the extension it generates.

### 6.2 Irreducibility criteria

1. **The pure-with-coprime-slope criterion.** A polynomial with `coeff 0 = 1` whose polygon is a
   single segment of slope `a/l` in lowest terms with `l` the degree is irreducible over `K`.
2. Deduce the Eisenstein criterion over `K` as the case `a = -1`, and prove the deduction against
   Mathlib's `Polynomial.IsEisensteinAt`. ⚠ State the orientation explicitly, because the two
   normalisations disagree on the sign: a *monic* Eisenstein polynomial of degree `n` has a polygon
   running from `(0, 1)` to `(n, 0)`, a single segment of slope `-1/n`, whose roots therefore have
   valuation `1/n`; its reverse, normalised by `coeff 0 = 1`, has the same slope `-1/n`, and it is
   to this form that clause 1 applies directly. §2.2.7 is the bridge, and the criterion must be
   stated in both normalisations.
3. A polynomial whose polygon has `r` distinct slopes with pairwise coprime data has at least `r`
   irreducible factors with prescribed degrees; state the bound the polygon gives on the
   factorisation type, and do not claim more than a bound, since the polygon does not determine the
   factorisation.

### 6.3 The adic and normed theories agree

This is the section that prevents the two Weierstrass theorems from drifting apart.

1. For `f` a power series over the valuation ring `𝒪` of `K`, relate `PowerSeries.IsRestricted c f`
   for `c ≤ 1` to the adic hypotheses of `Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`,
   and prove that `f` is distinguished at radius `1` of degree `i` in the sense of §2.4 if and only if
   it is a Weierstrass divisor of degree `i` in Mathlib's adic sense.
2. Deduce that Mathlib's adic Weierstrass division over `𝒪` and the normed Weierstrass division of
   §3.1 at radius `1` have the same content over `𝒪`, and prove each from the other where the
   hypotheses match.
3. For `f` over `𝒪` nonzero, define `μ f` as the minimum of the valuations of the coefficients and
   `λ f` as the *smallest* index at which that minimum is attained. Prove that `f = π^μ · u · P`
   with `u` a unit of `𝒪⟦X⟧` and `P` a distinguished polynomial of degree `λ`, and that both are
   read off the polygon: `μ` is the minimum value of the polygon, attained exactly on its face of
   slope `0`, and `λ` is the left endpoint of that face, `order f + faceLeft 0`. ⚠ It is the left
   endpoint, not the right: the roots of `P` are the zeros of `f` in the *open* unit disc, which are
   the slopes strictly less than `0`. For `f = p + X + X²` over `ℤ_p` the minimum `0` is attained at
   indices `1` and `2`, and `λ = 1`.
4. Prove `λ` and `μ` are additive on products, from §5.2.

### Examples

`1 + pX + p³X²` is irreducible over `ℚ_[p]`; `X^p - p` is Eisenstein with polygon the single
segment of slope `-1/p`, so its roots have valuation `1/p`; `Φ_p(X + 1) / p` is pure of slope
`-1/(p-1)` and irreducible by §6.2.1; `p + X + X²` over `ℤ_[p]` has `μ = 0` and `λ = 1`; the `λ`-
and `μ`-invariants of a product of two series over `ℤ_[p]`.

### Dependencies

Layers 1–5; Mathlib's Eisenstein and adic Weierstrass files; the local-fields-and-ramification
roadmap for §6.1.2.

---

## Dependency graph

```text
Layer 0 ──┐
          ├──→  Layer 2  →  Layer 3  →  Layer 4  →  Layer 6
Layer 1 ──┘                          ↘            ↗
                                        Layer 5
```

Layers 0 and 1 are independent of each other and of everything else. Layer 5 uses §0.6 and Layer 4
only for §5.2.3; Layer 6 uses Layers 4 and 5. The adic-spaces roadmap is cited once, at §3.1; the
local-fields-and-ramification roadmap is cited at §1.3.6 and §6.1.2.

## Acceptance examples

The following should be proved alongside the general theory, and they are the things a reviewer
should check are present. All are over `ℚ_p` with `v p = 1` unless stated.

- `normAddValZ ℚ_[p] = Padic.addValuation`, `normAddValQ ℂ_[p] p p = 1`, and
  `normAddValQ ℂ_[p] p (p^{1/3}) = 1/3`.
- The polygon of `1 - X` is the single unit segment of slope `0`, and `1 - pX` has slope `1`; the one
  root of each has valuation `0`, respectively `-1`.
- `1 + 3^{2j+1} X²` over `ℚ_3` is pure of slope `j + ½`, as an equality of rational numbers, and its
  two roots have valuation `-(j + ½)`. This is the shape of statement the additive normalisation
  exists for.
- `Φ_p(X + 1) / p` is pure of slope `-1/(p-1)`, is irreducible by §6.2.1, and all its roots
  `ζ - 1` have valuation `1/(p-1)`; `Φ_p` itself has polygon flat at height `0` and all its roots are
  units.
- `1 + pX + p³X²` has polygon with slopes `1, 2`, exactly one root of valuation `-1` and one of
  valuation `-2`, and factors accordingly by §3.4.
- `∑ pⁱ² Xⁱ` is entire, has unit slopes `1, 3, 5, …`, and exactly one zero of valuation `-(2i+1)` in
  `ℂ_[p]` for each `i`.
- `(1 - X)·∑ Xⁱ = 1`: the product formula fails here, and the failure is exactly the
  `SlopesUnbounded` hypothesis.
- `∑ Xⁱ/i!` has radius of convergence `p^{-1/(p-1)}` and no zero inside it.
- The series with coefficient valuations `⌈k√2⌉` has polygon the ray of slope `√2`: its heights are
  irrational although every point is integral.
- A polynomial with a collinear interior point: its polygon has two points on it that are not
  vertices, and the slope multiset is nevertheless correct.
- `X^p - p`: Eisenstein, polygon the single segment of slope `-1/p`, irreducible, roots of valuation
  `1/p`, generating a totally ramified extension of degree `p`.
- `p + X + X²` over `ℤ_[p]`: `μ = 0`, `λ = 1`, and the Weierstrass factorisation of §6.3.3 is
  explicit.

## Beyond this roadmap

⚠ **This section is a roadmap-for-a-roadmap. Do not attempt any of it here.** It records what this
roadmap is for, so that the conventions above are chosen with the sequel in mind.

The Newton polygon of the characteristic power series `det(1 - T·u)` of a compact operator on a
nonarchimedean Banach module reads the valuations of the operator's eigenvalues, via Layer 4 applied
to a series whose coefficients are determinants. That, and the resulting slope theory of Hecke
operators on spaces of overconvergent automorphic forms, are substantial developments in their own
right and belong in their own roadmaps. What they ask of this one is that Layers 4 and 5 hold for
series over a complete nonarchimedean *field*, and that the slopes be read with respect to the
normalised `ℤ`- or `ℚ`-valued valuation of Layer 1, so that a statement such as "the eigenvalues of
`U_3` have valuation `j + ½`" is an equality of rational numbers. Both are what is specified above.

## References

- K. S. Kedlaya, *p-adic differential equations*, 18.787 (MIT, Fall 2007), unit "Newton polygons",
  §§1–2, `https://kskedlaya.org/18.787/newton-poly.pdf` — [Ked07]. Proposition 1 there is Robba's
  lemma and Corollary 2 is the product formula; this is the primary source for Layers 0 and 5.
- N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58 (1984),
  Ch. IV §3 (vertices, p. 97) and §4 (the three types of polygon, pp. 99–102; Lemma 6 is the linear
  factor case of the product formula) — [Kob84].
- M. Lazard, *Les zéros des fonctions analytiques d'une variable sur un corps valué complet*,
  Publ. Math. IHÉS 14 (1962), 47–75 — [Laz62]. The primary source for Layer 4: zeros of a power
  series on a disc, and the role of the completeness and of the value group.
- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322 (1999), Ch. II §§3–4 (valuations,
  discrete valuations, completions) and §8 (extensions of valuations) — [Neu]. The source for the
  normalisations of Layer 1 and the ramification input of §6.1.
- S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261 (1984) — [BGR].
  BGR §1.4 for the Gauss norm and Gauss's lemma, BGR §3.2 for the spectral norm, BGR §5.2 for
  Weierstrass division and preparation in `K⟨X⟩` (keyed in BGR's own numbering, not this roadmap's).
- F. Q. Gouvêa, *p-adic Numbers: An Introduction*, 3rd ed. (2020), §6.4 — the elementary account of
  the polygon and the root valuations, and the source for the worked examples.
- L. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §7.1 — the `p`-adic
  Weierstrass preparation theorem and the `μ`- and `λ`-invariants of §6.3.
- Liu–Wan–Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J. 166 (2017);
  arXiv:1412.2584, §3.23 — [LWX]. The initial-segment form of the product formula in §5.3 is used
  there and is stated in that shape for it.

⚠ **Orientation.** [Kob84] and [Ked07] take the lower convex hull of `(i, v aᵢ)` with increasing
slopes, as this roadmap does, and a root of valuation `-m` corresponds to a slope `m`. Other
sources negate the slopes, take the upper hull, or plot `(i, -v aᵢ)`. When transcribing a statement,
check the orientation against convention 6 rather than assuming it.

## Existing Lean work

The principal source of existing code is `github.com/WilliamCoram/PhD` (Apache-2.0), at commit
`fdc44e2` (2026-09-12): the directories `PhD/Main/NewtonPolygons/` and
`PhD/Main/ForMathlib/NumberTheory/NewtonPolygon/` for Layers 0 and 2–5, and the six files
`PhD/Main/ForMathlib/RingTheory/Valuation/AddVal/{Basic,RankOne,Commensurable,Discrete}.lean`,
`PhD/Main/ForMathlib/Topology/Algebra/Valued/AddVal.lean` and `PhD/Main/ForMathlib/NumberTheory/Padics/AddVal.lean`
for Layer 1. It is the only formalisation of this material known to us; Layer 6 is new, and so is
§1.5.

The existing material in those directories is by William Coram, who has agreed to its integration
into Tau Ceti. ⚠ The wider repository also contains files by other authors, derived from the FLT
project and from Mathlib; those are not migration sources for this roadmap, and the provenance of
anything copied must be checked file-by-file rather than directory-by-directory.

Two separate audits are recorded below, for the reason the adic-spaces roadmap gives: a declaration
with no direct `sorry` is not the same as a theorem whose dependency cone is axiom-clean. The direct
column is a file-level `grep` count, which over-counts (comments match) and sees no cross-file
dependence. At the pin above, every file listed has a direct count of **0**. That pin
names the commit at which the source tree acquired its present layout; the mathematics it records
was complete at commit `1f43221` (2026-09-11). The transitive column must be regenerated at
migration by a `#print axioms` gate on the capstones in Tau Ceti CI; the source project reports
every directory listed clean on `propext`, `Classical.choice` and `Quot.sound`, and that claim is
to be re-verified, not carried over.

| Roadmap section | Existing source | Direct status at the pin | Transitive status | Roadmap status |
|---|---|---|---|---|
| §0.1 convex sequences | `NewtonPolygons/Height.lean` | no direct `sorry` | audit required | present, to be restated on the height function (convention 1) |
| §0.2 the specification | `NewtonPolygons/Spec.lean` | no direct `sorry` | audit required | present as `IsNewtonPolygonOf`; uniqueness is height-equality at the pin |
| §0.3 existence | `NewtonPolygons/SpecConstruction.lean`, `ForMathlib/…/NewtonPolygon/Construction.lean` | no direct `sorry` | audit required | present |
| §0.4 slopes and vertices | `ForMathlib/…/NewtonPolygon/Basic.lean`, `NewtonPolygons/Height.lean` | no direct `sorry` | audit required | present; slope **multiset** is new |
| §0.5 supporting lines and faces | `NewtonPolygons/Face.lean`, `Support.lean`, `OfSlopes.lean` | no direct `sorry` | audit required | present |
| §0.6 Minkowski sums | `NewtonPolygons/Product.lean` (`minkowskiHeight`) | no direct `sorry` | audit required | present, entangled with Layer 5; separate it |
| §1.1 usable target | `AddVal/Basic.lean`; also mathlib4#43578 and mathlib4#43580, which are the same material | no direct `sorry` | audit required | present; shape it as those pull requests do (conventions, above) |
| §1.2 real additive valuation | `AddVal/RankOne.lean`, `Valued/AddVal.lean` (`normAddVal`) | no direct `sorry` | audit required | present |
| §1.3 `ℤ`-valued, `ℚ_p` | `AddVal/Discrete.lean`, `Valued/AddVal.lean` (`normAddValZ`), `Padics/AddVal.lean` | no direct `sorry` | audit required | present; §1.3.6 and the Laurent-series instance are new |
| §1.4 `ℚ`-valued at an element | `AddVal/Commensurable.lean`, `Valued/AddVal.lean` (`normAddValQ`) | no direct `sorry` | audit required | present; the uniqueness statement §1.4.4 is new |
| §1.5 extensions and `ℂ_p` | — | — | — | new |
| §2.1–2.2 coefficient valuations and the polygon | `NewtonPolygons/CoeffVal.lean`, `ForMathlib/…/NewtonPolygon/PowerSeries.lean` | no direct `sorry` | audit required | present for `(normAddVal, id, exp 1)` only; the `(v, e, b)` form and §2.2.3, §2.2.8 are new |
| §2.3 Gauss norm as supporting value | scattered through `CoeffVal.lean` and `FirstBreak.lean` | no direct `sorry` | audit required | partial; the Legendre-transform statement and §2.3.4 are new |
| §2.4 purity and first breaks | `NewtonPolygons/FirstBreak.lean` | no direct `sorry` | audit required | present |
| §3.1 Weierstrass at an arbitrary radius | `PhD/Main/ForMathlib/` Weierstrass development | no direct `sorry` | audit required | present; coordinate with the adic-spaces roadmap §0.5 |
| §3.2 factorisation at the first break | `NewtonPolygons/PolynomialRoots.lean` | no direct `sorry` | audit required | present |
| §3.3 factorisation at a vertex | `NewtonPolygons/PowerSeriesZeros.lean` | no direct `sorry` | audit required | present |
| §3.4 slope factorisation | — | — | — | new as a single statement; the ingredients exist |
| §4.1 root counts | `NewtonPolygons/PolynomialRoots.lean`, `RootFaces.lean` | no direct `sorry` | audit required | present, stated with a hypothesised valuation on the closure and absolute values `exp m`; restate with the canonical valuation (convention 8) and in valuation form |
| §4.2 purity and irreducibility | `NewtonPolygons/FirstBreak.lean` | no direct `sorry` | audit required | partial |
| §4.3 zeros in a disc | `NewtonPolygons/PowerSeriesZeros.lean` | no direct `sorry` | audit required | present |
| §4.4 radius of convergence | `NewtonPolygons/RadiusOfConvergence.lean` | no direct `sorry` | audit required | present, including the density hypothesis |
| §4.5 entire series and Weierstrass products | — | — | — | new |
| §5.1–5.3 products | `NewtonPolygons/Product.lean` | no direct `sorry` | audit required | present |
| §5.4 Gauss norm of a product | — | — | — | new for power series; Mathlib has the polynomial case |
| Layer 6 | — | — | — | new |

⚠ **Do not treat the existing file layout as prescriptive.** The polygon code is organised around a
segment-decorated structure with `⊥` and `⊤` junk values in two places, and conventions 1 and 5
deliberately depart from it; the source author's own notes record the resulting awkwardness (a
degenerate one-point polygon has a finite height but a `⊥` unit slope, so finiteness of the height
does not exclude the junk slope and several statements carry a hypothesis excluding it). It is also
instantiated throughout at the unnormalised valuation `x ↦ -log ‖x‖`, which convention 2 makes the
least specific of three instances. The migration is expected to restate the theory on the height
function and over a general normed additive valuation, not to port the structure or the
normalisation.
