# Development Plan: rigid analytic geometry, Layer 0 (the Tate algebras)

Board: `.mathlib-quality/tauceti-rag-layer0/` (named; the default board path belongs to another
project — always pass this path to `/beastmode`, and never touch a sentinel that names another
board). Specification: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 0 (§0.1–§0.4)
and its Examples. Code: `PhD/TauCeti/Code/RigidAnalyticGeometry/`, module prefix
`PhD.TauCeti.Code.RigidAnalyticGeometry`, importing Mathlib and the Tau Ceti chain only — never
`PhD.Main.*` (CI-gated two-chain rule). Planned 2026-10-01/02.

## Goal

Everything BGR's Chapter 5 says about the Tate algebra `Tₙ = K⟨X₁, …, Xₙ⟩` that the later layers of
the roadmap consume, for a nonarchimedean normed field `K` (complete where stated):

```lean
-- the Tate algebra (TateAlgebra/Basic.lean)
abbrev Affinoid.TateAlgebra (K) [NormedField K] [IsUltrametricDist K] (n : ℕ) :=
  MvPowerSeries.Restricted K (1 : Fin n → ℝ)
-- §0.1.2  the reduction (TateAlgebra/Reduction.lean)
noncomputable def MvPowerSeries.Restricted.reductionEquiv :
    (unitClosedBall (Restricted K 1) ⧸ openUnitBallIdeal (Restricted K 1)) ≃+*
      MvPolynomial σ (ResidueField (unitClosedBall K))
theorem MvPowerSeries.Restricted.jacobson_bot : Ideal.jacobson (⊥ : Ideal (Restricted K 1)) = ⊥
-- §0.1.3–4  the Gauss norm is the supremum norm (TateAlgebra/MaxModulus.lean)      MILESTONE M1
theorem MvPowerSeries.Restricted.supSeminorm_eq_norm (f : Restricted K (1 : σ → ℝ)) :
    Affinoid.supSeminorm K f = ‖f‖
-- §0.2  Weierstrass finiteness and distinguished charts (Finiteness.lean, Chart.lean)
theorem IsWeierstrassPolynomial.finite_comp_ofTail (hω : IsWeierstrassPolynomial K n ω)
    (φ : TateAlgebra K (n + 1) →+* A) (hφ : φ.Finite) (h0 : φ (ofPolynomial K n ω) = 0) :
    (φ.comp (ofTail K n)).Finite
theorem exists_shear_isMulDistinguishedX0 {f : TateAlgebra K (n + 1)} (hf : f ≠ 0) :
    ∃ (e : Fin n → ℕ) (s : ℕ), IsMulDistinguishedX0 (shear K n e f) s
-- §0.3.2–4  Rückert's applications (TateAlgebra/Rueckert.lean)                    MILESTONE M2
instance : IsNoetherianRing (TateAlgebra K n)
instance : UniqueFactorizationMonoid (TateAlgebra K n)
instance : IsJacobsonRing (TateAlgebra K n)
theorem Affinoid.TateAlgebra.ringKrullDim_eq (K) … (n : ℕ) : ringKrullDim (TateAlgebra K n) = n
-- §0.3.1, §0.3.5  ideals are strictly closed (TateAlgebra/StrictlyClosed.lean)     MILESTONE M3
theorem MvPowerSeries.Restricted.exists_forall_norm_sub_le_ideal (I : Ideal 𝕋) (f : 𝕋) :
    ∃ a₀ ∈ I, ∀ a ∈ I, ‖f - a₀‖ ≤ ‖f - a‖
theorem MvPowerSeries.Restricted.norm_quotient_mk_mem_range_norm (I : Ideal 𝕋) (f : 𝕋) :
    ‖Ideal.Quotient.mk I f‖ ∈ Set.range (norm : K → ℝ)
-- §0.4  weak stability and Japaneseness, characteristic zero (TateAlgebra/Stable.lean)  MILESTONE M4
theorem Affinoid.TateAlgebra.isWeaklyStable_fractionRing (n : ℕ) :
    letI := IsFractionRing.normedField (TateAlgebra K n) (FractionRing (TateAlgebra K n))
    IsWeaklyStable (FractionRing (TateAlgebra K n))
theorem Affinoid.TateAlgebra.isJapaneseRing (n : ℕ) : IsJapaneseRing (TateAlgebra K n)
```

together with: the Banach-algebra structure, density of polynomials and `|Tₙ| = |K|` (§0.1.1); the
criteria for power-bounded, topologically nilpotent and unit elements (§0.1.2); evaluation and
substitution homomorphisms and their compatibility with the reduction; the supremum seminorm of a
Banach algebra and BGR 3.8.2/1–2; Weierstrass polynomials (§0.2.1); abstract Rückert overrings; bald
subrings and the lifting of orthonormal bases (Bosch 1.3); and the roadmap's worked examples.

**Not on this board (the user's call):** the characteristic-`p` half of §0.4.2–§0.4.3 (BGR 5.3.1/2
and Part A's b-separable modules, spaces of countable type, `K^{p⁻¹}`, tame modules). It fails the
confidence gate today — see `decomposition.md`, "Unticketed sub-tree" — and is recommended as a board
of its own once the `p`-adic functional analysis roadmap's §2.2/§2.4 exist in the chain.

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 0 | the specification |
| [BGR] | Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, Grundlehren 261 (1984). The PDF is an image scan; hand transcriptions with line locators: `references/bgr-5.1.md` (5.1.1–5.1.4, pp. 192–199), `bgr-5.2.md` (5.2.1–5.2.7, pp. 200–211), `bgr-5.3.1.md` (pp. 212–213), `bgr-3.2.md` (3.2.2/4, 3.2.3, 3.4.1, pp. 138–146), `bgr-3.5.md` (pp. 149–156), `bgr-3.8.md` (pp. 168–182), `bgr-2.md` (2.2.5, 2.2.6, 2.3, 2.6, 2.7.1), `bgr-4.md` (Chapter 4), `bgr-6.1.2.md`, `bgr-7.1.1.md` | every statement of the layer |
| [Bo] | Bosch, *Lectures on Formal and Rigid Geometry* (2008 preprint) — `references/bosch-lectures.txt`: §1.2 from l. 332 (1.2/4 l. 431, 1.2/5 l. 442, 1.2/6 l. 461, 1.2/7 l. 479, 1.2/8 l. 535, 1.2/9 l. 584, 1.2/10 l. 614, 1.2/12 l. 644, 1.2/13–15 l. 676–743), §1.3 from l. 746 (1.3/2 l. 767, 1.3/3 l. 774, 1.3/5 l. 820, 1.3/6 l. 839, 1.3/7 l. 885, 1.3/8 l. 935, 1.3/9 l. 944, 1.3/10 l. 956) | the second source for every statement; the *first* source for the maximum-modulus proof shape, the unit argument of 1.2/12, the dimension, and all of §1.3 |
| [SEAM] | `Restricted/**` — the restricted-power-series floor (see "The floor") | Gauss norm, completeness, `Tₙ₊₁ = Tₙ⟨X⟩`, Weierstrass division and preparation, units |
| [PFA] | `PhD/TauCeti/Code/PadicFunctionalAnalysis/{UnitBall, PowerBounded, Sums}.lean` (Tau Ceti chain, sorry-free) | unit balls, residue rings, norm criteria, product sums |
| [Mathlib] | pinned Mathlib (`bbc4475e`, `lean4 v4.33.0-rc1`) | see the inventory |

## The floor (decision, already executed)

[RM] says the adic-spaces roadmap's §0.5 "supplies" the ring `Tₙ`, its Gauss-norm topology,
`Tₙ ≅ T_{n−1}⟨Xₙ⟩` and Weierstrass division and preparation. None of that is in the Tau Ceti chain
of this repository. The roadmap's own rule decides what to do: *"Where a pull request is open, the
object is built here named and shaped as the pull request names and shapes it, so that if it lands
the Tau Ceti copy is deleted in favour of an import."* The user's mathlib4#42867 development (the
type `MvPowerSeries.Restricted`, its Gauss-norm `NormedRing`, completeness, `finSuccEquiv`,
multiplicative Weierstrass division and preparation) exists sorry-free under `PhD/Main/ForMathlib`;
it was **copied** (never imported: two-chain rule) into `Restricted/` — 21 files, 14 at the top level
and 7 under `Restricted/PowerSeries/`, by `scratch/port_floor.py`, with these changes only:

- imports rewritten; the local `Polynomial/GaussNorm` shadow and `MvPolynomial/GaussNorm` are not
  ported (two `norm_toRestricted` lemmas dropped);
- `PowerSeries.gaussNorm_C` and `gaussNorm_monomial` dropped (they now exist in Mathlib);
- `Units.lean` lost its power-bounded section (it is [PFA] here) and uses Mathlib's
  `isUnit_one_sub_of_norm_lt_one`;
- `Restricted/Algebra.lean` is new: the `Module` and `Algebra` instances of mathlib4#42867.

The floor is therefore not ticketed. `TateAlgebra/Tower.lean` (sorry-free) restates it at the unit
polyradius in the vocabulary of `Affinoid.TateAlgebra`: `coeffX0`, `ofPolynomial`, `ofTail`,
`isMulDistinguishedX0_iff`, and the six Weierstrass statements.

**Seam rules (binding).**

1. `Restricted R c` is an opaque `def`; cross it with term steps (`Restricted.ext`, `val_*`,
   `congrArg`), never by unfolding.
2. `Fin.tail (1 : Fin (n+1) → ℝ)` is definitionally but not syntactically `(1 : Fin n → ℝ)`.
   Crossing it is cheap only when the polyradius is given explicitly (`(c := (1 : Fin (n + 1) → ℝ))`);
   left to unification it times out. It is crossed once, in `Tower.lean`; **no other file mentions
   `Fin.tail`, `finSuccEquiv` of the floor, or `PowerSeries.Restricted`**.
3. Never `import Mathlib` in a file that imports the floor: the floor's `PowerSeries.IsRestricted`
   (the shape of mathlib4#39583/#42867) clashes with `Mathlib.RingTheory.PowerSeries.Restricted`.
   For the same reason do not import that Mathlib file or `Mathlib.RingTheory.Polynomial.GaussNorm`.
4. The distinguished variable is `X 0` (the one `MvPowerSeries.finSuccEquiv` splits off); BGR and
   Bosch distinguish the last variable.

## Mathlib inventory (every name verified by elaboration)

| Concept | Mathlib status | Board action |
|---|---|---|
| restricted series, Gauss norm as a function | `MvPowerSeries.IsRestricted`, `.subring`, `gaussNorm`, `HasGaussNorm` | [SEAM] builds the type and its normed-ring structure |
| `NoZeroDivisors (MvPowerSeries σ R)` | instance present | USE for `instIsDomain` |
| residue field of a local ring | `IsLocalRing.ResidueField`, `residue`, `ResidueField.map`, `residue_eq_zero_iff` | USE (the unit ball of a normed field is local: [PFA]) |
| polynomial maps | `MvPolynomial.map`, `eval₂`, `aeval`, `ringHom_ext`, `algHom_ext`, `finSuccEquiv`, `finSuccEquiv_coeff_coeff`, `natDegree_finSuccEquiv` | USE |
| sums in ultrametric groups | `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`, `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` | USE. ⚠ no `NonarchimedeanRing` instance for an ultrametric normed ring, so `Summable.mul_of_nonarchimedean` is unavailable: use [PFA] `IsUltrametricDist.summable_prod_map₂` |
| evaluation of restricted series | absent | PROVE (`Eval.lean`) |
| spectral norm | `spectralValue`, `spectralNorm`, `spectralAlgNorm`, `spectralNorm.normedField/normedAlgebra/completeSpace`, `NormedAlgebra.norm_eq_spectralNorm`, `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, `spectralNorm_extends`, `isNonarchimedean_spectralNorm`, `isPowMul_spectralNorm` (⚠ no `spectralNorm_pow`) | USE |
| supremum seminorm over `MaximalSpectrum` | absent | DEFINE (`SupSeminorm.lean`) |
| combinatorial Nullstellensatz | `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` | USE |
| roots of `X^m − 1` | `Polynomial.separable_X_pow_sub_C`, `card_rootSet_eq_natDegree`, `Splits.eval_root_derivative`, `SplittingField` | USE |
| Weierstrass polynomials, finiteness, charts | absent | DEFINE / PROVE |
| finite and integral ring maps | `RingHom.Finite.comp/of_surjective/of_comp_finite/to_isIntegral`, `Polynomial.Monic.finite_quotient` | USE |
| Rückert overrings | absent | DEFINE (`Rueckert.lean`) |
| noetherian transfer | `Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective`, `Polynomial.isNoetherianRing`, `isNoetherianRing_of_ringEquiv` (⚠ `isNoetherian_of_tower` goes the other way) | USE |
| Jacobson rings | `isJacobsonRing_iff_prime_eq`, `isJacobsonRing_of_isIntegral'`, `Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot`, `Ideal.map_jacobson_of_bijective`, `Ideal.mem_jacobson_bot` | USE |
| factoriality | `Polynomial.uniqueFactorizationMonoid`, `UniqueFactorizationMonoid.of_exists_prime_factors`, `Polynomial.Monic.isUnit_leadingCoeff_of_dvd`, `Polynomial.eq_of_monic_of_associated` | USE |
| Krull dimension | `ringKrullDim_quotient`, `Order.coheight_eq_krullDim_Ici`, `Order.rev_index_le_coheight`, `Order.krullDim_le_of_strictMono`, `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, `ringKrullDim_le_of_surjective`, `Ideal.comap_lt_comap_of_integral_mem_sdiff` | USE. ⚠ no "integral maps do not raise the dimension", no `Order.krullDim_le_iff`: PROVE two lemmas |
| bald rings, B-rings | absent | DEFINE (`Bald.lean`) |
| orthonormal families and bases | absent (PFA roadmap §2.2, unwritten) | SEAM: the two predicates verbatim from the PFA roadmap, with the expansion lemmas over a field (`Orthonormal.lean`) |
| linear algebra | `LinearIndepOn.extend` and its three lemmas, `Pi.basis`, `MvPolynomial.basisMonomials`, `LinearIndependent.disjoint_span_image`, `LinearMap.exists_leftInverse_of_injective`, `Subspace.dualAnnihilator_dualCoannihilator_eq` | USE |
| trace | `trace_eq_finrank_mul_minpoly_nextCoeff`, `traceForm_nondegenerate` (both in the root namespace) | USE |
| weakly stable fields, Japanese rings | absent | DEFINE |
| Dedekind's finiteness theorem | `IsIntegralClosure.finite` | USE |
| fraction-field norm | absent (`AbsoluteValue.toNormedField` exists) | DEFINE `IsFractionRing.normAbsoluteValue` |
| `ℚ_[p]` | `Padic.norm_p` (⚠ not `padicNormE.norm_p`), `Padic.norm_eq_zpow_neg_valuation` | USE in `Examples.lean` |

Names that do not exist at the pin, found while planning: `spectralNorm_pow`, `Int.cast_natAbs`
(use `Int.natAbs_eq`), `padicNormE.norm_p`, `Order.krullDim_le_iff`, `MvPolynomial.degreeOf_map_le`
(use `degrees_map_le`), `Polynomial.aeval_root_derivative_of_splits` (use
`Polynomial.Splits.eval_root_derivative`); `RingHom.charZero` goes from the codomain (use
`charZero_of_injective_ringHom`).

## File structure (as for a Tau Ceti PR; the home is in each module docstring)

| File | Roadmap | Tau Ceti home | Contents |
|---|---|---|---|
| `Restricted/**` (21 files) | floor | `TauCeti/RingTheory/MvPowerSeries/Restricted/**` | the ported floor; complete |
| `TateAlgebra/Basic.lean` | §0.1.1 | `TauCeti/RingTheory/TateAlgebra/Basic.lean` | `Affinoid.TateAlgebra`, normed algebra, density, unit-radius criteria |
| `TateAlgebra/Tower.lean` | floor | `…/TateAlgebra/Tower.lean` | `coeffX0`, `ofPolynomial`, `ofTail`, Weierstrass at the unit radius; complete |
| `TateAlgebra/Reduction.lean` | §0.1.2 | `…/TateAlgebra/Reduction.lean` | `reduction`, `reductionEquiv`, units, `jacobson_bot` |
| `TateAlgebra/Eval.lean` | preamble | `TauCeti/RingTheory/MvPowerSeries/Restricted/Eval.lean` | `eval₂`, `aeval`, contraction, extensionality |
| `TateAlgebra/EvalReduction.lean` | §0.1.3 | `…/TateAlgebra/Reduction.lean` | reduction commutes with evaluation and substitution |
| `SupSeminorm.lean` | conv. 4–5 | `TauCeti/RingTheory/Affinoid/SupSeminorm.lean` | `evalNorm`, `supSeminorm`, BGR 3.8.2/1–2 |
| `TateAlgebra/MaxModulus.lean` | §0.1.3–4 | `…/TateAlgebra/MaxModulus.lean` | maximum modulus, Gauss = sup |
| `TateAlgebra/Distinguished.lean` | §0.2.1 | `…/TateAlgebra/Weierstrass.lean` | dictionary for `coeffX0`, `IsWeierstrassPolynomial` |
| `TateAlgebra/Finiteness.lean` | §0.2.2 | `…/TateAlgebra/Weierstrass.lean` | BGR 5.2.3/3–4 |
| `TateAlgebra/Chart.lean` | §0.2.3 | `…/TateAlgebra/Chart.lean` | shears, distinguished charts |
| `Rueckert.lean` | §0.3 | `TauCeti/RingTheory/Rueckert.lean` | `IsRueckert` and its four inheritance theorems |
| `TateAlgebra/Rueckert.lean` | §0.3.2–4 | `…/TateAlgebra/Rueckert.lean` | noetherian, factorial, Jacobson, dimension |
| `Bald.lean` | §0.3.1 | `TauCeti/Analysis/Normed/Field/Bald.lean` | Bosch 1.3/2–3 |
| `PadicFunctionalAnalysis/Orthonormal.lean` | PFA §2.2 | `TauCeti/Analysis/Normed/Module/Ultra/Orthonormal.lean` | the two predicates and expansions |
| `OrthonormalLift.lean` | §0.3.1 | `…/Module/Ultra/OrthonormalLift.lean` | Bosch 1.3/6 |
| `TateAlgebra/StrictlyClosed.lean` | §0.3.1, §0.3.5 | `…/TateAlgebra/StrictlyClosed.lean` | Bosch 1.3/7–10, BGR 5.2.7/8 |
| `WeaklyStable.lean` | §0.4.1 | `TauCeti/Analysis/Normed/Field/WeaklyStable.lean` | `IsWeaklyStable`, BGR 3.5.1/3–4, fraction-field norm |
| `Japanese.lean` | §0.4.3 | `TauCeti/RingTheory/Japanese.lean` | `IsJapaneseRing`, BGR 4.3/2 |
| `TateAlgebra/Stable.lean` | §0.4.2–3 | `…/TateAlgebra/Stable.lean` | characteristic zero |
| `TateAlgebra/Examples.lean` | Examples | `TauCetiTest/RingTheory/TateAlgebra.lean` | acceptance examples |

Import graph: `Basic ← {Tower, Reduction, Eval}`; `{Eval, Reduction} ← EvalReduction`;
`{SupSeminorm, EvalReduction} ← MaxModulus`; `{Reduction, Tower} ← Distinguished ← {Finiteness, Chart}`
(`Chart` also imports `EvalReduction`); `{Rueckert, Chart, Finiteness} ← TateAlgebra/Rueckert`;
`{Orthonormal, Bald} ← OrthonormalLift`; `{OrthonormalLift, Reduction} ← StrictlyClosed`;
`{Japanese, WeaklyStable, TateAlgebra/Rueckert} ← Stable`;
`{MaxModulus, TateAlgebra/Rueckert, Stable, StrictlyClosed} ← Examples`. `SupSeminorm`, `Rueckert`,
`Bald`, `Orthonormal`, `WeaklyStable`, `Japanese` import Mathlib only.

## Dependency graph (by ticket group)

```text
G1 Basic ─┬─→ G2 Reduction ─┬─→ G4 EvalReduction ─┬─→ G6 MaxModulus (M1) ──────────────┐
          ├─→ G3 Eval ──────┘         │            │        ↑                           │
          │                           │            │   G5 SupSeminorm                   │
          └─→ G7 Distinguished ──┬─→ G8 Finiteness ─┬─→ G11 Tate/Rueckert (M2) ─┐       │
                 ↑ (G2)          └─→ G9 Chart ──────┘        ↑                  │       │
                                        ↑ (G4)          G10 Rueckert            │       │
G12 Bald ──────┬─→ G14 OrthonormalLift ─→ G15 StrictlyClosed (M3) ──────────────┼───────┤
G13 Orthonormal┘                              ↑ (G2)                            │       │
G16 WeaklyStable ─┬─→ G18 Stable (M4) ←─────────────────────────────────────────┘       │
G17 Japanese ─────┘        │                                                            │
                           └──────────────────────────→ G19 Examples ←──────────────────┘
                                                              │
                                                    T081 (chain root) → CLEANUP-FINAL
```

G5, G10, G12, G13, G16, G17 and the polynomial half of G9 (T038–T040) depend on nothing on the board.

## Generality and design decisions (binding for the tickets)

1. **The Tate algebra is the unit polyradius of the floor's type**: `Affinoid.TateAlgebra K n` is an
   `abbrev` for `MvPowerSeries.Restricted K (1 : Fin n → ℝ)`. Statements that do not need `Fin n` are
   proved for `Restricted K (1 : σ → ℝ)` with `σ` arbitrary (reduction, units, `jacobson_bot`) or
   finite (`MaxModulus`, `StrictlyClosed`), and statements that hold at every polyradius are stated
   there (`Basic.lean`, `Eval.lean`). `TateAlgebra K n` appears only where the tower `n ↦ n + 1` does.
2. **Weakest structure that carries the proof.** `NormedRing R` in `Basic.lean`; `NormedField K`
   without completeness or nontriviality wherever the reduction alone is used; `[CompleteSpace K]`
   exactly where a Neumann series, a Weierstrass division or an expansion must exist;
   `NontriviallyNormedField` only where a Mathlib lemma demands it (spectral normed-field structure,
   finite-dimensional continuity, power-boundedness).
3. **Predicates, not bundled structures.** `IsWeierstrassPolynomial`, `IsRueckert`, `Subring.IsBald`,
   `Subring.IsBRing`, `IsWeaklyStable`, `IsJapaneseRing` are `Prop`s; `IsRueckert` is stated for a
   ring homomorphism `φ : I[X] →+* I′` and a set `W`, so that formal and convergent power series are
   instances too.
4. **`evalNorm` is `spectralValue (minpoly K (mk f))`** — `spectralNorm` by definition, with no
   `Field` instance on the quotient — and is `0` at a non-algebraic residue class; `supSeminorm` is a
   real `iSup` over `MaximalSpectrum`. Both conventions reproduce BGR 3.8.1/2, including the value `0`
   on an empty spectrum.
5. **The fraction-field norm is not an instance.** `IsFractionRing.normedField A Q` is a reducible
   definition; statements about `Q(Tₙ)` as a normed field introduce it with `letI`.
6. **Orthonormal bases are the PFA roadmap's predicates**, reproduced verbatim (dense span, finite
   sums). Bosch's lifting theorem is proved in that form and needs no completeness; expansions exist
   when the field and the space are complete.
7. **Submodules first, ideals as a corollary**: strict closedness is proved for submodules of `T^ι`
   (Bosch 1.3/10) and specialised at `ι = Unit`.
8. **One conclusion per declaration.** The only conjunctions are in characterisations (`↔`) and under
   shared-witness existentials; see the statement-shape section of `decomposition.md`.
9. **Imports are minimal, per file**; when a proof needs a lemma from an unimported module, add that
   module (for example `PadicFunctionalAnalysis.Sums` in `Eval.lean`, T015).

## Declared deviations from a source's proof

Each is recorded at its leaf in `decomposition.md` with the passage that licenses it.

| Where | Source's route | Board's route | Why |
|---|---|---|---|
| maximum modulus (T025–T027) | BGR 5.1.4/3 takes the point in `Bⁿ(k_a)` and cites Lemma 3.4.1/4 (the residue field of `k_a` is algebraically closed) | a finite extension: the splitting field of `X^m − 1`, `‖m‖ = 1`, whose `m` roots of unity have distinct residues | `k_a` is not complete, so evaluation is not defined on it; BGR's remark allows any extension with enough residue classes; this is 3.4.1/4 for one polynomial |
| `evalNorm_le_norm` (T024) | BGR 3.8.2/1: residue norm of a closed maximal ideal and uniqueness of power-multiplicative norms | Bosch 1.2/12's unit argument, with a Neumann series in place of "Corollary 4" | no residue-norm machinery needed; works in any Banach algebra |
| Jacobson (T046) | BGR 5.2.5/3 ends with an integral equation of minimal degree | Mathlib's `isJacobsonRing_of_isIntegral'` for the finite map BGR constructs | same content, already in Mathlib |
| dimension `≤` (T044, T048) | BGR 6.1.2 Remark uses 7.1.1/3 | Bosch 1.2/10: integral descent through `I → I′/(ω)` | 7.1.1/3 needs Noether normalisation and `Max Tₙ` (Layers 1, 3) |
| strict closedness (T058–T070) | BGR 5.2.7/7: induction through cartesian `Q(Tₙ)`-modules | Bosch 1.3/3–10: bald rings and lifting of orthonormal bases | BGR's route needs Chapter 2 and 3.7.3, absent from the chain |

## Roadmap errata and clarifications found while planning

| # | Roadmap clause | Finding | Board action |
|---|---|---|---|
| E1 | §0.2.1 "monic of degree `s` with all non-leading coefficients of Gauss norm `< 1`" | not BGR 5.2.3/1 (monic with `|ω| = 1`), and wrong: `X − 1` is distinguished of order one and is its own Weierstrass polynomial | `IsWeierstrassPolynomial` is BGR's; README corrected |
| E2 | convention 2 ("Mathlib's subring … as a `K`-subalgebra"; "cited, never re-proved") | the board uses the type of mathlib4#42867, `MvPowerSeries.Restricted K 1`; the floor is in this chain, not cited from the adic-spaces roadmap | README clarified |
| E3 | §0.2.3 "`Xᵢ ↦ Xᵢ + Xₙ^{αᵢ}` … `α = (tⁿ⁻¹, …, t)`" | the code distinguishes `X 0` (Mathlib's `finSuccEquiv`): `X (i+1) ↦ X (i+1) + X 0 ^ (t ^ (i+1))` | README notes the convention |
| E4 | §0.1.3 "(… the finiteness of the residue fields is §1.2.4, and this item is stated once that is available)" | unnecessary: the point is constructed with a finite residue field | README corrected |
| E5 | §0.3.4 "`≤ n` because every maximal ideal is generated by `n` elements (BGR 7.1.1/3, proved in §3.1)" | a forward reference across three layers; Bosch 1.2/10's descent proves it in Layer 0 | README corrected |
| E6 | §0.3.1, §0.3.5 "(adic-spaces §0.5, `p`-adic-functional-analysis §1.4.1; cite)" | neither is in the chain; Bosch 1.3/7–10 proves closedness and strict closedness together | README corrected |
| E7 | §0.4.1 "the criterion of BGR 3.5.3 and the theorem of BGR 3.5.4 … State it with exactly the hypotheses BGR 3.5.4 carries" | checked against the source: BGR 5.3.1 uses 3.5.1/4 and 4.3/2 in characteristic zero, and 3.5.3/2, 4.1/4, 4.4/2 in characteristic `p`; 3.5.4/1 is about discrete valuation rings and is not used | README corrected; characteristic `p` declared out of this layer's board |
| E8 | §0.2.3 "Prove the relative form of Bosch 1.8/13: for `f ∈ A⟨ζ⟩` over an affinoid algebra `A` …" | needs affinoid algebras and `Sp A` (Layers 1, 3) | moved to §4.6, its consumer; Layer 0 gives the explicit and the finitely-many forms |
| E9 | Examples "`Q(T₁)` is not complete" | needs the zero-counting of Layer 2 or a Newton-polygon argument | moved to Layer 2's examples |
| E10 | preamble "The adic-spaces roadmap's §0.5 supplies: … substitution and evaluation, … the noetherianity of `Tₙ`" | neither is in the chain | supplied here (`Eval.lean`, `TateAlgebra/Rueckert.lean`); README corrected |
| E11 | convention 4 "Mathlib's `spectralNorm K (A ⧸ x)`" | needs a `Field` instance on the quotient | spelled `spectralValue (minpoly K (mk f))`; README clarified |
| E12 | Examples "the automorphism … making `X₁ − X₂` distinguished in `X₂`" | `X₁ − X₂` is already `X₂`-distinguished of order one | the example is the variable that is not the distinguished one; README corrected |

A note for the `p`-adic functional analysis roadmap (not an erratum of this one): its §2.2.2
"every `x` has a unique expansion" needs the scalar ring complete; over a non-complete field the
dense-span definition does not give expansions (`ℚ ⊂ ℚ_p`). `Orthonormal.lean` states it so.

## Build and verification protocol

- Skeleton gate: `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples` (the leaf
  imports all 19 skeleton files and the floor); `sorry` warnings only. Verified 2026-10-02: 2 722
  jobs, 0 errors.
- Import gate (CI): no `import PhD.Main.*` under `PhD/TauCeti/`.
- Each ticket: `lake build` of its module, then `#print axioms` on each declaration — only
  `propext`, `Classical.choice`, `Quot.sound`. `lake exe runLinter` on the module at cleanup.
- `/beastmode` runs inline as the main agent (user preference), one ticket at a time, naming this
  board. No `timeout` binary on this machine: use the tool timeout and check exit codes. One Lean
  process at a time (two swap-thrash this machine).
- The chain root `PhD/TauCeti.lean` gains `TateAlgebra.Examples` in T081 (the root lists leaf modules
  only). Append-only edit: another board may be editing the same file.
- ChatGPT plan validation (step 1h of `/develop`) was **not run**: the `chatgpt-math` MCP server
  failed to connect in this session.
