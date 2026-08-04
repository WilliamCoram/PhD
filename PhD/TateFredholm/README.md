# `PhD/TateFredholm/` — reading order and file guide

Compact operators and Fredholm determinants over a **commutative nonarchimedean
Banach–Tate ring** `R`: Bellaïche's proof architecture carried out under Johansson–Newton's
hypotheses, so there is no ground field anywhere and no Noetherian hypothesis outside
`Noetherian.lean` and one isolated statement in `Pr.lean`.

Status (2026-07-30): **complete** — 10 modules, ~5,250 lines, sorry-free, axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only). Build the whole tree with
`lake build PhD.Test.CompactOperatorsMerged`.

## Sources

| Tag | Reference |
| --- | --- |
| `[Bel]` | Bellaïche, *The Eigenbook*, §3.1 — published; draft §II.1 numbering also cited |
| `[JN]` | Johansson–Newton, *Extended eigenvarieties for overconvergent cohomology*, arXiv:1604.07739v4, §2.1 |
| `[Buz07]` | Buzzard, *Eigenvarieties*, §2 |
| `[Serre]` | Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*, IHÉS 12 (1962) |
| `[FvdP]` | Fresnel–van der Put, *Rigid Analytic Geometry and Its Applications*, Lemma 1.2.3 |
| `[Lud24]` | Ludwig, *Spectral theory and the Eigenvariety machine*, arXiv:2407.18073 |
| `[Hub94]` | Huber — open mapping theorem for Tate rings |

Citations name a statement's **origin**; the hypotheses in this development are the merged
ones (Tate base, no Noetherian), so a cited lemma is generally *more general* here than in
the source. Where a statement genuinely needed a hypothesis its source lacks, the
declaration's docstring says so.

## Dependency order

The import graph is a single chain, with `Noetherian.lean` hanging off `Matrix.lean` as a
side branch. Read top to bottom; each file imports only its predecessor.

```
Tate.lean                 foundations: Banach–Tate rings, summability
  ├─ AddVal.lean          ← side branch: the seam to ForMathlib's AddVal
  └─ OperatorNorm.lean    the operator norm; Open Mapping Theorem
       └─ Compact.lean    finite-rank, completely continuous
            └─ ModelSpace.lean       c(I,R); ON-able; property (Pr)
                 └─ Matrix.lean      matrix coefficients; truncations; IsCompactoid
                      ├─ Noetherian.lean   ← side branch: closedness of f.g. submodules
                      └─ Fredholm.lean     det(1 − Tu); the trace property
                           └─ Pr.lean      lifting; projectivity; the Noetherian statement
                                └─ Residue.lean    Serre's residue machinery
                                     └─ BaseChange.lean   norm change; base change; Serre
```

The leaves are `BaseChange.lean` (end of the main chain), `Noetherian.lean` and `AddVal.lean`;
the re-export stub `PhD/Test/CompactOperatorsMerged.lean` imports the first two to pull in the
main tree. `AddVal.lean` is optional — nothing in the development depends on it, it exists to
keep `v_ϖ` pinned to `ForMathlib`'s additive-valuation API.

---

## 1. `Tate.lean` — foundations

The base-ring setting, plus the summability principle every `tsum` downstream rests on.
Also holds the development's overview docstring and the full Lean ↔ sources dictionary.

| Declaration | Source |
| --- | --- |
| `Ix` | the index set as a discrete space (an implementation device, no source) |
| `IsMultiplicative` | `[JN]` Definition 2.1.1 — `‖ax‖ = ‖a‖‖x‖` |
| `PseudoUniformizer` | `[JN]` Definition 2.1.2 — a multiplicative unit `ϖ` with `‖ϖ‖ < 1` |
| `PseudoUniformizer.norm_pos`, `.norm_inv` | `[JN]` Def 2.1.2 and the remark following it |
| `IsTate` | `[JN]` Definition 2.1.2 — the standing hypothesis of the development |
| `PseudoUniformizer.val` | `[JN]` Definition 2.1.2 — the valuation `v_ϖ`, normalised so `v_ϖ(ϖ) = 1`, valued in `WithTop ℝ` with `∞` at `0` (the shape `NewtonPolygon` consumes). **Not an `AddValuation`**: the norm is only submultiplicative, so `v_ϖ` is only superadditive on products (`val_mul_le`), with equality under `[NormMulClass]` (`val_mul`). Built on `ForMathlib`'s `negLogNorm` |
| `PseudoUniformizer.val_eq_map_normAddVal` | `AddVal.lean` — over an ultrametric normed field, `v_ϖ` is `NormedField.normAddVal` rescaled by `-log ‖ϖ‖`; the seam that stops `v_ϖ` from forking off `ForMathlib`'s additive-valuation API |
| `isTate_of_normedAlgebra` | **the bridge lemma** (no source): every norm-unital Banach algebra over a nontrivially normed field is Tate, via `ϖ = λ·1`. This is what makes the development subsume `[Buz07]` and `[Bel]` concretely rather than morally |
| `summable_of_tendsto_cofinite`, `bddAbove_range_norm_of_tendsto_cofinite`, `norm_tsum_le_iSup` | `[Bel]` §II.1.5 footnote. **Not in Mathlib** — PR candidate |

`ϖ` replaces the ground field of the field-based settings: every use `[Bel]` makes of `ℚ_p`
is a scaling argument, and the pseudo-uniformizer performs it verbatim (`[JN]`: "Buzzard's
`ρ`-trick with `ϖ` for `ρ`").

## 2. `OperatorNorm.lean` — the operator norm and the OMT

`[Bel]` II.1.1 under `[JN]` Definition 2.1.4. Mathlib's `opNorm` requires a
`NontriviallyNormedField`, which we do not have, so the norm on `M →L[R] N` is built here
from scratch as a `sInf` and given a **`scoped`** `Norm` instance (open with
`open scoped TateFredholm` to avoid diamonds).

| Declaration | Notes |
| --- | --- |
| `norm_pseudoUniformizer_smul`, `_inv_smul`, `_zpow_smul` | ϖ-scaling: `‖ϖⁿ • x‖ = ‖ϖ‖ⁿ‖x‖` |
| `norm_def`, `opNorm_nonneg`, `opNorm_le_of_forall`, `opNorm_sub_comm` | basic API |
| `le_opNorm` | `‖u x‖ ≤ ‖u‖‖x‖` — proved by the ρ-trick: scale `x` into a ϖ-shell, apply the bound, unscale |
| `norm_add_le`, `opNorm_eq_zero_iff`, `opNorm_mul_le`, `opNorm_one_le`, `opNorm_sum_le`, `opNorm_pow_le` | normed-ring structure on the endomorphisms |
| `exists_lim_of_cauchySeq` | completeness of the operator norm |
| **`exists_preimage_norm_le`** | the **Open Mapping Theorem for Banach–Tate rings** (`[Hub94]` Lemma 2.4(i); `[JN]` p. 7 cite it). Quantitative form: a continuous surjection admits preimages with `‖m‖ ≤ C‖n‖`. Baire category with ϖ-shells replacing scalar inverses. **A genuine Mathlib gap** — PR candidate |
| `exists_inverse_of_norm_id_sub_lt_one` | Neumann series: `‖1 − w‖ < 1 ⟹ w` invertible |

## 3. `Compact.lean` — finite-rank and completely continuous operators

`[Bel]` Definition II.1.3 and Lemma II.1.4; `[JN]` Definition 2.1.5; blueprint 6.13.

| Declaration | Source |
| --- | --- |
| `IsFiniteRank` | range contained in a finitely generated submodule |
| `IsCompletelyContinuous` | metric closure of the finite-rank operators |
| `IsFiniteRank.isCompletelyContinuous`, `opNorm_comp_le`, `isCompletelyContinuous_of_tendsto` | basic API |
| `IsFiniteRank.add`, `.comp_left`, `.comp_right`; `IsCompletelyContinuous.comp_left`, `.comp_right` | `[Bel]` Lemma II.1.4 — the two-sided ideal property |

## 4. `ModelSpace.lean` — the model space and orthonormalisability

`[Bel]` Definitions II.1.5–II.1.6 and Example II.1.7; `[JN]` Definition 2.1.5;
blueprint 6.3–6.6.

| Declaration | Source |
| --- | --- |
| `cSpace`, notation `c(I, R)` | `[JN]` Definition 2.1.5 — families `I → R` vanishing along the cofinite filter, sup norm. Realised as Mathlib's `C₀` on the discrete index `Ix I`, which supplies the metric and completeness for free |
| `tendsto_cofinite`, `norm_eq_iSup`, `norm_apply_le`, `evalCLM`, `single`, `hasSum_single` | the coordinate API |
| `IsONable`, `IsPotentiallyONable` | `[JN]` Def 2.1.5 / `[Bel]` Def II.1.5–II.1.6 — isometric (resp. merely homeomorphic) isomorphism to `c(I, R)`. Defined by an isomorphism, as `[JN]` do; the `ONBasis`-structure formulation and its equivalence live in the Bellaïche blueprint file |
| `HasPr` | `[Bel]` §II.1.6 / `[JN]` Def 2.1.5 — property (Pr): a direct summand of a potentially ON-able module |
| `IsONable.isPotentiallyONable`, `IsPotentiallyONable.hasPr`, `isONable_cSpace` | the implications between the three |

## 5. `Matrix.lean` — matrices, truncations, and the compactness criterion

`[Bel]` §II.1.3: Lemma II.1.8 / published Lemma 3.1.12, Proposition II.1.9,
Scholium II.1.10; blueprint 6.11, 6.14.

| Declaration | Source |
| --- | --- |
| `matrixCoeff`, `tendsto_matrixCoeff_column` | `[Buz07]` p. 65 / `[Bel]` §II.1.3 — the matrix of an operator; columns vanish cofinitely |
| `norm_eq_iSup_matrixCoeff`, `exists_coeffEquiv` | `‖u‖` as a double sup of matrix entries; recovery of an operator from a bounded matrix |
| `truncation`, `norm_truncation_apply_le`, `truncation_mem_span`, `isFiniteRank_truncation` | the coordinate projections `π_S`, `S` finite — norm-decreasing, finite rank |
| **`exists_truncation_near`** | `[Bel]` **Lemma 3.1.12** (draft II.1.8): f.g. **closed** submodules are uniformly approximated by truncations. Carries `IsClosed (P : Set c(I,R))` — exactly `[Bel]` **Hypothesis 3.1.8**, which the published book assumes outright (noting it can fail) in order to drop Noetherianity; the draft §II.1 predates it. Automatic over a field, so this still subsumes `[Buz07]`/`[Serre]`. The docstring records a counterexample showing closedness cannot be dropped |
| `rowNorm`, `rowNorm_nonneg` | the row sup `r_j(u) = sup_i ‖a_{ij}‖` |
| **`IsCompactoid`** | cofinite row decay — **the organising notion**. The determinant theory consumes only this, which is why it needs no Noetherian hypothesis |
| `IsCompactoid.isCompletelyContinuous` | `[Bel]` Prop II.1.9 (⇐) — holds over **any** Banach–Tate ring |
| `tendsto_truncation_comp` | `[Bel]` Scholium II.1.10, compactoid form: `π_S ∘ u → u` |
| `IsCompactoid.comp_left`, `.comp_right` | `[Bel]` Lemma II.1.4 for compactoids |

The converse `IsCompletelyContinuous ⟹ IsCompactoid` needs closedness of f.g. submodules
and therefore lives in `Noetherian.lean`.

## 6. `Noetherian.lean` — the side branch: closedness of f.g. submodules

Every Noetherian hypothesis in the development is quarantined here. What this file supplies
is precisely `[Bel]` Hypothesis 3.1.8; `[Lud24]` Remark 2.25 observes that this hypothesis
is all `[Buz07]` Lemma 2.3(3) actually needs. A reader who prefers Bellaïche's axiomatic
route can skip this file and hypothesise its conclusion instead.

| Declaration | Source |
| --- | --- |
| `isClosed_of_finite` | `[FvdP]` Lemma 1.2.3 (Kedlaya's transcription, 18.727 notes): every submodule of a *module-finite* Banach module over a Noetherian Banach–Tate ring is closed. Closure is f.g. → OMT → geometric density iteration |
| `exists_truncation_injOn` | `[Buz07]` Lemma 2.3(a): some truncation is injective on a f.g. submodule (the column module is f.g. over a Noetherian base) |
| `isClosed_of_fg` | `[Buz07]` Lemma 2.3(b), transferred per `[Lud24]` Lemma 2.26(2) and Exercise 2.27 (`ϖ` for `ρ`): f.g. submodules of `c(I,R)` are closed |
| `IsCompletelyContinuous.isCompactoid` | `[Bel]` Prop II.1.9 (⇒) in `[JN]`'s setting — the bridge |
| `isCompletelyContinuous_iff_rowNorm` | `[JN]` Definition 2.1.5 / `[Bel]` Proposition II.1.9 — the compactness criterion, recovered over Noetherian bases |

## 7. `Fredholm.lean` — the Fredholm determinant

`[Bel]` §II.1.5 architecture under `[JN]`'s hypotheses; blueprint 6.16–6.17. Definitions are
norm-free; the theorems take `IsCompactoid` hypotheses and carry **no** Noetherian
hypothesis, so each strictly generalises its `[JN]` counterpart.

| Declaration | Source |
| --- | --- |
| `minor`, `summable_minor` | the principal `S × S` minors and their summability (ultrametric Hadamard bound + row decay) |
| `charCoeff`, `charPowerSeries`, `charCoeff_zero` | `[Bel]` §II.1.5 / `[JN]` p. 67 — `cₙ = (−1)ⁿ ∑_{|S| = n} det(minor)`, and `det(1 − Tu) ∈ R⟦T⟧` with `c₀ = 1` |
| `IsEntire`, `charPowerSeries_isEntire` | `[Bel]` Lemma II.1.14 — the determinant is entire (`R{{T}}`) |
| `norm_charCoeff_sub_le` | `[Bel]` Lemma II.1.15 — `‖cₙ(u) − cₙ(v)‖ ≤ max(‖u‖,‖v‖)^{n−1}‖u − v‖`, the quantitative continuity powering every limit argument |
| `charCoeff_eq_det_coeff` | `[Bel]` equation (II.1.2) — agreement with the algebraic determinant for row-supported operators. Its proof needed the principal-minors expansion `det(1 − tA) = ∑_S (−t)^{\|S\|} det(A_S)`, **missing from Mathlib** — PR candidate |
| **`charPowerSeries_comm`** | `[Bel]` **Proposition II.1.17** — the **trace property** `det(1 − T·uv) = det(1 − T·vu)`. The primitive invariance statement: truncate, pass to the limit by `norm_charCoeff_sub_le`, conclude by the finite-matrix identity |
| `charPowerSeries_conj` | `[Bel]` Corollary II.1.18; `[Buz07]` Lemma 2.5 / Corollary 2.6 — conjugation invariance, formal from the trace property. This is what extends `det(1 − Tu)` to potentially ON-able modules |
| `charPowerSeries_extendZero` | `[Buz07]` pp. 72–73; `[Bel]` §II.1.6 — extension by zero; with `_conj`, gives well-definedness on modules with property (Pr) |

## 8. `Pr.lean` — lifting, projectivity, and the one Noetherian statement

`[Bel]` Exercise II.1.19, Propositions II.1.20–II.1.21.

| Declaration | Source |
| --- | --- |
| `HasPr.exists_lift` | `[Bel]` Exercise II.1.19 — (Pr) as a lifting property along continuous surjections of Banach modules |
| `HasPr.projective` | `[Bel]` Proposition II.1.20 — finitely generated (Pr) modules are projective |
| `finite_projective_of_one_sub_compact_nilpotent` | `[Bel]` Proposition II.1.21 — **the only Noetherian statement outside `Noetherian.lean`**: if `P` has (Pr) and carries a compact `u` with `1 − u` nilpotent, then `P` is finitely generated and projective. The germ of Riesz theory |

## 9. `Residue.lean` — Serre's residue machinery

A sub-development feeding `isPotentiallyONable_of_uniformizer` in `BaseChange.lean`.
Source: `[Bel]` §II.1.4 (Hypothesis II.1.11, Lemma II.1.12, Theorem II.1.13, p. 58);
ultimately `[Serre]` Prop. 1. Internally labelled `R1`–`R7` by the decomposition pass.

| Step | Declarations | Content |
| --- | --- | --- |
| `R1` | `exists_norm_eq_zpow` | discreteness: the value group is `‖π‖^ℤ` (`[Bel]` p. 58) |
| `R2`–`R4` | `unitBall`, `unitBall_isUnit_iff`, `isMaximal_span_pi` | the unit ball as a subring, and `π·unitBall` as its maximal ideal — the residue field |
| `R5` | `exists_residue_approx` | a quotient-free "residue basis" interface: norm-one vectors whose residues form a basis. Indexed by a subset of `E` (an `∃ ι : Type _` phrasing would bind a universe independent of `E`) |
| `R6a`–`R6b`, `R6` | `exists_expansion_of_residue_approx`, `expansion_unique_of_residue_indep`, `isONable_of_discrete_norms` | `[Bel]` Lemma II.1.12 — successive π-adic approximation (the analytic heart), uniqueness of expansions, and assembly: discrete norms ⟹ ON-able |
| `R7` | `rescale_nonneg`, `rescale_le_rescale`, `le_rescale_and_rescale_lt`, `rescale_add_le`, `rescale_smul` | `[Bel]` Theorem II.1.13's norm-rescaling step: replace the norm by an equivalent one with values in `‖π‖^ℤ` |

## 10. `BaseChange.lean` — changing the norm, base change, and the classical case

`[JN]` Lemmas 2.1.6–2.1.7 and Proposition 2.1.8; `[Buz07]` Corollaries 2.9–2.10; and the
classical (field) specialisations.

| Declaration | Source |
| --- | --- |
| `norm_le_pow_of_equiv` | `[JN]` Lemma 2.1.6 — ϖ-power norm comparison |
| `norm_comparison_of_common_uniformizer` | `[JN]` Lemma 2.1.7 — two Tate norms sharing a uniformizer are comparable |
| `isCompactoid_map_equiv`, `charPowerSeries_map_equiv` | `[JN]` Proposition 2.1.8 — invariance under a bicontinuous ring isomorphism. A *topological* statement (`e` is only power-comparable, not bounded), so **not** a special case of `charPowerSeries_baseChange` |
| `isCompactoid_baseChange`, `charCoeff_baseChange`, `charPowerSeries_baseChange` | `[Bel]` Lemma II.1.23 (matrix-wise) / `[Buz07]` 2.9–2.10 — base change along a bounded homomorphism `ψ`: `cₙ(v) = ψ(cₙ(u))`, hence `det(1 − Tv) = ψ(det(1 − Tu))` |
| `Rescaled`, `isPotentiallyONable_of_uniformizer` | `[Bel]` Theorem II.1.13; `[Serre]` Prop. 1 — **Serre's theorem**: every Banach space over a discretely valued field is potentially ON-able. Intrinsically a field statement; phrased here against the merged setting via the bridge lemma |

---

## Notes for future work

**Mathematics still to do** (also recorded in `Tate.lean`'s TODO): Riesz theory and slope
factorizations/decompositions (`[Bel]` §II.2, `[JN]` §2.2) — the natural consumer of this
project's `NewtonPolygon` and `DivValueGroup` work; completed tensor products and the
`⊗̂`-form of base change; spectral varieties (`[JN]` §2.3).

**Mathlib PR candidates** surfaced by this development: the Banach–Tate open mapping
theorem; the ultrametric summability criterion (`summable_of_tendsto_cofinite`,
`norm_tsum_le_iSup`); the principal-minors expansion `det(1 − tA) = ∑_S (−t)^{|S|} det(A_S)`;
the ultrametric Hadamard determinant bound.

**The three source blueprints** in `PhD/Test/` (`CompactOperators.lean` for `[Buz07]`,
`CompactOperatorsBellaiche.lean` for `[Bel]`, `CompactOperatorsJohanssonNewton.lean` for
`[JN]`) are kept as source documentation, each with its own dictionary table and a section
explaining how its hypotheses differ. They are independent of this tree — do formalisation
work here, not there. `CompactOperatorsMerged.lean` is now only a re-export stub pointing
at this directory.
