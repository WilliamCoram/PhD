# `PhD/Main/TateFredholm/` — reading order and file guide

Compact operators and Fredholm determinants over a **commutative nonarchimedean
Banach–Tate ring** `R`: Bellaïche's proof architecture carried out under Johansson–Newton's
hypotheses, so there is no ground field anywhere and no Noetherian hypothesis outside
`05_Noetherian.lean` (since 2026-09-06 `06_Pr.lean`'s Proposition II.1.21 is Noetherian-free too).

Status (2026-09-02): **18 top-level modules + the `HandClean/` pair, ~11,050 lines,
sorry-free**, axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).  The core
determinant theory (§§1–10 below, 10 modules) was completed 2026-07-30 and is built by
`lake build PhD.Main.Test.CompactOperatorsMerged`; the later additions (§11 — Riesz theory,
block operators, generating functions, the slope bounds) landed through the
`tatefredholm-eigen`, `jacobs`/`jacobs-endgame`, `forms-*` and `slopes-hecke` boards
(2026-08-05 … 2026-09-01) and are built by their own targets, e.g.
`lake build PhD.Main.TateFredholm.«09_Riesz» PhD.Main.TateFredholm.«06_Slopes» PhD.Main.TateFredholm.«06_BlockOp»`.

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

Each filename carries **its depth in this folder's own import graph**: a file `NN_Name.lean`
imports only files of this folder with a strictly smaller `NN`.  Files that share a number
are independent of one another and can be read in any order.  Because the module names start with a
digit they are imported in French quotes:

```lean
import PhD.Main.TateFredholm.«09_Riesz»
```

- **00** — `Charpoly`, `Compose`, `HandClean/TateRings`, `Resultant`, `Tate`
- **01** — `AddVal`, `CharpolyPairing`, `HandClean/PseudoUniformiser`, `OperatorNorm`
- **02** — `Compact`
- **03** — `ModelSpace`
- **04** — `Matrix`, `TateAlgebra`
- **05** — `Fredholm`, `GenFun`, `Noetherian`
- **06** — `BlockOp`, `Pr`, `Slopes`, `TwoSidedBound`, `Unitriangular`, `WeightGenFun`
- **07** — `Conjugation`, `Residue`
- **08** — `BaseChange`, `BlockMap`
- **09** — `Riesz`
- **10** — `Entire`, `NewtonSlopes`
- **11** — `Coleman`, `SlopeFactor`
- **12** — `RieszColeman`
- **13** — `FiniteFactor`

The import graph is a single chain, with `05_Noetherian.lean` hanging off `04_Matrix.lean` as a
side branch. Read top to bottom; each file imports only its predecessor.

```
00_Tate.lean                 foundations: Banach–Tate rings, summability
  ├─ 01_AddVal.lean          ← side branch: the seam to ForMathlib's AddVal
  └─ 01_OperatorNorm.lean    the operator norm; Open Mapping Theorem
       └─ 02_Compact.lean    finite-rank, completely continuous
            └─ 03_ModelSpace.lean       c(I,R); ON-able; property (Pr)
                 ├─ 04_TateAlgebra.lean      ← side branch: K⟨X⟩ ≃ c(ℕ,K) (§11)
                 └─ 04_Matrix.lean      matrix coefficients; truncations; IsCompactoid
                      ├─ 05_Noetherian.lean   ← side branch: closedness of f.g. submodules
                      ├─ 05_GenFun.lean       ← side branch: generating functions (§11)
                      │    ├─ 06_WeightGenFun.lean   weight-action factors (§11)
                      │    └─ 06_Unitriangular.lean  unitriangular perturbations (§11)
                      └─ 05_Fredholm.lean     det(1 − Tu); the trace property
                           ├─ 06_BlockOp.lean      ← side branch: block operators (§11)
                           │    └─ 07_Conjugation.lean  diagonal intertwining (§11)
                           │         └─ 08_BlockMap.lean  block maps between fibres (§11)
                           ├─ 06_Slopes.lean       ← side branch (also ← GenFun): slope bounds (§11)
                           └─ 06_Pr.lean      lifting; projectivity; Prop II.1.21 (Noetherian-free)
                                └─ 07_Residue.lean    Serre's residue machinery
                                     └─ 08_BaseChange.lean   norm change; base change; Serre
                                          └─ 09_Riesz.lean    Riesz theory (§11)
```

Standalone: `00_Compose.lean` (mathlib-only imports; analytic substitution, §11) and the
`HandClean/` pair (`00_TateRings.lean` → `01_PseudoUniformiser.lean`, the Huber seam, §11).

The core chain ends at `08_BaseChange.lean`; the re-export stub
`PhD/Main/Test/CompactOperatorsMerged.lean` imports it and `05_Noetherian.lean` to pull in the
core tree. `01_AddVal.lean` is optional — nothing in the development depends on it, it exists to
keep `v_ϖ` pinned to `ForMathlib`'s additive-valuation API.

---

## 1. `00_Tate.lean` — foundations

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
| `PseudoUniformizer.val_eq_map_normAddVal` | `01_AddVal.lean` — over an ultrametric normed field, `v_ϖ` is `NormedField.normAddVal` rescaled by `-log ‖ϖ‖`; the seam that stops `v_ϖ` from forking off `ForMathlib`'s additive-valuation API |
| `isTate_of_normedAlgebra` | **the bridge lemma** (no source): every norm-unital Banach algebra over a nontrivially normed field is Tate, via `ϖ = λ·1`. This is what makes the development subsume `[Buz07]` and `[Bel]` concretely rather than morally |
| `summable_of_tendsto_cofinite`, `bddAbove_range_norm_of_tendsto_cofinite`, `norm_tsum_le_iSup` | `[Bel]` §II.1.5 footnote. **Not in Mathlib** — PR candidate |

`ϖ` replaces the ground field of the field-based settings: every use `[Bel]` makes of `ℚ_p`
is a scaling argument, and the pseudo-uniformizer performs it verbatim (`[JN]`: "Buzzard's
`ρ`-trick with `ϖ` for `ρ`").

## 2. `01_OperatorNorm.lean` — the operator norm and the OMT

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

## 3. `02_Compact.lean` — finite-rank and completely continuous operators

`[Bel]` Definition II.1.3 and Lemma II.1.4; `[JN]` Definition 2.1.5; blueprint 6.13.

| Declaration | Source |
| --- | --- |
| `IsFiniteRank` | range contained in a finitely generated submodule |
| `IsCompletelyContinuous` | metric closure of the finite-rank operators |
| `IsFiniteRank.isCompletelyContinuous`, `opNorm_comp_le`, `isCompletelyContinuous_of_tendsto` | basic API |
| `IsFiniteRank.add`, `.comp_left`, `.comp_right`; `IsCompletelyContinuous.comp_left`, `.comp_right` | `[Bel]` Lemma II.1.4 — the two-sided ideal property |

## 4. `03_ModelSpace.lean` — the model space and orthonormalisability

`[Bel]` Definitions II.1.5–II.1.6 and Example II.1.7; `[JN]` Definition 2.1.5;
blueprint 6.3–6.6.

| Declaration | Source |
| --- | --- |
| `cSpace`, notation `c(I, R)` | `[JN]` Definition 2.1.5 — families `I → R` vanishing along the cofinite filter, sup norm. Realised as Mathlib's `C₀` on the discrete index `Ix I`, which supplies the metric and completeness for free |
| `tendsto_cofinite`, `norm_eq_iSup`, `norm_apply_le`, `evalCLM`, `single`, `hasSum_single` | the coordinate API |
| `IsONable`, `IsPotentiallyONable` | `[JN]` Def 2.1.5 / `[Bel]` Def II.1.5–II.1.6 — isometric (resp. merely homeomorphic) isomorphism to `c(I, R)`. Defined by an isomorphism, as `[JN]` do; the `ONBasis`-structure formulation and its equivalence live in the Bellaïche blueprint file |
| `HasPr` | `[Bel]` §II.1.6 / `[JN]` Def 2.1.5 — property (Pr): a direct summand of a potentially ON-able module |
| `IsONable.isPotentiallyONable`, `IsPotentiallyONable.hasPr`, `isONable_cSpace` | the implications between the three |

## 5. `04_Matrix.lean` — matrices, truncations, and the compactness criterion

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
and therefore lives in `05_Noetherian.lean`.

## 6. `05_Noetherian.lean` — the side branch: closedness of f.g. submodules

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

## 7. `05_Fredholm.lean` — the Fredholm determinant

`[Bel]` §II.1.5 architecture under `[JN]`'s hypotheses; blueprint 6.16–6.17. Definitions are
norm-free; the theorems take `IsCompactoid` hypotheses and carry **no** Noetherian
hypothesis, so each strictly generalises its `[JN]` counterpart.

| Declaration | Source |
| --- | --- |
| `minor`, `summable_minor` | the principal `S × S` minors and their summability (ultrametric Hadamard bound + row decay) |
| `charCoeff`, `charPowerSeries`, `charCoeff_zero` | `[Bel]` §II.1.5 / `[JN]` p. 67 — `cₙ = (−1)ⁿ ∑_{|S| = n} det(minor)`, and `det(1 − Tu) ∈ R⟦T⟧` with `c₀ = 1` |
| `charPowerSeries_isEntire` | `[Bel]` Lemma II.1.14 — the determinant is entire (`R{{T}}`): `PowerSeries.IsRestricted C (charPowerSeries u)` for every radius `C > 0`, so it lives in `PowerSeries.Restricted R C` for all `C` |
| `norm_charCoeff_sub_le` | `[Bel]` Lemma II.1.15 — `‖cₙ(u) − cₙ(v)‖ ≤ max(‖u‖,‖v‖)^{n−1}‖u − v‖`, the quantitative continuity powering every limit argument |
| `charCoeff_eq_det_coeff` | `[Bel]` equation (II.1.2) — agreement with the algebraic determinant for row-supported operators. Its proof needed the principal-minors expansion `det(1 − tA) = ∑_S (−t)^{\|S\|} det(A_S)`, **missing from Mathlib** — PR candidate |
| **`charPowerSeries_comm`** | `[Bel]` **Proposition II.1.17** — the **trace property** `det(1 − T·uv) = det(1 − T·vu)`. The primitive invariance statement: truncate, pass to the limit by `norm_charCoeff_sub_le`, conclude by the finite-matrix identity |
| `charPowerSeries_conj` | `[Bel]` Corollary II.1.18; `[Buz07]` Lemma 2.5 / Corollary 2.6 — conjugation invariance, formal from the trace property. This is what extends `det(1 − Tu)` to potentially ON-able modules |
| `charPowerSeries_extendZero` | `[Buz07]` pp. 72–73; `[Bel]` §II.1.6 — extension by zero; with `_conj`, gives well-definedness on modules with property (Pr) |

## 8. `06_Pr.lean` — lifting, projectivity, and [Bel] Proposition II.1.21

`[Bel]` Exercise II.1.19, Propositions II.1.20–II.1.21.

| Declaration | Source |
| --- | --- |
| `HasPr.exists_lift` | `[Bel]` Exercise II.1.19 — (Pr) as a lifting property along continuous surjections of Banach modules |
| `HasPr.projective` | `[Bel]` Proposition II.1.20 — finitely generated (Pr) modules are projective |
| `finite_of_one_sub_compact_nilpotent` | `[Bel]` Proposition II.1.21, finiteness half — **Noetherian-free since 2026-09-06** (`tate-riesz` board): a complete `P` carrying a compact `u` with `1 − u` nilpotent is finitely generated |
| `finite_projective_of_one_sub_compact_nilpotent` | `[Bel]` Proposition II.1.21 — if `P` has (Pr) and carries a compact `u` with `1 − u` nilpotent, then `P` is finitely generated and projective. The germ of Riesz theory |

## 9. `07_Residue.lean` — Serre's residue machinery

A sub-development feeding `isPotentiallyONable_of_uniformizer` in `08_BaseChange.lean`.
Source: `[Bel]` §II.1.4 (Hypothesis II.1.11, Lemma II.1.12, Theorem II.1.13, p. 58);
ultimately `[Serre]` Prop. 1. Internally labelled `R1`–`R7` by the decomposition pass.

| Step | Declarations | Content |
| --- | --- | --- |
| `R1` | `exists_norm_eq_zpow` | discreteness: the value group is `‖π‖^ℤ` (`[Bel]` p. 58) |
| `R2`–`R4` | `PowerBounded.subring K (S := ℤ)` (ForMathlib), `isUnit_of_norm_eq_one`, `isMaximal_topologicalNilradical` | the unit ball *is* the power-bounded subring (`PowerBounded.isPowerBounded_iff_norm_le_one`); its units are the norm-one elements, and its topological nilradical is maximal — the residue field, with no uniformizer and no discreteness needed |
| `R5` | `exists_residue_approx` | a quotient-free "residue basis" interface: norm-one vectors whose residues form a basis. Indexed by a subset of `E` (an `∃ ι : Type _` phrasing would bind a universe independent of `E`) |
| `R6a`–`R6b`, `R6` | `exists_expansion_of_residue_approx`, `expansion_unique_of_residue_indep`, `isONable_of_discrete_norms` | `[Bel]` Lemma II.1.12 — successive π-adic approximation (the analytic heart), uniqueness of expansions, and assembly: discrete norms ⟹ ON-able |
| `R7` | `rescale_nonneg`, `rescale_le_rescale`, `le_rescale_and_rescale_lt`, `rescale_add_le`, `rescale_smul` | `[Bel]` Theorem II.1.13's norm-rescaling step: replace the norm by an equivalent one with values in `‖π‖^ℤ` |

## 10. `08_BaseChange.lean` — changing the norm, base change, and the classical case

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

## 11. Later additions (2026-08-05 … 2026-09-06)

Modules added after the core tree was completed, each generalised out of (or built for) an
application board.  All sorry-free.

| Module | Provenance | Content |
| --- | --- | --- |
| `09_Riesz.lean` (~2,870 lines) | `tatefredholm-eigen` board, complete 2026-08-05/06 | `PowerSeries.evalT`/`hasseDeriv`, the Fredholm resolvent with Serre's recursion, `fredholmDet` and its multiplicativity.  **Ring level** (any Banach–Tate `R`): Serre Prop. 11 (`isUnit_one_sub_smul_iff_isUnit_evalT`) and the Riesz projectors (`exists_rieszProjection`).  **Field level** (complete ultrametric, discretely valued for the last three): zeros of `det(1 − Tu)` are reciprocal eigenvalues; the factorisation `H = (1 − a⁻¹T)^h · H'`; `finrank = order`; the full Riesz decomposition (Serre Prop. 12, `exists_riesz_decomposition`) |
| `06_BlockOp.lean` | moved from the Jacobs fork 2026-08-18 (forms boards) | operators on `c(σ × I, R)` from a `σ × σ` matrix of operators; Serre's partition lemma `det(1 − Tu) = det(1 − Tu′)·det(1 − Tu″)` and the block-diagonal product; `restrictOp`/`reindexOp` transport |
| `07_Conjugation.lean` | `lwx-seam` board, 2026-09-05 | diagonal intertwining `D·M_v = M_u·D` (unit diagonal, no inverse) preserves every principal minor, hence `charPowerSeries` with **no compactness hypothesis** (`charPowerSeries_eq_of_diag_intertwine`); `blockDiag`/`diagBlockEquiv`, the block-diagonal operators and equivalences of `c(σ × I, R)` used to conjugate `heckeBlockOp` by the Colmez basis change blockwise |
| `05_GenFun.lean`, `06_WeightGenFun.lean`, `00_Compose.lean` | Jacobs application layer, generalised out of the fork | operators from two-variable generating functions `H_A(x,y)` (`ofGenFun`, row decay `RowIntAt`); the character-free weight-action factors `linSeries`/`quadSeries`; analytic substitution `compAn` of a Möbius series with nonzero constant term |
| `04_TateAlgebra.lean` | forms boards | the identification `K⟨X⟩ = PowerSeries.Restricted K 1 ≃ₗᵢ c(ℕ, K)`, monomials as ON basis |
| `06_Slopes.lean` | `slopes-hecke` board A1/A2 (2026-08-20); exact case 2026-09-01 | row-weight Hadamard/minor bounds; **the slope bound** `‖cₙ(u)‖ ≤ σ^{f n}` for any row weight `w` and weight-sum lower bound `f`; the combinatorial inputs (`choose_two`, block weight `Σ_{k<n}⌊k/d⌋`); **the exact case** ([Jacobs, Thm 2.12] at an arbitrary `ϖ`): unit rescaled minors force `v_ϖ(c_m) = m(m−1)/2` |
| `HandClean/TateRings.lean`, `HandClean/PseudoUniformiser.lean` | hand-written seam | `IsTate` (the normed [JN] notion) implies Huber's topological `IsTateRing`; the `PseudoUniformizer.val` API over general normed rings |
| `10_Entire.lean`, `00_Resultant.lean`, `11_Coleman.lean`, `00_Charpoly.lean`, `12_RieszColeman.lean`, `11_SlopeFactor.lean` | `tate-riesz` board, 2026-09-06 | the **ring-level Riesz theory** ([JN] Thm 2.2.2 = [Buz07] Thm 3.3 = [Bel] Thm II.2.18): entire series and Euclidean division (`10_Entire.lean`), `Res(charpoly A, g) = det g(A)` (`00_Resultant.lean`), Coleman's `D(B, P)` and the spectral mapping `det(1 − T·B(u)) = D(B, det(1 − Tu))` (`11_Coleman.lean`), `charpolyRev` base change / Sylvester / unipotent matrices (`00_Charpoly.lean`), the Riesz–Coleman projector and its refinements — rank `deg Q`, `det(1 − Tu \| Ker Q*(u)) = Q`, `det(1 − Tu \| N) = S`, `Ker Q*(u) = range (1 − p)`, uniqueness of the complement, [JN] 2.2.13's decomposition core (`12_RieszColeman.lean`) — and the vertex factorisation `F = P·G` with relatively prime factors ([Bel] Thm II.3.6, `11_SlopeFactor.lean`).  **No Noetherian hypothesis anywhere**; the Gelfand-spectrum form of the slope conditions and [JN] §2.3 stay out of scope (the factorisation is stated at the norm level, `IsDominantIndex ρ`) |
| `06_Unitriangular.lean` | `lwx-seam-m` board, 2026-09-06 | **`IsUnitriangularPerturbation M q`** — entries of norm `≤ 1`, unit diagonal, below-diagonal entries of norm `≤ q < 1`, finitely supported columns — and the resulting **isometric** self-equivalence of `c(ℕ, R)` (`equivOfPerturbation`, `norm_ofPerturbation`).  Proved directly by a largest-index argument plus a successive-approximation surjectivity, so it needs **no discretely valued residue field**: it replaces Colmez's reduction-mod-`p` criterion (Astérisque 330, Prop 1.1.5) and works over any complete ultrametric field.  Used for Amice's theorem at analyticity level `h` |
| `08_BlockMap.lean` | `lwx-seam-m` board, 2026-09-06 | block operators between *different* fibres: `blockOpMap`, the block-diagonal `blockMap f : c(σ × I, R) →L c(σ × I', R)`, its composition laws with `blockOp` on either side (`blockMap_comp_blockOp`, `blockOp_comp_blockMap`), functoriality (`blockMap_comp`), and the induced equivalence `blockMapEquiv`.  `06_BlockOp.lean`'s `blockDiag` is the case `I = I'` (`blockMap_eq_blockDiag`).  Needed because the disc model `c(ℤ/pʰ × ℕ, K)` and the Mahler model `c(ℕ, K)` have different fibres |
| `06_TwoSidedBound.lean` | `lwx-halo` board, tranche E (2026-09-03) | minor-level **two-sided** Hadamard bound: for a matrix with `‖A_{a,b}‖ ≤ r(a)·s(b)` and `r·s`-summability, `‖minor‖ ≤ ∏ r·∏ s` (`norm_minor_le_pow_sub`), summability of the minor expansion without any `IsTate` hypothesis (`summable_minor_of_two_sided`), the characteristic-coefficient bound `norm_charCoeff_le_pow_two_sided`, and the monotone comparison `sum_comp_div_le_sum_monotone` — the engine behind [LWX] Theorem 3.16's halo estimate (`PhD/Main/LWX/04_Halo.lean`) |

---

## Notes for future work

**Mathematics still to do** (`00_Tate.lean`'s TODO comment still carries the pre-Riesz version
of this list): the single-zero Riesz theory of the 2026-07-30 note is **done** (`09_Riesz.lean`,
§11), and the Newton-polygon seam is consumed by `06_Slopes.lean` and the fork's
`5_EigenSlopes.lean` bridge (every finite NP slope of `det(1 − Tu)` is the valuation of a
reciprocal eigenvalue).  The **ring-level (family) slope theory** is now done as well (2026-09-06, `tate-riesz`
board): `[JN]` Theorem 2.2.2 — for `F = det(1 − Tu) = QS` with `Q` a multiplicative
polynomial coprime to `S`, `ker Q*(u)` is finitely generated projective of rank `deg Q`
with a unique `u`-stable closed complement, and `det(1 − Tu)` splits accordingly — is
`12_RieszColeman.lean`, proved **without any Noetherian hypothesis**, together with the
norm-level slope-`≤ h` factorisation (`11_SlopeFactor.lean`) and [JN] 2.2.13's decomposition
core.  It is applied to the halo `U_p` over `A = Λ^{>1/p}[1/T]` in `PhD/Main/LWX/05_TateRiesz.lean`.
What remains from `[JN]` §2.2–2.3: the *Gelfand-spectrum* form of the slope conditions
(slopes read pointwise on the Berkovich spectrum rather than through the norm), spectral
varieties (`[JN]` §2.3), and completed tensor products / the `⊗̂`-form of base change.

**Mathlib PR candidates** surfaced by this development: the Banach–Tate open mapping
theorem; the ultrametric summability criterion (`summable_of_tendsto_cofinite`,
`norm_tsum_le_iSup`); the principal-minors expansion `det(1 − tA) = ∑_S (−t)^{|S|} det(A_S)`;
the ultrametric Hadamard determinant bound.

**The three source blueprints** in `PhD/Main/Test/` (`CompactOperators.lean` for `[Buz07]`,
`CompactOperatorsBellaiche.lean` for `[Bel]`, `CompactOperatorsJohanssonNewton.lean` for
`[JN]`) are kept as source documentation, each with its own dictionary table and a section
explaining how its hypotheses differ. They are independent of this tree — do formalisation
work here, not there. `CompactOperatorsMerged.lean` is now only a re-export stub pointing
at this directory.

- **Ultrametric `tsum` sharpening (2026-09-05, lwx-slopes board):** `PhD/Main/LWX/05_Sharpness.lean` adds
  two general lemmas in `namespace TateFredholm` next to `norm_tsum_le_iSup`:
  `norm_tsum_lt_of_forall_lt` (a null family with every term `< B` has sum of norm `< B`) and
  `norm_tsum_eq_of_forall_lt` (unique dominant term ⟹ the sum has exactly its norm).  Both are
  Mathlib-free of project notions and are upstream candidates alongside
  `summable_of_tendsto_cofinite` / `norm_tsum_le_iSup`; they should move to `00_Tate.lean` when that
  batch is prepared.
