# Development Plan — `lwx-theta` (the theta layer and the two assemblies)

**BOARD PATH: `.mathlib-quality/lwx-theta/`.**  The default `.mathlib-quality/` board is the
completed NewtonPolygons project — never touch it.  Every `/beastmode` run must name this board
path explicitly.  Planned 2026-09-06.

## STATUS: COMPLETE (2026-09-10)

All dispatchable tickets are done; `PhD/LWX/{Theta,StepOne,Degrees,AtkinLehnerInst,Bol,Touching,
ClassicalPoint,StepThree}.lean` are sorry-free and `lake build PhD` is green.  The milestones are
`LWX.isStepOneTouching_of_atkinLehnerHypothesis` (Step I, granted **H1**) and `LWX.degX_succ`
([LWX, Thm 1.3]'s degree formula, granted **H1 + H2**).  Two general API files were factored out
of the work — `PhD/TateFredholm/NewtonSlopes.lean` and `PhD/NewtonPolygons/RootFaces.lean`.
See `tickets.md`'s Summary for the full record, including the second B2 (S7.10) and its repair.

What is **not** proved and never was in scope: **H1** (`AtkinLehnerHypothesis`, [LWX, Prop 3.22])
and **H2** (`IsThetaExact`, the theta sequence's right-exactness).  The remaining open tickets are
`B8`, `T-AG5`, `AG-ζ`, `AG-ω₀` — all design/API gaps that need a source or a decision, not work.

**Follow-up board (planned 2026-09-10): `.mathlib-quality/lwx-theta-h2/`** discharges H2 from the
classical shapes and constructs `TargetData` at the classical points (closing `AG-ζ`); see its
`plan.md`.

## Goal

Board two of the LWX Step I / Step III development.  Three tranches:

1. **The shared theta layer** — the theta operator on the disc model, the identification of
   `ker θ^{k+1}` with the classical subspace, the dimension formula [LWX, (3.21.1)], the weight
   equivariance and the `U_p` intertwining.
2. **Step I** — classicality [LWX, Prop 2.15], then the squeeze against the completed Corollary
   3.18 lower bound, discharging `HasUnitBand` in `PhD/LWX/Vertices.lean`.
3. **Step III** — Hida's Corollary 3.21 at the coefficient level, and the degree bookkeeping.

**Scope as of 2026-09-06 (revised).**  Tranche 1, the seams, and the equivariance/intertwining
are fully ticketed (the latter designed in a dedicated pass).  Of tranche 2, everything whose
shape does not depend on the two remaining gaps is ticketed in `StepOne.lean`: Step I's conclusion
as a named definition, its bridge to Step II, Buzzard's small-slope argument in the abstract, and
the global dimension formula.  Of tranche 3, the Hida input at the coefficient level is ticketed
in `Degrees.lean`.  Still unticketed, and honestly so: everything downstream of T-AG3 (Newton
polygon of a product) and T-AG4 (Atkin–Lehner instantiation) — the converse half of classicality,
the squeeze itself, the control statement `ordDim = slope-zero dimension`, and the degree
formulas.  T-AG4 was expanded on 2026-09-09; the remaining gaps are T-AG3 and T-AG5 (H1a).

## Jacquet–Langlands dependencies (standing requirement)

**The per-result audit is `.mathlib-quality/lwx-stepone/JL-AUDIT.md`; read it before working any
ticket.**  For this board:

- **Tranche 1 has no Jacquet–Langlands dependency at all.**  [Bu04, Prop 4]'s first sentence (the
  kernel characterisation) and [LWX, (3.21.1)] are elementary; so are Buzzard's well-definedness
  identity and Hecke relation (he calls both "elementary to check").
- **Tranche 2 imports only the Jacquet–Langlands-free half of [Bu04, Prop 4]**, the passage at
  `references/bu04.txt:1125–1129`.  Its converse half at `bu04.txt:1122–1124` explicitly uses
  "Theorem 4.6.17 of [15], the fact that λ is an algebraic integer, and **the Jacquet-Langlands
  theorem**", and is **never imported**: leaf L2.4 derives the converse from hypothesis H1 plus
  non-negativity of slopes.  This is why classicality is not a hypothesis of this development.
- **Tranche 3's Hida input is taken at the coefficient level** and is Jacquet–Langlands-free;
  [LWX]'s own proof of Theorem 3.19 is a Newton-polygon argument on the characteristic series.
- **Neither hypothesis is a Jacquet–Langlands issue.**  H1 is now *available* rather than assumed
  at the reduction level: `LWX.roots_charpoly_atkinLehner` (board `lwx-atkinlehner`, complete
  2026-09-06) gives [LWX, Prop 3.22] in multiset form granted the operator identity, and that
  identity is being worked in `PhD/Test/AtkinLehnerIdentity.lean` (Step 1 of it is already
  proved).  H2 is right-exactness of the theta sequence, which [LWX] cites at `lwx.txt:2049` to
  Jones's BGG analogue — locally analytic representation theory, **not** Jacquet–Langlands.
  Recorded so no worker misfiles it.

## References

- **[LWX]** Liu–Wan–Xiao, arXiv:1412.2584v4; text at
  `.mathlib-quality/tate-riesz/references/lwx.txt`.  Prop 2.15 at `lwx.txt:913–920`; (3.21.1) at
  `lwx.txt:1755–1760`; Step I at `lwx.txt:1807–1846`; Step III at `lwx.txt:2014–2088`.
- **[Bu04]** Buzzard, *On p-adic families of automorphic forms*; text at
  `.mathlib-quality/lwx-stepone/references/bu04.txt`.  The theta operator at `bu04.txt:1050–1070`;
  well-definedness at `1074–1090`; the Hecke relation at `1095–1100`; Prop 4 at `1105–1129`.
- `.mathlib-quality/lwx-stepone/JL-AUDIT.md` — the plan of record and the audit.
- `.mathlib-quality/lwx-atkinlehner/` — board one, complete; supplies H1's reduction.

## Mathlib and project inventory

| Concept | Status | Our action |
|---|---|---|
| the disc model `c(ZMod (p^h) × ℕ, K)` | project: `PhD/LWX/DiscModel.lean`, sorry-free | USE |
| disc-model forms and `U_p` | project: `PhD/LWX/DiscForms.lean`, sorry-free | USE |
| [LWX, Prop 2.17] seam at every level | project: `SeamH.lean:401`, sorry-free | USE |
| operator from a coefficient matrix | project: `TateFredholm.ofCoeffs` (`GenFun.lean:178`) | USE |
| block-diagonal operator | project: `TateFredholm.blockMap` (`BlockMap.lean:41`) | USE |
| Cor 3.18 lower bound | project: `lwx-halo` board, complete | USE (tranche 2) |
| `HasUnitBand` + the touching bridge | project: `Vertices.lean:69`, `:769`, sorry-free | TARGET (tranche 2) |
| H1 in multiset form | project: `LWX.roots_charpoly_atkinLehner`, sorry-free | USE (tranche 2) |
| the theta operator | not in mathlib, not in project | **DEFINE** (tranche 1) |
| locally polynomial of degree ≤ k | not in mathlib, not in project | **DEFINE** (tranche 1) |

## File structure

- `PhD/LWX/Theta.lean` — tranche 1.  **New**, already skeletoned and building.
- `PhD/LWX/ConjChar.lean` — tranche 1b, the conjugate nebentypus.  **New**, skeletoned.
- `PhD/TateFredholm/FiniteFactor.lean` — tranche 1b, the finite factor of a Fredholm determinant.
  **New**, skeletoned.  General enough to be a future mathlib contribution.
- `PhD/LWX/StepOne.lean` — tranche 2, the stateable part.  **New**, skeletoned and building.
- `PhD/LWX/Degrees.lean` — tranche 3, Hida's input at the coefficient level.  **New**, skeletoned.
- `PhD/LWX/AtkinLehnerInst.lean` — the Atkin–Lehner instantiation: `θ` on the block model,
  `U_p`-stability of the classical subspace, the genuine matrices, and **H1 named on them**
  (`AtkinLehnerHypothesis = H1a ∧ H1b`).  **New**, skeletoned.

No file on this board is owned by another board: `lwx-seam-m`, `tate-riesz` and `lwx-atkinlehner`
are all complete, and none owned these paths.  The only other live sentinel is `qmf/`, whose files
are `PhD/QMF/*` and `PhD/Jacobs/*` — disjoint.

## The three connecting seams (added 2026-09-06)

Reviewing the board against what Step I actually consumes surfaced three pieces that no board
covered.  Two turned out to be independent of the theta layer and are now skeletoned and ticketed;
the third and a fourth are API gaps.

1. **The conjugate nebentypus** (S1, S2).  Step I applies the lower bound at a character *and its
   inverse*, and no `ω⁻¹` existed anywhere.  A planning correction made this small: `UpDatum`
   carries only the coset data, and the character enters at `UpDatum.matrix D ω`, so the same datum
   serves both characters.  All that is needed is the definition and its API.
2. **The finite factor of a Fredholm determinant** (S3).  Step I compares the slopes of the
   finite-dimensional classical piece with an initial block of the whole space's slopes.  The
   algebraic half — that the determinant genuinely factors, with the classical piece a polynomial
   of the right degree — composes two existing sorry-free project lemmas.
3. **The Newton polygon of a product** (T-AG3, API gap).  The *ordering* half of the same
   comparison: that the finite factor supplies the *initial* segment.  A grep over
   `PhD/NewtonPolygons/` finds no product or Minkowski-sum lemma; the building blocks
   (`unitSlope`, `heightFun`, `IsNewtonPolygonOf`) do exist.
4. **Instantiating the Atkin–Lehner reduction** (T-AG4 → expanded 2026-09-09).  The design pass
   found this is two things.  Pinning the genuine matrices and discharging H1 to the multiset
   pairing is stateable and is now ticketed (AL0–AL5).  *Constructing* the conjugation is hypothesis
   **H1a** and is the gap **T-AG5**: the Atkin–Lehner element is not in `M1` (its bottom-right entry
   is `0`, and `M1` needs a unit there) and does not preserve `ℤ_p`, so it has no action on the disc
   model at any level.  It acts only on the finite-dimensional classical subspace, through `Sym^k`.
   That construction is board-one-sized and independent of the theta tickets: recommended as its
   own board.

## Dependency graph

```
L1.1 thetaOne ──► L1.2 thetaDisc ──► L1.3 thetaDisc_apply ─┬─► L1.4 thetaDisc_zero
                                                            └─► L1.6 kernel = locPoly
L1.5 locPolyDegSubmodule ──────────────────────────────────┴─► L1.7 finrank

L1.3 + L1.5 ──► T-AG1a ──► T-AG1b ──► T-AG2 (U_p intertwining)  ──► T-AG4 (AL instantiation)
                                          │                            │
S3 (finite factor) ──► T-AG3 (polygon of product) ──► L2.6/L2.7 squeeze ◄┘ ──► SO0 IsStepOneTouching
SO2 (abstract small-slope) + T-AG2 ──► classical_of_slope_lt ──────────────────┘        │
SO4 (global (3.21.1))                                                                    ▼
S1 (invChar)                                                                  SO1 ──► HasUnitBand
D0–D3 (ordDim) ──► [T-AG3] ──► ordDim_eq_slopeZeroDim ──► Step III degree formulas (+ H2)
```

## Generality decisions

1. **The `p^{−hr}` scalar is not baked into `thetaDisc`.**  `d/dz = p^{−h} d/dw`, and carrying the
   scalar inside the operator would force a `p`-invertibility side condition into every statement
   about it.  It is a scalar; it multiplies at the call site.
2. **`thetaDisc` is `blockMap` of a single-disc operator**, not an `ofCoeffs` on the product index.
   Differentiation does not mix discs, so block-diagonality is the honest shape, and it lets the
   whole construction reuse the ℕ-indexed `ofCoeffs`.
3. **`finrank_locPolyDegSubmodule` is the local half of (3.21.1)**, without the class-number factor
   `t`.  The `t` enters once, in tranche 2's assembly over the block index.  Recorded because a
   reviewer could otherwise read the leaf as claiming the source's global formula.
4. **`CharZero K` is load-bearing exactly once**, in L1.6: over a field of characteristic `p ≤ k+1`
   the multiplier `(j+1)⋯(j+k+1)` can vanish and the kernel would be strictly larger.  The
   adversarial pass ran that attack; the hypothesis stays.
5. **Step I's conclusion becomes a named definition** (`IsStepOneTouching`, leaf L2.8) so that
   tranche 3 consumes it as a statement rather than as a project — the split point at which
   tranche 3 can become a third board run concurrently.

## Planning-pass notes

The first attempt built `thetaDisc` directly with `ofCoeffs` on the product index; `ofCoeffs` is
ℕ-indexed, so that failed to elaborate and was replaced by the `blockMap`-of-`thetaOne` shape,
which is also the mathematically honest one.  Two placeholder `True`-valued declarations for the
equivariance and the intertwining were drafted and then **removed**: a `True` stand-in reads as a
discharged obligation.  They are AG1 and AG2 instead.

**Review of 2026-09-06 (this pass).**  Rebuilding all five files and re-deriving the equivariance
against [Bu04, Prop 4]'s eigenvalue sentence found the determinant factor on the **wrong side** of
all three equivariance statements: the source says `θ f` has eigenvalue `λ/p^{k−1}`, divided,
which forces `θ ∘ U_p = p^r • (U_p ∘ θ)`; the draft had the opposite.  Confirmed by direct
differentiation at `r = 1`, weight `2`.  All three statements and their tickets were corrected, and
the check is now recorded in T-AG1a so no worker re-derives it.  The same review found the
ticketed line numbers had drifted by an added import; corrected.

No ChatGPT second opinion was obtained: the `chatgpt-math` MCP server failed to connect this
session.

## `/beastmode` session of 2026-09-09 — outcome, and the one design defect it found

**Everything dispatchable is closed.**  D1a/D1b/D1c (new sub-tickets), D1–D3, AL1a (new
sub-ticket), AL1, AL4, AL5, and CLEANUP-4 through CLEANUP-10 all landed sorry-free with standard
axioms; S1–S3 and SO1–SO4 were already proved and only needed their board statuses restored.
`runLinter` is clean on all six files (it caught two unused instance arguments that nothing else
did: `[Nonempty ι]` on `AtkinLehnerHypothesis`, and `[DecidableEq I] [DecidableEq I']` on
`blockMap_apply_prod`).  The six modules were added to `PhD.lean`.

**The defect.**  The 2026-09-06 design pass got two things right — the exponent `m = r + 1`, and
the side the determinant sits on — and one thing wrong.  It introduced a *common finite part*
`ν : UK →* Kˣ` so that `κ = x^{r+1}ν` and `κ' = x^{1−r}ν`, reasoning that a nebentypus should be
allowed to ride along.  But `kappaSlash` differentiates `κ(cz + d)` as a *power series in z*, and a
bare `MonoidHom` has no local-constancy: `d/dz[ν(cz+d)]` is not zero, and the extra term it
contributes has no counterpart on the right.  [Bu04, §7]'s display carries no nebentypus factor at
all, which is the tell we should have read off the source.  Deleting `ν` repairs all five
statements; the sketches are otherwise untouched.

The lesson worth carrying to the next board: **when a source's displayed identity omits a factor
the formalisation could carry, that omission is data.**  Check whether the factor is
differentiated by the operator in play before letting it into the hypotheses.

## Tranche 4 (same session): the repair, built rather than deferred

The B2 blocks five *ticketed signatures*, but the mathematics the repair needs is forced by the
source and independent of how the user words the fix, so it was built as new declarations in a new
file `PhD/LWX/Bol.lean` (plus two theorems in `AtkinLehnerInst.lean`).  Twelve tickets B1–B12, all
sorry-free with standard axioms, `runLinter` clean.

**The mathematical find.**  Buzzard's display is classically **Bol's identity**, and column by
column against `QMF.WeightSeries.yCoeff_genFun` it is a one-variable power-series statement.  The
crucial move was the parametrisation: writing the column index as `i = j + r` and stating

`∂^r (u^{j+r} · (L⁻¹)^{j+1}) = D^r · (j+r)_r · u^j · (L⁻¹)^{j+r+1}`,  `u = numX γ`, `L = linX γ`,

makes the statement subtraction-free and the induction on `r` (with `j` generalised) close on the
nose: one derivative gives two terms, the induction hypothesis applies to them at `j` and at
`j + 1`, and `Nat.succ_descFactorial_succ` / `Nat.descFactorial_succ` make both coefficients
`(j+r+1)_{r+1}`, leaving `C a·L − C c·u = C (det γ)`.  **A first plan that went through iterated
Leibniz plus a binomial identity was abandoned once this parametrisation was found** — neither is
needed, and the whole proof is about forty lines.

**Why the corrected statements are phrased against `autFactor`.**  Going from
`κ.toChar u = u^{r+1}` to `autFactor κ g = L^{r−1}` needs an `ExpansionData` for an *integer* power
of the identity character on an arbitrary subgroup; `QMF.algExpansionData` only covers exponents
`≥ 2` on `⊤`.  That construction is ticket B8, deferred with its design step named.  Stating the
equivariance against `autFactor` keeps the analytic content separate from the bookkeeping and is
what the disc and block versions consume anyway.

## User decision, 2026-09-09: the five false statements were removed

Asked to choose between repairing the ticketed signatures and retiring them, the user retired
them: "can you remove the false statements now - as I assume the corrected forms are all that we
need."  `thetaOne_comp_kappaSlash`, `thetaDisc_comp_discSlash` and `thetaDisc_comp_discHeckeBlock`
were deleted from `PhD/LWX/Theta.lean` (with the whole `Equivariance`/`Intertwining` section
scaffolding), and `thetaBlock_comp_discHeckeBlockOp` and
`mem_locPolyDegSubmoduleBlock_discHeckeBlockOp` from `PhD/LWX/AtkinLehnerInst.lean`.  Nothing
depended on them — the only references were docstrings, all now rewritten to point at the
`_of_autFactor` forms.  Tickets T-AG1a, T-AG1b, T-AG2, AL2, AL3 are marked RETIRED; the
counterexample stays on record in `b2_log.jsonl` and in the module docstrings, so the mistake
cannot be made twice.

**The board's Lean surface is now sorry-free.**

## `/develop --continue` of 2026-09-09: tranches 5–7 (Steps I and III)

Three new files, skeletoned and building:

```
Touching.lean (tranche 5, Step I)
  T5.1–T5.5  polygon of a product ≤ factor; determinants under H1
  T5.6–T5.9  classical subspace is U_p-stable from the shape (no theta)   ──► classicalMatrix
  T5.10–T5.18 finite factor: charPowerSeries U_p = R · charpolyRev(coordinate matrix)
  T5.19      height(n_{k+1}) ≤ −log‖det A‖                                (Minkowski)
  T5.20–T5.22 Cor 3.18 lower bound; (3.23.1)
  T5.23 ★    IsStepOneTouching, granted H1  ──► T5.24 HasUnitBand ──► lwx-slopes unconditional

ClassicalPoint.lean (tranche 6)
  C6.1–C6.3  ‖ζ−1‖^{p−1} = ‖p‖ ;  C6.4–C6.10 halo conditions, T'_1, s_1 = k ;
  C6.11–C6.14 the halo weight at T_{χ_k} has the classical shape ──► ClassicalData

StepThree.lean (tranche 7, Step III)
  S7.1 (AG-Z) zeros along the polygon ;  S7.2/S7.3 Cor 3.21 = ordDim (unconditional)
  S7.4/S7.5  bands = faces ;  S7.6 (needs G1) intertwining ;  S7.7 ‖U_p‖ ≤ 1
  S7.8/S7.9  complement slopes ≥ k+1 ;  S7.10/S7.11 classical faces + AL reflection
  S7.12      left gap = ordDim ω'   ;  S7.13 right gap = ordDim ω₁ (H2)
  S7.14–S7.16 ★ degree formulas
```

Design decisions of this pass (details and attack logs in `decomposition.md`):
1. Step I uses the Minkowski *upper* bound instead of classicality; classicality is a corollary.
2. The finite factor uses the one-sided `v·w = 0` splitting; the coordinate truncation does not
   commute with `U_p`, so S3's commuting form is not applicable (it stays as general API).
3. The classical subspace's stability is proved from the weight's shape directly (mirroring
   `QMF.polySubmodule_stable`), not through the theta target.
4. Nebentypus constants: the `_of_autFactor` equivariance is generalised in place (G1); the
   classical shape carries constants `u`; Step III demands the target's constants to match
   (`TargetData`), and identifying them is the design gap AG-ζ.
5. H2 enters as `IsThetaExact`, a determinant identity, exactly where the source says "by the exact
   sequence".
6. The twisted characters `ω⁻¹ω₀^{2k}`, `ωω₀^{−2k−2}` are parameters of the theorems; spelling
   them needs the Teichmüller character (AG-ω₀).  `invChar` (S1) is the `k = 0` case.
