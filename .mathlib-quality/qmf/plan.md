# Development Plan: Quaternionic modular forms of general weight (QMF)

**BOARD PATH: `.mathlib-quality/qmf/`** — all QMF board artifacts live here.  The default
`.mathlib-quality/` path is the parallel NewtonPolygon board (another agent): never read,
write, or archive it from QMF work.  Every `/beastmode` invocation for QMF must be told
this path explicitly.

## Goal
Formalise Buzzard's spaces of automorphic forms on a (totally definite) quaternion
algebra at general weight — [Buzzard, *Eigenvarieties*, §9] `L(U, A)`, the monoid
`Mₜ`/`Σ₀(γ)`, the classical weight modules `L_{n,v}`, Hecke operators `[UηU]`, and the
class-set decomposition `L(U,A) ≅ ∏_λ A^{Γ_λ}` — as a two-layer library in `PhD/QMF/`:
an abstract layer (group + submonoid + monoid-module; no topology, no arithmetic) and an
FLT-style quaternionic instantiation.  Weight 2 with trivial coefficients recovers the
FLT picture (bridge lemma).  End state of this tranche: skeleton fully proved (no
sorries), cleanup-clean.  Follow-on tranches (recorded as API gaps AG1–AG3 in
decomposition.md): overconvergent `A_{κ,r}` + property (Pr) + `U_π` compactness
(TateFredholm hookup), Fujisaki port, multi-place `p`.

## Conventions
- LEFT actions throughout (Loeffler Def 3.3.2 shape); dictionary to Buzzard's right
  modules via the adjugate anti-isomorphism — see decomposition.md "Handedness".
- FLT mock-up style: definitions typecheck for `[Ring D] [Algebra F D]` +
  `RigidificationAt F D v`; real hypotheses (totally real, totally definite, split at
  `v ∣ p`) only ever on theorems that need them.  No central-character field.
- `PhD/QMF/FLTstuff/` = vendored FLT files.  Existing copies (Basic, HeckeOperators/*,
  InnerProduct, FiniteDimensional) are REFERENCE-ONLY (imports `FLT.*`, do not compile
  here).  User authorised porting needed FLT files into FLTstuff (classic headers,
  imports rewritten to `PhD.QMF.FLTstuff.*`, v4.32→v4.33 fixes).  New QMF files must not
  import non-compiling FLTstuff files.
- **NO lake dependencies beyond mathlib (+ checkdecls/doc-gen4) — user directive
  2026-08-03.  All FLT reuse is by porting lines into this repo, never by `require`.**

## Mathlib / FLT inventory
| Concept | Status | Action |
|---|---|---|
| `MulAction.fixedPoints`, `DoubleCoset.Quotient`, `Quotient.mk''` | mathlib | USE |
| `FixedPoints.submodule` | FLT only | VENDORED into HeckeMonoid.lean |
| Abstract Hecke (group case) | FLT `AbstractHeckeOperator` | GENERALISED to submonoid (HeckeMonoid.lean); FLT proofs are the template |
| `FiniteAdeleRing` (= restricted product), `RestrictedProduct.evalRingHom`, `adicCompletion`, `Valued` | mathlib | USE |
| `MvPolynomial.homogeneousSubmodule`, `aeval` | mathlib | USE |
| Fujisaki `finiteDoubleCoset` | FLT (Buzzard–Coram) | PORT later (T016), nothing here depends on it |
| DoubleCoset extensions (`mk`, `σ`-sections, `ofLeft`…) | FLT (Coram–Buzzard–Yang) | PORT (T015) to get the canonical (section-free) decomposition |
| Rigidification | FLT global `WithRigidification` | NEW local-at-`v` `RigidificationAt` (weaker: split at `v` only) |

## File structure (skeleton built 2026-08-03, `lake build PhD.QMF.Quaternionic` green)
```
PhD/QMF/HeckeMonoid.lean          -- FixedPoints.submodule, fixedPointsOfLE, [UgV] for Δ ≤ G
PhD/QMF/AutomorphicFunction.lean  -- structure, Δ-action, levelSubmodule = L(U,A), level Hecke
PhD/QMF/Decomposition.lean        -- stabilizerAt (Γ_λ), evalAtReps, Buzzard's iso, wt-2 bridge
PhD/QMF/Sigma0.lean               -- Σ₀(γ) over any Valued field, detUnits, eta (U_ϖ element)
PhD/QMF/WeightModule.lean         -- matrixSubst, detChar, WeightModule R n ν (L_{n,v})
PhD/QMF/Quaternionic.lean         -- Dfx, globalUnits, toMatrix, levelMonoid, QMF.Space, Hecke
```

## Dependency graph
```
T001,T002 → T003 (Hecke core)      T005 → T006 → T007 (space)      T011 (Σ₀)   T012 → T013 (weights)
T004 (cpt-open finiteness, indep)  T007+T001 → T008 → T009 → T010  T011+T013 → T014 (global)
T015 (DoubleCoset port, indep)     T009+T014 → T018 (milestone)    T014(+mulSingle) → T017 (U_ϖ elt)
T016 (Fujisaki port, indep, large, user-priority decision)
```

## Generality decisions
- Abstract layer: arbitrary `[Group G]`, `Submonoid Δ`, `[AddCommMonoid A]`,
  `[DistribMulAction Δ A]`, semiring `R` with `SMulCommClass` — mathlib-grade; candidate
  for FLT-upstreaming (names kept FLT-compatible where vendored).
- `Sigma0` over any `Valued K Γ₀` field with threshold `γ < 1` (Buzzard's `v(π)^t` is a
  special case); `γ < 1` is necessary (counterexample recorded in decomposition.md L3.1).
- Weight module over any `CommRing R` with `Algebra K R`; abstract character
  `ν : Σ₀ →* Rˣ` (Buzzard's `det^v` = `detChar`).
- Single place `v`; `v ∣ p` never assumed in definitions (irrelevant to them).

---

# AG-B tranche (opened 2026-08-05): the `U₃` identification

**Goal**: `Jacobs.U3.heckeU3_apply_classRep` (unconditional block-matrix identity) +
`eval_classRep_injective` (completeness, under `HClassNumberOne`) — discharging the
identification debt of `PhD/Jacobs/U3Data.lean`.  Full decomposition (prose proofs,
verbatim quotes, attack logs): `decomposition.md` "AG-B tranche".

**Code home** (user decision 2026-08-05): Jacobs-specific files in `PhD/Jacobs/U3/`
(Setting, KappaAction, Hurwitz, Level, ClassSet, EtaDecomposition, Factorisations,
Matrix); the generic matrix-recipe lemma in `PhD/QMF/HeckeMatrix.lean`.  Skeleton green
(3594 jobs, sorries only).  Build: `lake build PhD.Jacobs.U3.Matrix` (pulls the chain).

**Mathlib inventory** (verified at this rev): `ℍ[ℚ]` division ring ✓ USE;
`hensels_lemma` ✓ USE; `Rat.HeightOneSpectrum.primesEquiv` + `ℚ_[p]`-comparison ✓ USE;
`NormedField (adicCompletion K v)` ✓ USE; Hurwitz order ✗ DEFINE (mathlib-native
`Subring ℍ[ℚ]`; FLT's standalone structure deliberately NOT ported — its (1.4.4) is
itself sorried); noncommutative Euclidean/right-PID ✗ DEFINE (concrete, no typeclass).

**Sub-tranches** (dependency order; B-LOC ∥ B-GLOB ∥ B-CN1 largely parallel):
- **B-LOC** (local analysis): Σ₁(9), κ-action, action laws, Prop 2.6 — `KappaAction`,
  parts of `Setting`.
- **B-SET** (instantiation): K₃ pack, ν₃, θ₃ — `Setting`.
- **B-GLOB** (global data): Hurwitz order+units, U₀(1)/U₁(9), Thm 2.1 computation,
  Lemma 2.2, Lemma 2.3, the nine certificates — `Hurwitz`, `Level`, `ClassSet`,
  `EtaDecomposition`, `Factorisations`.
- **B-CN1** (class number one): Euclidean → principal → idelic dictionary →
  `hClassNumberOne` — `Hurwitz`, `Level`.  **DEFERRED (user 2026-08-05)**: FLT states
  the same lemma (`completed_units`) and is expected to cover it — not ours to fill
  yet; B06/B18 sit deferred until FLT's proof lands (then: port + re-audit).
  Everything else takes `HClassNumberOne` as an explicit hypothesis, so the tranche
  completes to its accepted end state without B-CN1.
- **B-MTX** (assembly): generic recipe + blocks + endpoint — `HeckeMatrix`, `Matrix`.

**Generality decisions**: concrete `K₃`/`v₃`/`D` throughout (the abstract-K κ-theory and
general quaternion orders are recorded /generalise candidates, NOT this tranche);
left-action convention per the QMF library; `Σ₁(9)` (not `Σ₀`) as the acting monoid —
κ needs the 1-unit entry, Teichmüller-twisted κ deferred.

**Risks (named)**: L6.5 idelic dictionary (largest single leaf; ticket carries its own
sub-plan and a fallback to line-by-line Voight 27.6.8); determinant-twist normalisation
at L4.3 (b2-precedented, amendment-not-patch rule recorded); v4.33 instance-path seams
(θ₃ instance, board-precedented); left-convention data tables recomputation (L4.1).
