# Development Plan: `IsNewtonPolygonOf` — the Newton polygon as a lower convex hull

Started 2026-08-03. Predecessor project (Martin Weierstrass) archived in
`archive-2026-07-martin-weierstrass/`.

## Goal

A geometric specification predicate for the Newton polygon API in
`PhD/ForMathlib/NumberTheory/NewtonPolygon/`, with all new code in **`PhD/NewtonPolygons/`**
(user-designated folder, outside ForMathlib until PR-ready):

```lean
structure IsNewtonPolygonOf (v : ℕ → WithTop Γ) (P : NewtonPolygon₀ (Γ := Γ)) : Prop where
  start_le    : ∀ k : ℕ, (k : ℤ) < P.starting_point.1 → v k = ⊤
  start_mem   : ∃ k : ℕ, (k : ℤ) = P.starting_point.1 ∧ v k = (P.starting_point.2 : WithTop Γ)
  height_le   : ∀ k : ℕ, P.height k ≤ pointHeight v k
  isGreatest  : ∀ Q, Q.starting_point.1 = P.starting_point.1 →
                  (∀ k : ℕ, Q.height k ≤ pointHeight v k) → Q.IsBelow P
```

with (milestones):
- **Uniqueness** `IsNewtonPolygonOf.height_eq` (height-level; structure-level uniqueness is
  false — collinear splits — see decomposition.md L2),
- **Existence** `isNewtonPolygonOf_newtonPolygon₀OfSeq` under `∃ i, v i ≠ ⊤` and
  `IsAdmissible v` (both necessary; see L16),
- spec-level extraction lemmas that will replace the algorithm-driven geometry of
  `PhD/Test/test.lean` (`step_slope_le`, `firstBreak_slope_le`, `HasFirstBreak`, `IsPure`) in
  a later refactor (the refactor itself is OUT of scope for this board).

## References

- Blueprint `blueprint/src/chapter/NP.tex` (Definition 1 = the hull definition; the algorithm;
  purity). Verbatim quotes in `decomposition.md`.
- Koblitz GTM 58, Ch. IV §3–4 (cross-reference; statement shapes only).
- Design rationale + attack logs: `decomposition.md` (this board's source of truth for *why*
  each statement has its shape).

## Mathlib Inventory (searched 2026-08-03)

| Concept | Mathlib status | Action |
|---|---|---|
| Newton polygon | absent | this project |
| lower convex hull of a point set | absent | `IsNewtonPolygonOf` |
| discrete convexity / chord bounds for walked heights | absent (`ConvexOn.slope_mono_adjacent` is real-function-valued; bridging costlier than direct proofs) | `Height.lean` |
| `Set.Infinite.exists_gt`, `le_of_forall_pos_le_add`, `Finset.sum_range_succ`, `Nat.find_*`, `WithTop`/`WithBotTop` order API | present | USE |

## File structure (all new code in PhD/NewtonPolygons/)

- `Height.lean` — `unitSlope`, `vertexX`, `heightFun`, convexity + chord lemmas, domain
  lemmas. Imports ForMathlib `.../NewtonPolygon/Basic`. Algorithm-free.
- `Spec.lean` — `pointHeight`, `IsNewtonPolygonOf`, uniqueness, `unitSlope_zero_mul_le`,
  `IsPure`. Imports `Height`. Algorithm-free.
- `SpecConstruction.lean` — `IsAdmissible`, algorithm line bounds, walk correspondence,
  existence, power-series corollary, degenerate converses. Imports `Spec` + ForMathlib
  `.../NewtonPolygon/PowerSeries`.

Skeleton committed with `:= by sorry` everywhere; `lake build PhD.NewtonPolygons.SpecConstruction`
passes (37 sorries, no errors).

## Dependency graph

```
T001 vertexX/heightFun ─→ T002 walk corr. ─→ T003 unitSlope_mono ─→ T005 chords ─┐
                     └──→ T004 domain lemmas ─────────────────────↗              │
T006 pointHeight ─→ T007 uniqueness            T005+T006 ─→ T008 extraction ─→ T010 admissibility
T011 line bounds ──┐                                                             │
T012 ray approx ───┼─→ T014 walk corr. (constructed) ─→ T015 below ─┐            │
T013 anchors ──────┘                          T016 isGreatest ←─────┴─(T005,T012,T014)
T017 assembly (milestone) ← T013, T015, T016, CLEANUP-ALL-1
```

## Generality decisions

- Everything over `{Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ]` — matching the existing
  `NewtonPolygon₀`/Construction generality; no injectivity of `algebraMap` assumed anywhere
  (uniqueness is height-level precisely so this isn't needed).
- Spec is algorithm-free (imports only Basic) so it can be PR'd/reviewed independently of the
  construction.
- `IsAdmissible` quantifies over all points (not just the anchor): what the inductions
  consume, and implied by any affine lower bound (`isAdmissible_of_affine_bound`).
- Chord lemmas in division-free multiplied-out form to avoid `div` side conditions.

## Deferred / out of scope (recorded so nobody re-plans them silently)

- Structure-level uniqueness / canonical representatives (needs a no-collinear-splits
  canonicity notion; FALSE as-is, decomposition.md L2).
- Refactor of `PhD/Test/test.lean` §5.4–5.7 onto the spec (next board, after this one lands).
- Height-level `IsPure` (representation-independent purity) — only if the test.lean refactor
  turns out to need it.

## Execution

Workers run via `/beastmode`, one ticket at a time, per `tickets.md`. ChatGPT MCP not
configured this session — plan validation step skipped.
